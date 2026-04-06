/**
 * bentdecode_sweep.cpp
 * By Mohammed Al-Anezi
 *
 * Bent Function SAT Encoder + Decoder: (n, d) sweep variant.
 *
 * Runs the bent function search for every pair (n, d) with
 *   1 <= n <= MAX_N  and  1 <= d <= n,
 * iterating in the order (1,1), (2,1), (2,2), (3,1), (3,2), (3,3), ...
 * A fresh CaDiCaL solver is created for each pair.  Results are printed
 * to stdout so the entire run can be captured with:
 *
 *   ./bentdecode_sweep > results.txt
 *
 * Note: bent functions exist only for even n.  Odd-n trials will return
 * UNSAT and are included so the log is complete.
 *
 * Key optimisations (same as bentdecode_truncated.cpp):
 *
 *   1. Phase variable elimination: s_{x,ω} is not materialised as a SAT
 *      variable; the correct F_x / ¬F_x literal is passed directly to the
 *      cardinality encoder.
 *
 *   2. Flat counter arrays: the sequential-counter table s[i][j] is a
 *      single contiguous int[] of known size (n+1)*(k+1).
 *
 *   3. Fixed-size Walsh literal buffer: zero_lits[N_MAX] is on the stack;
 *      N_MAX = 2^MAX_N is the compile-time upper bound.
 *
 *   4. Optimised forced-cardinality clauses: reverse-propagation clauses
 *      omitted for j > minimum (matches encode.py exactly).
 *
 *   5. O(1) parity via __builtin_parity.
 *
 *   6. O(1) ANF monomial containment via precomputed bitmasks.
 */

#include <iostream>
#include <vector>
#include <string>
#include <map>
#include <chrono>
#include <cstdlib>
#include <cstring>
#include <cstdio>
#include <cassert>
#include <functional>
#include <algorithm>
#include <memory>
#include <csignal>
#include <unistd.h>   // for alarm()

#include "cadical.hpp"

// Configuration: edit these to change the sweep bounds
#define MAX_N          8   // sweep n from 1 to MAX_N (inclusive)
#define MAX_D          8   // sweep d from 1 to min(n, MAX_D) (inclusive)
#define NORMALIZE      1    // 1 = fix f(0) = 0 for every trial
#define SYM_BREAK      1    // 1 = enforce a1 <= a2 <= ... <= aN on linear terms
#define MAX_ANF_WEIGHT 0    // max non-zero ANF coefficients, excl. constant (0 = no limit)

#define TRACK_TIME     1
#define PRINT_TIME     1

#define MAX_SOLVER_SECONDS 3600   // 60 minutes per trial

// Compile-time upper bound on 2^n.
// zero_lits[N_MAX] is stack-allocated once and reused across all trials.
#define N_MAX          (1 << MAX_N)

using namespace std;

// Globals: reset between each (n, d) trial via resetGlobals()
#if TRACK_TIME == 1
double g_enc_anf_time       = 0.0;
double g_enc_tt_time        = 0.0;
double g_enc_walsh_time     = 0.0;
double g_enc_norm_sym_time  = 0.0;
double g_solve_time         = 0.0;
double g_decode_time        = 0.0;
#endif

static CaDiCaL::Solver* volatile g_timeout_solver = nullptr;
static volatile sig_atomic_t g_timeout_occurred = 0;

extern "C" void timeout_handler(int) {
    g_timeout_occurred = 1;
    if (g_timeout_solver) {
        g_timeout_solver->terminate();   // tell CaDiCaL to stop
    }
}

// Clause counters indexed by clause length (0 = unit, 1 = binary, 2 = ternary).
static unsigned long long g_clause_count[3] = {0, 0, 0};

/**
 * @brief Resets all global timing and clause-count accumulators to zero.
 * Must be called before each (n, d) trial so per-trial statistics are clean.
 */
static void resetGlobals() {
#if TRACK_TIME == 1
	g_enc_anf_time      = 0.0;
	g_enc_tt_time       = 0.0;
	g_enc_walsh_time    = 0.0;
	g_enc_norm_sym_time = 0.0;
	g_solve_time        = 0.0;
	g_decode_time       = 0.0;
#endif
	g_clause_count[0] = g_clause_count[1] = g_clause_count[2] = 0;
}

// Bit-level helpers
/**
 * @brief Computes popcount(v) mod 2 using a bit-opeartion, O(1).
 *
 * @param v Input integer.
 * @returns 0 or 1.
 */
static inline int parity(int v) {
    return __builtin_parity(v);
}

static inline int safe_pow2(int exp) {
    return (exp < 0) ? 0 : (1 << exp);
}

// SAT clause helpers (match CaDiCaL's add()/clause() API)
/**
 * @brief Adds a unit clause (single forced literal) to the solver.
 */
static inline void clause1(CaDiCaL::Solver& s, int a) {
	g_clause_count[0]++;
	s.add(a); s.add(0);
}

/**
 * @brief Adds a two-literal clause to the solver.
 */
static inline void clause2(CaDiCaL::Solver& s, int a, int b) {
	g_clause_count[1]++;
	s.add(a); s.add(b); s.add(0);
}

/**
 * @brief Adds a three-literal clause to the solver.
 */
static inline void clause3(CaDiCaL::Solver& s, int a, int b, int c) {
	g_clause_count[2]++;
	s.add(a); s.add(b); s.add(c); s.add(0);
}

// XOR encoding
/**
 * @brief Encodes result = a XOR b as four clauses (matches encode.py _encode_xor_pair).
 *
 * The four clauses are the standard Tseytin expansion of result <-> (a ⊕ b):
 *   ( a ∨  b ∨ ¬r):   if both false, r must be false
 *   (¬a ∨ ¬b ∨ ¬r):   if both true,  r must be false
 *   ( a ∨ ¬b ∨  r):   if b true and a false, r must be true
 *   (¬a ∨  b ∨  r):   if a true and b false, r must be true
 *
 * @returns Fresh variable r representing a XOR b.
 */
static int encodeXorPair(CaDiCaL::Solver& s, int& vc, int a, int b) {
	int r = s.declare_one_more_variable();
	clause3(s,  a,  b, -r);
	clause3(s, -a, -b, -r);
	clause3(s,  a, -b,  r);
	clause3(s, -a,  b,  r);
	return r;
}

/**
 * @brief Encodes the XOR of an arbitrary list of literals.
 *
 * Matches encode.py _encode_xor exactly:
 *   - 0 inputs  -> fresh variable forced false (unit clause ¬r).
 *   - 1 input   -> returns that literal unchanged (no new variable).
 *   - 2 inputs  -> single XOR gadget (4 clauses, 1 aux var).
 *   - k inputs  -> left-associative chain of (k-1) XOR gadgets, introducing (k-1) aux variables and 4(k-1) clauses.
 *
 * A balanced binary tree would give the same clause count but shallower
 * implication depth; left-associative is simpler and sufficient here.
 *
 * @param vars  Input literals (may be empty).
 * @returns     A literal whose value equals XOR of all inputs.
 */
static int encodeXor(CaDiCaL::Solver& s, int& vc, const int* vars, int len) {
	if (len == 0) {
		int r = s.declare_one_more_variable();
		clause1(s, -r); // force false
		return r;
	}
	if (len == 1) return vars[0];
	int result = encodeXorPair(s, vc, vars[0], vars[1]);
	for (int i = 2; i < len; i++)
		result = encodeXorPair(s, vc, result, vars[i]);
	return result;
}

// Cardinality encoding  (sequential counter, matches encode.py)
/**
 * @brief Allocates the flat counter table and emits boundary unit clauses.
 *
 * The 2-D counter table s[i][j] (0 <= i <= n, 0 <= j <= k) is stored as a
 * single contiguous array of (n+1)*(k+1) fresh SAT variables, indexed as
 * sv[i*(k+1) + j].  This avoids the vector<vector<int>> overhead and
 * keeps the table in a single heap allocation.
 *
 * Boundary conditions (same as encode.py):
 *   s[i][0] = ⊤ for all i  (at least 0 of i variables are true, trivially)
 *   s[0][j] = ⊥ for j >= 1  (at least 1 of 0 variables, impossible)
 *
 * @param n   Number of input variables.
 * @param k   maximum + 1 (the forbidden column).
 * @param vc  Variable counter (updated in place).
 * @returns   Owning pointer to the flat variable array.
 */
static unique_ptr<int[]> allocCounter(CaDiCaL::Solver& s, int& vc, int n, int k) {
	int total = (n + 1) * (k + 1);
	auto sv = make_unique<int[]>(total);
	for (int i = 0; i < total; i++) sv[i] = s.declare_one_more_variable();

	// s[i][0] = true  (trivially, 0 satisfied)
	for (int i = 0; i <= n; i++) clause1(s,  sv[i*(k+1) + 0]);
	// s[0][j] = false (0 variables can't satisfy j>=1)
	for (int j = 1; j <= k; j++) clause1(s, -sv[0*(k+1) + j]);

	return sv;
}

/**
 * @brief Encodes an auxiliary variable E that is true iff
 *   minimum <= #{true variables} <= maximum.
 *
 * Matches encode.py add_auxiliary_cardinality_clause exactly.
 * Used in the Walsh constraints (Step 5) where we need to express
 * "exactly k_low OR exactly k_high zeros" as a clause over two
 * auxiliary variables E_low and E_high.
 *
 * All four propagation clauses are emitted for every (i,j):
 *   forward:   s[i-1][j]          -> s[i][j]
 *   increment: x_i ∧ s[i-1][j-1]  -> s[i][j]
 *   reverse-1: s[i][j]            -> s[i-1][j] ∨ x_i
 *   reverse-2: s[i][j]            -> s[i-1][j-1]
 *
 * The reverse clauses are needed here because E must be an exact
 * biconditional (true iff the count is in [l, k-1]).
 *
 * @param variables  Input literals (pointer + length).
 * @param n          Length of variables array.
 * @param minimum    Lower bound (inclusive).
 * @param maximum    Upper bound (inclusive).
 * @returns SAT variable index for E.
 */
static int addAuxCardinality(CaDiCaL::Solver& s, int& vc,
                              const int* variables, int n,
                              int minimum, int maximum) {
	const int k = maximum + 1;
	const int l = minimum;

	auto sv = allocCounter(s, vc, n, k);
	// sv[i][j] accessed as sv[i*(k+1)+j]

	for (int i = 1; i <= n; i++) {
		const int xi = variables[i - 1];
		for (int j = 1; j <= k; j++) {
			const int sij  = sv[ i      * (k+1) + j    ];
			const int sim1j  = sv[(i-1) * (k+1) + j    ];
			const int sim1jm1= sv[(i-1) * (k+1) + (j-1)];

			clause2(s, -sim1j,   sij);           // forward propagation
			clause3(s, -xi, -sim1jm1, sij);      // increment
			if (j <= l) {
				clause3(s, -sij,  sim1j,  xi);       // reverse: came from carry or xi
				clause2(s, -sij,  sim1jm1);          // reverse: j-1 must have been set
			}
		}
	}

	// Link auxiliary output variable E biconditionally to the count range.
	int E = s.declare_one_more_variable();
	clause2(s, -E,  sv[n*(k+1) + l]);          // E -> at least minimum
	clause2(s, -E, -sv[n*(k+1) + k]);          // E -> not at least maximum+1
	clause3(s, -sv[n*(k+1) + l], sv[n*(k+1) + k], E); // converse
	return E;
}

/**
 * @brief Directly enforces minimum <= #{true vars} <= maximum via unit clauses
 *   and a sequential counter.  No auxiliary output variable is produced.
 *
 * Matches encode.py add_forced_cardinality_clause exactly, including the
 * key optimisation: the two reverse-propagation clauses are only emitted
 * when j <= l (minimum).  For j > l the upper-bound unit clauses on
 * s[i][k] already prevent over-counting, so the reverse clauses are
 * redundant and their omission saves O(n*(k-l)) clauses per call.
 *
 * Boundary unit clauses (same as auxiliary version, plus bounds):
 *   s[n][j] = ⊤ for j = 1..l      (at least minimum satisfied)
 *   s[i][k] = ⊥ for i = 1..n      (at most maximum satisfied)
 *
 * @param variables  Input literals (pointer + length).
 * @param n          Length of variables array.
 * @param minimum    Lower bound (inclusive).
 * @param maximum    Upper bound (inclusive).
 */
static void addForcedCardinality(CaDiCaL::Solver& s, int& vc,
                                  const int* variables, int n,
                                  int minimum, int maximum) {
	const int k = maximum + 1;
	const int l = minimum;

	auto sv = allocCounter(s, vc, n, k);

	// Enforce lower bound: at least l of all n vars must be true.
	for (int j = 1; j <= l; j++) clause1(s,  sv[n*(k+1) + j]);
	// Enforce upper bound: none of the "at least k" counters may be true.
	for (int i = 1; i <= n; i++) clause1(s, -sv[i*(k+1) + k]);

	for (int i = 1; i <= n; i++) {
		const int xi = variables[i - 1];
		for (int j = 1; j <= k; j++) {
			const int sij    = sv[ i      * (k+1) + j    ];
			const int sim1j  = sv[(i-1)   * (k+1) + j    ];
			const int sim1jm1= sv[(i-1)   * (k+1) + (j-1)];

			// Forward propagation (always needed).
			clause2(s, -sim1j,   sij);           // s[i-1][j] -> s[i][j]
			clause3(s, -xi, -sim1jm1, sij);      // x_i ∧ s[i-1][j-1] -> s[i][j]

			// Reverse propagation only needed up to the lower bound (j <= l).
			// For j > l the upper-bound unit clauses make these redundant.
			// Omitting them saves O(n*(k-l)) clauses, significant when k ≈ N/2 and l = k_low (roughly N/2 - 2^{n/2-1}).
			if (j <= l) {
				clause3(s, -sij, sim1j, xi);     // s[i][j] -> s[i-1][j] ∨ x_i
				clause2(s, -sij, sim1jm1);       // s[i][j] -> s[i-1][j-1]
			}
		}
	}
}

// Combinatorial helper
/**
 * @brief Generates all size-r subsets of {1, ..., n} in lexicographic order.
 *
 * Uses a recursive backtracking generator.  Results are appended to
 * `result`; the caller should reserve capacity before calling if the total count C(n,r) is known.
 *
 * @param n       Upper bound (inclusive, 1-based).
 * @param r       Subset size.
 * @param result  Output: each element is a sorted vector of r integers.
 */
static void generateCombinations(int n, int r, vector<vector<int>>& result) {
	vector<int> combo(r);
	function<void(int, int)> gen = [&](int start, int idx) {
		if (idx == r) { result.push_back(combo); return; }
		for (int i = start; i <= n; i++) {
			combo[idx] = i;
			gen(i + 1, idx + 1);
		}
	};
	gen(1, 0);
}

// Encoder data structures
/**
 * @brief Identity of one ANF monomial and its SAT variable.
 *
 * subset:  sorted vector of 1-based variable indices (empty = constant term).
 * mask:    bitmask: bit (i-1) set iff i ∈ subset.  Allows O(1) containment.
 * var:     the corresponding SAT variable index (1-based).
 */
struct ANFVar {
	vector<int> subset;
	uint64_t    mask;
	int         var;
};

/**
 * @brief All variable mappings produced by encodeBentFunction().
 *
 * anf_vars:   one entry per ANF monomial, in allocation order.
 * tt_vars:    tt_vars[x] = SAT variable for f(x), x in [0, 2^n).
 * var_count:  total SAT variables allocated (== vc at end of encoding).
 * n, max_degree:  problem parameters for reference by the decoder.
 */
struct EncoderResult {
	vector<ANFVar> anf_vars;
	vector<int>    tt_vars;
	int            var_count;
	int            n;
	int            max_degree;
};

// Encoder
/**
 * @brief Encodes the n-variable bent function search problem into `solver`.
 *
 * Parameters n and max_deg are passed explicitly so the function can be
 * called for any (n, d) pair in the sweep without recompilation.
 *
 * Steps:
 *   1. Allocate ANF variables (one per monomial of degree <= max_deg).
 *   2. Allocate truth-table variables F_x, one per x ∈ [0, 2^n).
 *   3. Optional: ANF weight constraint via addForcedCardinality.
 *   4. ANF -> truth-table: F_x <-> ⊕_{S ⊆ supp(x)} a_S via XOR chain.
 *   5. Walsh bentness: for each ω, #{x : f(x) = ⟨ω,x⟩} ∈ {k_low, k_high} via two addAuxCardinality calls and a disjunction clause.
 *   6. Normalisation:    ¬a_∅ and ¬F_0  (fixes f(0) = 0).
 *   7. Symmetry breaking: a_i -> a_{i+1} for i = 1..n-1.
 *
 * @param solver     Fresh CaDiCaL solver (must be newly constructed).
 * @param n          Number of input variables.
 * @param max_deg    Maximum ANF algebraic degree.
 * @param zero_lits  Caller-supplied buffer of size >= 2^n, reused across
 *                   trials to avoid repeated stack allocation.
 * @returns EncoderResult with all variable maps needed for decoding.
 */
static EncoderResult encodeBentFunction(CaDiCaL::Solver& solver, int n, int max_deg, int* zero_lits) {
	const int N_inputs  = 1 << n;   // 2^n

	int vc = 0;
	EncoderResult enc;
	enc.n          = n;
	enc.max_degree = max_deg;

	// ----------------------------------------------------------
	// Step 1: Allocate ANF variables
	//
	// One variable per subset S ⊆ {1,...,n} with |S| <= max_deg.
	// The bitmask mask_S encodes S so that containment S ⊆ supp(x)
	// can be tested as (x & mask_S) == mask_S in O(1).
	// ----------------------------------------------------------
#if TRACK_TIME == 1
	auto t0 = chrono::steady_clock::now();
#endif

	// Pre-compute total ANF variable count to reserve capacity.
	// Sum_{k=0}^{max_deg} C(n,k).
	int anf_count = 0;
	{
		// Compute C(n,k) incrementally: C(n,0)=1, C(n,k)=C(n,k-1)*(n-k+1)/k
		long long ck = 1;
		for (int k = 0; k <= max_deg; k++) {
			anf_count += (int)ck;
			if (k < max_deg) ck = ck * (n - k) / (k + 1);
		}
	}
	enc.anf_vars.reserve(anf_count);

	// Constant term (empty subset, mask = 0).
	enc.anf_vars.push_back({ {}, 0ULL, solver.declare_one_more_variable() });

	// Linear terms (degree 1).
	for (int i = 1; i <= n; i++)
		enc.anf_vars.push_back({ {i}, 1ULL << (i - 1), solver.declare_one_more_variable() });

	// Higher-degree terms (degree 2 .. max_deg).
	for (int deg = 2; deg <= max_deg; deg++) {
		vector<vector<int>> combos;
		// Reserve C(n,deg) entries.
		combos.reserve(anf_count); // conservative upper bound; shrinks naturally
		generateCombinations(n, deg, combos);
		for (auto& sub : combos) {
			uint64_t mask = 0;
			for (int idx : sub) mask |= (1ULL << (idx - 1));
			enc.anf_vars.push_back({ sub, mask, solver.declare_one_more_variable() });
		}
	}

	cout << "ANF variables:          " << enc.anf_vars.size() << "\n";

	// ----------------------------------------------------------
	// Step 2: Truth-table variables F_x for x in [0, 2^n).
	//
	// tt_vars[x] is the SAT variable whose truth value equals f(x).
	// We know the exact count, so resize rather than push_back.
	// ----------------------------------------------------------
	enc.tt_vars.resize(N_inputs);
	for (int x = 0; x < N_inputs; x++)
		enc.tt_vars[x] = solver.declare_one_more_variable();

	cout << "Truth-table variables:  " << N_inputs << "\n";

	// ----------------------------------------------------------
	// Step 3: Optional ANF weight constraint.
	//
	// Limits the number of non-zero ANF coefficients (excluding the
	// constant term) to at most MAX_ANF_WEIGHT.  Useful when searching
	// for sparse bent functions.
	// ----------------------------------------------------------
#if MAX_ANF_WEIGHT > 0
	{
		// Collect all non-constant ANF variable indices.
		int nc = (int)enc.anf_vars.size() - 1; // exclude constant
		auto non_const = make_unique<int[]>(nc);
		int idx = 0;
		for (auto& av : enc.anf_vars)
			if (!av.subset.empty())
				non_const[idx++] = av.var;
		addForcedCardinality(solver, vc, non_const.get(), nc, 0, MAX_ANF_WEIGHT);
		cout << "ANF weight constraint:  at most " << MAX_ANF_WEIGHT << "\n";
	}
#endif

	// ----------------------------------------------------------
	// Step 4: ANF -> truth-table constraints.
	//
	//   F_x <-> ⊕_{S ⊆ supp(x), |S|<=d} a_S
	//
	// For each x, collect the ANF variables whose monomials divide x
	// (i.e., supp(S) ⊆ supp(x)), compute their XOR via a left-associative
	// chain of XOR gadgets, and link the result to F_x biconditionally.
	//
	// The constant term is always included; for each other ANF variable av,
	// containment is checked in O(1) as (x & av.mask) == av.mask.
	//
	// rel_buf is reused across iterations to avoid per-x allocation.
	// Its maximum size is enc.anf_vars.size() <= 2^n.
	// ----------------------------------------------------------
#if TRACK_TIME == 1
	g_enc_anf_time = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
	t0 = chrono::steady_clock::now();
#endif

	const int const_var = enc.anf_vars[0].var;

	// Stack buffer for the relevant ANF variables of a single x.
	// Maximum possible size is enc.anf_vars.size().
	auto rel_buf = make_unique<int[]>(enc.anf_vars.size());

	for (int x = 0; x < N_inputs; x++) {
		// Build the list of ANF variables active at this input x.
		int rel_len = 0;
		rel_buf[rel_len++] = const_var; // constant always active

		for (size_t ai = 1; ai < enc.anf_vars.size(); ai++) {
			const auto& av = enc.anf_vars[ai];
			// S ⊆ supp(x) iff every bit of mask_S is set in x.
			if ((x & av.mask) == av.mask)
				rel_buf[rel_len++] = av.var;
		}

		const int f_var = enc.tt_vars[x];

		if (rel_len == 1) {
			// F_x <-> a_∅, simple biconditional, no XOR gadget needed.
			clause2(solver, -f_var,     const_var);
			clause2(solver, -const_var, f_var);
		} else {
			// F_x <-> XOR(rel_buf[0..rel_len-1])
			int xr = encodeXor(solver, vc, rel_buf.get(), rel_len);
			clause2(solver, -f_var, xr);
			clause2(solver, -xr,    f_var);
		}
	}

	cout << "ANF->TT constraints:     " << N_inputs << "\n";

#if TRACK_TIME == 1
	g_enc_tt_time = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
	t0 = chrono::steady_clock::now();
#endif

	// ----------------------------------------------------------
	// Step 5: Walsh / bentness conditions (phase variables eliminated).
	//
	// By the counting reformulation (see report Section 2.2):
	//   f is bent iff for every ω:
	//     #{x : f(x) = ⟨ω,x⟩} ∈ { k_low, k_high }
	//   where k_low  = 2^{n-1} - 2^{n/2-1}
	//         k_high = 2^{n-1} + 2^{n/2-1}
	//
	// The zero-indicator literal for (x, ω) is:
	//   ¬F_x  if ⟨ω,x⟩ = 0  (agreement means F_x is false)
	//    F_x  if ⟨ω,x⟩ = 1  (agreement means F_x is true)
	//
	// zero_lits is a caller-supplied buffer of size N_MAX = 2^MAX_N,
	// allocated once in main and reused across all trials.
	//
	// Two auxiliary variables E_low and E_high capture the two exact
	// counts; the clause (E_low ∨ E_high) forces exactly one to hold.
	// ----------------------------------------------------------
	const int k_low  = safe_pow2(n - 1) - safe_pow2(n / 2 - 1);
	const int k_high = safe_pow2(n - 1) + safe_pow2(n / 2 - 1);

	cout << "Bent condition:         #zeros per ω in {" << k_low << ", " << k_high << "}\n";

	const int print_every = max(1, N_inputs / 32);

	for (int omega = 0; omega < N_inputs; omega++) {
		// Build zero-indicator literals for this ω.
		// parity(x & omega) = ⟨ω,x⟩ mod 2, computed in O(1).
		for (int x = 0; x < N_inputs; x++)
			zero_lits[x] = parity(x & omega) ? enc.tt_vars[x] : -enc.tt_vars[x];

		// Auxiliary variable true iff exactly k_low zero-indicators are true.
		int E_low  = addAuxCardinality(solver, vc, zero_lits, N_inputs, k_low,  k_low);
		// Auxiliary variable true iff exactly k_high zero-indicators are true.
		int E_high = addAuxCardinality(solver, vc, zero_lits, N_inputs, k_high, k_high);

		// At least one of the two exact counts must hold for this ω.
		clause2(solver, E_low, E_high);

		if (omega % print_every == 0 || omega == N_inputs - 1)
			cout << "Walsh constraints:      " << (omega + 1) << "/" << N_inputs << "\r" << flush;
	}

	cout << "Walsh constraints:      " << N_inputs << "/" << N_inputs << "\n";

#if TRACK_TIME == 1
	g_enc_walsh_time = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
	t0 = chrono::steady_clock::now();
#endif

	// ----------------------------------------------------------
	// Step 6: Normalisation  f(0) = 0
	//
	// By affine invariance (Property 8), adding the constant 1 to any
	// bent function yields another bent function.  Fixing f(0) = 0
	// selects one canonical representative from each {f, f⊕1} pair,
	// halving the number of solutions without excluding any class.
	//
	// Two equivalent unit clauses: ¬a_∅ (ANF constant = 0) and ¬F_0
	// (truth table at 0 = 0).  Both encode the same constraint; having
	// both gives the solver an earlier propagation opportunity.
	// ----------------------------------------------------------
#if NORMALIZE == 1
	clause1(solver, -enc.anf_vars[0].var); // a_∅ = 0
	clause1(solver, -enc.tt_vars[0]);      // F_0 = 0
	cout << "Normalisation:          f(0) = 0\n";
#endif

	// ----------------------------------------------------------
	// Step 7: Symmetry breaking  a_1 <= a_2 <= ... <= a_n
	//
	// By affine invariance, permuting the n input variables maps any
	// bent function to another bent function.  Enforcing a non-decreasing
	// order on the linear ANF coefficients a_1,...,a_n breaks the n!
	// input-permutation symmetries, keeping only one canonical ordering.
	//
	// Each inequality a_i <= a_{i+1} is the implication a_i -> a_{i+1},
	// encoded as the clause (¬a_i ∨ a_{i+1}).
	// ----------------------------------------------------------
#if SYM_BREAK == 1
	{
		// Collect linear-term variables a_1, ..., a_n in index order.
		// They were allocated in order in Step 1, so indices 1..n in anf_vars.
		vector<int> lin_vars;
		lin_vars.reserve(n);
		for (int i = 1; i <= n; i++)
			for (auto& av : enc.anf_vars)
				if (av.subset.size() == 1 && av.subset[0] == i) {
					lin_vars.push_back(av.var);
					break;
				}

		int sym_clauses = 0;
		for (size_t i = 0; i + 1 < lin_vars.size(); i++) {
			clause2(solver, -lin_vars[i], lin_vars[i + 1]); // a_i -> a_{i+1}
			sym_clauses++;
		}
		if (sym_clauses > 0)
			cout << "Symmetry breaking:      " << sym_clauses << " linear-term ordering clauses\n";
		else
			cout << "Symmetry breaking:      skipped (no linear terms in subset)\n";
	}
#endif

#if TRACK_TIME == 1
	g_enc_norm_sym_time = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
#endif

	enc.var_count = vc;
	return enc;
}

// Decoder
/**
 * @brief Reads a SAT solution from `solver` and prints a full human-readable
 *   description of the decoded bent function.
 *
 * Decodes:
 *   - Truth table  f(x) for x = 0 .. 2^n - 1
 *   - ANF coefficients  a_S for each monomial S in the encoding
 *   - ANF expression string  (e.g. "x1x2 xor x3x4")
 *   - Truth table in hex and binary (little-endian: f(0) is LSB)
 *   - Walsh-Hadamard verification using the standard dot-product inner
 *     product, computed independently of the SAT encoding to confirm correctness.
 *
 * @param solver  Must have returned 10 (SAT) from solve().
 * @param enc     The EncoderResult produced by encodeBentFunction().
 */
static void decodeSolution(CaDiCaL::Solver& solver, const EncoderResult& enc) {
#if TRACK_TIME == 1
	auto t0 = chrono::steady_clock::now();
#endif

	const int n    = enc.n;
	const int N_in = 1 << n;

	// --- Truth table ---
	// Read f(x) for each x from the solver model.
	vector<int> tt(N_in);
	for (int x = 0; x < N_in; x++)
		tt[x] = (solver.val(enc.tt_vars[x]) > 0) ? 1 : 0;

	// --- ANF coefficients ---
	// Keyed by subset for sorted display.
	map<vector<int>, int> anf;
	for (auto& av : enc.anf_vars)
		anf[av.subset] = (solver.val(av.var) > 0) ? 1 : 0;

	// --- ANF string ---
	string anf_str;
	for (auto& [sub, coeff] : anf) {
		if (!coeff) continue;
		if (!anf_str.empty()) anf_str += " xor ";
		if (sub.empty()) {
			anf_str += "1";
		} else {
			for (int i : sub) anf_str += "x" + to_string(i);
		}
	}
	if (anf_str.empty()) anf_str = "0";

	// --- Truth table as hex (little-endian: f(0) is LSB) ---
	uint64_t tt_val = 0;
	for (int x = 0; x < N_in; x++)
		if (tt[x]) tt_val |= (1ULL << x);
	const int hex_digits = (N_in + 3) / 4;

	// --- Bentness verification (independent of SAT encoding) ---
	// Recompute the Walsh-Hadamard transform from the decoded truth table
	// and check |W_f(ω)| = 2^{n/2} for every ω.  A failure here indicates
	// a bug in the encoding rather than a solver error.
	const int expected_mag = 1 << (n / 2);
	bool is_bent = true;
	for (int omega = 0; omega < N_in && is_bent; omega++) {
		int total = 0;
		for (int x = 0; x < N_in; x++)
			total += (tt[x] ^ parity(x & omega)) ? -1 : 1;
		if (abs(total) != expected_mag) {
			cerr << "  WARNING: W_f(" << omega << ") = " << total
			     << " (expected +/-" << expected_mag << ")\n";
			is_bent = false;
		}
	}

#if TRACK_TIME == 1
	g_decode_time = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
#endif

	// --- Print ---
	cout << "\n" << string(62, '=') << "\n";
	cout << "BENT FUNCTION  (n=" << n << ", max_degree=" << enc.max_degree << ")\n";
	cout << string(62, '=') << "\n";

	cout << "\nAlgebraic Normal Form:\n";
	cout << "  f(x) = " << anf_str << "\n";

	cout << "\nANF Coefficients (non-zero only):\n";
	bool any_nonzero = false;
	for (auto& [sub, coeff] : anf) {
		if (!coeff) continue;
		string label;
		if (sub.empty()) {
			label = "{}";
		} else {
			label = "{";
			for (size_t i = 0; i < sub.size(); i++) {
				if (i) label += ",";
				label += to_string(sub[i]);
			}
			label += "}";
		}
		cout << "  a_" << label << " = 1\n";
		any_nonzero = true;
	}
	if (!any_nonzero) cout << "  (all zero)\n";

	cout << "\nTruth Table (" << N_in << " values, little-endian):\n";
	printf("  Hex: 0x%0*llx\n", hex_digits, (unsigned long long)tt_val);
	cout << "  Bin: ";
	for (int x = 0; x < N_in; x++) cout << tt[x];
	cout << "\n";

	cout << "\nBentness Verification:\n";
	if (is_bent)
		cout << "  PASS - all Walsh coefficients = +/-" << expected_mag << "\n";
	else
		cout << "  FAIL - see warnings above\n";

	cout << string(62, '=') << "\n";
}

// Main: (n, d) sweep
int main(int argc, char* argv[]) {
	// Stack-allocated Walsh literal buffer, sized for the largest possible
	// N_inputs = 2^MAX_N.  Declared here and passed into each trial to
	// avoid re-allocating it on the stack inside the loop.
	int zero_lits[N_MAX];

	const string sep(62, '=');

	cout << sep << "\n";
	cout << "Bent Function SAT Sweep\n";
	cout << "  Sweeping n = 1.." << MAX_N << ",  d = 1..n\n";
	cout << "  Normalize:         " << (NORMALIZE ? "yes" : "no") << "\n";
	cout << "  Symmetry breaking: " << (SYM_BREAK ? "yes" : "no") << "\n";
#if MAX_ANF_WEIGHT > 0
	cout << "  Max ANF weight:    " << MAX_ANF_WEIGHT << "\n";
#endif
	cout << sep << "\n\n" << flush;

	auto sweep_start = chrono::steady_clock::now();

	// Iterate (n, d) pairs in the order:
	//   (1,1), (2,1),(2,2), (3,1),(3,2),(3,3), ...
	for (int n = 1; n <= MAX_N; n++) {
		for (int d = 1; d <= min(n, MAX_D); d++) {

			// Trial header: printed to stdout so it appears in the log file before any encoding output.
			cout << sep << "\n";
			cout << "Starting trial for order n=" << n
			     << ", max degree d=" << d
			     << " for Bent Function over F_2\n";
			if (n % 2 != 0)
				cout << "  (Note: n is odd, bent functions do not exist; "
				        "expecting UNSAT)\n";
			cout << sep << "\n";
			cout << "  Normalize:         " << (NORMALIZE ? "yes" : "no") << "\n";
			cout << "  Symmetry breaking: " << (SYM_BREAK ? "yes" : "no") << "\n";
			cout << "\n" << flush;

			// Reset per-trial accumulators.
			resetGlobals();

			// Fresh solver: CaDiCaL state is not reusable across problems.
			CaDiCaL::Solver solver;
			
			g_timeout_solver = &solver;
			signal(SIGALRM, timeout_handler);
			alarm(MAX_SOLVER_SECONDS);
			
			// ---- Encoding ----
			cout << "--- Encoding ---\n" << flush;
#if TRACK_TIME == 1
			auto enc_wall_start = chrono::steady_clock::now();
#endif

			EncoderResult enc = encodeBentFunction(solver, n, d, zero_lits);

#if TRACK_TIME == 1
			double enc_wall = chrono::duration<double>(
				chrono::steady_clock::now() - enc_wall_start).count();
			cout << "Encoding wall time:     " << enc_wall << "s\n";
#endif

			// ---- Clause statistics ----
			cout << "\n--- Clause statistics ---\n";
			cout << "  Variables:            " << solver.vars() << "\n";
			cout << "  Clauses of length 1:  " << g_clause_count[0] << "\n";
			cout << "  Clauses of length 2:  " << g_clause_count[1] << "\n";
			cout << "  Clauses of length 3:  " << g_clause_count[2] << "\n";
			cout << "  Total clauses:        "
			     << (g_clause_count[0] + g_clause_count[1] + g_clause_count[2])
			     << "\n";

			// ---- Solving ----
			cout << "\n--- Solving ---\n" << flush;
#if TRACK_TIME == 1
			auto solve_start = chrono::steady_clock::now();
#endif

			int result = solver.solve();

#if TRACK_TIME == 1
			g_solve_time = chrono::duration<double>(
				chrono::steady_clock::now() - solve_start).count();
			cout << "Solve time:             " << g_solve_time << "s\n";
#endif

			double trial_elapsed = chrono::duration<double>(
				chrono::steady_clock::now() - enc_wall_start).count();

			// ---- Decode / report ----
			if (result == 10) {
				cout << "Result:                 SAT - bent function found\n";
				decodeSolution(solver, enc);
			} else if (result == 20) {
				cout << "\nResult: UNSAT - no bent function with n="
				     << n << ", d=" << d << ".\n";
			} else if (result == 0) {
				cout << "\nResult: TIMEOUT (exceeded " << MAX_SOLVER_SECONDS << " seconds)\n";
			} else {
				cout << "\nResult: UNKNOWN (solver returned " << result << ")\n";
			}

			cout << "\nTrial elapsed time: " << trial_elapsed << "s\n";

#if TRACK_TIME == 1 && PRINT_TIME == 1
			cout << "\n=== TIMING BREAKDOWN ===\n";
			cout << "  ANF variable setup:     " << g_enc_anf_time      << "s\n";
			cout << "  ANF -> truth table:     " << g_enc_tt_time        << "s\n";
			cout << "  Walsh conditions:       " << g_enc_walsh_time     << "s\n";
			cout << "  Norm + sym. breaking:   " << g_enc_norm_sym_time  << "s\n";
			cout << "  Encoding total (wall):  " << enc_wall             << "s\n";
			cout << "  Solving:                " << g_solve_time         << "s\n";
			cout << "  Decoding:               " << g_decode_time        << "s\n";
			cout << "  Trial total:            " << trial_elapsed        << "s\n";
#endif
			cout << "\n" << flush;
		} // d loop
	} // n loop

	double sweep_elapsed = chrono::duration<double>(
		chrono::steady_clock::now() - sweep_start).count();

	cout << sep << "\n";
	cout << "Sweep complete.  Total time: " << sweep_elapsed << "s\n";
	cout << sep << "\n";

	return 0;
}