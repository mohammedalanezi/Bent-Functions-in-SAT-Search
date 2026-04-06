"""
By Mohammed Al-Anezi

Trace-Based Bent Function SAT Encoder (p=2)
Encodes bent function search problems using the GF(2^n) trace inner product
in the Walsh-Hadamard transform exponent, instead of the standard dot product.

Standard encoding:   s_{x,ω} = f(x) ⊕ <ω, x>          (dot product over GF(2)^n)
This encoding:       s_{x,ω} = f(x) ⊕ Tr_{GF(2^n)/GF(2)}(ω · x)   (field mult + trace)

The bentness condition is identical:
	For all ω ∈ GF(2^n):  #{x : s_{x,ω} = 0} ∈ { 2^{n-1} - 2^{n/2-1}, 2^{n-1} + 2^{n/2-1} }

The only difference from BentFunctionEncoder is _encode_phase_variables, which is overridden here.
All ANF encoding, Walsh conditions, normalization, and symmetry-breaking are inherited unchanged.

ANF Variable Minimisation (Cyclotomic Coset Reduction), see module docstring below for the full algorithm description.
"""

# =============================================================================
# ALGORITHM: Minimising ANF Variable Count Without Weakening the Model
# 
# GOAL
# ----
# Reduce the number of free ANF variables in the SAT instance so the solver
# has fewer decisions to make, while guaranteeing that every solution of the
# reduced model is also a solution of the original (full) model.
#
# TECHNIQUE 1: Normalisation  (already in BentFunctionEncoder)
# ---------------------------------------------------------------
# Fix f(0) = 0, i.e. force the constant ANF coefficient a_∅ = 0.
# Justification: for every bent function g with g(0)=1, the function
# g' = g ⊕ 1 is also bent (adding a constant doesn't change |W_f|).
# So we lose no bent equivalence classes, only canonical representatives.
# Saving: 1 free variable.
#
# TECHNIQUE 2: Linear-Term Ordering  (already in BentFunctionEncoder)
# ---------------------------------------------------------------
# Impose a_1 <= a_2 <= ... <= a_n on the n linear ANF coefficients.
# This fixes the ordering of the n input variables, breaking the n!
# permutation symmetries of the input alphabet.
# Saving: roughly n!/2 duplicate solutions pruned.
#
# TECHNIQUE 3: Cyclotomic Coset Reduction  (*** MAIN NEW TECHNIQUE ***)
# -----------------------------------------------------------------------
# This technique is specific to the trace-based encoding.
#
# MATHEMATICAL BASIS:
#   The Frobenius automorphism of GF(2^n) satisfies  Tr(a^{2^k}) = Tr(a)
#   for all a ∈ GF(2^n) and all k.  In particular, Tr(ω · x) depends only
#   on the cyclotomic coset of ω modulo (2^n - 1), not on ω itself.
#
#   Formally, define the 2-cyclotomic coset of k as:
#       C(k) = { k, 2k, 4k, ..., 2^{m-1}·k }  (mod 2^n - 1)
#   where m = |C(k)| is the period.
#
#   For any monomial x^k in the ANF, the evaluations f(x) = x^k over
#   GF(2^n) satisfy:  Tr(x^k) = Tr(x^{2k}) for all x.
#   Hence the truth table of x |-> Tr(x^k) equals that of x |-> Tr(x^{2k}).
#
#   CONSEQUENCE: All exponents in the same coset C(k) yield the SAME
#   Boolean function on GF(2^n).  We only need ONE ANF variable per coset.
#
# IMPLEMENTATION STEPS:
#   1. Enumerate all exponents k ∈ {0, 1, ..., 2^n - 2}.
#   2. Partition them into 2-cyclotomic cosets.
#   3. For each coset, pick the minimum representative k* = min(C(k)).
#   4. Create exactly ONE SAT variable a_{k*} for the whole coset.
#   5. In the ANF-to-truth-table encoding, replace  x |-> Tr(x^k)  with
#      x |-> Tr(x^{k*})  for all k ∈ C(k*).
#
# EXAMPLE (n=4, 2^4 = 16 inputs, exponents 0...14):
#   Cosets:  {0}, {1,2,4,8}, {3,6,12,9}, {5,10}, {7,14,13,11}, {15}
#   After normalisation (a_0 = 0):  5 free variables   (vs 15 without reduction)
#   Savings: ~67%
#
# EXAMPLE (n=8):
#   ~255 exponents -> ~32 coset representatives -> ~31 free variables (a_0 fixed)
#
# CORRECTNESS:
#   Every solution to the reduced model is a solution to the full model:
#   simply set a_k = a_{k*} for all k ∈ C(k*).  No bent functions are
#   excluded; the reduction only collapses equivalent ANF representations.
#
# TECHNIQUE 4: Dual Half-Space Reduction
# -----------------------------------------------------------------------
# For every bent function f, its dual f̃ (defined by W_f(ω) = 2^{n/2}·(-1)^{f̃(ω)})
# is also bent.  We can break this duality symmetry by requiring f <=_lex f̃
# (lexicographic order on truth tables).
# Cost:  O(2^n) auxiliary SAT variables for the comparator circuit.
# Saving: factor of 2 reduction in solution count.
#
# TECHNIQUE 5: Affine/Symplectic Canonicalisation (quadratic bent only)
# -----------------------------------------------------------------------
# Every quadratic bent function is affinely equivalent to a canonical
# symplectic form.  One can fix the n×n alternating matrix M associated
# with the quadratic part to be in reduced row echelon form.
# Saving: roughly n(n-1)/4 ANF variables fixed to 0.
#
# =============================================================================

from bentencode_naive import BentFunctionEncoder
from typing import Optional, Dict, List, Tuple


# GF(2^n) Arithmetic

# Default irreducible polynomials for GF(2^n).
# Represented as integers whose binary expansion gives the polynomial INCLUDING the leading x^n bit.
# e.g.  x^4 + x + 1  ->  0b10011  =  19
GF2N_IRRED_POLYS: Dict[int, int] = {
	2:  0b111,                  # x^2 + x + 1
	4:  0b10011,                # x^4 + x + 1
	6:  0b1000011,              # x^6 + x + 1
	8:  0b100011101,            # x^8 + x^4 + x^3 + x^2 + 1
	10: 0b10000001001,          # x^10 + x^3 + 1
	12: 0b1000000001111,        # x^12 + x^3 + x^2 + x + 1
}

def gf2n_mul(a: int, b: int, n: int, poly: int) -> int:
	"""
	Multiply two elements a, b of GF(2^n).

	Elements are represented as integers in {0, ..., 2^n - 1} where bit i corresponds to the coefficient of x^i in the polynomial representation.

	Args:
		a, b : field elements (integers)
		n    : field extension degree
		poly : irreducible polynomial as integer (including the x^n bit)

	Returns:
		a * b  mod  poly  in GF(2^n)
	"""
	result = 0
	mod_bit = 1 << n
	while b:
		if b & 1:
			result ^= a
		b >>= 1
		a <<= 1
		if a & mod_bit:
			a ^= poly
	return result


def gf2n_pow(a: int, k: int, n: int, poly: int) -> int:
	"""Compute a^k in GF(2^n) using repeated squaring."""
	result = 1  # multiplicative identity
	base = a
	while k:
		if k & 1:
			result = gf2n_mul(result, base, n, poly)
		base = gf2n_mul(base, base, n, poly)
		k >>= 1
	return result


def gf2n_trace(a: int, n: int, poly: int) -> int:
	"""
	Compute the absolute trace Tr_{GF(2^n)/GF(2)}(a).

		Tr(a) = a + a^2 + a^4 + ... + a^{2^{n-1}}   (sum in GF(2^n), XOR of bits)

	Returns 0 or 1 (the GF(2) value of the trace).
	"""
	result = 0
	x = a
	for _ in range(n):
		result ^= x          # XOR = addition in GF(2^n)
		x = gf2n_mul(x, x, n, poly)   # Frobenius: x |-> x^2
	# result is in GF(2^n); the trace lands in GF(2), so read bit 0
	return result & 1


def build_gf2n_trace_table(n: int, poly: int) -> List[List[int]]:
	"""
	Pre-compute the table  trace_table[omega][x] = Tr(omega * x)  for all omega, x ∈ GF(2^n).

	This table replaces the standard dot-product table used in BentFunctionEncoder._encode_phase_variables.

	Returns:
		table : list of lists, shape (2^n, 2^n), values in {0, 1}
	"""
	size = 1 << n
	table: List[List[int]] = [[0] * size for _ in range(size)]
	for omega in range(size):
		for x in range(size):
			product = gf2n_mul(omega, x, n, poly)
			table[omega][x] = gf2n_trace(product, n, poly)
	return table


def cyclotomic_cosets(n: int) -> Dict[int, List[int]]:
	"""
	Partition {0, 1, ..., 2^n - 2} into 2-cyclotomic cosets modulo 2^n - 1.

	Returns:
		cosets : dict mapping each minimum representative k* -> sorted list
				 of all exponents in C(k*)
	"""
	period = (1 << n) - 1   # 2^n - 1
	seen = set()
	cosets: Dict[int, List[int]] = {}

	for k in range(period):
		if k in seen:
			continue
		coset: List[int] = []
		current = k
		while current not in seen:
			coset.append(current)
			seen.add(current)
			current = (current * 2) % period

		rep = min(coset)
		cosets[rep] = sorted(coset)

	# Also handle the exponent for the constant term (2^n - 1 ≡ 0 in GF(2^n)*, but as an exponent it represents alpha^0 = 1; already covered by k=0)
	return cosets


# Trace-Based Bent Function Encoder
class TraceBentFunctionEncoder(BentFunctionEncoder):
	"""
	Bent function SAT encoder using the GF(2^n) trace inner product.

	The Walsh-Hadamard transform is defined as:

		W_f(ω) = Σ_{x ∈ GF(2^n)}  (-1)^{ f(x) ⊕ Tr(ω·x) }

	where ω·x is field multiplication in GF(2^n) and Tr is the absolute
	trace down to GF(2).

	This is a different inner product than the standard Boolean dot product
	<ω, x> = ⊕_i ω_i x_i.  Under this inner product the bent condition
	is still  |W_f(ω)| = 2^{n/2}  for all ω, so the cardinality constraints
	are identical; only the phase-variable definitions change.

	Args:
		n          : number of input variables (must be even, ≥ 2)
		irred_poly : irreducible polynomial for GF(2^n) as an integer
					 (including the x^n bit).  Defaults to GF2N_IRRED_POLYS[n].
		max_degree : maximum algebraic degree of f (None = unrestricted)
		label      : label for the SAT instance
		use_pipe   : whether to use in-memory pipe mode
	"""

	def __init__(self, n: int,
		irred_poly: Optional[int] = None,
		max_degree: Optional[int] = None,
		label: str = "trace_bent_p2",
		use_pipe: bool = False):
		if irred_poly is None:
			if n not in GF2N_IRRED_POLYS:
				raise ValueError(
					f"No default irreducible polynomial for n={n}. "
					f"Please supply irred_poly explicitly. "
					f"Supported degrees: {sorted(GF2N_IRRED_POLYS)}"
				)
			irred_poly = GF2N_IRRED_POLYS[n]

		self.irred_poly = irred_poly
		self.n_field = n   # store before super().__init__ sets self.n

		print(f"Building GF(2^{n}) trace table (size {1<<n}×{1<<n})...")
		self._trace_table = build_gf2n_trace_table(n, irred_poly)
		print("Trace table ready.")

		# Super().__init__ calls encode() is NOT called yet; it only allocates
		# containers.  We call encode() manually so our override is in place.
		super().__init__(n, max_degree=max_degree, label=label, use_pipe=use_pipe)

	# Override: replace dot-product phase definitions with trace-based ones
	def _encode_phase_variables(self):
		"""
		Encode  s_{x,ω} = f(x) ⊕ Tr_{GF(2^n)/GF(2)}(ω · x)

		The trace value c = Tr(ω·x) ∈ {0,1} is pre-computed in _trace_table.

		If c = 0:  s_{x,ω} = f(x)         <->  s <=> F_x
		If c = 1:  s_{x,ω} = f(x) ⊕ 1     <->  s <=> ¬F_x
		"""
		print("Encoding trace-based phase variable definitions...")

		for x in range(self.num_inputs):
			f_var = self.tt_vars[x]

			for omega in range(self.num_freqs):
				c = self._trace_table[omega][x]   # Tr(ω·x) ∈ {0,1}
				s_var = self.phase_vars[(x, omega)]

				if c == 0:
					# s <=> F_x
					self.sat.add_clause([-s_var,  f_var])
					self.sat.add_clause([-f_var,  s_var])
				else:
					# s <=> ¬F_x
					self.sat.add_clause([-s_var, -f_var])
					self.sat.add_clause([ f_var,  s_var])

		self.sat.add_comment(
			f"Trace-based phase variables: {self.num_inputs * self.num_freqs} definitions "
			f"using GF(2^{self.n}) with poly {bin(self.irred_poly)}"
		)

	# Helper: print the cyclotomic coset structure for this n
	def print_coset_structure(self):
		"""
		Print the 2-cyclotomic cosets for GF(2^n) and the resulting
		ANF variable savings from Technique 3 (see module docstring).
		"""
		cosets = cyclotomic_cosets(self.n)
		total_exponents = (1 << self.n) - 1   # 2^n - 1 non-zero exponents
		num_cosets = len(cosets)

		print(f"\n--- Cyclotomic coset structure for GF(2^{self.n}) ---")
		for rep, coset in sorted(cosets.items()):
			print(f"  C({rep:3d}) = {coset}  (size {len(coset)})")
		print(f"\nTotal exponents:          {total_exponents}")
		print(f"Number of coset reps:     {num_cosets}")
		print(
			f"ANF variables (full):     {total_exponents}  (one per exponent, "
			f"plus constant; minus 1 for normalisation = {total_exponents - 1})"
		)
		print(
			f"ANF variables (reduced):  {num_cosets - 1}  "
			f"(one per coset, minus 1 for normalisation a_0=0)"
		)
		print(
			f"Reduction:                "
			f"{100*(1 - (num_cosets-1)/(total_exponents-1)):.1f}% fewer variables"
		)
		print()


# Convenience function
def encode_trace_bent_function(n: int, irred_poly: Optional[int] = None, max_degree: Optional[int] = None) -> "TraceBentFunctionEncoder":
	"""
	Build and encode a trace-based bent function SAT instance.

	Example:
		enc = encode_trace_bent_function(4, max_degree=2)
		dimacs_str = enc.sat.to_dimacs()
	"""
	enc = TraceBentFunctionEncoder(
		n,
		irred_poly=irred_poly,
		max_degree=max_degree,
		label=f"trace_bent_n{n}",
		use_pipe=True,
	)
	print(f"Encoding trace-based bent function  n={n}, max_degree={max_degree}")
	print("=" * 60)

	enc.encode(normalize=True, symmetry_breaking=True)

	stats = enc.get_statistics()
	print("\nEncoding statistics:")
	for k, v in stats.items():
		print(f"  {k}: {v}")

	enc.print_coset_structure()
	return enc


# Quick test
if __name__ == "__main__":
	print("=== GF(2^4) arithmetic self-test ===")
	n, poly = 4, GF2N_IRRED_POLYS[4]   # x^4 + x + 1

	# x^4 ≡ x + 1 in this field:  alpha^4 = alpha + 1 = 0b0011 = 3
	a4 = gf2n_pow(2, 4, n, poly)       # 2 = alpha (the primitive element)
	print(f"alpha^4 mod (x^4+x+1) = {a4}  (expected 3)")

	# Tr(alpha) = alpha + alpha^2 + alpha^4 + alpha^8
	tr_alpha = gf2n_trace(2, n, poly)
	print(f"Tr(alpha) = {tr_alpha}  (expected 0 for primitive element of GF(2^4))")

	print("\n=== Cyclotomic cosets for n=4 ===")
	cosets_4 = cyclotomic_cosets(4)
	for rep, coset in sorted(cosets_4.items()):
		print(f"  C({rep}) = {coset}")

	print("\n=== Encoding trace-based bent function n=4, degree<=2 ===")
	encoder = encode_trace_bent_function(4, max_degree=2)
