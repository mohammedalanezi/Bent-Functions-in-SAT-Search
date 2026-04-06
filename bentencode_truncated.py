"""
By Mohammed Al-Anezi

Bent Function SAT Encoder (Truncated / Restricted ANF variant)
Encodes bent function search problems into SAT instances using the SATEncoder module.

Extends the base encoder with three ANF-restriction modes that reduce the search space and speed up both encoding and solving:
  anf_subset:       Provide an explicit list of monomials.  Only those get SAT variables; all others are implicitly fixed to 0.
  random_anf_size:  Randomly pick this many monomials (constant term always included).
  max_anf_weight:   Add a global cardinality bound: at most this many ANF coefficients (excluding the constant) may be non-zero simultaneously.

Key optimisations vs the original bentencode.py
------------------------------------------------
1. Phase variables ELIMINATED.
   s_{x,ω} = F_x ⊕ ⟨ω,x⟩ is always either F_x (dot=0) or ¬F_x (dot=1).
   Instead of allocating a variable and two definitional clauses per (x,ω) pair,
   we pass the appropriate truth-table literal directly to the cardinality encoder.
   For n=8 this removes 65 536 variables and 131 072 clauses.

2. Parity computed by bit trick.
   ⟨ω,x⟩ = popcount(ω & x) mod 2, computed in O(1) with bit-twiddling.

3. ANF subset mask precomputed.
   Monomial S ⊆ support(x)  iff  (x & mask_S) == mask_S, tested in O(1) per pair instead of iterating over the indices of S.

4. Walsh cardinality encoded directly.
   The redundant _encode_exact_zeros wrapper (which added 2 extra variables and 4 extra clauses per ω 
   just to re-expose what add_auxiliary_cardinality_clause already returned) is removed.
"""

from encode import SATEncoder
from decode import SATDecoder
from typing import List, Tuple, Dict, Optional
import math, os
from itertools import combinations

script_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(script_dir)


def _parity(v: int) -> int:
	"""Return popcount(v) mod 2 using bit-twiddling (O(log w) ops)."""
	v ^= v >> 16
	v ^= v >> 8
	v ^= v >> 4
	v ^= v >> 2
	v ^= v >> 1
	return v & 1

class BentFunctionEncoder:
	"""Encodes bent function search problems into SAT instances."""

	def __init__(self, n: int,
		max_degree: Optional[int] = None,
		label: str = "bent_function",
		use_pipe: bool = False,
		anf_subset: Optional[List[Tuple[int, ...]]] = None,
		random_anf_size: Optional[int] = None,
		max_anf_weight: Optional[int] = None):
		"""
		Initialize a bent function encoder for n variables.

		Args:
			n             : Number of input variables (must be even).
			max_degree    : Maximum algebraic degree.  None = unrestricted (= n).
			label         : Label for the SAT instance.
			use_pipe      : Whether to use in-memory pipe mode.
			anf_subset    : Explicit list of monomials (as index-tuples) to include.
							All other monomials are implicitly 0.
							The constant term () is always added if absent.
			random_anf_size : If anf_subset is None, randomly select this many
							  non-constant monomials (constant term always included).
			max_anf_weight  : At most this many non-constant ANF coefficients may
							  be non-zero (global cardinality constraint).
		"""
		if n % 2 != 0:
			raise ValueError(f"n must be even for bent functions; got n={n}.")

		self.n = n
		self.max_degree = max_degree if max_degree is not None else n
		self.num_inputs = 1 << n   # 2^n
		self.num_freqs  = 1 << n   # 2^n
		self.max_anf_weight = max_anf_weight

		self.sat = SATEncoder(label=label, use_pipe=use_pipe, warning_bool=False)

		# Determine which monomials get SAT variables
		if anf_subset is not None:
			# Work on a copy so we don't mutate the caller's list
			self.anf_subset = list(anf_subset)
			if () not in self.anf_subset:
				self.anf_subset.append(())
			print(f"Using custom ANF subset: {len(self.anf_subset)} monomials (including constant).")
		elif random_anf_size is not None:
			self.anf_subset = self._generate_random_anf_subset(random_anf_size)
			print(f"Randomly selected {len(self.anf_subset)} ANF monomials (including constant).")
		else:
			self.anf_subset = None
			print("Using full ANF (all monomials up to max_degree).")

		# Variable containers
		self.anf_vars: Dict[Tuple[int, ...], int] = {}
		self.tt_vars:  List[int] = []
		# phase_vars are ELIMINATED in this implementation (see module docstring)

		# Precomputed bitmask for each monomial subset (built in _create_variables)
		self._anf_masks: Dict[Tuple[int, ...], int] = {}

		self.solutions: List[List[int]] = []

	# Public API
	def encode(self, normalize: bool = True, symmetry_breaking: bool = True):
		"""
		Encode the complete bent function problem into SAT.

		Args:
			normalize        : Whether to fix f(0) = 0.
			symmetry_breaking: Whether to add a₁ <= a₂ <= ... <= aₙ ordering.
		"""
		self._create_variables()
		self._add_anf_weight_constraint()
		self._encode_anf_to_truth_table()
		self._encode_walsh_conditions()

		if normalize:
			self._add_normalization_constraints()
		if symmetry_breaking:
			self._add_symmetry_breaking_constraints()

		self.sat.finalize_encoding()

	def get_statistics(self) -> Dict:
		"""Return a summary of the encoded problem."""
		return {
			"n":               self.n,
			"max_degree":      self.max_degree,
			"anf_vars":        len(self.anf_vars),
			"tt_vars":         len(self.tt_vars),
			"max_anf_weight":  self.max_anf_weight,
			"num_variables":   self.sat.var_counter,
			"num_clauses":     self.sat.clause_counter,
		}

	def save_to_file(self, filename: str = "bent_function.cnf"):
		"""Write the DIMACS CNF encoding to a file."""
		dimacs = self.sat.to_dimacs()
		if dimacs is False:
			# Already streamed to sat.encoding_path during encoding
			print(f"Encoding was streamed to '{self.sat.encoding_path}' during encode().")
			return
		with open(filename, 'w') as f:
			f.write(dimacs)
		print(f"Saved encoding to '{filename}'.")

	def get_dimacs_string(self) -> str:
		"""Return the DIMACS CNF representation as a string (pipe/in-memory mode)."""
		return self.sat.to_dimacs()

	# Step 1: Variable creation
	def _create_variables(self):
		"""Create ANF variables and truth-table variables."""

		# --- ANF variables ---
		print(f"Creating ANF variables  (n={self.n}, max_degree={self.max_degree})...")

		if self.anf_subset is None:
			# Full ANF: constant + all degree-1..max_degree monomials
			self.anf_vars[()] = self.sat.new_variable()
			for i in range(1, self.n + 1):
				self.anf_vars[(i,)] = self.sat.new_variable()
			for degree in range(2, self.max_degree + 1):
				for subset in combinations(range(1, self.n + 1), degree):
					self.anf_vars[subset] = self.sat.new_variable()
		else:
			for subset in self.anf_subset:
				self.anf_vars[subset] = self.sat.new_variable()

		# Precompute bitmasks: subset {i1,i2,...} -> (1<<(i1-1))|(1<<(i2-1))|...
		# Used for fast containment tests in _encode_anf_to_truth_table.
		for subset in self.anf_vars:
			mask = 0
			for idx in subset:
				mask |= 1 << (idx - 1)
			self._anf_masks[subset] = mask

		self.sat.add_comment(f"ANF variables: {len(self.anf_vars)}")

		# --- Truth-table variables ---
		print(f"Creating truth table variables  ({self.num_inputs} inputs)...")
		for _ in range(self.num_inputs):
			self.tt_vars.append(self.sat.new_variable())

		# NOTE: Phase variables s_{x,ω} are NOT created here.
		# They are replaced by direct tt_var literals in _encode_walsh_conditions.

		self.sat.add_comment(f"Total variables after creation: {self.sat.var_counter}")

	# Step 2: ANF weight constraint (optional)
	def _add_anf_weight_constraint(self):
		"""Limit the total number of non-zero ANF coefficients (excluding constant)."""
		if self.max_anf_weight is None:
			return

		non_const_vars = [v for s, v in self.anf_vars.items() if s != ()]
		if not non_const_vars:
			return

		self.sat.add_forced_cardinality_clause(non_const_vars, 0, self.max_anf_weight)
		self.sat.add_comment(
			f"ANF weight constraint: at most {self.max_anf_weight} non-zero coefficients"
		)

	# Step 3: ANF -> truth table
	def _encode_anf_to_truth_table(self):
		"""
		Encode  F_x = ⊕_{S ⊆ support(x),  S ∈ anf_vars} a_S  for each x.

		Uses precomputed bitmasks for O(1) subset containment tests.
		"""
		print("Encoding ANF -> truth table constraints...")

		const_var = self.anf_vars[()]  # always present

		for x in range(self.num_inputs):
			# Collect all ANF variables whose monomial is contained in support(x)
			relevant_vars = [const_var]
			for subset, var in self.anf_vars.items():
				if not subset:
					continue   # constant already added
				mask = self._anf_masks[subset]
				if (x & mask) == mask:   # subset ⊆ support(x)
					relevant_vars.append(var)

			f_var = self.tt_vars[x]

			if len(relevant_vars) == 1:
				# F_x <-> a_∅  (two unit-implication clauses)
				self.sat.add_clause([-f_var,  const_var])
				self.sat.add_clause([-const_var, f_var])
			else:
				# F_x <-> XOR(relevant_vars)
				xor_result = self.sat._encode_xor(relevant_vars)
				self.sat.add_clause([-f_var,  xor_result])
				self.sat.add_clause([-xor_result, f_var])

		self.sat.add_comment(f"ANF->TT: {self.num_inputs} constraints")

	# Step 4: Walsh / bentness conditions  (phase variables ELIMINATED)
	def _encode_walsh_conditions(self):
		"""
		Encode  |W_f(ω)| = 2^{n/2}  for all ω.

		Instead of creating a phase variable s_{x,ω} for each (x,ω) pair and
		then counting its zeros, we observe that:

			s_{x,ω} = F_x ⊕ ⟨ω,x⟩

		so s_{x,ω} = 0  iff  F_x = ⟨ω,x⟩.

		When ⟨ω,x⟩ = 0:  (s=0) <-> (F_x=0)  -> zero-indicator literal = ¬F_x
		When ⟨ω,x⟩ = 1:  (s=0) <-> (F_x=1)  -> zero-indicator literal = +F_x

		We pass these literals directly to add_auxiliary_cardinality_clause,
		which counts the TRUE ones, giving us the count of zeros in the phase
		array without ever allocating a phase variable.
		"""
		print("Encoding Walsh spectrum (bentness) constraints...")

		k_low  = (1 << (self.n - 1)) - (1 << (self.n // 2 - 1))
		k_high = (1 << (self.n - 1)) + (1 << (self.n // 2 - 1))

		print(f"  Bent condition: #zeros per ω ∈ {{{k_low}, {k_high}}}")

		# Print at 0 %, 25 %, 50 %, 75 %, 100 %
		checkpoints = {self.num_freqs * p // 4 for p in range(5)}
		checkpoints.add(self.num_freqs - 1)

		for omega in range(self.num_freqs):
			if omega in checkpoints:
				pct = omega * 100 // self.num_freqs
				print(f"  Walsh constraints: {omega}/{self.num_freqs}  ({pct}%)")

			# Build zero-indicator literals directly from truth-table variables
			zero_lits = []
			for x in range(self.num_inputs):
				dot = _parity(x & omega)         # ⟨ω,x⟩ mod 2, O(1)
				if dot == 0:
					zero_lits.append(-self.tt_vars[x])   # zero <-> ¬F_x
				else:
					zero_lits.append(self.tt_vars[x])    # zero <->  F_x

			# Create auxiliary variables: E_low = True iff exactly k_low zeros
			#                             E_high = True iff exactly k_high zeros
			E_low  = self.sat.add_auxiliary_cardinality_clause(zero_lits, k_low,  k_low)
			E_high = self.sat.add_auxiliary_cardinality_clause(zero_lits, k_high, k_high)

			# Require at least one to hold
			self.sat.add_clause([E_low, E_high])

		print(f"  Walsh constraints: {self.num_freqs}/{self.num_freqs}")
		self.sat.add_comment(f"Walsh spectrum: {self.num_freqs} constraints")

	# Step 5: Normalisation
	def _add_normalization_constraints(self):
		"""Fix f(0) = 0 (equivalently, a_∅ = 0 and F_0 = 0)."""
		print("Adding normalisation  f(0)=0...")
		self.sat.add_clause([-self.anf_vars[()]])
		self.sat.add_clause([-self.tt_vars[0]])
		self.sat.add_comment("Normalised: f(0) = 0")

	# Step 6: Symmetry breaking
	def _add_symmetry_breaking_constraints(self):
		"""
		Add a_1 <= a_2 <= ... <= a_n on the linear ANF coefficients.

		Skips any pair where one or both of the linear terms is absent from anf_vars (which happens when using a restricted anf_subset).
		"""
		if self.n < 2:
			return

		added = 0
		for i in range(1, self.n):
			if (i,) not in self.anf_vars or (i + 1,) not in self.anf_vars:
				# One or both terms not in the subset, skip this pair.
				# The missing term is implicitly 0, so the ordering is trivially satisfied or not constrainable; either way no clause needed.
				continue
			a_i       = self.anf_vars[(i,)]
			a_i_next  = self.anf_vars[(i + 1,)]
			# a_i <= a_(i+1)  <->  a_i -> a_(i+1)
			self.sat.add_implication_clause([a_i], [a_i_next])
			added += 1

		if added:
			self.sat.add_comment(f"Symmetry breaking: ordering on {added} adjacent linear-term pairs")
		else:
			print("  (symmetry breaking: no adjacent linear-term pairs in ANF subset, skipped)")

	# Helpers
	def _generate_random_anf_subset(self, k: int) -> List[Tuple[int, ...]]:
		"""
		Return a list of k monomials including the constant term.

		Selects k-1 non-constant monomials uniformly at random from all
		monomials up to self.max_degree.

		Args:
			k: Total number of monomials to include (must be ≥ 1).
		"""
		import random

		all_monomials: List[Tuple[int, ...]] = []
		for i in range(1, self.n + 1):
			all_monomials.append((i,))
		for degree in range(2, self.max_degree + 1):
			for subset in combinations(range(1, self.n + 1), degree):
				all_monomials.append(subset)

		total = len(all_monomials)
		want  = k - 1    # reserve one slot for the constant term

		if want < 0:
			raise ValueError("random_anf_size must be at least 1.")
		if want > total:
			raise ValueError(
				f"Cannot select {k} monomials: only {total} non-constant monomials "
				f"available for n={self.n}, max_degree={self.max_degree}."
			)

		selected = random.sample(all_monomials, want)
		selected.append(())   # constant term
		return selected

# Convenience wrapper
def encode_and_save_bent_function(
	n: int,
	max_degree: Optional[int] = None,
	anf_subset: Optional[List[Tuple[int, ...]]] = None,
	random_anf_size: Optional[int] = None,
	max_anf_weight: Optional[int] = None,
	output_file: str = "bent_function.cnf",
) -> BentFunctionEncoder:
	"""
	Encode a bent function problem and save it to a DIMACS CNF file.

	Args:
		n              : Number of input variables.
		max_degree     : Maximum ANF degree (None = unrestricted).
		anf_subset     : Explicit monomial list (None = use full / random).
		random_anf_size: Number of monomials to pick randomly (None = ignore).
		max_anf_weight : Maximum number of non-zero ANF coefficients (None = ignore).
		output_file    : Destination .cnf filename.

	Returns:
		The populated BentFunctionEncoder instance.
	"""
	encoder = BentFunctionEncoder(
		n,
		max_degree=max_degree,
		label=f"bent_n{n}_d{max_degree}",
		use_pipe=True,
		anf_subset=anf_subset,
		random_anf_size=random_anf_size,
		max_anf_weight=max_anf_weight,
	)

	print(f"Encoding bent function  n={n}, max_degree={max_degree}")
	print("=" * 55)

	encoder.encode(normalize=True, symmetry_breaking=True)

	stats = encoder.get_statistics()
	print("\nEncoding statistics:")
	for key, value in stats.items():
		print(f"  {key}: {value}")

	encoder.save_to_file(output_file)
	return encoder

# example demo
if __name__ == "__main__":
	n = 4

	satsolver_path = os.path.join(parent_dir, "cadical-exhaust-master", "build", "cadical")

	# --- Demo 1: Full ANF, degree <= 2 ---
	print(f"\n{'='*55}")
	print(f"Demo 1: n={n}, full ANF, max_degree=2")
	print(f"{'='*55}")
	encoder = encode_and_save_bent_function(n, max_degree=2, output_file=f"test_bent_{n}_full.cnf")

	decoding = SATDecoder(use_pipe=True)
	wall_time = decoding.run_sat_solver(
		satsolver_path,
		input_content=encoder.sat.to_dimacs(),
		display_to_console=True,
	)

	if decoding.get_satisfiability():
		print("SAT, assignment (true vars):", decoding.get_variable_assignment())
	else:
		print("UNSAT")

	# --- Demo 2: Restricted ANF subset ---
	print(f"\n{'='*55}")
	print(f"Demo 2: n={n}, restricted subset (only quadratic cross-terms)")
	print(f"{'='*55}")
	quad_subset = list(combinations(range(1, n + 1), 2))  # all degree-2 pairs
	encoder2 = BentFunctionEncoder(n, max_degree=2, label="bent_quad_subset",
									use_pipe=True, anf_subset=quad_subset)
	encoder2.encode(normalize=True, symmetry_breaking=True)
	stats2 = encoder2.get_statistics()
	print("Statistics:", stats2)

	# --- Demo 3: Random subset ---
	print(f"\n{'='*55}")
	print(f"Demo 3: n={n}, random 6 monomials")
	print(f"{'='*55}")
	encoder3 = BentFunctionEncoder(n, max_degree=n, label="bent_random",
									use_pipe=True, random_anf_size=6)
	encoder3.encode(normalize=True, symmetry_breaking=True)
	print("Statistics:", encoder3.get_statistics())