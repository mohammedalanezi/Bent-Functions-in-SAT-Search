"""
By Mohammed Al-Anezi

Trace-Based Bent Function SAT Decoder
Decodes SAT solver output from TraceBentFunctionEncoder instances.

Mirrors BentFunctionDecoder but verification uses the GF(2^n) trace
inner product in the Walsh-Hadamard transform, matching the encoding:

	W_f(ω) = Σ_{x ∈ GF(2^n)} (-1)^{ f(x) ⊕ Tr_{GF(2^n)/GF(2)}(ω·x) }

Bent condition (same threshold as standard):
	|W_f(ω)| = 2^{n/2}  for all ω.

Usage:
	encoder = TraceBentFunctionEncoder(4, max_degree=2, use_pipe=True)
	encoder.encode()

	sat_dec = SATDecoder(use_pipe=True)
	sat_dec.run_sat_solver(solver_path, input_content=encoder.sat.to_dimacs())

	if sat_dec.get_satisfiability():
		decoder = TraceBentFunctionDecoder(encoder, sat_dec.get_contents())
		decoder.print_solution()
"""

from typing import List, Dict, Tuple, Optional
from bentencode_trace import TraceBentFunctionEncoder, cyclotomic_cosets
from decode import SATDecoder
import os

script_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(script_dir)


class TraceBentFunctionDecoder:
	"""Decodes SAT solver solutions from TraceBentFunctionEncoder instances."""

	def __init__(self, encoder_instance: TraceBentFunctionEncoder, sat_output: str = None):
		"""
		Initialize decoder with the encoder that produced the SAT instance.

		Args:
			encoder_instance : The TraceBentFunctionEncoder used for encoding
			sat_output       : Raw SAT solver output string (optional)
		"""
		self.encoder = encoder_instance
		self.n = encoder_instance.n
		self.max_degree = encoder_instance.max_degree

		# Variable maps (from encoder)
		self.anf_vars   = encoder_instance.anf_vars
		self.tt_vars    = encoder_instance.tt_vars
		self.phase_vars = encoder_instance.phase_vars

		# GF(2^n) trace table (re-used from encoder)
		self._trace_table = encoder_instance._trace_table

		# Parsed variable assignment
		self.assignment: Dict[int, bool] = {}

		if sat_output:
			self.parse_sat_output(sat_output)

	# Parsing
	def parse_sat_output(self, sat_output: str) -> Dict[int, bool]:
		"""
		Parse SAT solver output to extract variable assignments.

		Args:
			sat_output: SAT solver output string

		Returns:
			Dictionary mapping variable ID -> True/False
		"""
		self.assignment = {}

		if "UNSAT" in sat_output or "UNSATISFIABLE" in sat_output:
			print("UNSATISFIABLE: No bent function found for given constraints.")
			return {}

		for line in sat_output.strip().split('\n'):
			line = line.strip()
			if not line.startswith('v'):
				continue
			for part in line[1:].strip().split():
				if part == '0':
					break
				var_id = int(part)
				self.assignment[abs(var_id)] = (var_id > 0)

		return self.assignment

	# Decoding
	def decode_truth_table(self) -> List[int]:
		"""
		Decode truth table values f(x) ∈ {0, 1} for x = 0...2^n-1.

		Returns:
			List of n integers, each 0 or 1.
		"""
		return [1 if self.assignment.get(v, False) else 0 for v in self.tt_vars]

	def decode_anf(self) -> Dict[Tuple[int, ...], int]:
		"""
		Decode ANF coefficients from the SAT solution.

		Returns:
			Dictionary mapping subset -> coefficient value (0 or 1)
		"""
		return {
			subset: (1 if self.assignment.get(var_id, False) else 0)
			for subset, var_id in self.anf_vars.items()
		}

	def decode_phase_values(self) -> Dict[Tuple[int, int], int]:
		"""
		Decode all phase variables s_{x,ω} = f(x) ⊕ Tr(ω·x).

		Returns:
			Dictionary mapping (x, ω) -> value in {0, 1}
		"""
		return {
			(x, omega): (1 if self.assignment.get(var_id, False) else 0)
			for (x, omega), var_id in self.phase_vars.items()
		}

	def decode_anf_by_coset(self) -> Dict[int, int]:
		"""
		Decode ANF coefficients grouped by cyclotomic coset representative.

		In the trace encoding every monomial in the same 2-cyclotomic coset evaluates identically (Frobenius invariance), so the encoder assigns
		them the same SAT variable.  This method returns a mapping from each minimum coset representative to its coefficient value.

		Returns:
			Dictionary mapping coset representative k* -> coefficient (0 or 1)
		"""
		cosets = cyclotomic_cosets(self.n)
		result: Dict[int, int] = {}
		# ANF vars are keyed by singleton tuples (i,) for linear terms, etc.
		# The trace encoding uses standard BentFunctionEncoder ANF vars which are indexed by subsets of {1,...,n}. 
		# The coset reduction is a separate optimisation not yet implementated, so we print it here for analytical view.
		anf = self.decode_anf()
		for rep in sorted(cosets.keys()):
			# Map exponent -> ANF subset (single-element for degree-1 terms)
			subset = (rep,) if rep != 0 else ()
			if subset in anf:
				result[rep] = anf[subset]
		return result

	# Formatting helpers
	def anf_to_string(self, anf_coeffs: Optional[Dict] = None) -> str:
		"""
		Convert ANF coefficients to a readable algebraic expression.

		Example output: "x1x2 ⊕ x3x4 ⊕ x1x2x3"

		Args:
			anf_coeffs: If None, decode from current assignment.

		Returns:
			String like  "1 ⊕ x1 ⊕ x1x2"  or  "0"  for the zero function.
		"""
		if anf_coeffs is None:
			anf_coeffs = self.decode_anf()

		terms = []
		for subset in sorted(anf_coeffs.keys(), key=lambda s: (len(s), s)):
			if anf_coeffs[subset] == 1:
				if len(subset) == 0:
					terms.append("1")
				else:
					terms.append("".join(f"x{i}" for i in sorted(subset)))

		return " ⊕ ".join(terms) if terms else "0"

	def truth_table_to_hex(self, truth_table: Optional[List[int]] = None) -> str:
		"""
		Convert truth table to little-endian hexadecimal string.

		Args:
			truth_table: If None, decode from current assignment.

		Returns:
			String like  "0x6996..."
		"""
		if truth_table is None:
			truth_table = self.decode_truth_table()

		value = sum(bit << i for i, bit in enumerate(truth_table))
		hex_digits = (len(truth_table) + 3) // 4
		return f"0x{value:0{hex_digits}x}"

	def truth_table_to_binary(self, truth_table: Optional[List[int]] = None) -> str:
		"""
		Convert truth table to binary string (little-endian: f(0) first).

		Args:
			truth_table: If None, decode from current assignment.

		Returns:
			String like  "0110100110010110..."
		"""
		if truth_table is None:
			truth_table = self.decode_truth_table()
		return "".join(str(b) for b in truth_table)

	# Verification
	def compute_trace_walsh_spectrum(
		self, truth_table: Optional[List[int]] = None
	) -> List[int]:
		"""
		Compute the full trace-based Walsh-Hadamard spectrum.

			W_f(ω) = Σ_{x} (-1)^{ f(x) ⊕ Tr(ω·x) }

		Args:
			truth_table: If None, decode from current assignment.

		Returns:
			List of 2^n integer Walsh coefficients, one per ω.
		"""
		if truth_table is None:
			truth_table = self.decode_truth_table()

		N = 1 << self.n
		walsh = []
		for omega in range(N):
			total = 0
			for x in range(N):
				exponent = truth_table[x] ^ self._trace_table[omega][x]
				total += 1 if exponent == 0 else -1
			walsh.append(total)
		return walsh

	def verify_bentness(self, truth_table: Optional[List[int]] = None) -> bool:
		"""
		Verify that the decoded function is bent under the trace inner product.

		Checks  |W_f(ω)| = 2^{n/2}  for all ω.

		Args:
			truth_table: If None, decode from current assignment.

		Returns:
			True if bent, False (with warning messages) otherwise.
		"""
		if truth_table is None:
			truth_table = self.decode_truth_table()

		expected = 1 << (self.n // 2)
		walsh = self.compute_trace_walsh_spectrum(truth_table)

		is_bent = True
		for omega, w in enumerate(walsh):
			if abs(w) != expected:
				print(f"  WARNING: W_f({omega}) = {w}  (expected ±{expected})")
				is_bent = False
		return is_bent

	def compute_dual(self, truth_table: Optional[List[int]] = None) -> List[int]:
		"""
		Compute the dual bent function f̃ defined by:

			W_f(ω) = 2^{n/2} · (-1)^{f̃(ω)}

		The dual is also bent (under the same trace inner product).

		Args:
			truth_table: If None, decode from current assignment.

		Returns:
			Truth table of the dual function as a list of {0,1} values.
		"""
		if truth_table is None:
			truth_table = self.decode_truth_table()

		expected = 1 << (self.n // 2)
		walsh = self.compute_trace_walsh_spectrum(truth_table)

		dual = []
		for w in walsh:
			if w == expected:
				dual.append(0)
			elif w == -expected:
				dual.append(1)
			else:
				raise ValueError(
					f"Walsh coefficient {w} is not ±{expected}; "
					"function may not be bent."
				)
		return dual

	# Display
	def print_solution(self, verify: bool = True, show_walsh: bool = False):
		"""
		Print a human-readable summary of the decoded bent function.

		Args:
			verify     : Whether to verify bentness (runs full Walsh transform)
			show_walsh : Whether to print the full Walsh spectrum
		"""
		print(f"\n{'='*62}")
		print(f"TRACE BENT FUNCTION  (n={self.n}, max_degree={self.max_degree})")
		print(f"{'='*62}")

		anf        = self.decode_anf()
		truth_table = self.decode_truth_table()

		print(f"\nAlgebraic Normal Form:")
		print(f"  f(x) = {self.anf_to_string(anf)}")

		print(f"\nTruth Table ({len(truth_table)} values):")
		print(f"  Hex: {self.truth_table_to_hex(truth_table)}")
		print(f"  Bin: {self.truth_table_to_binary(truth_table)}")

		print(f"\nANF Coefficients (non-zero only):")
		printed_any = False
		for subset, value in sorted(anf.items(), key=lambda kv: (len(kv[0]), kv[0])):
			if value:
				label = "∅" if not subset else "{" + ",".join(map(str, subset)) + "}"
				print(f"  a_{label} = 1")
				printed_any = True
		if not printed_any:
			print("  (all zero, zero function)")

		# Cyclotomic coset summary
		cosets = cyclotomic_cosets(self.n)
		print(f"\nCyclotomic coset summary  (n={self.n}):")
		print(f"  {len(cosets)} cosets -> {len(cosets)-1} free ANF vars after normalisation")

		if verify:
			print(f"\nBentness verification (trace Walsh transform):")
			if self.verify_bentness(truth_table):
				print(f"  ✓ Bent, all Walsh coefficients = ±{1 << (self.n // 2)}")

				dual = self.compute_dual(truth_table)
				dual_hex = self.truth_table_to_hex(dual)
				print(f"\nDual function  f̃:")
				print(f"  Hex: {dual_hex}")
				print(f"  Bin: {''.join(str(b) for b in dual)}")

				is_self_dual = (truth_table == dual)
				print(f"  Self-dual: {'yes' if is_self_dual else 'no'}")
			else:
				print(f"  ✗ NOT BENT, check encoding or SAT output")

		if show_walsh:
			walsh = self.compute_trace_walsh_spectrum(truth_table)
			print(f"\nFull Walsh spectrum (trace-based):")
			for omega, w in enumerate(walsh):
				print(f"  W({omega:>4}) = {w:>+6}")

		print(f"{'='*62}")

	def save_solution(self, filename: str = "trace_bent_function.txt"):
		"""
		Save the decoded solution to a text file.

		Args:
			filename: Output filename
		"""
		anf         = self.decode_anf()
		truth_table = self.decode_truth_table()
		is_bent     = self.verify_bentness(truth_table)
		dual        = self.compute_dual(truth_table) if is_bent else None

		with open(filename, 'w') as f:
			f.write(f"Trace-Based Bent Function Solution  (n={self.n})\n")
			f.write(f"Maximum algebraic degree: {self.max_degree}\n")
			f.write(f"Inner product: Tr_{{GF(2^{self.n})/GF(2)}}(omega * x)\n")
			f.write("=" * 55 + "\n\n")

			f.write(f"Algebraic Normal Form:\n")
			f.write(f"  f(x) = {self.anf_to_string(anf)}\n\n")

			f.write(f"ANF Coefficients (non-zero):\n")
			for subset, v in sorted(anf.items(), key=lambda kv: (len(kv[0]), kv[0])):
				if v:
					label = "∅" if not subset else "{" + ",".join(map(str, subset)) + "}"
					f.write(f"  a_{label} = 1\n")

			f.write(f"\nTruth Table (hex, little-endian): {self.truth_table_to_hex(truth_table)}\n")
			f.write(f"Truth Table (binary, little-endian):\n")
			f.write(f"  {self.truth_table_to_binary(truth_table)}\n\n")

			f.write("Verification:\n")
			if is_bent:
				f.write(f"  ✓ Bent  (all Walsh coefficients = ±{1 << (self.n // 2)})\n")
			else:
				f.write("  ✗ NOT BENT\n")

			if dual is not None:
				f.write(f"\nDual function f~:\n")
				f.write(f"  Hex: {self.truth_table_to_hex(dual)}\n")
				f.write(f"  Bin: {''.join(str(b) for b in dual)}\n")
				f.write(f"  Self-dual: {'yes' if truth_table == dual else 'no'}\n")

		print(f"Solution saved to '{filename}'.")

# Example usage
if __name__ == "__main__":
	from bentencode_trace import TraceBentFunctionEncoder

	n = 4
	max_degree = 4

	print(f"Encoding trace-based bent function  n={n}, max_degree={max_degree}...")
	encoder = TraceBentFunctionEncoder(n, max_degree=max_degree, use_pipe=True)
	encoder.encode(normalize=True, symmetry_breaking=True)

	satsolver_path = os.path.join(parent_dir, "cadical-exhaust-master", "build", "cadical")

	sat_dec = SATDecoder(use_pipe=True)
	print("Running SAT solver...")
	wall_time = sat_dec.run_sat_solver(
		satsolver_path,
		input_content=encoder.sat.to_dimacs(),
		display_to_console=True,
	)

	if sat_dec.get_satisfiability():
		decoder = TraceBentFunctionDecoder(encoder, sat_dec.get_contents())
		decoder.print_solution(verify=True, show_walsh=False)
		decoder.save_solution(f"trace_bent_n{n}_deg{max_degree}.txt")

		timings = sat_dec.get_timings()
		if timings:
			print(f"\nSolver timings: {timings}")
		print(f"Wall time: {wall_time}s")
	else:
		print("No bent function found (UNSAT).")
