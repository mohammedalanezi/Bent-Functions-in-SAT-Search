"""
Bent Function SAT Decoder for Truncated Model
Decodes SAT solver output to reconstruct bent functions.

By Mohammed Al-Anezi.
"""

from typing import List, Dict, Tuple, Optional
import itertools
import re

import bentencode_truncated 

class BentFunctionDecoder:
	"""Decodes SAT solver solutions to bent function representations."""
	
	def __init__(self, encoder_instance, sat_output: str = None):
		"""
		Initialize decoder with the encoder instance used for encoding.
		
		Args:
			encoder_instance: The BentFunctionEncoder instance used for encoding
			sat_output: Raw SAT solver output (optional)
		"""
		self.encoder = encoder_instance
		self.n = encoder_instance.n
		self.max_degree = encoder_instance.max_degree
		
		# Variable mappings from encoder (handle missing phase_vars gracefully)
		self.anf_vars = encoder_instance.anf_vars
		self.tt_vars = encoder_instance.tt_vars
		if hasattr(encoder_instance, 'phase_vars'):
			self.phase_vars = encoder_instance.phase_vars
		else:
			self.phase_vars = None  # truncated encoder has no phase variables
			print("Note: Encoder has no phase variables (truncated mode). decode_phase_values() will return empty dict.")
		
		# Solution storage
		self.assignment: Dict[int, bool] = {}
		self.solutions: List[Dict] = []
		
		if sat_output:
			self.parse_sat_output(sat_output)
	
	def parse_sat_output(self, sat_output: str) -> Dict[int, bool]:
		"""
		Parse SAT solver output to extract variable assignments.
		
		Args:
			sat_output: SAT solver output string
		
		Returns:
			Dictionary mapping variable ID -> True/False
		"""
		# Clear previous assignment
		self.assignment = {}
		
		# Check for UNSAT
		if "UNSAT" in sat_output or "UNSATISFIABLE" in sat_output:
			print("UNSATISFIABLE: No bent function found for given constraints.")
			return {}
		
		# Find assignment line(s)
		lines = sat_output.strip().split('\n')
		for line in lines:
			line = line.strip()
			if line.startswith('v '):  # DIMACS model line
				parts = line[1:].strip().split()  # Skip 'v'
				for part in parts:
					if part == '0':
						continue
					var_id = int(part)
					if var_id > 0:
						self.assignment[var_id] = True
					else:
						self.assignment[abs(var_id)] = False
		
		# If no 'v' lines found, try to parse simple assignment format
		if not self.assignment:
			for line in lines:
				if line.startswith('SAT'):
					continue
				if line and not line.startswith('c'):
					parts = line.split()
					for part in parts:
						if part == '0' or part == 'SAT' or part == 'UNSAT':
							continue
						var_id = int(part)
						if var_id > 0:
							self.assignment[var_id] = True
						else:
							self.assignment[abs(var_id)] = False
		
		return self.assignment
	
	def decode_anf(self) -> Dict[Tuple[int, ...], int]:
		"""
		Decode ANF coefficients from SAT solution.
		
		Returns:
			Dictionary mapping subset -> coefficient value (0/1)
		"""
		anf_coeffs = {}
		for subset, var_id in self.anf_vars.items():
			value = self.assignment.get(var_id, False)
			anf_coeffs[subset] = 1 if value else 0
		
		return anf_coeffs
	
	def decode_truth_table(self) -> List[int]:
		"""
		Decode truth table from SAT solution.
		
		Returns:
			List of function values f(x) for x = 0..2^n-1
		"""
		truth_table = []
		for i, var_id in enumerate(self.tt_vars):
			value = self.assignment.get(var_id, False)
			truth_table.append(1 if value else 0)
		
		return truth_table
	
	def decode_phase_values(self) -> Dict[Tuple[int, int], int]:
		"""
		Decode phase variables s_{x,ω} from SAT solution.
		Only available if encoder created phase variables.
		
		Returns:
			Dictionary mapping (x, ω) -> value (0/1)
		"""
		if self.phase_vars is None:
			print("Warning: Phase variables not present in encoder (truncated mode).")
			return {}
		
		phase_values = {}
		for (x, ω), var_id in self.phase_vars.items():
			value = self.assignment.get(var_id, False)
			phase_values[(x, ω)] = 1 if value else 0
		
		return phase_values
	
	def anf_to_string(self, anf_coeffs: Optional[Dict] = None) -> str:
		"""
		Convert ANF coefficients to algebraic expression string.
		
		Args:
			anf_coeffs: ANF coefficients (if None, use decoded ones)
		
		Returns:
			String representation like "x1x2 ⊕ x3x4"
		"""
		if anf_coeffs is None:
			anf_coeffs = self.decode_anf()
		
		terms = []
		
		# Sort subsets by size then lexicographically
		sorted_subsets = sorted(anf_coeffs.keys(), 
							   key=lambda s: (len(s), s))
		
		for subset in sorted_subsets:
			if anf_coeffs[subset] == 1:
				if len(subset) == 0:
					terms.append("1")  # Constant term
				else:
					term = "".join([f"x{i}" for i in sorted(subset)])
					terms.append(term)
		
		if not terms:
			return "0"
		
		return " ⊕ ".join(terms)
	
	def truth_table_to_hex(self, truth_table: Optional[List[int]] = None) -> str:
		"""
		Convert truth table to hexadecimal representation.
		
		Args:
			truth_table: Truth table values (if None, use decoded ones)
		
		Returns:
			Hexadecimal string (little-endian)
		"""
		if truth_table is None:
			truth_table = self.decode_truth_table()
		
		# Little-endian: f(0) is LSB
		value = 0
		for i, bit in enumerate(truth_table):
			if bit:
				value |= (1 << i)
		
		# Calculate number of hex digits needed
		hex_digits = (len(truth_table) + 3) // 4
		return f"0x{value:0{hex_digits}x}"
	
	def truth_table_to_binary(self, truth_table: Optional[List[int]] = None) -> str:
		"""
		Convert truth table to binary string.
		
		Args:
			truth_table: Truth table values (if None, use decoded ones)
		
		Returns:
			Binary string (little-endian)
		"""
		if truth_table is None:
			truth_table = self.decode_truth_table()
		
		return "".join(str(bit) for bit in truth_table)
	
	def verify_bentness(self) -> bool:
		"""
		Verify that the decoded function is actually bent.
		
		Returns:
			True if bent, False otherwise
		"""
		truth_table = self.decode_truth_table()
		n = self.n
		N = 1 << n  # 2^n
		
		# Compute Walsh-Hadamard transform
		walsh = [0] * N
		
		for ω in range(N):
			total = 0
			for x in range(N):
				# Compute dot product <ω, x>
				dot_product = 0
				for i in range(n):
					if ((ω >> i) & 1) and ((x >> i) & 1):
						dot_product ^= 1
				
				# f(x) ⊕ <ω, x>
				if truth_table[x] ^ dot_product:
					total -= 1
				else:
					total += 1
			
			walsh[ω] = total
		
		# Check if all values are ±2^{n/2}
		expected_magnitude = 1 << (n // 2)
		for value in walsh:
			if abs(value) != expected_magnitude:
				print(f"WARNING: Walsh value {value} not equal to ±{expected_magnitude}")
				return False
		
		return True
	
	def print_solution(self, solution_index: int = 0, verify: bool = True):
		"""
		Print a human-readable representation of the bent function.
		
		Args:
			solution_index: Index of solution to print
			verify: Whether to verify bentness
		"""
		print(f"\n{'='*60}")
		print(f"BENT FUNCTION (n={self.n}, max degree={self.max_degree})")
		print(f"{'='*60}")
		
		# Get decoded values
		anf = self.decode_anf()
		truth_table = self.decode_truth_table()
		
		# Print ANF
		print(f"\nAlgebraic Normal Form (ANF):")
		print(f"  f(x) = {self.anf_to_string(anf)}")
		
		# Print truth table
		print(f"\nTruth Table ({len(truth_table)} values):")
		print(f"  Hex: {self.truth_table_to_hex(truth_table)}")
		print(f"  Bin: {self.truth_table_to_binary(truth_table)}")
		
		# Print ANF coefficients
		print(f"\nANF Coefficients:")
		for subset, value in sorted(anf.items(), key=lambda x: (len(x[0]), x[0])):
			if value:
				subset_str = "∅" if not subset else "{" + ",".join(map(str, subset)) + "}"
				print(f"  a_{subset_str} = {value}")
		
		# Verify bentness
		if verify:
			print(f"\nVerification:")
			if self.verify_bentness():
				print("  ✓ Function is bent (all Walsh coefficients = ±2^{n/2})")
			else:
				print("  ✗ Function might not be bent!")
		
		print(f"{'='*60}")
	
	def save_solution(self, filename: str = "bent_function.txt"):
		"""
		Save solution to a text file.
		
		Args:
			filename: Output filename
		"""
		with open(filename, 'w') as f:
			f.write(f"Bent Function Solution (n={self.n})\n")
			f.write(f"Maximum algebraic degree: {self.max_degree}\n")
			f.write("=" * 50 + "\n\n")
			
			anf = self.decode_anf()
			truth_table = self.decode_truth_table()
			
			f.write(f"Algebraic Normal Form:\n")
			f.write(f"f(x) = {self.anf_to_string(anf)}\n\n")
			
			f.write(f"ANF Coefficients:\n")
			for subset, value in sorted(anf.items(), 
									   key=lambda x: (len(x[0]), x[0])):
				if value:
					subset_str = "∅" if not subset else "{" + ",".join(map(str, subset)) + "}"
					f.write(f"a_{subset_str} = {value}\n")
			f.write("\n")
			
			f.write(f"Truth Table (hex): {self.truth_table_to_hex(truth_table)}\n")
			f.write(f"Truth Table (binary, little-endian):\n")
			f.write(self.truth_table_to_binary(truth_table) + "\n\n")
			
			f.write("Verification:\n")
			if self.verify_bentness():
				f.write("✓ Function is bent\n")
			else:
				f.write("✗ Function might not be bent\n")

# Example usage (as before, uses truncated encoder)
if __name__ == "__main__":
	import os
	from decode import SATDecoder

	input_variables = 10
	max_degree = 2
	anf_subset = None
	random_anf_size = None
	max_anf_weight = 10

	# Encode using truncated encoder
	encoder = bentencode_truncated.encode_and_save_bent_function(
		input_variables, max_degree, anf_subset, random_anf_size, max_anf_weight,
		output_file=f"test_bent_{input_variables}_{max_degree}.cnf"
	)
	
	script_dir = os.path.dirname(os.path.abspath(__file__))
	parent_dir = os.path.dirname(script_dir)

	exhaust_satsolver_path = os.path.join(parent_dir, "cadical-exhaust-master", "build", "cadical-exhaust")
	satsolver_path = os.path.join(parent_dir, "cadical-exhaust-master", "build", "cadical")

	decoding = SATDecoder(use_pipe=True)

	print("Started SAT Instance...")
	wall_time = decoding.run_sat_solver(
		satsolver_path, 
		input_content=encoder.sat.to_dimacs(),
		display_to_console=True)
	
	if decoding.get_satisfiability():
		# Decode the solution
		decoder = BentFunctionDecoder(encoder, decoding.get_contents())
		decoder.print_solution()
		
		# Save to file
		decoder.save_solution(f"decoded_bent_function_{input_variables}_{max_degree}.txt")
		print(f"\nSolution saved to 'decoded_bent_function_{input_variables}_{max_degree}.txt'")
		
		process_time_value = decoding.get_timings()['process-time-since-initialization']
		print(f"The SAT Instance took {process_time_value}s")
	else:
		print("No bent function can be found.")