"""
By Mohammed Al-Anezi

Bent Function SAT Encoder
Encodes bent function search problems into SAT instances using the SATEncoder module.
"""

from encode import SATEncoder
from decode import SATDecoder
from typing import List, Tuple, Dict, Optional
import math, os
from itertools import combinations

script_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(script_dir)

class BentFunctionEncoder:
    """Encodes bent function search problems into SAT instances."""
    
    def __init__(self, n: int, max_degree: Optional[int] = None, 
                 label: str = "bent_function", use_pipe: bool = False):
        """
        Initialize a bent function encoder for n variables.
        
        Args:
            n: Number of input variables
            max_degree: Maximum algebraic degree (None means unrestricted)
            label: Label for the SAT instance
            use_pipe: Whether to use in-memory pipe mode
        """
        self.n = n
        self.max_degree = max_degree if max_degree is not None else n
        self.num_inputs = 1 << n  # 2^n
        self.num_freqs = 1 << n   # 2^n
        
        # Initialize SAT encoder
        self.sat = SATEncoder(label=label, use_pipe=use_pipe, warning_bool=False)
        
        # Variable dictionaries
        self.anf_vars: Dict[Tuple[int, ...], int] = {}  # ANF coefficients
        self.tt_vars: List[int] = []                    # Truth table values F_x
        self.phase_vars: Dict[Tuple[int, int], int] = {}  # Phase variables s_{x,ω}
        self.count_vars: Dict[int, List[int]] = {}      # Counting variables for each ω
        
        # Generated bent functions
        self.solutions: List[List[int]] = []
        
    def encode(self, normalize: bool = True, symmetry_breaking: bool = True):
        """
        Encode the complete bent function problem.
        
        Args:
            normalize: Whether to normalize f(0)=0
            symmetry_breaking: Whether to add symmetry breaking constraints
        """
        self._create_variables()
        self._encode_anf_to_truth_table()
        self._encode_phase_variables()
        self._encode_walsh_conditions()
        
        if normalize:
            self._add_normalization_constraints()
        if symmetry_breaking:
            self._add_symmetry_breaking_constraints()
        
        self.sat.finalize_encoding()
    
    def _create_variables(self):
        """Create all SAT variables needed for the encoding."""
        
        # 1. Create ANF variables (a_S) for subsets S of size ≤ max_degree
        print(f"Creating ANF variables for n={self.n}, max_degree={self.max_degree}...")
        
        # Constant term (empty subset)
        self.anf_vars[()] = self.sat.new_variable()
        
        # Linear terms
        for i in range(1, self.n + 1):
            self.anf_vars[(i,)] = self.sat.new_variable()
        
        # Higher degree terms (up to max_degree)
        for degree in range(2, self.max_degree + 1):
            for subset in combinations(range(1, self.n + 1), degree):
                self.anf_vars[subset] = self.sat.new_variable()
        
        self.sat.add_comment(f"ANF variables: {len(self.anf_vars)} total")
        
        # 2. Create truth table variables (F_x)
        print(f"Creating truth table variables for {self.num_inputs} inputs...")
        for x in range(self.num_inputs):
            self.tt_vars.append(self.sat.new_variable())
        
        # 3. Create phase variables (s_{x,ω})
        print(f"Creating phase variables for {self.num_inputs}×{self.num_freqs} pairs...")
        for x in range(self.num_inputs):
            for ω in range(self.num_freqs):
                self.phase_vars[(x, ω)] = self.sat.new_variable()
        
        self.sat.add_comment(f"Total variables created: {self.sat.var_counter}")
    
    def _encode_anf_to_truth_table(self):
        """Encode the relationship between ANF coefficients and truth table values."""
        print("Encoding ANF to truth table constraints...")
        
        for x in range(self.num_inputs):
            # Get binary representation of x
            x_bits = [(x >> i) & 1 for i in range(self.n)]
            
            # Find all subsets S such that S ⊆ support(x) and |S| ≤ max_degree
            relevant_subsets = []
            
            # Constant term is always included
            relevant_subsets.append(())
            
            # Check each ANF subset
            for subset, var in self.anf_vars.items():
                if not subset:  # Skip empty subset (already included)
                    continue
                
                # Check if subset is contained in support(x)
                # i.e., for all i in subset, x has bit i-1 = 1
                if all(x_bits[i-1] == 1 for i in subset):
                    relevant_subsets.append(subset)
            
            # Create XOR of all relevant ANF variables
            anf_vars_list = [self.anf_vars[subset] for subset in relevant_subsets]
            
            if len(anf_vars_list) == 1:
                # Simple equivalence: F_x = a_∅
                a_var = anf_vars_list[0]
                f_var = self.tt_vars[x]
                
                # F_x <=> a_∅
                # (F_x -> a_∅) and (a_∅ -> F_x)
                self.sat.add_clause([-f_var, a_var])    # F_x -> a_∅
                self.sat.add_clause([-a_var, f_var])    # a_∅ -> F_x
            else:
                # XOR encoding: F_x = ⨁_{S} a_S
                # We'll create auxiliary XOR variable
                xor_result = self.sat._encode_xor(anf_vars_list)
                f_var = self.tt_vars[x]
                
                # F_x <=> xor_result
                self.sat.add_clause([-f_var, xor_result])    # F_x -> XOR
                self.sat.add_clause([-xor_result, f_var])    # XOR -> F_x
        
        self.sat.add_comment(f"Added {self.num_inputs} ANF-to-truth-table constraints")
    
    def _encode_phase_variables(self):
        """Encode phase variables: s_{x,ω} = F_x ⊕ ⟨ω,x⟩."""
        print("Encoding phase variable definitions...")
        
        for x in range(self.num_inputs):
            x_bits = [(x >> i) & 1 for i in range(self.n)]
            
            for ω in range(self.num_freqs):
                ω_bits = [(ω >> i) & 1 for i in range(self.n)]
                
                # Compute dot product ⟨ω,x⟩ = ⨁_{i} ω_i·x_i (mod 2)
                dot_product = sum(ω_bits[i] & x_bits[i] for i in range(self.n)) % 2
                
                # Get variables
                f_var = self.tt_vars[x]
                s_var = self.phase_vars[(x, ω)]
                
                if dot_product == 0:
                    # s_{x,ω} = F_x ⊕ 0 = F_x
                    # So s_{x,ω} <=> F_x
                    self.sat.add_clause([-s_var, f_var])    # s -> F
                    self.sat.add_clause([-f_var, s_var])    # F -> s
                else:  # dot_product == 1
                    # s_{x,ω} = F_x ⊕ 1 = ¬F_x
                    # So s_{x,ω} <=> ¬F_x
                    self.sat.add_clause([-s_var, -f_var])   # s -> ¬F
                    self.sat.add_clause([f_var, s_var])     # ¬F -> s
        
        self.sat.add_comment(f"Added {self.num_inputs * self.num_freqs} phase variable definitions")
    
    def _encode_walsh_conditions(self):
        """
        Encode bentness condition: For each ω, the number of zeros 
        in {s_{x,ω}} must be 2^{n-1} ± 2^{n/2-1}.
        """
        print("Encoding Walsh spectrum (bentness) constraints...")
        
        # For bent functions with n variables:
        expected_zeros_low = (1 << (self.n - 1)) - (1 << (self.n // 2 - 1))
        expected_zeros_high = (1 << (self.n - 1)) + (1 << (self.n // 2 - 1))
        
        print(f"Bent condition: For each ω, #zeros ∈ {{{expected_zeros_low}, {expected_zeros_high}}}")
        print("very slow, needs to be sped up for n=8")#TODO:, between 105-106 it just stops)
        # For each frequency ω, count zeros in phase variables
        for ω in range(self.num_freqs):
            # Collect all phase variables for this ω
            phase_vars_for_ω = [self.phase_vars[(x, ω)] for x in range(self.num_inputs)]
            
            # We need to count where s_{x,ω} = 0 (i.e., F_x = ⟨ω,x⟩)
            # Since s=0 means equality, we can count zeros directly
            
            # Add cardinality constraint: exactly expected_zeros_low OR expected_zeros_high zeros
            # We'll create an auxiliary variable for each case and require at least one
            
            # Case 1: exactly expected_zeros_low zeros
            aux_low = self.sat.new_variable()
            self._encode_exact_zeros(phase_vars_for_ω, expected_zeros_low, aux_low)
            
            # Case 2: exactly expected_zeros_high zeros
            aux_high = self.sat.new_variable()
            self._encode_exact_zeros(phase_vars_for_ω, expected_zeros_high, aux_high)
            
            # Require: (exactly low zeros) OR (exactly high zeros)
            self.sat.add_clause([aux_low, aux_high])

            print(f"{ω}/{self.num_freqs}")
        
        self.sat.add_comment(f"Added {self.num_freqs} Walsh spectrum constraints")
    
    def _encode_exact_zeros(self, variables: List[int], k: int, aux_var: int):
        """
        Encode that exactly k of the variables are 0 (false).
        Returns an auxiliary variable that is true iff exactly k are 0.
        """
        # Note: variable=0 means false, variable=1 means true
        # We want exactly k variables to be 0 (false)
        
        n = len(variables)
        
        # Create negated variables (since we're counting zeros)
        negated_vars = [-v for v in variables]
        
        # Enforce: aux_var -> (exactly k variables are 0)
        # and: (exactly k variables are 0) -> aux_var
        
        # We'll use the auxiliary cardinality clause
        # But note: we need to count zeros, not ones
        # So we count negated variables being true
        
        # First encode: if aux_var is true, then exactly k of negated_vars are true
        # We can use add_auxiliary_cardinality_clause with min=max=k
        
        # Create a temporary variable that's true iff exactly k negated_vars are true
        temp_var = self.sat.add_auxiliary_cardinality_clause(negated_vars, k, k)
        
        # aux_var -> temp_var
        self.sat.add_clause([-aux_var, temp_var])
        
        # temp_var -> aux_var
        self.sat.add_clause([-temp_var, aux_var])
        
        return aux_var
    
    def _add_normalization_constraints(self):
        """Add normalization: f(0) = 0 (constant term = 0)."""
        print("Adding normalization constraints (f(0)=0)...")
        
        # Constant term a_∅ = 0
        self.sat.add_clause([-self.anf_vars[()]])
        
        # F_0 = 0 (truth table at 0)
        self.sat.add_clause([-self.tt_vars[0]])

        # we only need one of these unit clauses, since they encode same end result, both added does speed it up
        
        self.sat.add_comment("Normalized: f(0) = 0")
    
    def _add_symmetry_breaking_constraints(self):
        """
        Add symmetry breaking constraints to reduce solution space.
        Common: order ANF coefficients lexicographically, or fix some patterns.
        """
        if self.n >= 2: # a₁ ≤ a₂ ≤ a₃ ≤ ... ≤ aₙ
            for i in range(1, self.n):
                a_i = self.anf_vars[(i,)]
                a_i_plus_1 = self.anf_vars[(i+1,)]
                # aᵢ ≤ aᵢ₊₁  means  aᵢ → aᵢ₊₁
                self.sat.add_implication_clause([a_i], [a_i_plus_1])

            self.sat.add_comment(f"Symmetry breaking: a1 <= a2 <= ... <= a{self.n}")
    
    def save_to_file(self, filename: str = "bent_function.cnf"):
        """Save the encoded SAT instance to a DIMACS CNF file."""
        self.sat.set_encoding_path(filename)
        self.sat.finalize_encoding()
        print(f"Saved bent function encoding to {filename}")

        print("THIS DOESN'T WORK, NEED TO RECODE save_to_File")
        print("REWRITE SATEncoder's to_dimacs so DUMPED FILES, STILL CAN BE TAKEN FROM")
        print("     THEN USE THAT FOR INFORMATION ON WHAT TO SAVE TO FILE")
    
    def get_dimacs_string(self) -> str:
        """Get the DIMACS CNF representation as a string."""
        return self.sat.to_dimacs()
    
    def get_statistics(self) -> Dict:
        """Get statistics about the encoded problem."""
        return {
            "n": self.n,
            "max_degree": self.max_degree,
            "num_variables": self.sat.var_counter,
            "num_clauses": self.sat.clause_counter,
            "num_anf_vars": len(self.anf_vars),
            "num_tt_vars": len(self.tt_vars),
            "num_phase_vars": len(self.phase_vars)
        }


# Example usage function
def encode_and_save_bent_function(n: int, max_degree: Optional[int] = None, output_file: str = "bent_function.cnf"):
    """
    Convenience function to encode and save a bent function problem.
    
    Example:
        encode_and_save_bent_function(4, max_degree=2, output_file="bent_quadratic_4.cnf")
    """
    encoder = BentFunctionEncoder(n, max_degree, label=f"bent_n{n}_d{max_degree}", use_pipe=True)
    
    print(f"Encoding bent function with n={n}, max_degree={max_degree}")
    print("=" * 50)
    
    encoder.encode(normalize=not False, symmetry_breaking=True)
    
    stats = encoder.get_statistics()
    print("\nEncoding statistics:")
    for key, value in stats.items():
        print(f"  {key}: {value}")
    
    encoder.save_to_file(output_file)
    print(f"\nSaved to {output_file}")

    print("maybe remove all pipe functionality from this script")
    
    return encoder


# For testing/development
if __name__ == "__main__":
    n = 4
    print(f"\nTesting with n={n} (quadratic bent functions)...")
    encoder = encode_and_save_bent_function(n, max_degree=2, output_file="test_bent_4.cnf")
        
    script_dir = os.path.dirname(os.path.abspath(__file__))
    parent_dir = os.path.dirname(script_dir)

    exhaust_satsolver_path = os.path.join(parent_dir, "cadical-exhaust-master", "build", "cadical-exhaust")
    satsolver_path = os.path.join(parent_dir, "cadical-exhaust-master", "build", "cadical")

    decoding = SATDecoder(file_path="test_bent.txt")

    wall_time = decoding.run_sat_solver(
        satsolver_path, 
        input_content=encoder.sat.to_dimacs(),
        display_to_console=True)
    
    if decoding.get_satisfiability():
        print(decoding.get_variable_assignment())