# Bent Function SAT Encoder/Decoder

**Author:** Mohammed Al-Anezi  
**Date:** 2026-03-10  

This project encodes the search for **bent Boolean functions** (maximum nonlinearity) as a SAT problem and solves it using the CaDiCaL SAT solver. It supports:
- Single‑run mode for fixed `(n, max_degree)`.
- Sweep mode that tests all `(n, d)` pairs within given bounds.
- A Python trace‑based encoder that uses the finite‑field inner product.
- A Python “naive” encoder (`bentencode_naive.py`) that is slower but easier to understand.
- A Python truncated encoder that reduces the number of variables and clauses while being as powerful as the naive encoder.

All C++ code links directly to the CaDiCaL library (no external DIMACS files), leading to high performance. If you wish to run this program, I **strongly recommend** you use the C++ version of the code since it is easier to modify and understand (if you know C++).

---

## 1. Files in the Distribution

| File                         | Description                                                                 |
|------------------------------|-----------------------------------------------------------------------------|
| `bentdecode_truncated.cpp`   | Main C++ encoder/decoder for a single `(n, max_degree)` instance.           |
| `bentdecode_truncated_sweep.cpp` | Sweep version: runs all `(n, d)` pairs up to `MAX_N` and `MAX_D`.        |
| `bentencode_naive.py`, `bentdecode_naive.py`    | Python encoder and decoder using the standard dot product, simpler, but slower. Depends on `encode.py` and `decode.py`. |
| `bentencode_truncated.py`, `bentencode_truncated.py`    | Python encoder and decoder but more optimized. Depends on `encode.py` and `decode.py`. |
| `bentencode_trace.py`, `bentdecode_trace.py`        | Python encoder and decoder using trace‑based inner product (GF(2ⁿ) multiplication).     |
| `Makefile`                   | Builds the two C++ executables.                                             |
| `README.md` (this file)      | Compilation, configuration, and usage instructions.                         |

---

## 2. Dependencies

### Required
- **CaDiCaL** SAT solver (version 2.1.3 or later), library version  
  – Download from [https://github.com/arminbiere/cadical](https://github.com/arminbiere/cadical)  
  – Build according to its instructions (typically `./configure && make`).  
  – The provided Makefile expects `libcadical.a` at `../cadical-master/build/libcadical.a`.  
    *Adjust the `CADICAL_DIR` variable in the Makefile if your CaDiCaL installation is elsewhere.*
- **C++20 compiler** (g++ >= 10 or clang >= 12)  
- **Python 3** (for the Python encoders), with no extra packages (uses only standard library).  
- For `bentencode_naive.py` and `bentencode_truncated.py`: the supporting files `encode.py` and `decode.py` must be present in the same directory (they implement `SATEncoder` and `SATDecoder`).

---

## 3. Compilation

### Using the Makefile
```bash
# Rename the provided makefile
mv Makefile\ -Copy.txt Makefile

# Build the single‑run executable
make single

# Build the sweep executable
make sweep

# Build an AddressSanitizer version (debugging)
make asan

# Clean all built files
make clean
```

### Manual compilation (example)
```
# Single‑run
g++ -std=c++20 -O3 -I../cadical-master/src -o bentdecode_truncated bentdecode_truncated.cpp ../cadical-master/build/libcadical.a

# Sweep
g++ -std=c++20 -O3 -I../cadical-master/src -o bentdecode_truncated_sweep bentdecode_truncated_sweep.cpp ../cadical-master/build/libcadical.a
```

---

## 4. Configuration

### 4.1 Single‑run (`bentdecode_truncated.cpp`)

Edit the macros at the top of the file:

```cpp
#define N              8    // number of input variables (must be even)
#define MAX_DEGREE     3    // maximum ANF algebraic degree
#define NORMALIZE      1    // 1 = fix f(0) = 0
#define SYM_BREAK      1    // 1 = enforce a1 <= a2 <= ... <= aN
#define MAX_ANF_WEIGHT 0    // max non‑zero ANF coeffs (0 = no limit)
#define TRACK_TIME     1    // 1 = measure per‑phase times
#define PRINT_TIME     1    // 1 = print timing breakdown
#define MAX_RUNTIME    0    // timeout in seconds (0 = disabled)
```

Then compile and run:
```bash
./bentdecode_truncated
```

### 4.2 Sweep run (`bentdecode_truncated_sweep.cpp`)

Similar macros, plus sweep bounds:

```cpp
#define MAX_N          10   // sweep n from 1 to MAX_N (inclusive)
#define MAX_D          10   // sweep d from 1 to min(n, MAX_D)
#define MAX_SOLVER_SECONDS 3600   // timeout per (n,d) trial
```

Then:
```bash
./bentdecode_truncated_sweep > results.txt
```

The sweep prints a detailed line for every `(n,d)` pair, including SAT/UNSAT/TIMEOUT, variable/clause counts, and timing.

### 4.3 Python trace encoder (`bentencode_trace.py`)

Run directly:
```bash
python3 bentencode_trace.py
```

It will self‑test with `n=4`, `max_degree=2`. To change parameters, edit the `__main__` block or call `encode_trace_bent_function(n, irred_poly, max_degree)`.

### 4.4 Python naive encoder (`bentencode_naive.py` or `bentencode_truncated.py`)

This encoder uses the standard dot product `<ω,x>` and is simpler but much slower (especially for `n>=6`). It depends on `encode.py` and `decode.py` (which provide `SATEncoder` and `SATDecoder`).  

To run it:
```bash
python3 bentencode_naive.py # or python3 bentencode_truncated.py
```

By default it encodes a quadratic bent function search for `n=4`, writes a DIMACS file `test_bent_4.cnf`, and attempts to solve it using an external CaDiCaL binary (paths are hardcoded, you may need to adjust them).  

To modify the parameters, edit the `__main__` section or use the `encode_and_save_bent_function()` function. Example:
```python
encoder = encode_and_save_bent_function(6, max_degree=3, output_file="bent_6_3.cnf")
```

---

## 5. Output

### When SAT (bent function found)
- Full truth table (hex and binary, little‑endian).
- Algebraic Normal Form (ANF) as a XOR of monomials.
- List of non‑zero ANF coefficients.
- Independent Walsh‑Hadamard verification (`PASS` if all coefficients have magnitude `2^(n/2)`).

### When UNSAT
- A short message stating that no bent function exists for the given `(n, d)`.

### When TIMEOUT (sweep mode only)
- The trial is marked `TIMEOUT` and the solver is terminated.

Example excerpt for `n=2, d=2`:
```
Result: SAT - bent function found

==============================================================
BENT FUNCTION  (n=2, max_degree=2)
==============================================================

Algebraic Normal Form:
  f(x) = x1 xor x1x2 xor x2

ANF Coefficients (non-zero only):
  a_{1} = 1
  a_{1,2} = 1
  a_{2} = 1

Truth Table (4 values, little-endian):
  Hex: 0xe
  Bin: 0111

Bentness Verification:
  PASS - all Walsh coefficients = +/-2
```

---

## 6. Notes on the Encoding

- **Phase variable elimination** removes the explicit `s_{x,ω}` variables, saving ~`2^(2n)` variables and clauses.
- **Sequential counters** (Sinz encoding) are used for the Walsh cardinality constraints, with an optimisation that omits reverse propagation clauses for `j > minimum` (saves up to 50% of counter clauses).
- **ANF containment** is tested in O(1) using precomputed bitmasks.
- **XOR chains** are built left‑associatively, introducing auxiliary variables only when needed.

---

## 7. Troubleshooting

| Problem                          | Likely solution                                                                 |
|----------------------------------|---------------------------------------------------------------------------------|
| `cadical.hpp: No such file`      | Set `CADICAL_DIR` correctly in the Makefile or add `-I/path/to/cadical/src`.    |
| `undefined reference to CaDiCaL` | Link against `libcadical.a`. The Makefile assumes it is in `$(CADICAL_DIR)/build/`. |
| Sweep runs out of memory         | Reduce `MAX_N` (e.g., to 8) or increase system swap. The Walsh constraints dominate memory. |
| Python script fails              | Ensure Python 3 is used; the script uses only the standard library.             |
| `bentencode_naive.py` (or `bentencode_truncated.py`) missing `encode.py` | The naive encoder requires `encode.py` and `decode.py` (not included in this repository by default). You must obtain them separately or use the C++ version instead. |

---

## 8. Contact & Further Work

- **Repository:** [https://github.com/mohammedalanezi/Bent-Functions-in-SAT-Search](https://github.com/mohammedalanezi/Bent-Functions-in-SAT-Search)  
- **Future directions:**  
  - Implement cyclotomic coset reduction (outlined in `bentencode_trace.py`) to drastically cut ANF variables.  
  - Add constraints to force the solver to find bent functions **inequivalent** to known families (Gold, Kasami, etc.).  
  - Run the sweep on larger clusters (e.g., Compute Canada) for `n=7` and `n=8` with longer timeouts.

For questions or assistance, please contact Mohammed Al‑Anezi.
