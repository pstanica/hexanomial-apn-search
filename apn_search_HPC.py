# FILE: apn_search_HPC.py
#
# APN Hexanomial Search and Classification - CORRECTED VERSION
# This version includes proper CCZ-equivalence testing based on the Magma code
#
# Key improvements:
# 1. Implements proper gammaRank (from Magma cryptocriteria1.txt)
# 2. Removed incorrect BC classification tables
# 3. Uses only TRUE CCZ-invariants for classification
# 4. DeltaRank is optional (too slow for large fields)

from collections import Counter, defaultdict
import time
from sage.all import GF, Matrix, ZZ, log, vector, VectorSpace, PolynomialRing

# ============================================================================
# PART 1: APN SEARCH FUNCTIONS (UNCHANGED)
# ============================================================================

def check_condition_C1(A, B, C, D, E, q):
    """Check if (C1) holds - if so, NOT APN"""
    if C == 0 and D == 0 and A != 0:
        if A**q * B == B**q and A**q * E == E**q:
            return True
    return False

def check_condition_C2(A, B, C, D, E, q):
    """Check if (C2) holds - if so, NOT APN"""
    if A*C*D != 0:
        if A**(q+1) == 1 and D == A*C**q and B**q == A**q*B and E**q == A**q*E:
            return True
    return False

def compute_h1(A, B, C, D, q):
    """Compute h1 polynomial"""
    return (A**(q+1) * B**(q+1) + A * B**(2*q) + A**q * B**2 + 
            B**2 * C**q * D**q + B**(q+1) * C**(q+1) + 
            B**(q+1) * D**(q+1) + B**(q+1) + B**(2*q) * C * D)

def check_condition_C6(A, C, D, q):
    """Check if (C6) holds"""
    return (A*D**q + C != 0 or 
            A**(q+1) + C**(q+1) + D**(q+1) + 1 != 0)

def check_condition_C7(A, B, C, D, q):
    """Check if (C7) holds"""
    return compute_h1(A, B, C, D, q) != 0

def is_candidate_APN(A, B, C, D, E, q):
    """Check if parameters avoid all proven non-APN conditions."""
    if A == 0:
        return False
    
    if check_condition_C1(A, B, C, D, E, q):
        return False
    if check_condition_C2(A, B, C, D, E, q):
        return False
    
    if check_condition_C6(A, C, D, q) and check_condition_C7(A, B, C, D, q):
        return False
    
    return True

def get_field_info(F, q):
    """Get minimal polynomial and generator information for the field."""
    gen = F.gen()
    min_poly = F.modulus()
    return gen, min_poly
    
def test_APN_property(A, B, C, D, E, F, q):
    """
    Test if the function is APN by checking the differential equation.
    """
    for a in F:
        if a == 0:
            continue
            
        solutions = set()
        for x in F:
            val = (A*a + a**(2*q)*E + a**q*D)*x**2
            val += (a**2*A + a**(2*q)*C + a**q*B)*x
            val += (a**2*E + a*C + a**q)*x**(2*q)
            val += (a**2*D + a*B + a**(2*q))*x**q
            
            if val == 0:
                solutions.add(x)
        
        trivial = {F(0), a}
        if not solutions.issubset(trivial):
            return False
    
    return True

def format_polynomial_for_file(A, B, C, D, E, q):
    """Format polynomial for file output"""
    terms = []
    
    if A != 0:
        terms.append(f"({A})*x^3")
    if B != 0:
        terms.append(f"({B})*x^{q+1}")
    if C != 0:
        terms.append(f"({C})*x^{2*q+1}")
    if D != 0:
        terms.append(f"({D})*x^{q+2}")
    if E != 0:
        terms.append(f"({E})*x^{2*q+2}")
    
    terms.append(f"x^{3*q}")
    
    return " + ".join(terms)

def format_for_file_with_coeffs(A, B, C, D, E, q):
    """Output format: coefficients followed by polynomial
    Use integer representation for field elements to make Magma parsing easier
    """
    F = A.parent()
    
    # Convert field elements to integer representation (0 to q^2-1)
    def field_to_int(elem):
        # Get the polynomial representation
        poly_list = elem.polynomial().list()
        # Convert to integer using polynomial evaluation at 2
        # For GF(q^2) with generator a, element sum(c_i * a^i) -> sum(c_i * 2^i)
        return sum(int(c) * (2**i) for i, c in enumerate(poly_list))
    
    A_int = field_to_int(A)
    B_int = field_to_int(B)
    C_int = field_to_int(C)
    D_int = field_to_int(D)
    E_int = field_to_int(E)
    
    # Also include symbolic representation for human readability
    coeffs_int = f"{A_int},{B_int},{C_int},{D_int},{E_int}"
    coeffs_sym = f"{A},{B},{C},{D},{E}"
    poly = format_polynomial_for_file(A, B, C, D, E, q)
    
    return f"{coeffs_int} # {coeffs_sym} | {poly}"

def search_APN_hexanomials(n, max_candidates=None, max_time=None, 
                            verbose=True, output_file=None, 
                            progress_interval=1000):
    """
    Search for APN hexanomials over F_{2^n}^2.
    """
    q = 2**n
    F = GF(q**2, 'a')
    
    if verbose:
        print(f"Searching over F_{{2^{n}}}^2 (GF({q**2})) where q = {q}")
        print(f"Field size: {q**2}, Total param space: {(q**2)**5}")
        if max_candidates:
            print(f"Max candidates to test: {max_candidates}")
        if max_time:
            print(f"Max time: {max_time} seconds")
        if output_file:
            print(f"Output file: {output_file}")
        print()
    
    candidates_tested = 0
    candidates_filtered = 0
    apn_found = []
    start_time = time.time()
    
    file_handle = None
    if output_file:
        file_handle = open(output_file, 'w')
        gen, min_poly = get_field_info(F, q)
        file_handle.write(f"# APN Hexanomials over F_{{2^{n}}}^2 (q = {q})\n")
        file_handle.write(f"# Format: A,B,C,D,E | polynomial\n")
        file_handle.write(f"# Field: GF({q**2}, 'a')\n")
        file_handle.write(f"# Primitive element: a\n")
        file_handle.write(f"# Minimal polynomial: {min_poly}\n\n")
    
    try:
        if q <= 4 and max_candidates is None:
            if verbose:
                print("Running exhaustive search...\n")
            
            total_iterations = F.order()**5
            total_iterations_float = float(total_iterations)
            check_interval = max(1, total_iterations // 200)
            count = 0
            
            for A in F:
                if max_time and (time.time() - start_time) > max_time:
                    break
                    
                for B in F:
                    for C in F:
                        for D in F:
                            if max_time and (time.time() - start_time) > max_time:
                                break
                            for E in F:
                                count += 1
                                if verbose and count % check_interval == 0:
                                    progress_percent = float(count / total_iterations_float * 100)
                                    print(f"  ... progress: {progress_percent:.1f}%")
                                    
                                if is_candidate_APN(A, B, C, D, E, q):
                                    candidates_tested += 1
                                    
                                    if test_APN_property(A, B, C, D, E, F, q):
                                        apn_found.append((A, B, C, D, E))
                                        
                                        if file_handle:
                                            output_str = format_for_file_with_coeffs(A, B, C, D, E, q)
                                            file_handle.write(f"{output_str}\n")
                                            file_handle.flush()
                                        
                                        if verbose and len(apn_found) % 100 == 0 and len(apn_found) > 0:
                                            print(f"  >>> Found {len(apn_found)} APN functions...")
                                else:
                                    candidates_filtered += 1
        else:
            if verbose:
                limit_str = f"up to {max_candidates}" if max_candidates else "unlimited"
                print(f"Running random search ({limit_str} candidates)...\n")
            
            tested_set = set()
            
            while True:
                if max_candidates and candidates_tested >= max_candidates:
                    if verbose:
                        print(f"\nCandidate limit reached ({max_candidates})")
                    break
                    
                if max_time and (time.time() - start_time) > max_time:
                    if verbose:
                        print(f"\nTime limit reached ({max_time}s)")
                    break
                
                A = F.random_element()
                B = F.random_element()
                C = F.random_element()
                D = F.random_element()
                E = F.random_element()
                
                param_tuple = (A, B, C, D, E)
                if param_tuple in tested_set:
                    continue
                tested_set.add(param_tuple)
                
                if is_candidate_APN(A, B, C, D, E, q):
                    candidates_tested += 1
                    
                    if verbose and candidates_tested % progress_interval == 0:
                        elapsed = time.time() - start_time
                        rate = candidates_tested / elapsed if elapsed > 0 else 0
                        print(f"Tested: {candidates_tested} | Found: {len(apn_found)} | "
                              f"Rate: {rate:.1f} tests/sec | Elapsed: {elapsed:.1f}s")
                    
                    if test_APN_property(A, B, C, D, E, F, q):
                        apn_found.append((A, B, C, D, E))
                        
                        if file_handle:
                            output_str = format_for_file_with_coeffs(A, B, C, D, E, q)
                            file_handle.write(f"{output_str}\n")
                            file_handle.flush()
                        
                        if verbose:
                            print(f"  >>> APN #{len(apn_found)} found! (Tested {candidates_tested})")
                else:
                    candidates_filtered += 1
    
    finally:
        if file_handle:
            file_handle.close()
    
    elapsed_time = time.time() - start_time
    if verbose:
        print("\n" + "="*70)
        print("SEARCH COMPLETE")
        print("="*70)
        total_seen = candidates_tested + candidates_filtered
        if total_seen == 0:
            total_seen = 1
        print(f"Total candidates considered: {total_seen}")
        print(f"Candidates filtered by theory: {candidates_filtered} ({candidates_filtered/float(total_seen) * 100:.1f}%)")
        print(f"Candidates fully tested: {candidates_tested} ({candidates_tested/float(total_seen) * 100:.1f}%)")
        print(f"APN functions found: {len(apn_found)}")
        print(f"Total time: {elapsed_time:.2f} seconds")
        if candidates_tested > 0 and elapsed_time > 0:
            print(f"Average rate: {candidates_tested/elapsed_time:.1f} tests/sec")
        if output_file:
            print(f"Results written to: {output_file}")
        print()
    
    return apn_found

# ============================================================================
# PART 2: PROPER CCZ-INVARIANT COMPUTATION (FROM MAGMA)
# ============================================================================

def build_function_table(A, B, C, D, E, F, q):
    """Build complete lookup table for f(x)."""
    table = {}
    for x in F:
        fx = (x * (A*x**2 + B*x**q + C*x**(2*q)) + 
              x**2 * (D*x**q + E*x**(2*q)) + 
              x**(3*q))
        table[x] = fx
    return table

def compute_gamma_rank_magma(A, B, C, D, E, F, q):
    """
    Compute gamma-rank following the Magma implementation.
    This is the rank of the incidence matrix of graph cosets.
    
    From Magma code:
    function gammaRank(polyF)
        Fn:=BaseRing(Parent(polyF));
        n:=2*Degree(Fn);  // n is the total dimension (Fn is the codomain field)
        M:=ZeroMatrix(GF(2),2^n,2^n);
        W:=VectorSpace(GF(2),n);
        
        Gf:={W!(Eltseq(v) cat Eltseq(Evaluate(polyF,v))): v in Fn};
        for w in W do
            ww:=[Integers()!w[i]:i in [1..n]];
            j:=SequenceToInteger(ww,2)+1;
            GFtilde:={r+w:r in Gf};
            for v in GFtilde do
                vv:=[Integers()!v[i]:i in [1..n]];
                i:=SequenceToInteger(vv,2)+1;
                M[i][j]:=1;
            end for;
        end for;
        return Rank(M);
    end function;
    """
    print(f"    Computing Gamma-rank (Magma-style)...")
    start_time = time.time()
    
    # Build function table
    func_table = build_function_table(A, B, C, D, E, F, q)
    
    # CRITICAL: Match the Magma code exactly
    # Magma: n := 2*Degree(Fn) where Fn is the base field
    # Our F is GF(q^2), which has degree over GF(2)
    n_field = F.degree()  # Degree of F over GF(2)
    n_total = 2 * n_field  # Total dimension for graph (x, F(x))
    
    print(f"    Field F = GF({F.cardinality()})")
    print(f"    n_field (degree of F over GF(2)) = {n_field}")
    print(f"    n_total (dimension of graph) = {n_total}")
    
    # Create vector space GF(2)^n_total
    W = VectorSpace(GF(2), n_total)
    print(f"    Vector space: GF(2)^{n_total}, cardinality={W.cardinality()}")
    
    # Create the graph Gf = {(v, F(v)) : v in F}
    # Each element v in F and F(v) is represented as a vector in GF(2)^n_field
    Gf_set = set()
    
    for v in F:
        fv = func_table[v]
        # Convert v and fv to bit vectors of length n_field
        v_poly_list = v.polynomial().list()
        fv_poly_list = fv.polynomial().list()
        
        # Pad to exactly n_field length
        v_bits = v_poly_list + [0]*(n_field - len(v_poly_list))
        fv_bits = fv_poly_list + [0]*(n_field - len(fv_poly_list))
        
        # Ensure exactly n_field elements
        v_bits = v_bits[:n_field]
        fv_bits = fv_bits[:n_field]
        
        # Concatenate to get element of GF(2)^(2n_field) = GF(2)^n_total
        graph_bits = v_bits + fv_bits
        
        # Must be exactly n_total length
        if len(graph_bits) != n_total:
            print(f"Warning: graph_bits length {len(graph_bits)} != {n_total}")
            continue
            
        Gf_set.add(tuple(graph_bits))  # Use tuple for hashing
    
    # Convert back to vectors for arithmetic
    Gf = [W(list(vec)) for vec in Gf_set]
    
    print(f"    Graph Gf size: {len(Gf)} (should be {F.cardinality()})")
    
    if len(Gf) != F.cardinality():
        print(f"    WARNING: Graph size mismatch!")
        print(f"    Expected: {F.cardinality()}, Got: {len(Gf)}")
    
    # Create the 2^n x 2^n matrix over GF(2)
    matrix_size = 2**n_total
    M = Matrix(GF(2), matrix_size, matrix_size)
    
    print(f"    Building {matrix_size}x{matrix_size} incidence matrix...")
    
    # For each w in W (columns)
    for w_vec in W:
        # Convert w to integer index (column)
        w_bits = [int(w_vec[i]) for i in range(n_total)]
        j = sum(w_bits[i] * (2**i) for i in range(n_total))  # Binary to decimal
        
        # Compute Gf_tilde = {r + w : r in Gf}
        Gf_tilde = [r + w_vec for r in Gf]
        
        # For each v in Gf_tilde (rows)
        for v_vec in Gf_tilde:
            # Convert v to integer index (row)
            v_bits = [int(v_vec[i]) for i in range(n_total)]
            i = sum(v_bits[k] * (2**k) for k in range(n_total))
            
            # Set M[i, j] = 1
            M[i, j] = 1
    
    print(f"    Computing matrix rank...")
    rank = M.rank()
    
    elapsed = time.time() - start_time
    print(f"    Gamma-rank: {rank} (time: {elapsed:.2f}s)")
    
    return rank

def compute_differential_uniformity(func_table, F):
    """
    Compute differential uniformity and spectrum.
    TRUE CCZ-INVARIANT.
    """
    max_delta = 0
    spectrum = defaultdict(int)
    
    for a in F:
        if a == 0:
            continue
        
        derivative_counts = defaultdict(int)
        for x in F:
            diff = func_table[x + a] + func_table[x]
            derivative_counts[diff] += 1
        
        for b, count in derivative_counts.items():
            max_delta = max(max_delta, count)
            spectrum[count] += 1
    
    # Account for zero entries
    num_a = F.order() - 1
    total_pairs = num_a * F.order()
    pairs_accounted = sum(spectrum.values())
    spectrum[0] = total_pairs - pairs_accounted
    
    spectrum_tuple = tuple(sorted(spectrum.items()))
    return max_delta, spectrum_tuple

def compute_walsh_spectrum(func_table, F, q):
    """
    Compute Walsh spectrum distribution.
    TRUE CCZ-INVARIANT (up to sign).
    """
    walsh_values = []
    
    for a in F:
        for b in F:
            if a == 0 and b == 0:
                walsh_values.append(F.order())
                continue
                
            walsh_sum = 0
            for x in F:
                fx = func_table[x]
                inner = a * fx + b * x
                trace_val = inner.trace()
                trace_int = ZZ(trace_val)
                walsh_sum += (-1)**trace_int
            
            walsh_values.append(abs(walsh_sum))
    
    walsh_counter = Counter(walsh_values)
    return tuple(sorted(walsh_counter.items()))

def check_permutation_property(func_table, F):
    """
    Check if function is a permutation.
    TRUE CCZ-INVARIANT.
    """
    return len(set(func_table.values())) == len(F)

def compute_ccz_invariants(A, B, C, D, E, F, q):
    """
    Compute TRUE CCZ-invariants for classification.
    Uses Magma-style gamma-rank.
    """
    print(f"    Building function table...")
    func_table = build_function_table(A, B, C, D, E, F, q)
    
    print(f"    Computing differential spectrum...")
    diff_uniform, diff_spectrum = compute_differential_uniformity(func_table, F)
    
    print(f"    Computing Walsh spectrum...")
    walsh_spectrum = compute_walsh_spectrum(func_table, F, q)
    
    print(f"    Checking permutation property...")
    is_perm = check_permutation_property(func_table, F)
    
    # Gamma-rank from Magma
    gamma_rank = compute_gamma_rank_magma(A, B, C, D, E, F, q)
    
    invariants = {
        'differential_uniformity': diff_uniform,
        'differential_spectrum': diff_spectrum,
        'walsh_spectrum': walsh_spectrum,
        'gamma_rank': gamma_rank,
    }
    
    return invariants

def create_ccz_invariant_key(inv):
    """
    Create classification key using ONLY true CCZ-invariants.
    """
    return (
        inv['differential_spectrum'],
        inv['walsh_spectrum'],
        inv['gamma_rank'],
    )

# ============================================================================
# PART 3: CLASSIFICATION FUNCTIONS
# ============================================================================

def parse_apn_file(filename, n):
    """Parse APN file with format: A_int,B_int,C_int,D_int,E_int # A_sym,B_sym,C_sym,D_sym,E_sym | polynomial"""
    q = 2**n
    try:
        F = GF(q**2, 'a')
    except Exception as e:
        print(f"Error creating field GF({q**2}): {e}")
        return [], None, 0
        
    functions = []
    
    print(f"Reading from {filename}...")
    
    # Helper: Convert integer to field element
    def int_to_field_element(i, F):
        if i == 0:
            return F(0)
        
        # Convert integer to field element using binary representation
        a = F.gen()
        result = F(0)
        power = 0
        
        while i > 0:
            if i % 2 == 1:
                result += a**power
            i = i // 2
            power += 1
        
        return result
    
    try:
        with open(filename, 'r') as f:
            for line_num, line in enumerate(f, 1):
                line = line.strip()
                if not line or line.startswith('#'):
                    continue
                    
                if '|' not in line:
                    continue
                
                # Split on '#' first to get integer part
                if '#' in line:
                    parts = line.split('#', 1)
                    coeffs_str = parts[0].strip()
                else:
                    # Old format without #
                    parts = line.split('|', 1)
                    coeffs_str = parts[0].strip()
                
                # Parse integer coefficients
                parts = coeffs_str.split(',')
                if len(parts) != 5:
                    print(f"Warning: Line {line_num} has wrong format")
                    continue
                
                try:
                    # Try parsing as integers first (new format)
                    try:
                        A_int = int(parts[0].strip())
                        B_int = int(parts[1].strip())
                        C_int = int(parts[2].strip())
                        D_int = int(parts[3].strip())
                        E_int = int(parts[4].strip())
                        
                        # Convert integers to field elements
                        A = int_to_field_element(A_int, F)
                        B = int_to_field_element(B_int, F)
                        C = int_to_field_element(C_int, F)
                        D = int_to_field_element(D_int, F)
                        E = int_to_field_element(E_int, F)
                    except ValueError:
                        # Fall back to symbolic parsing (old format)
                        A = F(parts[0].strip())
                        B = F(parts[1].strip())
                        C = F(parts[2].strip())
                        D = F(parts[3].strip())
                        E = F(parts[4].strip())
                    
                    functions.append((A, B, C, D, E))
                except Exception as e:
                    print(f"Warning: Line {line_num} parse error: {e}")
                    continue
    except FileNotFoundError:
        print(f"Error: File not found: {filename}")
        return [], None, 0
    
    print(f"Loaded {len(functions)} APN functions")
    return functions, F, q

def select_class_representative(members, F, q):
    """Select a canonical representative from an equivalence class."""
    def score_function(coeffs):
        A, B, C, D, E, inv = coeffs
        
        non_zero = sum([A != 0, B != 0, C != 0, D != 0, E != 0])
        
        int_repr = []
        for c in [A, B, C, D, E]:
            poly_list = c.polynomial().list()
            poly_list.extend([0] * (F.degree() - len(poly_list)))
            int_repr.extend(poly_list)
            
        return (non_zero, tuple(int_repr))
    
    representative = min(members, key=score_function)
    return representative[:5]

def format_function_readable(A, B, C, D, E, q):
    """Format function in readable form."""
    term_dict = {}
    F = A.parent()
    
    if A != 0:
        term_dict[3] = term_dict.get(3, 0) + A
    if B != 0:
        exp = int(q+1)
        term_dict[exp] = term_dict.get(exp, 0) + B
    if C != 0:
        exp = int(2*q+1)
        term_dict[exp] = term_dict.get(exp, 0) + C
    if D != 0:
        exp = int(q+2)
        term_dict[exp] = term_dict.get(exp, 0) + D
    if E != 0:
        exp = int(2*q+2)
        term_dict[exp] = term_dict.get(exp, 0) + E
    
    exp = int(3*q)
    term_dict[exp] = term_dict.get(exp, 0) + F(1)
    
    terms = [(coeff, exp) for exp, coeff in term_dict.items() if coeff != 0]
    terms.sort(key=lambda x: x[1])
    
    num_terms = len(terms)
    type_names = {1: "Monomial", 2: "Binomial", 3: "Trinomial", 
                  4: "Quadrinomial", 5: "Pentanomial", 6: "Hexanomial"}
    func_type = type_names.get(num_terms, f"{num_terms}-nomial")
    
    poly_parts = []
    for coeff, exp in terms:
        if coeff == 1:
            poly_parts.append(f"x^{exp}")
        else:
            # Field was defined as GF(q^2, 'a'), so str(coeff) will use 'a'
            coeff_str = str(coeff)
            poly_parts.append(f"({coeff_str})*x^{exp}")
    
    poly_str = " + ".join(poly_parts)
    
    return func_type, poly_str

def export_for_magma(input_file, output_file, n):
    """Export APN functions from Python format to Magma format"""
    q = 2**n
    
    with open(output_file, 'w') as f:
        f.write(f"// APN Hexanomials for classification in Magma\n")
        f.write(f"// Field: GF({q}^2), n={n}, q={q}\n\n")
        f.write(f"q := {q};\n")
        f.write(f"FF<w> := GF(q^2);\n")
        f.write(f"R<x> := PolynomialRing(FF);\n\n")
        f.write(f"apn_functions := [\n")
        
        count = 0
        with open(input_file, 'r') as inp:
            for line in inp:
                if line.strip() and not line.startswith('#'):
                    parts = line.split('#')[0].strip().split(',')
                    if len(parts) == 5:
                        count += 1
                        A, B, C, D, E = [int(p.strip()) for p in parts]
                        f.write(f"  [{A}, {B}, {C}, {D}, {E}]")
                        f.write(f",\n")
        
        f.write(f"\n];\n\n")
        f.write(f"print \"Loaded\", #apn_functions, \"APN functions\";\n")

def classify_with_enhanced_invariants(functions, F, q, output_file):
    """
    Classify using proper CCZ-invariants with Magma-style gamma-rank.
    """
    if not F:
        print("Error: Invalid field provided to classification.")
        return {}
    
    print(f"\nComputing CCZ-invariants for {len(functions)} functions...")
    print("Using: Differential spectrum, Walsh spectrum, Permutation property, Gamma-rank (Magma)")
    
    start_time = time.time()
    
    invariant_classes = defaultdict(list)
    
    for idx, (A, B, C, D, E) in enumerate(functions):
        print(f"\nProcessing function {idx + 1}/{len(functions)}: ({A}, {B}, {C}, {D}, {E})")
        
        inv = compute_ccz_invariants(A, B, C, D, E, F, q)
        inv_key = create_ccz_invariant_key(inv)
        invariant_classes[inv_key].append((A, B, C, D, E, inv))
    
    elapsed = time.time() - start_time
    print(f"\nInvariant computation completed in {elapsed:.1f} seconds")
    print(f"Found {len(invariant_classes)} distinct CCZ-invariant classes (RIGOROUS LOWER BOUND)")
    
    print(f"\nWriting results to {output_file}...")
    
    with open(output_file, 'w') as f:
        gen, min_poly = get_field_info(F, q)
        f.write(f"# CCZ-Invariant Classification (Magma-Style Gamma-Rank)\n")
        f.write(f"# Total functions analyzed: {len(functions)}\n")
        f.write(f"# Distinct CCZ-invariant classes (LOWER BOUND): {len(invariant_classes)}\n")
        f.write(f"# Field: F_{{2^{int(log(q,2))}}}^2 (q = {q})\n")
        f.write(f"# Invariants: differential_spectrum, walsh_spectrum, gamma_rank\n")
        f.write(f"# All invariants are TRUE CCZ-invariants\n\n")
        
        sorted_classes = sorted(invariant_classes.items(), 
                                key=lambda x: len(x[1]), reverse=True)
        
        for class_num, (inv_key, members) in enumerate(sorted_classes, 1):
            rep_A, rep_B, rep_C, rep_D, rep_E = select_class_representative(members, F, q)
            func_type, poly_str = format_function_readable(rep_A, rep_B, rep_C, rep_D, rep_E, q)
            
            f.write(f"{'=' * 70}\n")
            f.write(f"CCZ-EQUIVALENCE CLASS {class_num}: {len(members)} functions\n")
            f.write(f"{'=' * 70}\n\n")
            
            f.write(f"REPRESENTATIVE ({func_type}):\n")
            f.write(f"  Coefficients: A={rep_A}, B={rep_B}, C={rep_C}, D={rep_D}, E={rep_E}\n")
            f.write(f"  f(x) = {poly_str}\n\n")
            
            sample_inv = members[0][5]
            f.write(f"CCZ-INVARIANTS:\n")
            f.write(f"  Differential uniformity: {sample_inv['differential_uniformity']}\n")
            f.write(f"  Differential spectrum: {sample_inv['differential_spectrum']}\n")
            f.write(f"  Walsh spectrum (first 5): {str(sample_inv['walsh_spectrum'][:5])}...\n")
            #f.write(f"  Is permutation: {sample_inv['is_permutation']}\n")
            f.write(f"  Gamma-rank (Magma): {sample_inv['gamma_rank']}\n\n")
            
            f.write(f"ALL FUNCTIONS IN CLASS:\n")
            for i, (A, B, C, D, E, inv) in enumerate(members[:50]):
                f.write(f"  {i+1}. A={A}, B={B}, C={C}, D={D}, E={E}\n")
            
            if len(members) > 50:
                f.write(f"  ... and {len(members) - 50} more\n")
            
            f.write("\n")
            f.flush()
    
    print(f"\nClassification complete! Results written to {output_file}")
    print(f"\nRIGOROUS LOWER BOUND: At least {len(invariant_classes)} distinct CCZ-equivalence classes")
    
    return invariant_classes

# ============================================================================
# MAIN EXECUTION
# ============================================================================

if __name__ == "__main__":
    
    print("APN Hexanomial Search and Classification")
    print("This version uses proper Magma-style gamma-rank for CCZ-equivalence")
    print("WARNING: Gamma-rank computation is VERY slow for n >= 3")
    print()
    
    # --- Experiment 1: F_4 (n=1) ---
    print("\n" + "=" * 70)
    print("STARTING: F_4 (n=1, q=2) - Exhaustive Search")
    print("=" * 70)
    N_FIELD_1 = 1
    
    apn_F4 = search_APN_hexanomials(n=N_FIELD_1, output_file="apn_hexanomials_F4.txt", verbose=True)
    
    if len(apn_F4) > 0:
        print("\n--- Starting F_4 Classification ---")
        functions_F4, F4, q4 = parse_apn_file("apn_hexanomials_F4.txt", n=N_FIELD_1)
        if F4:
            classes_F4 = classify_with_enhanced_invariants(
                functions_F4, F4, q4, "apn_CCZclassified_F4_corrected.txt"
            )
        print("--- F_4 Classification Complete ---")
    
    # --- Experiment 2: F_16 (n=2) ---
    print("\n" + "=" * 70)
    print("STARTING: F_16 (n=2, q=4) - Exhaustive Search")
    print("=" * 70)
    N_FIELD_2 = 2
    
    apn_F16 = search_APN_hexanomials(n=N_FIELD_2, output_file="apn_hexanomials_F16.txt", verbose=True)
    
    if len(apn_F16) > 0:
        print("\n--- Starting F_16 Classification ---")
        print("WARNING: This will take a long time due to gamma-rank computation")
        functions_F16, F16, q16 = parse_apn_file("apn_hexanomials_F16.txt", n=N_FIELD_2)
        if F16:
            classes_F16 = classify_with_enhanced_invariants(
                functions_F16, F16, q16, "apn_CCZclassified_F16_corrected.txt"
            )
        print("--- F_16 Classification Complete ---")

    # --- Experiment 3: F_64 (n=3) ---
    print("\n" + "=" * 70)
    print("STARTING: F_64 (n=3, q=8) - Random Search")
    print("=" * 70)
    N_FIELD_3 = 3
    
    MAX_CANDIDATES_F64 = 120000
    MAX_TIME_F64 = 21600
    PROGRESS_INTERVAL_F64 = 3000
    
    apn_F64 = search_APN_hexanomials(
        n=N_FIELD_3, 
        max_candidates=MAX_CANDIDATES_F64,
        max_time=MAX_TIME_F64,
        output_file="apn_hexanomials_F64.txt",
        progress_interval=PROGRESS_INTERVAL_F64,
        verbose=True
    )
    if len(apn_F64) > 0:
        print("\n--- F_64 Search Complete ---")
        print(f"Found {len(apn_F64)} APN functions")
        print(f"Results saved to apn_hexanomials_F64.txt")
        
        # Export to Magma format
        print("\n--- Exporting F_64 for Magma Classification ---")
        export_for_magma("apn_hexanomials_F64.txt", "apn_F64_magma.txt", N_FIELD_3)
        print("Exported to apn_F64_magma.txt")
        print("\nTo classify in Magma, use either:")
        print('  Option 1: magma field:=64 ccz_classify_all.magma')
        print('  Option 2: load "apn_F64_magma.txt"; load "cryptocriteria1.txt";')

    # --- Experiment 4: F_256 (n=4) ---
    print("\n" + "=" * 70)
    print("STARTING: F_256 (n=4, q=16) - Random Search")
    print("=" * 70)
    N_FIELD_4 = 4
    
    MAX_CANDIDATES_F256 = 200000
    MAX_TIME_F256 = 43200
    PROGRESS_INTERVAL_F256 = 3000
    
    apn_F256 = search_APN_hexanomials(
        n=N_FIELD_4, 
        max_candidates=MAX_CANDIDATES_F256,
        max_time=MAX_TIME_F256,
        output_file="apn_hexanomials_F256.txt",
        progress_interval=PROGRESS_INTERVAL_F256,
        verbose=True
    )

    if len(apn_F256) > 0:
        print("\n--- F_256 Search Complete ---")
        print(f"Found {len(apn_F256)} APN functions")
        print(f"Results saved to apn_hexanomials_F256.txt")
        
        # Export to Magma format
        print("\n--- Exporting F_256 for Magma Classification ---")
        export_for_magma("apn_hexanomials_F256.txt", "apn_F256_magma.txt", N_FIELD_4)
        print("Exported to apn_F256_magma.txt")
        print("\nTo classify in Magma, use either:")
        print('  Option 1: magma field:=256 ccz_classify_all.magma')
        print('  Option 2: load "apn_F256_magma.txt"; load "cryptocriteria1.txt";')
        
    print("\n" + "=" * 70)
    print("ALL EXPERIMENTS COMPLETE")
    print("=" * 70)
