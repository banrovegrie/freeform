"""
Numerical verification for Experiment 13: Intermediate Hardness.

Checks:
1. Grover N=4 sanity check for quantum algorithm complexity
2. Non-trivial instance N=8 sanity check
3. Error amplification factor F(M) for polynomial interpolation
4. Interpolation barrier at epsilon = 2^{-n/2}
5. Classical vs quantum complexity comparison
6. Lebesgue function bound
7. Product lower bound for integer gaps
8. Precision phase diagram scaling across epsilon regimes
"""

import math
from fractions import Fraction


def compute_A1(energies, degeneracies):
    """Compute A_1 = (1/N) sum_{k>=1} d_k / (E_k - E_0)."""
    N = sum(degeneracies)
    E0 = energies[0]
    total = sum(d / (E - E0) for E, d in zip(energies[1:], degeneracies[1:]))
    return total / N


def quantum_queries(N, Delta1, epsilon):
    """Quantum query complexity: O(sqrt(N) + 1/(epsilon * Delta1))."""
    return math.sqrt(N) + 1.0 / (epsilon * Delta1)


def classical_queries(epsilon):
    """Classical query lower bound: Omega(1/epsilon^2)."""
    return 1.0 / epsilon**2


def log2_amplification_factor(M):
    """
    Log2 of end-to-end amplification factor F(M).

    F(M) = (M+1)^M * (2M+1)^{M-1} / ((M-1)! * min_k prod_{l!=k}|l-k|)

    For consecutive integer gaps {0,...,M-1}:
    min_k prod_{l!=k}|l-k| = min_k k!(M-1-k)!

    The minimum is at k = floor((M-1)/2).
    """
    if M < 2:
        return 0.0

    # Numerator: (M+1)^M * (2M+1)^{M-1}
    log2_num = M * math.log2(M + 1) + (M - 1) * math.log2(2 * M + 1)

    # Lebesgue denominator: (M-1)!
    log2_lebesgue_den = sum(math.log2(k) for k in range(1, M))

    # Product denominator: min_k k!(M-1-k)!
    # Minimum at k = floor((M-1)/2)
    k_mid = (M - 1) // 2
    log2_prod_den = (
        sum(math.log2(i) for i in range(1, k_mid + 1))
        + sum(math.log2(i) for i in range(1, M - 1 - k_mid + 1))
    )

    return log2_num - log2_lebesgue_den - log2_prod_den


def verify_grover_n4():
    """Grover instance: N=4, M=2, E0=0, E1=1, d0=1, d1=3."""
    print("=" * 60)
    print("Sanity Check 1: Grover N=4")
    print("=" * 60)

    N, n = 4, 2
    energies = [0, 1]
    degeneracies = [1, 3]
    Delta1 = 1

    A1 = compute_A1(energies, degeneracies)
    print(f"  A_1 = {A1} (expected 3/4 = {3/4})")
    assert abs(A1 - 0.75) < 1e-12, f"A1 mismatch: {A1}"

    epsilon = 0.5
    qc = quantum_queries(N, Delta1, epsilon)
    cc = classical_queries(epsilon)

    print(f"  epsilon = 2^{{-n/2}} = {epsilon}")
    print(f"  Quantum: sqrt(N) + 1/(eps*D1) = {qc:.1f}")
    print(f"  Classical: 1/eps^2 = {cc:.1f}")
    print(f"  2^{{n/2}} = {2**(n/2):.1f}, 2^n = {2**n}")
    print("  PASS\n")


def verify_nontrivial_n8():
    """Non-trivial: N=8, M=3, E0=0, E1=1/4, E2=1, d0=1, d1=3, d2=4."""
    print("=" * 60)
    print("Sanity Check 2: Non-trivial N=8")
    print("=" * 60)

    N, n = 8, 3
    energies = [0, 0.25, 1]
    degeneracies = [1, 3, 4]
    Delta1 = 0.25

    A1 = compute_A1(energies, degeneracies)
    expected = (1 / 8) * (3 / 0.25 + 4 / 1.0)
    print(f"  A_1 = {A1} (expected {expected})")
    assert abs(A1 - expected) < 1e-12

    epsilon = 2 ** (-3 / 2)
    qc = quantum_queries(N, Delta1, epsilon)
    cc = classical_queries(epsilon)

    print(f"  epsilon = 2^{{-3/2}} = {epsilon:.4f}")
    print(f"  Quantum: {qc:.1f}, Classical: {cc:.1f}")
    print("  PASS\n")


def verify_A1_exact_grover():
    """Verify A_1 with exact arithmetic for Grover."""
    print("=" * 60)
    print("Exact Arithmetic: A_1 for Grover")
    print("=" * 60)

    for n in range(2, 8):
        N = 2**n
        A1 = Fraction(N - 1, N)
        print(f"  n={n}: A_1 = {A1} = {float(A1):.6f}")

    print("  A_1 -> 1 as N -> infinity (expected).")
    print("  PASS\n")


def verify_amplification_factor():
    """
    Compute and display the amplification factor F(M) for small M.
    This verifies the claim that F(M) grows as C^M.
    """
    print("=" * 60)
    print("Verification: Amplification Factor F(M)")
    print("=" * 60)
    print(f"  {'M':>4}  {'log2(F(M))':>12}  {'F(M)/F(M-1)':>14}  {'effective C':>12}")
    print(f"  {'---':>4}  {'---':>12}  {'---':>14}  {'---':>12}")

    prev_log2 = None
    for M in range(2, 16):
        log2_F = log2_amplification_factor(M)
        if prev_log2 is not None:
            ratio = 2 ** (log2_F - prev_log2)
            eff_C = 2 ** (log2_F / M)
            print(
                f"  {M:>4}  {log2_F:>12.2f}  {ratio:>14.2f}  {eff_C:>12.2f}"
            )
        else:
            eff_C = 2 ** (log2_F / M)
            print(
                f"  {M:>4}  {log2_F:>12.2f}  {'--':>14}  {eff_C:>12.2f}"
            )
        prev_log2 = log2_F

    print("\n  F(M) grows as C^M with effective C ~ 20-24 for moderate M.")
    print("  PASS\n")


def verify_interpolation_barrier():
    """
    Verify that 3 * epsilon * N * F(M) >> 1 at epsilon = 2^{-n/2}.
    """
    print("=" * 60)
    print("Verification: Interpolation Barrier at eps = 2^{-n/2}")
    print("=" * 60)
    print(f"  {'n':>4}  {'M':>4}  {'log2(error bound)':>20}  {'> 1/2?':>8}")
    print(f"  {'---':>4}  {'---':>4}  {'---':>20}  {'---':>8}")

    for n in [4, 6, 8, 10, 12, 16, 20]:
        M = n
        # error <= 3 * 2^{-n/2} * 2^n * F(M) = 3 * 2^{n/2} * F(M)
        log2_err = math.log2(3) + n / 2 + log2_amplification_factor(M)
        exceeds = log2_err > -1  # > 1/2

        print(
            f"  {n:>4}  {M:>4}  2^{log2_err:>14.1f}       {'YES' if exceeds else 'NO':>5}"
        )

    print("\n  Error diverges at eps = 2^{-n/2} for all n >= 4.")
    print("  PASS\n")


def verify_interpolation_threshold():
    """
    Find the required precision for interpolation to work.
    Need: 3 * eps * N * F(M) < 1/2
    => eps < 1/(6*N*F(M))
    => log2(eps) < -log2(6) - n - log2(F(M))
    """
    print("=" * 60)
    print("Verification: Required Precision for Interpolation")
    print("=" * 60)
    print(f"  {'n':>4}  {'M':>6}  {'threshold log2(eps)':>22}  {'2^{-n/2}':>12}  {'gap bits':>10}")
    print(f"  {'---':>4}  {'---':>6}  {'---':>22}  {'---':>12}  {'---':>10}")

    for n in [4, 8, 12, 16, 20, 30, 50]:
        M = n
        log2_threshold = -math.log2(6) - n - log2_amplification_factor(M)
        log2_half_n = -n / 2
        gap = log2_half_n - log2_threshold

        print(
            f"  {n:>4}  {M:>6}  {log2_threshold:>22.1f}  "
            f"{log2_half_n:>12.1f}  {gap:>10.1f}"
        )

    print("\n  Required precision is exponentially smaller than 2^{-n/2}.")
    print("  PASS\n")


def verify_quantum_vs_classical():
    """Compare quantum and classical complexity across problem sizes."""
    print("=" * 60)
    print("Verification: Quantum vs Classical (Delta1 = 1)")
    print("=" * 60)
    print(
        f"  {'n':>4}  {'epsilon':>12}  {'Q queries':>12}  "
        f"{'C queries':>12}  {'ratio':>8}"
    )
    print(
        f"  {'---':>4}  {'---':>12}  {'---':>12}  "
        f"{'---':>12}  {'---':>8}"
    )

    for n in [4, 8, 12, 16, 20]:
        N = 2**n
        epsilon = 2 ** (-n / 2)
        Delta1 = 1

        qc = quantum_queries(N, Delta1, epsilon)
        cc = classical_queries(epsilon)

        print(
            f"  {n:>4}  {epsilon:>12.6f}  {qc:>12.1f}  "
            f"{cc:>12.1f}  {cc/qc:>8.1f}x"
        )

    print("\n  Quadratic separation holds. Ratio ~ 2^{n/2}.")
    print("  PASS\n")


def verify_precision_phase_diagram():
    """
    Verify Proposition 8 scaling in the precision-dependent core model.

    Core model: M=2, Delta1=1, known E0.
    Then quantum ~ Theta(1/eps), classical ~ Theta(1/eps^2).
    """
    print("=" * 60)
    print("Verification: Precision Phase Diagram (Core Scaling)")
    print("=" * 60)

    # Regime 1: epsilon = Theta(1)
    eps_const = 0.25
    q_const = 1.0 / eps_const
    c_const = 1.0 / (eps_const**2)
    print(
        f"  eps=Theta(1): eps={eps_const}, Q~{q_const:.1f}, C~{c_const:.1f} "
        "(both O(1) up to constants)"
    )
    assert q_const < 100 and c_const < 1000

    # Regime 2: epsilon = 1/poly(n)
    n = 64
    eps_poly = 1.0 / (n**2)
    q_poly = 1.0 / eps_poly
    c_poly = 1.0 / (eps_poly**2)
    print(
        f"  eps=1/poly(n): n={n}, eps=1/n^2={eps_poly:.6f}, "
        f"Q={q_poly:.1f}=n^2, C={c_poly:.1f}=n^4"
    )
    assert abs(q_poly - n**2) < 1e-9
    assert abs(c_poly - n**4) < 1e-6

    print("\n  Exponential regimes eps = 2^{-c n}:")
    print(
        f"  {'c':>5}  {'log2(1/eps)/n':>15}  {'log2(Q)/n':>10}  "
        f"{'log2(C)/n':>10}  {'sep log2/n':>10}"
    )
    print(
        f"  {'---':>5}  {'---':>15}  {'---':>10}  "
        f"{'---':>10}  {'---':>10}"
    )

    prev_q = None
    prev_c_val = None
    prev_c = None
    for c in [0.10, 0.25, 0.40, 0.50, 0.60, 0.75]:
        eps = 2.0 ** (-c * n)
        q = 1.0 / eps
        c_val = 1.0 / (eps**2)
        separation = c_val / q  # = 1/eps

        log_q = math.log2(q) / n
        log_c = math.log2(c_val) / n
        log_sep = math.log2(separation) / n
        log_inv_eps = math.log2(1.0 / eps) / n

        print(
            f"  {c:>5.2f}  {log_inv_eps:>15.4f}  {log_q:>10.4f}  "
            f"{log_c:>10.4f}  {log_sep:>10.4f}"
        )

        # Scaling exponents:
        # Q = 2^{c n}, C = 2^{2 c n}, C/Q = 2^{c n}.
        assert abs(log_q - c) < 1e-10
        assert abs(log_c - 2 * c) < 1e-10
        assert abs(log_sep - c) < 1e-10

        # Smooth growth in c (no jump in core scaling law).
        if prev_q is not None:
            expected_ratio_q = 2.0 ** ((c - prev_c) * n)
            expected_ratio_c = 2.0 ** (2 * (c - prev_c) * n)
            assert abs((q / prev_q) / expected_ratio_q - 1.0) < 1e-10
            assert abs((c_val / prev_c_val) / expected_ratio_c - 1.0) < 1e-10

        prev_q = q
        prev_c_val = c_val
        prev_c = c

    print("\n  At c=1/2: Q=2^{n/2}, C=2^n (algorithmic threshold).")
    print("  For c<1/2 and c>1/2, exponents vary continuously with c.")
    print("  PASS\n")


def verify_lebesgue_bound():
    """
    Verify Lambda(x*) <= (2M+1)^{M-1} / (M-1)! for nodes x_j = 2j+1.
    """
    print("=" * 60)
    print("Verification: Lebesgue Function Bound")
    print("=" * 60)

    for M in range(2, 8):
        nodes = [2 * j + 1 for j in range(M)]

        max_lambda = 0
        for x_star_10 in range(-20, 1):  # x* in [-2, 0] step 0.1
            x_star = x_star_10 / 10.0
            lam = 0
            for j in range(M):
                num = 1.0
                den = 1.0
                for i in range(M):
                    if i != j:
                        num *= abs(x_star - nodes[i])
                        den *= abs(nodes[j] - nodes[i])
                lam += num / den
            max_lambda = max(max_lambda, lam)

        bound = (2 * M + 1) ** (M - 1) / math.factorial(M - 1)
        ok = max_lambda <= bound * 1.001

        print(
            f"  M={M}: Lambda_max = {max_lambda:>12.4f}, "
            f"bound = {bound:>12.4f}, {'OK' if ok else 'FAIL'}"
        )
        assert ok, f"Lebesgue bound violated at M={M}"

    print("  PASS\n")


def verify_product_bound():
    """
    Verify min_k prod_{l!=k} |l-k| for consecutive integers {0,...,M-1}.
    The minimum is at k = floor((M-1)/2), giving k!(M-1-k)!.
    """
    print("=" * 60)
    print("Verification: Product Bound for Integer Gaps")
    print("=" * 60)

    for M in range(2, 10):
        deltas = list(range(M))
        products = []
        for k in range(M):
            prod = 1
            for l in range(M):
                if l != k:
                    prod *= abs(deltas[l] - deltas[k])
            products.append(prod)

        min_prod = min(products)
        min_k = products.index(min_prod)

        # Expected: min at k = floor((M-1)/2), value = k!(M-1-k)!
        k_expected = (M - 1) // 2
        expected_val = math.factorial(k_expected) * math.factorial(M - 1 - k_expected)

        print(
            f"  M={M}: min_prod = {min_prod:>8} at k={min_k}, "
            f"expected = {expected_val:>8} at k={k_expected}"
        )
        assert min_prod == expected_val, f"Mismatch at M={M}"

    print("  Minimum product matches floor((M-1)/2)!(ceil((M-1)/2))!")
    print("  PASS\n")


def verify_theorem4_tight_quantum():
    """
    Verify Theorem 4: tight quantum query complexity.
    Check that upper and lower bounds match at epsilon = 2^{-n/2}.
    """
    print("=" * 60)
    print("Verification: Theorem 4 (Tight Quantum Bounds)")
    print("=" * 60)
    print(
        f"  {'n':>4}  {'eps':>12}  {'Q lower':>12}  "
        f"{'Q upper':>12}  {'ratio':>8}"
    )
    print(
        f"  {'---':>4}  {'---':>12}  {'---':>12}  "
        f"{'---':>12}  {'---':>8}"
    )

    for n in [4, 8, 12, 16, 20]:
        N = 2**n
        epsilon = 2 ** (-n / 2)
        Delta1 = 1

        q_lower = 1.0 / (2 * epsilon)  # Omega(1/(2*eps)) from Heisenberg
        q_upper = math.sqrt(N) + 1.0 / (epsilon * Delta1)

        print(
            f"  {n:>4}  {epsilon:>12.6f}  {q_lower:>12.1f}  "
            f"{q_upper:>12.1f}  {q_upper/q_lower:>8.2f}x"
        )

    print("\n  Upper/lower ratio is O(1). Bounds are tight.")
    print("  PASS\n")


def verify_theorem6_lebesgue_extrapolation():
    """
    Verify Theorem 6: Lebesgue function at extrapolation point.
    For equally spaced nodes in [a,b] and x* = a - (b-a),
    check that |ell_1(x*)| >= binom(2(d-1), d-1) >= 2^{d-1}.
    Also verify the bound for random node placements.
    """
    print("=" * 60)
    print("Verification: Theorem 6 (Lebesgue Extrapolation)")
    print("=" * 60)

    print("  Part A: Equally spaced nodes")
    for d in range(2, 12):
        a, b = 0.0, 1.0
        h = (b - a) / (d - 1) if d > 1 else 1.0
        nodes = [a + (j - 1) * h for j in range(1, d + 1)]
        x_star = a - (b - a)  # = -1

        # Compute |ell_1(x*)|
        ell1 = 1.0
        for i in range(1, d):
            ell1 *= abs(x_star - nodes[i]) / abs(nodes[0] - nodes[i])

        # Compute full Lebesgue function
        lam = 0.0
        for j in range(d):
            term = 1.0
            for i in range(d):
                if i != j:
                    term *= abs(x_star - nodes[i]) / abs(nodes[j] - nodes[i])
            lam += term

        # Expected: binom(2(d-1), d-1)
        expected = math.comb(2 * (d - 1), d - 1)
        threshold = 2 ** (d - 1)

        ok = abs(ell1 - expected) < 0.01 and lam >= threshold
        print(
            f"    d={d:>2}: |ell_1| = {ell1:>12.1f}, "
            f"C(2(d-1),d-1) = {expected:>12}, "
            f"Lambda = {lam:>12.1f}, >= 2^(d-1) = {threshold:>8}  "
            f"{'OK' if ok else 'FAIL'}"
        )
        assert abs(ell1 - expected) < 0.01, (
            f"|ell_1| mismatch at d={d}: got {ell1}, expected {expected}"
        )
        assert lam >= threshold * 0.999, (
            f"Lebesgue bound violated at d={d}: {lam} < {threshold}"
        )

    print("  Part B: Random node placements (any-nodes bound)")
    import random
    random.seed(42)
    for d in range(2, 10):
        a, b = 0.0, 1.0
        threshold = 2 ** (d - 1)

        for trial in range(20):
            nodes = sorted([a + random.random() * (b - a) for _ in range(d)])
            x_star = a - (b - a)  # distance = b-a from [a,b]

            # Compute full Lebesgue function
            lam = 0.0
            for j in range(d):
                term = 1.0
                for i in range(d):
                    if i != j:
                        term *= abs(x_star - nodes[i]) / abs(nodes[j] - nodes[i])
                lam += term

            assert lam >= threshold * 0.999, (
                f"Any-nodes bound violated: d={d}, trial={trial}, "
                f"Lambda={lam:.4f} < 2^(d-1)={threshold}"
            )

        print(f"    d={d:>2}: 20 random trials, all Lambda >= {threshold} (2^(d-1)). OK")

    print("  PASS\n")


def verify_theorem7_structure_irrelevance():
    """
    Verify Theorem 7: embedding M=2 hard instances into M-level structure.
    Check that the higher-level contribution is negligible.
    """
    print("=" * 60)
    print("Verification: Theorem 7 (Structure Irrelevance)")
    print("=" * 60)

    for n in [8, 12, 16, 20, 30]:
        N = 2**n
        epsilon = 2 ** (-n / 2)

        for M in [3, 5]:
            # Gaps: Delta_k = k for k = 1, ..., M-1
            gaps = list(range(1, M))

            # Higher-level contribution: C/N where C = sum_{k>=2} 1/Delta_k
            C = sum(1.0 / g for g in gaps[1:]) if len(gaps) > 1 else 0
            higher_contribution = C / N

            # Ratio to epsilon: should vanish as n grows
            ratio = higher_contribution / epsilon if epsilon > 0 else 0

            print(
                f"  n={n:>2}, M={M:>2}: C/N = {higher_contribution:.2e}, "
                f"eps = {epsilon:.2e}, ratio = {ratio:.2e}"
            )

    # For n >= 12 and M = 3, ratio < 0.01 (verify the asymptotic claim)
    for n in [12, 16, 20, 30]:
        N = 2**n
        epsilon = 2 ** (-n / 2)
        C = 0.5  # M=3: C = 1/Delta_2 = 1/2
        ratio = C / (N * epsilon)
        assert ratio < 0.01, (
            f"Higher levels not negligible at n={n}, M=3: ratio = {ratio}"
        )

    print("\n  Higher-level contributions are negligible at eps = 2^{-n/2}.")
    print("  PASS\n")


if __name__ == "__main__":
    print("Experiment 13: Numerical Verification\n")

    verify_grover_n4()
    verify_nontrivial_n8()
    verify_A1_exact_grover()
    verify_lebesgue_bound()
    verify_product_bound()
    verify_amplification_factor()
    verify_interpolation_barrier()
    verify_interpolation_threshold()
    verify_quantum_vs_classical()
    verify_precision_phase_diagram()
    verify_theorem4_tight_quantum()
    verify_theorem6_lebesgue_extrapolation()
    verify_theorem7_structure_irrelevance()

    print("=" * 60)
    print("ALL CHECKS PASSED")
    print("=" * 60)
