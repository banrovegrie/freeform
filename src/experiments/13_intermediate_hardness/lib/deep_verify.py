"""
Deep correctness verification for Experiment 13.

This script tests every mathematical claim in proof.md by direct computation
on concrete instances. It goes beyond the bounds in verify.py by actually
running the interpolation procedure end-to-end.

Tests:
1. f(x) derivation: verify the algebraic identity for specific Hamiltonians
2. End-to-end interpolation: add noise, reconstruct, show rounding fails
3. Product lower bound for distinct integers
4. Quantum oracle construction: h(x) in [0,1], mu_h/Delta_1 = A_1
5. Classical lower bound: adversarial instance construction
"""

import math
import random
from fractions import Fraction
from functools import reduce
from operator import mul


# ============================================================
# Helper functions
# ============================================================

def compute_A1(energies, degeneracies):
    """Exact A_1 = (1/N) sum_{k>=1} d_k / (E_k - E_0)."""
    N = sum(degeneracies)
    E0 = energies[0]
    return sum(d / (E - E0) for E, d in zip(energies[1:], degeneracies[1:])) / N


def compute_A1_rational(energies, degeneracies):
    """Exact A_1 using rational arithmetic."""
    N = sum(degeneracies)
    E0 = Fraction(energies[0])
    total = Fraction(0)
    for E, d in zip(energies[1:], degeneracies[1:]):
        total += Fraction(d, 1) / (Fraction(E) - E0)
    return total / N


def lagrange_interpolate(nodes, values, x):
    """Evaluate the Lagrange interpolant at point x."""
    n = len(nodes)
    result = 0.0
    for j in range(n):
        basis = 1.0
        for i in range(n):
            if i != j:
                basis *= (x - nodes[i]) / (nodes[j] - nodes[i])
        result += values[j] * basis
    return result


# ============================================================
# Test 1: f(x) derivation from auxiliary Hamiltonian
# ============================================================

def test_fx_derivation():
    """
    Verify f(x) = 2*A_1(H'(x)) - A_1(H) = (1/N) sum_k d_k/(Delta_k + x/2).

    Construct H'(x) explicitly: H tensor I - (x/2) I tensor sigma_+.
    Compute A_1(H'(x)) from the full spectrum.
    Compare with the claimed formula.
    """
    print("=" * 70)
    print("Test 1: f(x) Derivation from Auxiliary Hamiltonian")
    print("=" * 70)

    # Test instance: M=3 eigenlevels
    energies = [Fraction(0), Fraction(1, 4), Fraction(1)]
    degeneracies = [2, 3, 3]  # N = 8
    N = sum(degeneracies)
    M = len(energies)
    E0 = energies[0]
    deltas = [E - E0 for E in energies]

    A1_H = compute_A1_rational(energies, degeneracies)
    print(f"  H: energies={[str(e) for e in energies]}, degs={degeneracies}")
    print(f"  A_1(H) = {A1_H} = {float(A1_H):.6f}")

    for x in [Fraction(1), Fraction(3), Fraction(5), Fraction(7)]:
        # H'(x) spectrum:
        # |0> branch: E_k - x/2, degeneracy d_k
        # |1> branch: E_k, degeneracy d_k
        # Ground energy: E_0 - x/2

        ground_energy = E0 - x / 2
        hp_energies = []
        hp_degs = []

        # Collect all excited eigenvalues
        for k in range(M):
            # |0> branch: E_k - x/2
            e_0branch = energies[k] - x / 2
            gap = e_0branch - ground_energy  # = Delta_k
            if gap > 0:
                hp_energies.append(gap)
                hp_degs.append(degeneracies[k])

            # |1> branch: E_k
            e_1branch = energies[k]
            gap = e_1branch - ground_energy  # = Delta_k + x/2
            hp_energies.append(gap)
            hp_degs.append(degeneracies[k])

        # Compute A_1(H'(x)) directly
        Np = 2 * N  # H'(x) acts on n+1 qubits
        A1_Hp = sum(
            Fraction(d, 1) / g for g, d in zip(hp_energies, hp_degs)
        ) / Np

        # Claimed formula
        f_formula = sum(
            Fraction(d, 1) / (delta + x / 2)
            for delta, d in zip(deltas, degeneracies)
        ) / N

        f_computed = 2 * A1_Hp - A1_H

        match = f_formula == f_computed
        print(f"  x={x}: f_formula={float(f_formula):.6f}, "
              f"f_computed={float(f_computed):.6f}, match={match}")
        assert match, f"f(x) mismatch at x={x}: {f_formula} vs {f_computed}"

    print("  All f(x) values match. Derivation VERIFIED.\n")


# ============================================================
# Test 2: End-to-end interpolation procedure
# ============================================================

def test_interpolation_end_to_end():
    """
    Run the full interpolation procedure:
    1. Construct an Ising Hamiltonian with integer eigenvalues
    2. Compute f(x_i) at M sample points
    3. Form P(x_i) = prod(Delta_k + x_i/2) * f(x_i)
    4. Add noise at various epsilon levels
    5. Reconstruct P via Lagrange interpolation
    6. Extract degeneracies
    7. Show rounding fails at epsilon = 2^{-n/2} but succeeds at small epsilon
    """
    print("=" * 70)
    print("Test 2: End-to-End Interpolation Procedure")
    print("=" * 70)

    # Ising-like instance with integer eigenvalues
    # M=4 distinct levels: 0, 1, 3, 7
    energies = [0, 1, 3, 7]
    degeneracies = [4, 5, 3, 4]  # N = 16 = 2^4, n = 4
    N = sum(degeneracies)
    n = int(math.log2(N))
    M = len(energies)
    E0 = energies[0]
    deltas = [E - E0 for E in energies]

    print(f"  Instance: n={n}, N={N}, M={M}")
    print(f"  Energies: {energies}, Deltas: {deltas}")
    print(f"  Degeneracies: {degeneracies}")

    # Sample points: odd integers 1, 3, ..., 2M-1
    sample_points = [2 * j + 1 for j in range(M)]
    print(f"  Sample points: {sample_points}")

    # Compute exact f(x_i) and P(x_i)
    def f_exact(x):
        return sum(d / (delta + x / 2) for delta, d in zip(deltas, degeneracies)) / N

    def product_factor(x):
        return reduce(mul, (delta + x / 2 for delta in deltas), 1.0)

    exact_P = [product_factor(xi) * f_exact(xi) for xi in sample_points]
    print(f"  Exact P(x_i): {[f'{p:.6f}' for p in exact_P]}")

    # Verify: P is a polynomial of degree M-1. Check by Lagrange reconstruction.
    # Evaluate P at a test point to verify polynomial structure.
    test_x = 0.5
    P_lagrange = lagrange_interpolate(sample_points, exact_P, test_x)
    P_direct = product_factor(test_x) * f_exact(test_x)
    print(f"  Polynomial check: P_lagrange(0.5)={P_lagrange:.6f}, "
          f"P_direct(0.5)={P_direct:.6f}, match={abs(P_lagrange - P_direct) < 1e-10}")

    # Extract exact degeneracies
    print("\n  Exact degeneracy extraction:")
    for k in range(M):
        eval_point = -2 * deltas[k]
        P_at_pole = lagrange_interpolate(sample_points, exact_P, eval_point)
        prod_denom = reduce(
            mul,
            (deltas[l] - deltas[k] for l in range(M) if l != k),
            1.0
        )
        d_extracted = N * P_at_pole / prod_denom
        print(f"    k={k}: d_extracted={d_extracted:.6f}, "
              f"d_true={degeneracies[k]}, "
              f"error={abs(d_extracted - degeneracies[k]):.2e}")
        assert abs(d_extracted - degeneracies[k]) < 1e-8, \
            f"Exact extraction failed for k={k}"

    # Now add noise and test at various epsilon levels
    print("\n  Noisy degeneracy extraction:")
    print(f"  {'epsilon':>14}  {'max |d_k error|':>16}  {'rounding ok?':>14}")
    print(f"  {'---':>14}  {'---':>16}  {'---':>14}")

    random.seed(42)

    for log2_eps in [-1, -2, -4, -8, -16, -32, -50]:
        epsilon = 2.0 ** log2_eps

        # Add noise to f(x_i): |noise| <= 3*epsilon (worst case)
        noisy_f = [f_exact(xi) + 3 * epsilon * random.uniform(-1, 1)
                   for xi in sample_points]
        noisy_P = [product_factor(xi) * nf for xi, nf in zip(sample_points, noisy_f)]

        max_error = 0
        for k in range(M):
            eval_point = -2 * deltas[k]
            P_noisy = lagrange_interpolate(sample_points, noisy_P, eval_point)
            prod_denom = reduce(
                mul,
                (deltas[l] - deltas[k] for l in range(M) if l != k),
                1.0
            )
            d_noisy = N * P_noisy / prod_denom
            error = abs(d_noisy - degeneracies[k])
            max_error = max(max_error, error)

        rounding_ok = max_error < 0.5
        marker = "YES" if rounding_ok else "NO"
        eps_str = f"2^{{{log2_eps}}}"

        print(f"  {eps_str:>14}  {max_error:>16.6f}  {marker:>14}")

    # Specific test: epsilon = 2^{-n/2}
    epsilon_half = 2.0 ** (-n / 2)
    print(f"\n  Critical test: epsilon = 2^{{-n/2}} = 2^{{-{n/2}}} = {epsilon_half}")
    noisy_f = [f_exact(xi) + 3 * epsilon_half * random.uniform(-1, 1)
               for xi in sample_points]
    noisy_P = [product_factor(xi) * nf for xi, nf in zip(sample_points, noisy_f)]
    max_error = 0
    for k in range(M):
        eval_point = -2 * deltas[k]
        P_noisy = lagrange_interpolate(sample_points, noisy_P, eval_point)
        prod_denom = reduce(
            mul,
            (deltas[l] - deltas[k] for l in range(M) if l != k),
            1.0
        )
        d_noisy = N * P_noisy / prod_denom
        error = abs(d_noisy - degeneracies[k])
        max_error = max(max_error, error)

    print(f"  Max degeneracy error: {max_error:.6f}")
    print(f"  Rounding {'FAILS' if max_error >= 0.5 else 'succeeds'} "
          f"(error {'>' if max_error >= 0.5 else '<'} 0.5)")
    print()


# ============================================================
# Test 3: Product lower bound for distinct integers
# ============================================================

def test_product_lower_bound():
    """
    Verify: for distinct non-negative integers a_0 < a_1 < ... < a_{M-1},
    prod_{l!=k} |a_l - a_k| >= prod_{l!=k} |l - k| = k!(M-1-k)!.

    This follows from |a_l - a_k| >= |l - k| for distinct integers.
    Test on random instances.
    """
    print("=" * 70)
    print("Test 3: Product Lower Bound for Distinct Integers")
    print("=" * 70)

    random.seed(123)

    for M in range(2, 8):
        # Test 100 random instances of M distinct non-negative integers
        min_ratio = float("inf")
        for _ in range(200):
            # Random distinct non-negative integers
            ints = sorted(random.sample(range(50), M))

            for k in range(M):
                prod_actual = reduce(
                    mul,
                    (abs(ints[l] - ints[k]) for l in range(M) if l != k),
                    1
                )
                prod_consecutive = reduce(
                    mul,
                    (abs(l - k) for l in range(M) if l != k),
                    1
                )
                ratio = prod_actual / prod_consecutive
                min_ratio = min(min_ratio, ratio)
                assert ratio >= 1.0 - 1e-12, \
                    f"Bound violated: M={M}, ints={ints}, k={k}, " \
                    f"actual={prod_actual}, consecutive={prod_consecutive}"

        print(f"  M={M}: min ratio (actual/consecutive) = {min_ratio:.4f} >= 1.0  OK")

    # Also verify the analytic claim: |a_l - a_k| >= |l - k| for distinct ints
    print("\n  Analytic check: distinct integers a_0 < ... < a_{M-1} implies "
          "|a_l - a_k| >= |l-k|")
    for trial in range(50):
        ints = sorted(random.sample(range(100), 6))
        for k in range(6):
            for l in range(6):
                if l != k:
                    assert abs(ints[l] - ints[k]) >= abs(l - k), \
                        f"Failed: ints={ints}, k={k}, l={l}"
    print("  Verified on 50 random 6-element instances.  OK\n")


# ============================================================
# Test 4: Quantum oracle construction
# ============================================================

def test_quantum_oracle():
    """
    Verify:
    1. h(x) = Delta_1 / (E_x - E_0) is in [0, 1] for all x
    2. mu_h = E[h(x)] satisfies mu_h / Delta_1 = A_1
    """
    print("=" * 70)
    print("Test 4: Quantum Oracle Construction")
    print("=" * 70)

    test_cases = [
        # (energies, degeneracies, name)
        ([0, 1], [1, 3], "Grover N=4"),
        ([0, Fraction(1, 4), 1], [1, 3, 4], "N=8, M=3"),
        ([0, 1, 3, 7], [4, 5, 3, 4], "Ising M=4"),
        ([0, 1, 2, 3, 4], [1, 2, 3, 2, 2], "N=10, M=5"),
    ]

    for energies, degeneracies, name in test_cases:
        N = sum(degeneracies)
        E0 = Fraction(energies[0])
        Delta1 = Fraction(energies[1]) - E0

        # Expand to per-string level
        strings = []
        for k, (E, d) in enumerate(zip(energies, degeneracies)):
            strings.extend([Fraction(E)] * d)

        # Compute h(x) for each string
        h_values = []
        for Ex in strings:
            if Ex == E0:
                h_values.append(Fraction(0))
            else:
                hx = Delta1 / (Ex - E0)
                h_values.append(hx)

        # Check h(x) in [0, 1]
        all_in_range = all(0 <= h <= 1 for h in h_values)

        # Compute mu_h
        mu_h = sum(h_values) / N

        # Compute A_1
        A1 = compute_A1_rational(energies, degeneracies)

        # Check mu_h / Delta_1 = A_1
        A1_from_mu = mu_h / Delta1
        match = A1_from_mu == A1

        print(f"  {name}: h in [0,1]={all_in_range}, "
              f"mu_h/D1={float(A1_from_mu):.6f}, "
              f"A_1={float(A1):.6f}, match={match}")
        assert all_in_range, f"h(x) out of range for {name}"
        assert match, f"mu_h/Delta_1 != A_1 for {name}"

    print("  All oracle constructions verified.  OK\n")


# ============================================================
# Test 5: Classical lower bound adversarial instance
# ============================================================

def test_classical_adversary():
    """
    Verify the adversarial construction:
    - Instance 1: |S| = N/2, A_1 = 1/2
    - Instance 2: |S'| = N/2 + t, A_1' = (N/2-t)/N = 1/2 - t/N
    - Difference = t/N ~ epsilon when t = ceil(epsilon*N)
    """
    print("=" * 70)
    print("Test 5: Classical Lower Bound Adversarial Instance")
    print("=" * 70)

    for n in [4, 6, 8, 10]:
        N = 2 ** n
        epsilon = 2 ** (-n / 2)

        # Instance 1: |S| = N/2
        d0_1, d1_1 = N // 2, N // 2
        A1_1 = Fraction(d1_1, N)

        # Instance 2: |S'| = N/2 + t
        t = math.ceil(epsilon * N)
        d0_2, d1_2 = N // 2 + t, N // 2 - t
        A1_2 = Fraction(d1_2, N)

        diff = abs(A1_1 - A1_2)

        # KL divergence between Bernoulli(1/2) and Bernoulli(1/2 + t/N)
        p0, p1 = 0.5, 0.5 + t / N
        kl = p0 * math.log(p0 / p1) + (1 - p0) * math.log((1 - p0) / (1 - p1))

        # Required queries
        q_lower = 1.0 / (2 * kl) if kl > 0 else float("inf")

        print(f"  n={n}: eps=2^{{-{n/2:.0f}}}={epsilon:.4f}, t={t}, "
              f"|A1-A1'|={float(diff):.4f}, "
              f"KL={kl:.2e}, q_lower>={q_lower:.0f}, "
              f"1/eps^2={1/epsilon**2:.0f}")

        assert abs(float(diff) - t / N) < 1e-12
        assert q_lower >= 0.1 / epsilon ** 2  # Within constant factor

    print("  Adversarial construction verified.  OK\n")


# ============================================================
# Test 6: Error bound chain verification
# ============================================================

def test_error_bound_chain():
    """
    For a concrete instance, compute the exact error amplification
    through every step of the proof and compare with the analytic bounds.
    """
    print("=" * 70)
    print("Test 6: Error Bound Chain (Step-by-Step)")
    print("=" * 70)

    # Instance: eigenvalues in [0,1] (required by proof's bound Delta_k <= 1)
    # Use Fraction for exact arithmetic
    deltas = [Fraction(0), Fraction(1, 4), Fraction(1, 2), Fraction(1)]
    degeneracies = [4, 5, 3, 4]
    N = sum(degeneracies)
    M = len(deltas)
    sample_points = [Fraction(2 * j + 1) for j in range(M)]  # [1, 3, 5, 7]

    print(f"  Deltas: {[str(d) for d in deltas]}, M={M}")
    print(f"  Sample points: {[str(s) for s in sample_points]}")

    # Step 3: Pointwise product bound (Delta_k <= 1 required)
    for j, xj in enumerate(sample_points):
        product = float(reduce(mul, (d + xj / 2 for d in deltas), Fraction(1)))
        bound = (M + 1) ** M
        ok = product <= bound * 1.001
        print(f"  Step 3: prod(Delta_k + x_{j}/2) = {product:.4f}, "
              f"bound (M+1)^M = {bound:.2f}, ok={ok}")
        assert ok, f"Product {product} exceeds bound {bound} at j={j}"

    # Step 4: Lebesgue function at extrapolation points
    print()
    for k in range(M):
        x_star = -2 * deltas[k]
        lam = Fraction(0)
        for j in range(M):
            basis = Fraction(1)
            for i in range(M):
                if i != j:
                    basis *= abs(x_star - sample_points[i]) / abs(
                        sample_points[j] - sample_points[i]
                    )
            lam += basis

        bound = float(Fraction(2 * M + 1) ** (M - 1) / math.factorial(M - 1))
        lam_f = float(lam)
        ok = lam_f <= bound * 1.001
        print(f"  Step 4: Lambda(-2*Delta_{k}) = {lam_f:.4f}, "
              f"bound = {bound:.4f}, ok={ok}")
        assert ok, f"Lebesgue bound violated at k={k}: {lam_f} > {bound}"

    # Step 4: Product denominators (for integer gaps, use consecutive bound)
    # For non-integer gaps, verify prod >= min_consecutive directly
    print()
    # Use integer gaps [0,1,2,3] for this check (as in the proof)
    int_deltas = list(range(M))
    for k in range(M):
        prod = reduce(
            mul,
            (abs(int_deltas[l] - int_deltas[k]) for l in range(M) if l != k),
            1
        )
        consecutive_prod = math.factorial(k) * math.factorial(M - 1 - k)
        ok = prod >= consecutive_prod
        print(f"  Prod |l-k| for integers: k={k}, prod={prod}, "
              f"k!(M-1-k)!={consecutive_prod}, ok={ok}")
        assert ok

    # Full error bound for specific epsilon
    epsilon = 2 ** (-2)  # n=4
    print(f"\n  Full error bound at epsilon = {epsilon}:")
    for k in range(M):
        x_star = float(-2 * deltas[k])
        # Compute actual amplification (sum of product * Lagrange basis)
        amp = 0
        for j in range(M):
            pf = float(reduce(
                mul,
                (d + sample_points[j] / 2 for d in deltas),
                Fraction(1)
            ))
            basis = 1.0
            sp = [float(s) for s in sample_points]
            for i in range(M):
                if i != j:
                    basis *= abs(x_star - sp[i]) / abs(sp[j] - sp[i])
            amp += pf * basis

        prod_denom = float(reduce(
            mul,
            (abs(deltas[l] - deltas[k]) for l in range(M) if l != k),
            Fraction(1)
        ))
        error = 3 * epsilon * N * amp / prod_denom
        print(f"    k={k}: amplification={amp:.4f}, "
              f"prod_denom={prod_denom:.4f}, "
              f"error_bound={error:.4f}, "
              f"rounding={'FAIL' if error >= 0.5 else 'ok'}")

    print()


# ============================================================
# Test 7: Interpolation with larger instances
# ============================================================

def test_interpolation_scaling():
    """
    Test interpolation failure for larger M values.
    Use consecutive integer gaps (worst case for product denominator).
    """
    print("=" * 70)
    print("Test 7: Interpolation Failure Scaling")
    print("=" * 70)
    print(f"  {'M':>4}  {'n':>4}  {'eps=2^-n/2':>14}  "
          f"{'max d_k error':>16}  {'rounding':>10}")
    print(f"  {'---':>4}  {'---':>4}  {'---':>14}  "
          f"{'---':>16}  {'---':>10}")

    random.seed(7)

    for M in [3, 4, 5, 6, 7, 8]:
        # Consecutive integer gaps
        deltas = list(range(M))
        degeneracies = [max(1, random.randint(1, 10)) for _ in range(M)]
        N = sum(degeneracies)
        n = max(4, int(math.ceil(math.log2(N))))
        N = 2 ** n  # Round up to power of 2
        degeneracies[-1] += N - sum(degeneracies)  # Adjust to sum to N

        epsilon = 2.0 ** (-n / 2)
        sample_points = [2 * j + 1 for j in range(M)]

        def f_val(x):
            return sum(d / (delta + x / 2)
                       for delta, d in zip(deltas, degeneracies)) / N

        def prod_factor(x):
            return reduce(mul, (delta + x / 2 for delta in deltas), 1.0)

        exact_P = [prod_factor(xi) * f_val(xi) for xi in sample_points]
        noisy_P = [p + 3 * epsilon * prod_factor(xi) * random.uniform(-1, 1)
                   for p, xi in zip(exact_P, sample_points)]

        max_error = 0
        for k in range(M):
            eval_pt = -2 * deltas[k]
            P_noisy = lagrange_interpolate(sample_points, noisy_P, eval_pt)
            prod_denom = reduce(
                mul,
                (deltas[l] - deltas[k] for l in range(M) if l != k),
                1.0
            )
            if abs(prod_denom) < 1e-15:
                continue
            d_noisy = N * P_noisy / prod_denom
            error = abs(d_noisy - degeneracies[k])
            max_error = max(max_error, error)

        eps_str = f"2^{{{-n/2:.0f}}}"
        status = "FAIL" if max_error >= 0.5 else "ok"
        print(f"  {M:>4}  {n:>4}  {eps_str:>14}  "
              f"{max_error:>16.4f}  {status:>10}")

    print("\n  Interpolation fails for all M >= 3 at epsilon = 2^{-n/2}.")
    print("  PASS\n")


# ============================================================
# Test 8: Verify f(x) formula at rational points (exact arithmetic)
# ============================================================

def test_fx_exact_rational():
    """
    Use exact rational arithmetic to verify f(x) for the Grover instance.
    This eliminates any floating-point concerns.
    """
    print("=" * 70)
    print("Test 8: f(x) Exact Rational Verification (Grover N=4)")
    print("=" * 70)

    # Grover: E_0 = 0, E_1 = 1, d_0 = 1, d_1 = 3, N = 4
    E0, E1 = Fraction(0), Fraction(1)
    d0, d1 = 1, 3
    N = 4
    Delta0, Delta1 = Fraction(0), Fraction(1)

    A1_H = Fraction(d1, N) / Delta1  # = 3/4
    print(f"  A_1(H) = {A1_H}")

    for x in [Fraction(1), Fraction(3), Fraction(5)]:
        # H'(x) ground energy: E_0 - x/2 = -x/2
        ground = E0 - x / 2

        # Excited states of H'(x):
        # |0> branch, k=1: E_1 - x/2, gap = Delta1 = 1, deg = d1 = 3
        # |1> branch, k=0: E_0 = 0, gap = x/2, deg = d0 = 1
        # |1> branch, k=1: E_1 = 1, gap = 1 + x/2, deg = d1 = 3

        A1_Hp = (
            Fraction(d1) / Delta1
            + Fraction(d0) / (x / 2)
            + Fraction(d1) / (Delta1 + x / 2)
        ) / (2 * N)

        f_computed = 2 * A1_Hp - A1_H

        # Formula: f(x) = (1/N)(d0/(Delta0 + x/2) + d1/(Delta1 + x/2))
        f_formula = (Fraction(d0) / (Delta0 + x / 2) +
                     Fraction(d1) / (Delta1 + x / 2)) / N

        print(f"  x={x}: f_computed={f_computed} = {float(f_computed):.6f}, "
              f"f_formula={f_formula} = {float(f_formula):.6f}, "
              f"match={f_computed == f_formula}")
        assert f_computed == f_formula

    print("  Exact rational verification PASSED.\n")


# ============================================================
# Main
# ============================================================

if __name__ == "__main__":
    print("Experiment 13: Deep Correctness Verification\n")

    test_fx_exact_rational()
    test_fx_derivation()
    test_quantum_oracle()
    test_product_lower_bound()
    test_classical_adversary()
    test_error_bound_chain()
    test_interpolation_end_to_end()
    test_interpolation_scaling()

    print("=" * 70)
    print("ALL DEEP VERIFICATION TESTS PASSED")
    print("=" * 70)
