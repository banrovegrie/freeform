"""
Numerical verification of claims from experiment 11 (schedule optimality extensions).

This script uses only the Python standard library.

Claims verified:
  1. Exact Grover integral closed form
  2. C_bound^2 / I_bound ratio for Grover converges to 1089/1806
  3. Exact Grover ratio C_exact^2 / I_exact -> 0
  4. Integral scaling for gap flatness exponent alpha
  5. Measure condition constant classification by alpha
  6. Partial-information degradation: RC vs JRS sensitivity model
  7. Structured-family constant comparison (ferromagnetic Ising instance)
  8. Explicit A1-error propagation formulas used in Corollary I.1
"""

from __future__ import annotations

import math
from itertools import product
from math import comb


# ---------------------------------------------------------------------------
# Generic helpers
# ---------------------------------------------------------------------------


def simpson_integral(func, a: float, b: float, n: int) -> float:
    """Composite Simpson rule with n even subintervals."""
    if n <= 0 or (n % 2) != 0:
        raise ValueError("n must be a positive even integer.")
    h = (b - a) / n
    total = func(a) + func(b)
    for i in range(1, n):
        x = a + i * h
        total += (4.0 if i % 2 else 2.0) * func(x)
    return total * h / 3.0


def jacobi_eigenvalues_symmetric(matrix, tol: float = 1e-12, max_iter: int = 120000):
    """
    Eigenvalues of a real symmetric matrix via Jacobi rotations.

    Sufficient for the small reduced blocks used in this experiment.
    """
    n = len(matrix)
    A = [row[:] for row in matrix]

    for _ in range(max_iter):
        p = 0
        q = 1 if n > 1 else 0
        max_val = 0.0

        for i in range(n):
            for j in range(i + 1, n):
                v = abs(A[i][j])
                if v > max_val:
                    max_val = v
                    p = i
                    q = j

        if max_val < tol:
            break

        app = A[p][p]
        aqq = A[q][q]
        apq = A[p][q]
        if apq == 0.0:
            continue

        tau = (aqq - app) / (2.0 * apq)
        t = math.copysign(1.0 / (abs(tau) + math.sqrt(1.0 + tau * tau)), tau)
        c = 1.0 / math.sqrt(1.0 + t * t)
        s = t * c

        for k in range(n):
            if k != p and k != q:
                aik = A[k][p]
                akq = A[k][q]
                A[k][p] = A[p][k] = c * aik - s * akq
                A[k][q] = A[q][k] = s * aik + c * akq

        A[p][p] = c * c * app - 2.0 * s * c * apq + s * s * aqq
        A[q][q] = s * s * app + 2.0 * s * c * apq + c * c * aqq
        A[p][q] = A[q][p] = 0.0

    vals = [A[i][i] for i in range(n)]
    vals.sort()
    return vals


# ---------------------------------------------------------------------------
# Grover helpers
# ---------------------------------------------------------------------------


def grover_gap_squared(s: float, N: int) -> float:
    return (2.0 * s - 1.0) ** 2 * (1.0 - 1.0 / N) + 1.0 / N


def grover_sublevel_measure(x: float, N: int) -> float:
    g_min = 1.0 / math.sqrt(N)
    if x < g_min:
        return 0.0
    if x >= 1.0:
        return 1.0
    return math.sqrt((N * x * x - 1.0) / (N - 1.0))


# ---------------------------------------------------------------------------
# Claim 1: Exact Grover integral
# ---------------------------------------------------------------------------


def verify_claim1() -> None:
    print("=" * 72)
    print("CLAIM 1: Exact Grover integral")
    print("=" * 72)
    print()
    print("  I_exact = N/sqrt(N-1) * arctan(sqrt(N-1))")
    print()

    Ns = [4, 10, 100, 1000]

    print(f"  {'N':>6s}  {'I_numerical':>14s}  {'I_exact':>14s}  {'Rel Error':>12s}")
    print(f"  {'-'*6}  {'-'*14}  {'-'*14}  {'-'*12}")

    for N in Ns:
        integrand = lambda s: 1.0 / grover_gap_squared(s, N)
        I_num = simpson_integral(integrand, 0.0, 1.0, n=200000)
        I_exact = N / math.sqrt(N - 1.0) * math.atan(math.sqrt(N - 1.0))
        rel_err = abs(I_num - I_exact) / I_exact

        print(f"  {N:>6d}  {I_num:>14.8f}  {I_exact:>14.8f}  {rel_err:>12.2e}")
        assert rel_err < 5e-9, f"Claim 1 failed for N={N}: rel_err={rel_err}"

    I_exact_4 = 4.0 * math.pi / (3.0 * math.sqrt(3.0))
    I_formula_4 = 4.0 / math.sqrt(3.0) * math.atan(math.sqrt(3.0))
    print()
    print(f"  N=4 special: 4*pi/(3*sqrt(3)) = {I_exact_4:.8f}")
    print(f"  N=4 formula: 4/sqrt(3)*arctan(sqrt(3)) = {I_formula_4:.8f}")
    print(f"  Match: {abs(I_exact_4 - I_formula_4) < 1e-14}")
    print()


# ---------------------------------------------------------------------------
# Claim 2: C_bound^2 / I_bound for Grover
# ---------------------------------------------------------------------------


def verify_claim2() -> None:
    print("=" * 72)
    print("CLAIM 2: C_bound^2 / I_bound for Grover")
    print("=" * 72)
    print()

    Ns = [4, 10, 100, 1000]

    print(f"  {'N':>6s}  {'C_bound':>12s}  {'I_bound':>12s}  {'C^2/I':>12s}")
    print(f"  {'-'*6}  {'-'*12}  {'-'*12}  {'-'*12}")

    for N in Ns:
        A1 = (N - 1.0) / N
        A2 = A1
        cL = A1 * (A1 + 1.0) / A2
        one_minus_s0 = N / (2.0 * N - 1.0)

        C_bound = 3.0 * A2 / (A1 * (A1 + 1.0)) + 30.0 * one_minus_s0
        I_bound = (
            3.0 * A2 / (A1 * (A1 + 1.0))
            + 900.0 * one_minus_s0 * one_minus_s0 * A1 * (A1 + 1.0) / A2
        )
        ratio = C_bound * C_bound / I_bound

        print(f"  {N:>6d}  {C_bound:>12.6f}  {I_bound:>12.6f}  {ratio:>12.6f}")

    limit = 1089.0 / 1806.0
    N = 10**7
    A1 = (N - 1.0) / N
    A2 = A1
    one_minus_s0 = N / (2.0 * N - 1.0)
    C_bound = 3.0 * A2 / (A1 * (A1 + 1.0)) + 30.0 * one_minus_s0
    I_bound = 3.0 * A2 / (A1 * (A1 + 1.0)) + 900.0 * one_minus_s0 * one_minus_s0 * A1 * (A1 + 1.0) / A2
    ratio_big = C_bound * C_bound / I_bound

    print()
    print("  Asymptotic limit: C_bound^2/I_bound -> 1089/1806 ~ 0.603")
    print(f"  Numerical check at N={N}: {ratio_big:.9f}")
    assert abs(ratio_big - limit) < 5e-7, "Claim 2 asymptotic check failed"
    print()


# ---------------------------------------------------------------------------
# Claim 3: Exact C^2 / I_exact ratio for Grover
# ---------------------------------------------------------------------------


def verify_claim3() -> None:
    print("=" * 72)
    print("CLAIM 3: Exact C^2 / I_exact for Grover")
    print("=" * 72)
    print()
    print("  C_exact = 1, so C^2/I = 1/I = sqrt(N-1)/(N*arctan(sqrt(N-1)))")
    print()

    Ns = [4, 10, 100, 1000]

    print(f"  {'N':>6s}  {'C^2/I_exact':>14s}  {'2/(pi*sqrt(N))':>16s}  {'Ratio':>10s}")
    print(f"  {'-'*6}  {'-'*14}  {'-'*16}  {'-'*10}")

    for N in Ns:
        I_exact = N / math.sqrt(N - 1.0) * math.atan(math.sqrt(N - 1.0))
        c_over_i = 1.0 / I_exact
        asymptotic = 2.0 / (math.pi * math.sqrt(N))
        ratio = c_over_i / asymptotic
        print(f"  {N:>6d}  {c_over_i:>14.8f}  {asymptotic:>16.8f}  {ratio:>10.4f}")

    # asymptotic ratio tends to 1
    N = 10**7
    I_exact = N / math.sqrt(N - 1.0) * math.atan(math.sqrt(N - 1.0))
    c_over_i = 1.0 / I_exact
    asymptotic = 2.0 / (math.pi * math.sqrt(N))
    ratio = c_over_i / asymptotic
    assert abs(ratio - 1.0) < 3e-4, "Claim 3 asymptotic ratio check failed"

    print()
    print("  Both quantities go to 0, and their ratio goes to 1.")
    print()


# ---------------------------------------------------------------------------
# Claim 4: Integral scaling for general alpha
# ---------------------------------------------------------------------------


def alpha_profile_integral(alpha: float, g_min: float, c: float = 1.0) -> float:
    """
    Exact integral for g(s)=max(g_min, c|s-1/2|^alpha) on [0,1].
    """
    delta = (g_min / c) ** (1.0 / alpha)
    if delta >= 0.5:
        return 1.0 / (g_min * g_min)

    window = 2.0 * delta / (g_min * g_min)

    if abs(1.0 - 2.0 * alpha) < 1e-14:
        tail = 2.0 * math.log(0.5 / delta)
    else:
        exponent = 1.0 - 2.0 * alpha
        tail = 2.0 * (0.5 ** exponent - delta ** exponent) / exponent

    return window + tail


def verify_claim4() -> None:
    print("=" * 72)
    print("CLAIM 4: Integral scaling for general alpha")
    print("=" * 72)
    print()

    alphas = [0.5, 1.0, 2.0]
    g_mins = [0.1, 0.01, 0.001]

    for alpha in alphas:
        print(f"  alpha = {alpha}")
        print()

        if alpha == 0.5:
            print("    Theoretical scaling: Theta(log(1/g_min))")
            print()
            print(f"    {'g_min':>10s}  {'Integral':>14s}  {'log(1/g_min)':>14s}  {'I/log':>10s}")
            print(f"    {'-'*10}  {'-'*14}  {'-'*14}  {'-'*10}")
            ratios = []
            for gm in g_mins:
                I_val = alpha_profile_integral(alpha, gm)
                log_val = math.log(1.0 / gm)
                r = I_val / log_val
                ratios.append(r)
                print(f"    {gm:>10.4f}  {I_val:>14.6f}  {log_val:>14.6f}  {r:>10.4f}")
            assert max(ratios) - min(ratios) < 0.25, "Claim 4 alpha=0.5 ratio not stable"

        else:
            exponent = 1.0 / alpha - 2.0
            print(f"    Theoretical scaling: Theta(g_min^({1.0/alpha:.1f} - 2) = g_min^{exponent:.1f})")
            print()
            print(f"    {'g_min':>10s}  {'Integral':>14s}  {'g_min^exp':>14s}  {'I/scaling':>10s}")
            print(f"    {'-'*10}  {'-'*14}  {'-'*14}  {'-'*10}")
            ratios = []
            for gm in g_mins:
                I_val = alpha_profile_integral(alpha, gm)
                scaling = gm ** exponent
                r = I_val / scaling
                ratios.append(r)
                print(f"    {gm:>10.4f}  {I_val:>14.6f}  {scaling:>14.6f}  {r:>10.4f}")
            assert max(ratios) - min(ratios) < 0.6, f"Claim 4 alpha={alpha} ratio not stable"

        print()


# ---------------------------------------------------------------------------
# Claim 5: Measure condition constant by alpha
# ---------------------------------------------------------------------------


def sublevel_measure_symmetric(x: float, alpha: float, g_min: float) -> float:
    if x < g_min:
        return 0.0
    half_width = x ** (1.0 / alpha)
    return min(1.0, 2.0 * half_width)


def numerical_C(alpha: float, g_min: float) -> float:
    # Dense scan around relevant regions: near g_min, near crossover, and large x.
    x_vals = [g_min * (1.0 + i / 2000.0) for i in range(2001)]

    # Add logarithmic grid up to 5.
    x0 = max(g_min, 1e-12)
    x1 = 5.0
    num_log = 4000
    ratio = x1 / x0
    for i in range(num_log + 1):
        x_vals.append(x0 * (ratio ** (i / num_log)))

    best = 0.0
    for x in x_vals:
        if x <= 0.0:
            continue
        mu = sublevel_measure_symmetric(x, alpha, g_min)
        best = max(best, mu / x)
    return best


def verify_claim5() -> None:
    print("=" * 72)
    print("CLAIM 5: Measure condition constant for general alpha")
    print("=" * 72)
    print()

    alphas = [0.5, 1.0, 2.0]
    g_mins = [0.1, 0.01, 0.001]

    print(f"  {'alpha':>6s}  {'g_min':>10s}  {'C_numerical':>14s}  {'C_theory':>14s}")
    print(f"  {'-'*6}  {'-'*10}  {'-'*14}  {'-'*14}")

    for alpha in alphas:
        for gm in g_mins:
            c_num = numerical_C(alpha, gm)
            if alpha <= 1.0:
                c_theory = 2.0 ** alpha
            else:
                c_theory = 2.0 * (gm ** (1.0 / alpha - 1.0))

            print(f"  {alpha:>6.1f}  {gm:>10.4f}  {c_num:>14.6f}  {c_theory:>14.6f}")
            rel_err = abs(c_num - c_theory) / c_theory
            assert rel_err < 2e-3, (
                f"Claim 5 failed for alpha={alpha}, g_min={gm}: "
                f"C_num={c_num}, C_theory={c_theory}"
            )

        print()


# ---------------------------------------------------------------------------
# Claim 6: Partial-information comparison (Proposition I)
# ---------------------------------------------------------------------------


def rc_overhead(eps_a1: float, delta_a1: float) -> float:
    return max(1.0, eps_a1 / delta_a1)


def jrs_overhead(delta_c_over_c: float, delta_g_over_g: float) -> float:
    if delta_g_over_g >= 1.0:
        raise ValueError("delta_g_over_g must be < 1.")
    return (1.0 + delta_c_over_c) ** 2 / (1.0 - delta_g_over_g)


def verify_claim6() -> None:
    print("=" * 72)
    print("CLAIM 6: Partial-information degradation (RC vs JRS)")
    print("=" * 72)
    print()

    # Unstructured scale: N=2^40, d0=A2=1 => delta_A1 = 2/sqrt(N)=2^(-19)
    n = 40
    N = 2 ** n
    delta_a1 = 2.0 / math.sqrt(N)

    # Simple sensitivity model for JRS constants:
    # delta_C/C = L_C * eps_A1, delta_g/g = L_g * eps_A1.
    L_c = 0.8
    L_g = 0.5

    eps_values = [delta_a1 / 10.0, delta_a1, 1e-5, 1e-4, 1e-3, 1e-2]

    print(f"  n={n}, delta_A1={delta_a1:.3e}")
    print(f"  JRS model: delta_C/C={L_c}*eps_A1, delta_g/g={L_g}*eps_A1")
    print()
    print(f"  {'eps_A1':>12s}  {'RC overhead':>12s}  {'JRS overhead':>12s}")
    print(f"  {'-'*12}  {'-'*12}  {'-'*12}")

    rows = []
    for eps in eps_values:
        rc = rc_overhead(eps, delta_a1)
        jrs = jrs_overhead(L_c * eps, L_g * eps)
        rows.append((eps, rc, jrs))
        print(f"  {eps:>12.3e}  {rc:>12.6f}  {jrs:>12.6f}")

    # Checks encoding the proposition's practical message.
    # 1) RC grows as eps/delta_A1 once eps exceeds delta_A1.
    eps = 1e-3
    assert rc_overhead(eps, delta_a1) > 100.0

    # 2) JRS overhead remains mild for the same eps when relative errors are small.
    assert jrs_overhead(L_c * eps, L_g * eps) < 1.01

    eps = 1e-2
    assert jrs_overhead(L_c * eps, L_g * eps) < 1.04

    print()
    print("  RC overhead explodes once eps_A1 >> delta_A1.")
    print("  JRS overhead tracks relative errors in (C, g_min) and stays near-constant here.")
    print()


# ---------------------------------------------------------------------------
# Claim 7: Structured-family constant comparison (Remark J)
# ---------------------------------------------------------------------------


def ising_chain_with_field_distribution(n: int, J: int = 1, h: int = 1):
    """
    Open ferromagnetic chain with uniform nonnegative field.

    Cost:
      C(sigma) = sum_i J*(1-s_i s_{i+1})/2 + sum_i h*(1-s_i)/2
    with spins s_i in {-1,+1}.
    """
    if n < 2:
        raise ValueError("n must be >= 2")

    counts = {}
    for sigma in product([-1, 1], repeat=n):
        c = 0
        for i in range(n - 1):
            c += J * ((1 - sigma[i] * sigma[i + 1]) // 2)
        for i in range(n):
            c += h * ((1 - sigma[i]) // 2)
        counts[c] = counts.get(c, 0) + 1
    return counts


def normalized_levels_from_counts(counts):
    """Return levels (E, d) after shift and normalization to [0,1]."""
    costs = sorted(counts)
    c0 = costs[0]
    cmax = costs[-1]
    scale = cmax - c0
    levels = [((c - c0) / scale, counts[c]) for c in costs]
    return levels


def structured_constants_from_levels(
    levels,
    N: int,
    coarse_steps: int = 1500,
    refine_iters: int = 80,
    bracket_radius: float = 0.06,
):
    energies = [E for E, _ in levels]
    degeneracies = [d for _, d in levels]

    d0 = next(d for E, d in levels if E == 0.0)
    delta = min(E for E, _ in levels if E > 0.0)

    A1 = sum(d / E for E, d in levels if E > 0.0) / N
    A2 = sum(d / (E * E) for E, d in levels if E > 0.0) / N

    s_star = A1 / (A1 + 1.0)

    vec = [math.sqrt(d / N) for d in degeneracies]

    def reduced_eigs(s: float):
        m = len(levels)
        H = [[-(1.0 - s) * vec[i] * vec[j] for j in range(m)] for i in range(m)]
        for i in range(m):
            H[i][i] += s * energies[i]
        return jacobi_eigenvalues_symmetric(H)

    def full_gap(s: float):
        eigs = reduced_eigs(s)
        lam0 = eigs[0]
        candidates = [eigs[1] - lam0]

        # Orthogonal sectors within each energy shell (driver acts as 0 there).
        for E, d in levels:
            if d > 1:
                candidates.append(s * E - lam0)

        return min(candidates)

    # Coarse scan + local ternary refinement.
    s_best = 0.0
    g_best = float("inf")
    for i in range(coarse_steps + 1):
        s = i / float(coarse_steps)
        g = full_gap(s)
        if g < g_best:
            g_best = g
            s_best = s

    left = max(0.0, s_best - bracket_radius)
    right = min(1.0, s_best + bracket_radius)
    for _ in range(refine_iters):
        m1 = left + (right - left) / 3.0
        m2 = right - (right - left) / 3.0
        if full_gap(m1) < full_gap(m2):
            right = m2
        else:
            left = m1

    s_min = 0.5 * (left + right)
    g_min = full_gap(s_min)

    k = 0.25
    a = delta / 12.0
    assert a > k * g_min, "Need a > k*g_min for s0 formula"

    s0 = s_star - (k * g_min * (1.0 - s_star)) / (a - k * g_min)

    C = 3.0 * A2 / (A1 * (A1 + 1.0)) + 30.0 * (1.0 - s0) / delta
    I = (
        3.0 * A2 / (A1 * (A1 + 1.0))
        + 900.0 * (1.0 - s0) ** 2 * A1 * (A1 + 1.0) / (A2 * delta * delta)
    )

    ratio = C * C / I

    return {
        "A1": A1,
        "A2": A2,
        "Delta": delta,
        "d0": d0,
        "s_star": s_star,
        "g_min": g_min,
        "s_min": s_min,
        "s0": s0,
        "C": C,
        "I": I,
        "ratio": ratio,
    }


def grover_bound_ratio(N: int) -> float:
    A1 = (N - 1.0) / N
    A2 = A1
    one_minus_s0 = N / (2.0 * N - 1.0)
    C = 3.0 * A2 / (A1 * (A1 + 1.0)) + 30.0 * one_minus_s0
    I = 3.0 * A2 / (A1 * (A1 + 1.0)) + 900.0 * one_minus_s0 * one_minus_s0 * A1 * (A1 + 1.0) / A2
    return C * C / I


def verify_claim7() -> None:
    print("=" * 72)
    print("CLAIM 7: Structured-family C^2/I comparison (ferromagnetic Ising)")
    print("=" * 72)
    print()

    n = 10
    N = 2 ** n
    counts = ising_chain_with_field_distribution(n=n, J=1, h=1)
    levels = normalized_levels_from_counts(counts)
    vals = structured_constants_from_levels(levels, N)

    ratio_grover = grover_bound_ratio(N)

    print(f"  Instance: open ferromagnetic chain, n={n}, J=1, h=1")
    print(f"  N={N}, levels={len(levels)}, d0={vals['d0']}")
    print(f"  A1={vals['A1']:.10f}, A2={vals['A2']:.10f}, Delta={vals['Delta']:.10f}")
    print(f"  s*={vals['s_star']:.10f}, g_min={vals['g_min']:.10f} at s={vals['s_min']:.10f}")
    print(f"  s0={vals['s0']:.10f}")
    print(f"  C={vals['C']:.10f}, I={vals['I']:.10f}")
    print(f"  C^2/I (structured)={vals['ratio']:.10f}")
    print(f"  C^2/I (Grover bound, same N)={ratio_grover:.10f}")

    # Core comparison used in Remark J.
    assert vals["ratio"] < 1.0, "Need C^2/I < 1 for JRS structural advantage"
    assert vals["ratio"] > ratio_grover, "Structured ratio should exceed Grover ratio in this instance"

    # Stability checks against expected values used in proof text.
    assert abs(vals["A1"] - 1.5848010225) < 2e-6
    assert abs(vals["A2"] - 2.8410286701) < 2e-6
    assert abs(vals["Delta"] - (1.0 / 7.0)) < 1e-12
    assert abs(vals["ratio"] - 0.7122006784) < 2e-6

    print()
    print("  Structured instance yields C^2/I > Grover's 0.603-level ratio.")
    print("  JRS remains tighter than RC (ratio < 1), but by a smaller margin.")
    print()

    # Robustness check: same family for multiple sizes.
    print("  Family-level robustness scan (same model, n in {8, 10, 12}):")
    for n_scan in [8, 10, 12]:
        N_scan = 2 ** n_scan
        counts_scan = ising_chain_with_field_distribution(n=n_scan, J=1, h=1)
        levels_scan = normalized_levels_from_counts(counts_scan)
        vals_scan = structured_constants_from_levels(levels_scan, N_scan, coarse_steps=1000, refine_iters=60)
        ratio_g_scan = grover_bound_ratio(N_scan)
        print(
            f"    n={n_scan}: structured={vals_scan['ratio']:.6f}, "
            f"grover={ratio_g_scan:.6f}, delta={vals_scan['ratio'] - ratio_g_scan:.6f}"
        )
        assert vals_scan["ratio"] < 1.0

    print()
    print("  Field-strength robustness scan (n=10, J=1, h in {1,2,3,4}):")
    for h_scan in [1, 2, 3, 4]:
        counts_h = ising_chain_with_field_distribution(n=10, J=1, h=h_scan)
        levels_h = normalized_levels_from_counts(counts_h)
        vals_h = structured_constants_from_levels(levels_h, 2 ** 10, coarse_steps=1000, refine_iters=60)
        ratio_g_h = grover_bound_ratio(2 ** 10)
        print(
            f"    h={h_scan}: structured={vals_h['ratio']:.6f}, "
            f"grover={ratio_g_h:.6f}, delta={vals_h['ratio'] - ratio_g_h:.6f}"
        )
        assert vals_h["ratio"] < 1.0
        assert vals_h["ratio"] > ratio_g_h

    print()


# ---------------------------------------------------------------------------
# Claim 8: Explicit A1 propagation formulas (Corollary I.1)
# ---------------------------------------------------------------------------


def verify_claim8() -> None:
    print("=" * 72)
    print("CLAIM 8: Explicit A1-error propagation formulas (Corollary I.1)")
    print("=" * 72)
    print()

    def g_ratio_exact(A: float, e: float) -> float:
        # g_mod(A) proportional to A/(A+1), so ratio is exact and kappa cancels.
        return ((A + e) / (A + e + 1.0)) / (A / (A + 1.0)) - 1.0

    def g_ratio_formula(A: float, e: float) -> float:
        return e / (A * (A + e + 1.0))

    def cleft_ratio_exact(A: float, e: float) -> float:
        # C_left(A) proportional to 1/(A(A+1)); beta cancels in ratio.
        left_new = 1.0 / ((A + e) * (A + e + 1.0))
        left_old = 1.0 / (A * (A + 1.0))
        return left_new / left_old - 1.0

    def cleft_ratio_formula(A: float, e: float) -> float:
        return -(((2.0 * A + 1.0) * e + e * e) / ((A + e) * (A + e + 1.0)))

    # Deterministic sample points spanning moderate A and small relative errors.
    A_values = [0.4, 0.75, 1.2, 2.0, 3.5]
    eps_values = [1e-3, 5e-3, 1e-2]

    print(f"  {'A':>6s}  {'eps':>8s}  {'|g_exact-g_form|':>16s}  {'|c_exact-c_form|':>16s}")
    print(f"  {'-'*6}  {'-'*8}  {'-'*16}  {'-'*16}")

    for A in A_values:
        for eps in eps_values:
            # test both signs to exercise asymmetric denominators
            for sgn in (-1.0, 1.0):
                e = sgn * eps
                assert abs(e) < A  # Corollary assumption

                g_e = g_ratio_exact(A, e)
                g_f = g_ratio_formula(A, e)
                c_e = cleft_ratio_exact(A, e)
                c_f = cleft_ratio_formula(A, e)

                g_err = abs(g_e - g_f)
                c_err = abs(c_e - c_f)

                print(f"  {A:>6.2f}  {abs(e):>8.3e}  {g_err:>16.3e}  {c_err:>16.3e}")
                assert g_err < 1e-12
                assert c_err < 1e-12

                # Bound checks from Corollary I.1
                chi_g = abs(e) / (A * (A + 1.0 - abs(e)))
                chi_c = abs(e) * (2.0 * A + 1.0 + abs(e)) / ((A - abs(e)) * (A + 1.0 - abs(e)))
                assert abs(g_e) <= chi_g + 1e-12
                assert abs(c_e) <= chi_c + 1e-12

                # JRS overhead control using explicit bounds
                overhead_exact = ((1.0 + abs(c_e)) ** 2) / (1.0 - abs(g_e))
                overhead_bound = ((1.0 + chi_c) ** 2) / (1.0 - chi_g)
                assert overhead_exact <= overhead_bound + 1e-12

    print()
    print("  Exact identities and upper bounds match Corollary I.1 numerically.")
    print()


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main() -> None:
    print()
    print("Numerical Verification: Schedule Optimality Extensions")
    print("Experiment 11")
    print()

    verify_claim1()
    verify_claim2()
    verify_claim3()
    verify_claim4()
    verify_claim5()
    verify_claim6()
    verify_claim7()
    verify_claim8()

    print("=" * 72)
    print("All claims verified.")
    print("=" * 72)


if __name__ == "__main__":
    main()
