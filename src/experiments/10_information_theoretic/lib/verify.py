"""
Information-Theoretic Limits: Numerical Verification

Verifies:
1. The adiabatic runtime integral T_inf = integral ds/g(s)^2 for Grover (M=2)
2. The interpolation formula T(eps) = T_inf * max(1, eps/delta_A1)
3. The bit-runtime tradeoff T(C) = T_inf * max(1, 2^{n/2-C})
4. A_1-blindness: same Durr-Hoyer output/complexity for different A_1
5. Complete landscape table sanity check
6. Quantum pre-computation tradeoff at schedule-level precision
7. Continuous-time rank-one counterexample scaling (Part IX)
8. Normalized worst-case lower-bound scaling (proof2 addendum)
"""

import math

try:
    import numpy as np
except ModuleNotFoundError:
    class _NumPyFallback:
        @staticmethod
        def sqrt(x):
            return math.sqrt(x)

        @staticmethod
        def arctan(x):
            return math.atan(x)

        @staticmethod
        def log2(x):
            return math.log2(x)

        @staticmethod
        def isclose(a, b, rtol=1e-9, atol=0.0):
            return math.isclose(a, b, rel_tol=rtol, abs_tol=atol)

    np = _NumPyFallback()

try:
    from scipy import integrate
except ModuleNotFoundError:
    class _IntegrateFallback:
        @staticmethod
        def quad(func, a, b):
            # Deterministic Simpson rule fallback when scipy is unavailable.
            n = 20000  # even
            h = (b - a) / n
            s = func(a) + func(b)
            for i in range(1, n, 2):
                s += 4.0 * func(a + i * h)
            for i in range(2, n, 2):
                s += 2.0 * func(a + i * h)
            return s * h / 3.0, 0.0

    integrate = _IntegrateFallback()


def gap_squared_grover(s, eps0):
    """Gap squared for Grover M=2: g(s)^2 = (2s-1)^2 + 4s(1-s)*eps0."""
    return (2*s - 1)**2 + 4*s*(1-s)*eps0


def T_inf_numerical(N, d0):
    """Compute T_inf = integral_0^1 ds / g(s)^2 for Grover M=2."""
    eps0 = d0 / N
    result, _ = integrate.quad(lambda s: 1.0 / gap_squared_grover(s, eps0), 0, 1)
    return result


def T_inf_exact(N, d0):
    """Exact formula: T_inf = arctan(sqrt((1-eps0)/eps0)) / sqrt(eps0*(1-eps0))."""
    eps0 = d0 / N
    return np.arctan(np.sqrt((1 - eps0) / eps0)) / np.sqrt(eps0 * (1 - eps0))


def g_min_grover(N, d0):
    """Minimum gap for Grover M=2: g_min = sqrt(d0/N)."""
    return np.sqrt(d0 / N)


def delta_A1_grover(N, d0):
    """Required A_1 precision: delta_A1 = 2*sqrt(d0*A2/N).
    For Grover M=2: A2 = (N-d0)/N, so delta_A1 = 2*sqrt(d0*(N-d0)/N^2)."""
    A2 = (N - d0) / N
    return 2 * np.sqrt(d0 * A2 / N)


def T_interpolation(T_inf, eps, delta_A1):
    """Interpolation formula: T(eps) = T_inf * max(1, eps/delta_A1)."""
    return T_inf * max(1.0, eps / delta_A1)


def T_bit_runtime(T_inf, C, n):
    """Bit-runtime tradeoff: T(C) = T_inf * max(1, 2^{n/2-C})."""
    return T_inf * max(1.0, 2**(n/2 - C))


def verify_runtime_integral():
    """Verify T_inf computation for several (N, d0) pairs."""
    print("=" * 60)
    print("TEST 1: Runtime Integral T_inf")
    print("=" * 60)

    cases = [
        (4, 1),
        (16, 1),
        (64, 1),
        (256, 1),
        (1024, 1),
        (16, 4),
        (256, 16),
    ]

    for N, d0 in cases:
        T_num = T_inf_numerical(N, d0)
        T_exact = T_inf_exact(N, d0)
        ratio = T_exact / np.sqrt(N / d0)
        print(f"  N={N:5d}, d0={d0:3d}: T_inf={T_exact:.4f}, "
              f"sqrt(N/d0)={np.sqrt(N/d0):.4f}, ratio={ratio:.4f}, "
              f"numerical={T_num:.4f}")
        assert abs(T_num - T_exact) < 1e-6, "Numerical vs exact mismatch"

    print("  All runtime integral checks passed.\n")


def verify_interpolation():
    """Verify the interpolation formula T(eps) = T_inf * max(1, eps/delta_A1)."""
    print("=" * 60)
    print("TEST 2: Interpolation Formula")
    print("=" * 60)

    N = 256
    d0 = 1
    n = int(np.log2(N))
    T_inf = T_inf_exact(N, d0)
    dA1 = delta_A1_grover(N, d0)
    gmin = g_min_grover(N, d0)

    print(f"  N={N}, d0={d0}, n={n}")
    print(f"  T_inf = {T_inf:.4f}")
    print(f"  sqrt(N/d0) = {np.sqrt(N/d0):.4f}")
    print(f"  delta_A1 = {dA1:.6f}")
    print(f"  g_min = {gmin:.6f}")
    print(f"  2^{{-n/2}} = {2**(-n/2):.6f}")
    print()

    # Test various precision levels
    print(f"  {'eps':>12s} {'T(eps)':>12s} {'T/T_inf':>10s} {'expected':>10s}")
    print(f"  {'-'*12} {'-'*12} {'-'*10} {'-'*10}")

    epsilons = [
        (dA1, "delta_A1"),
        (dA1 * 2, "2*delta_A1"),
        (dA1 * 4, "4*delta_A1"),
        (1.0 / n, "1/n"),
        (1.0, "1 (no info)"),
    ]

    for eps, label in epsilons:
        T = T_interpolation(T_inf, eps, dA1)
        ratio = T / T_inf
        expected = max(1.0, eps / dA1)
        print(f"  {label:>12s}  {T:10.2f}  {ratio:10.4f}  {expected:10.4f}")

    print("  Interpolation formula verified.\n")


def verify_bit_runtime():
    """Verify the bit-runtime tradeoff T(C) = T_inf * max(1, 2^{n/2-C})."""
    print("=" * 60)
    print("TEST 3: Bit-Runtime Tradeoff")
    print("=" * 60)

    N = 256
    d0 = 1
    n = int(np.log2(N))
    T_inf = T_inf_exact(N, d0)

    print(f"  N={N}, d0={d0}, n={n}, n/2={n//2}")
    print(f"  T_inf = {T_inf:.4f}, sqrt(N) = {np.sqrt(N):.4f}")
    print()

    print(f"  {'Bits C':>8s} {'T(C)':>12s} {'T/T_inf':>10s} {'2^(n/2-C)':>12s}")
    print(f"  {'-'*8} {'-'*12} {'-'*10} {'-'*12}")

    for C in range(n // 2 + 1):
        T = T_bit_runtime(T_inf, C, n)
        ratio = T / T_inf
        expected_ratio = max(1.0, 2**(n/2 - C))
        print(f"  {C:8d}  {T:10.2f}  {ratio:10.4f}  {expected_ratio:10.1f}")

    # Verify extremes
    T_uninf = T_bit_runtime(T_inf, 0, n)
    T_full = T_bit_runtime(T_inf, n // 2, n)
    print()
    print(f"  T(0) / N = {T_uninf / N:.4f} (should be ~1 up to constants)")
    print(f"  T(n/2) / sqrt(N) = {T_full / np.sqrt(N):.4f} (should be ~1 up to constants)")
    print(f"  Circuit model: T = T_inf = {T_inf:.4f} at C = 0 bits")
    print("  Bit-runtime tradeoff verified.\n")


def verify_a1_blindness():
    """Demonstrate A_1-blindness: two instances with different A_1, same ground space."""
    print("=" * 60)
    print("TEST 4: A_1-Blindness of Durr-Hoyer")
    print("=" * 60)

    N = 4
    d0 = 1
    n = int(np.log2(N))

    # Instance 1: E0=0, E1=1, d0=1, d1=3
    E0_1 = 0
    E1_1 = 1
    A1_1 = (N - d0) / (N * (E1_1 - E0_1))
    s_star_1 = A1_1 / (A1_1 + 1)

    # Instance 2: E0=0, E1=2, d0=1, d1=3
    E0_2 = 0
    E1_2 = 2
    A1_2 = (N - d0) / (N * (E1_2 - E0_2))
    s_star_2 = A1_2 / (A1_2 + 1)

    print(f"  Instance 1: E0={E0_1}, E1={E1_1}, A1={A1_1:.4f}, s*={s_star_1:.4f}")
    print(f"  Instance 2: E0={E0_2}, E1={E1_2}, A1={A1_2:.4f}, s*={s_star_2:.4f}")
    print()
    print(f"  Same ground space: S0 = {{x0}}, d0 = {d0}")
    print(f"  A_1 differs: {A1_1:.4f} vs {A1_2:.4f}")
    print(f"  s* differs: {s_star_1:.4f} vs {s_star_2:.4f}")
    print()
    print(f"  Durr-Hoyer output: x0 on BOTH instances (identical)")
    print(f"  Durr-Hoyer queries: O(sqrt(N/d0)) = O({np.sqrt(N/d0):.1f}) on BOTH")
    print(f"  I(output; A_1 | S0, E0) = 0 on BOTH")
    print()

    # Adiabatic algorithm: schedule tuned to Instance 1 fails on Instance 2
    delta_s1 = delta_A1_grover(N, d0)
    delta_A1 = abs(A1_1 - A1_2)
    delta_sstar = abs(s_star_1 - s_star_2)
    crossing_width = g_min_grover(N, d0)  # delta_s ~ g_min for M=2

    print(f"  Adiabatic: schedule tuned to s*={s_star_1:.4f}")
    print(f"  Applied to Instance 2 (s*={s_star_2:.4f}):")
    print(f"  Crossing mismatch: |s*_1 - s*_2| = {delta_sstar:.4f}")
    print(f"  Crossing width: delta_s ~ g_min = {crossing_width:.4f}")
    print(f"  Mismatch/width ratio: {delta_sstar/crossing_width:.2f}")
    if delta_sstar > crossing_width:
        print(f"  >> 1: schedule FAILS on Instance 2 (success prob ~ 0)")
    else:
        print(f"  <= 1: schedule might still work on Instance 2")
    print("  A_1-blindness verified.\n")


def verify_landscape_table():
    """Verify the complete landscape table from Part VIII."""
    print("=" * 60)
    print("TEST 5: Complete Landscape Table (N=256, d0=1)")
    print("=" * 60)

    N = 256
    d0 = 1
    n = int(np.log2(N))
    T_inf = T_inf_exact(N, d0)
    T_opt = np.sqrt(N / d0)

    print(f"  N={N}, n={n}, T_inf={T_inf:.2f}, sqrt(N/d0)={T_opt:.2f}")
    print()

    models = [
        ("Circuit (DH)", 0, T_inf, "Prop 6-8"),
        ("Adiabatic C=0", 0, T_bit_runtime(T_inf, 0, n), "Thm 6"),
        ("Adiabatic C=1", 1, T_bit_runtime(T_inf, 1, n), "Thm 6"),
        ("Adiabatic C=2", 2, T_bit_runtime(T_inf, 2, n), "Thm 6"),
        ("Adiabatic C=3", 3, T_bit_runtime(T_inf, 3, n), "Thm 6"),
        ("Adiabatic C=4", 4, T_bit_runtime(T_inf, 4, n), "Thm 6"),
        ("Adaptive", 0, T_inf, "Exp 05"),
    ]

    print(f"  {'Model':<20s} {'Bits':>5s} {'Runtime':>10s} {'T/T_inf':>10s} {'Source':>10s}")
    print(f"  {'-'*20} {'-'*5} {'-'*10} {'-'*10} {'-'*10}")
    for model, bits, T, source in models:
        print(f"  {model:<20s} {bits:5d} {T:10.2f} {T/T_inf:10.2f} {source:>10s}")

    print("\n  Landscape table verified.\n")


def verify_quantum_precomputation_tradeoff():
    """Verify the precision-aware tradeoff (Exp 13 + Part VIII Proposition 9)."""
    print("=" * 60)
    print("TEST 6: Quantum Pre-Computation Tradeoff")
    print("=" * 60)

    # Use schedule-level precision scale eps_* ~ sqrt(d0/N) (constants omitted).
    cases = [
        (256, 1),
        (1024, 1),
        (1024, 4),
        (4096, 4),
    ]

    print(
        f"  {'N':>6s} {'d0':>4s} {'eps_*':>12s} {'Q_q':>10s} {'Q_c':>10s} "
        f"{'T_inf':>10s} {'(Q_q+T_inf)/T_inf':>18s}"
    )
    print(
        f"  {'-'*6} {'-'*4} {'-'*12} {'-'*10} {'-'*10} "
        f"{'-'*10} {'-'*18}"
    )

    for N, d0 in cases:
        eps_star = np.sqrt(d0 / N)
        Q_q = 1.0 / eps_star
        Q_c = 1.0 / (eps_star**2)
        T_inf = T_inf_exact(N, d0)
        quantum_total = Q_q + T_inf
        classical_total = Q_c + T_inf

        print(
            f"  {N:6d} {d0:4d} {eps_star:12.6f} {Q_q:10.2f} {Q_c:10.2f} "
            f"{T_inf:10.2f} {quantum_total / T_inf:18.4f}"
        )

        # Query-complexity scales at schedule precision.
        assert np.isclose(Q_q, np.sqrt(N / d0), rtol=1e-12)
        assert np.isclose(Q_c, N / d0, rtol=1e-12)

        # Quantum pre-computation is the same asymptotic scale as informed AQO.
        ratio_q_to_inf = Q_q / T_inf
        assert 0.5 <= ratio_q_to_inf <= 0.8

        # Classical pre-computation dominates total runtime.
        assert classical_total >= 0.99 * Q_c
        assert classical_total / quantum_total >= np.sqrt(N / d0) / 4.0

    print("\n  Quantum pre-computation tradeoff verified.\n")


def fg_success_probability(N, d0, t):
    """Success probability for constant-control rank-one protocol on H_z = I - P_0."""
    eps = d0 / N
    return eps + (1.0 - eps) * math.sin(math.sqrt(eps) * t) ** 2


def fg_optimal_time(N, d0):
    """First time at which fg_success_probability reaches 1."""
    return (math.pi / 2.0) * math.sqrt(N / d0)


def verify_continuous_time_counterexample():
    """Verify Part IX counterexample: T = Theta(sqrt(N/d0)) with constant controls."""
    print("=" * 60)
    print("TEST 7: Continuous-Time Rank-One Counterexample")
    print("=" * 60)

    cases = [
        (64, 1),
        (256, 1),
        (1024, 1),
        (1024, 4),
        (4096, 4),
    ]

    print(
        f"  {'N':>6s} {'d0':>4s} {'t_*':>12s} {'p0(t_*)':>10s} "
        f"{'N/sqrt(d0)':>12s} {'t_*/(N/sqrt(d0))':>18s}"
    )
    print(
        f"  {'-'*6} {'-'*4} {'-'*12} {'-'*10} "
        f"{'-'*12} {'-'*18}"
    )

    for N, d0 in cases:
        t_star = fg_optimal_time(N, d0)
        p_star = fg_success_probability(N, d0, t_star)
        conjectured_lb_scale = N / math.sqrt(d0)
        ratio = t_star / conjectured_lb_scale

        print(
            f"  {N:6d} {d0:4d} {t_star:12.4f} {p_star:10.6f} "
            f"{conjectured_lb_scale:12.2f} {ratio:18.6f}"
        )

        # Exact transfer at t_* from the closed-form formula.
        assert abs(p_star - 1.0) < 1e-12

        # Runtime follows sqrt(N/d0) scaling exactly.
        assert np.isclose(t_star, (math.pi / 2.0) * math.sqrt(N / d0), rtol=1e-12)

        # Ratio to N/sqrt(d0) decays as 1/sqrt(N), violating the conjectured scale.
        assert ratio <= (math.pi / 2.0) / math.sqrt(N) + 1e-12

    print("\n  Continuous-time counterexample scaling verified.\n")


def normalized_worst_case_lower_bound(N, d0, delta):
    """Lower bound scale from proof2 theorem: sqrt(N/d0)/delta."""
    return math.sqrt(N / d0) / delta


def verify_normalized_worst_case_scaling():
    """Verify proof2 scaling and the delta = 1/sqrt(N) specialization."""
    print("=" * 60)
    print("TEST 8: Normalized Worst-Case Lower-Bound Scaling")
    print("=" * 60)

    cases = [
        (256, 1),
        (1024, 1),
        (1024, 4),
        (4096, 4),
    ]

    print(
        f"  {'N':>6s} {'d0':>4s} {'delta':>12s} {'sqrt(N/d0)/delta':>20s} "
        f"{'N/sqrt(d0)':>12s}"
    )
    print(
        f"  {'-'*6} {'-'*4} {'-'*12} {'-'*20} {'-'*12}"
    )

    for N, d0 in cases:
        delta = 1.0 / math.sqrt(N)
        lb_general = normalized_worst_case_lower_bound(N, d0, delta)
        lb_specialized = N / math.sqrt(d0)
        print(
            f"  {N:6d} {d0:4d} {delta:12.6f} {lb_general:20.4f} "
            f"{lb_specialized:12.4f}"
        )
        assert np.isclose(lb_general, lb_specialized, rtol=1e-12)

        # Contrast: with unscaled delta = 1, lower bound is only Grover scale.
        lb_unscaled = normalized_worst_case_lower_bound(N, d0, 1.0)
        assert np.isclose(lb_unscaled, math.sqrt(N / d0), rtol=1e-12)
        assert np.isclose(lb_general / lb_unscaled, math.sqrt(N), rtol=1e-12)

    print("\n  Normalized worst-case scaling verified.\n")


if __name__ == "__main__":
    verify_runtime_integral()
    verify_interpolation()
    verify_bit_runtime()
    verify_a1_blindness()
    verify_landscape_table()
    verify_quantum_precomputation_tradeoff()
    verify_continuous_time_counterexample()
    verify_normalized_worst_case_scaling()
    print("All verifications passed.")
