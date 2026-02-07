"""
Numerical verification for Experiment 11 open research threads (proof2/main2/main3).

Claims verified:
  1) Explicit p=3/2 JRS prefactor simplification:
     B_JRS(3/2) = 8*A*C_mu + 63*A^2*C_mu^2.
  2) Quantitative runtime-constant comparison on Grover and one structured instance.
  3) Closed-form runtime for RC-safe exponential slowdown schedule on
     the alpha=1 linear-cusp model and its exponential overhead lower bound.
  4) Class-level penalty theorem checks for logarithmic, polynomial, and
     stretched-exponential slowdown penalties.

This script uses only the Python standard library.
"""

from __future__ import annotations

import math


# ---------------------------------------------------------------------------
# Generic helpers
# ---------------------------------------------------------------------------


def simpson_integral(func, a: float, b: float, n: int) -> float:
    if n <= 0 or n % 2 != 0:
        raise ValueError("n must be a positive even integer")
    h = (b - a) / n
    total = func(a) + func(b)
    for i in range(1, n):
        x = a + i * h
        total += (4.0 if i % 2 else 2.0) * func(x)
    return total * h / 3.0


# ---------------------------------------------------------------------------
# Claim 1: Explicit JRS prefactor
# ---------------------------------------------------------------------------


def b_jrs_prefactor(a_norm: float, c_mu: float, p: float) -> float:
    """
    Explicit prefactor derived from JRS Theorem 3 + power-law schedule bounds.

    B_JRS(p) = 2*A*C_mu*p/(p-1) + 2*A*C_mu
               + 7*A^2*C_mu^2*p*(3-p)/((p-1)*(2-p)).
    """
    if not (1.0 < p < 2.0):
        raise ValueError("p must be in (1,2)")
    term1 = 2.0 * a_norm * c_mu * p / (p - 1.0)
    term2 = 2.0 * a_norm * c_mu
    term3 = (
        7.0
        * a_norm
        * a_norm
        * c_mu
        * c_mu
        * p
        * (3.0 - p)
        / ((p - 1.0) * (2.0 - p))
    )
    return term1 + term2 + term3


def b_jrs_prefactor_p32_closed(a_norm: float, c_mu: float) -> float:
    return 8.0 * a_norm * c_mu + 63.0 * a_norm * a_norm * c_mu * c_mu


def ghat_from_params(a1: float, a2: float, d0: float, n_dim: int) -> float:
    return 2.0 * a1 / (a1 + 1.0) * math.sqrt(d0 / (n_dim * a2))


def verify_claim1() -> None:
    print("=" * 72)
    print("CLAIM 1: Explicit JRS prefactor extraction")
    print("=" * 72)
    print()

    # Algebraic check of p=3/2 simplification.
    samples = [(2.0, 1.0), (2.0, 3.5), (1.7, 12.0)]
    print(f"  {'A':>8s}  {'C_mu':>12s}  {'B_general':>16s}  {'B_closed':>16s}  {'Abs Err':>12s}")
    print(f"  {'-'*8}  {'-'*12}  {'-'*16}  {'-'*16}  {'-'*12}")

    for a_norm, c_mu in samples:
        b_general = b_jrs_prefactor(a_norm, c_mu, 1.5)
        b_closed = b_jrs_prefactor_p32_closed(a_norm, c_mu)
        err = abs(b_general - b_closed)
        print(f"  {a_norm:>8.3f}  {c_mu:>12.6f}  {b_general:>16.6f}  {b_closed:>16.6f}  {err:>12.2e}")
        assert err < 1e-10

    print()
    print("  p=3/2 identity verified: B_JRS = 8*A*C_mu + 63*A^2*C_mu^2")
    print()


# ---------------------------------------------------------------------------
# Claim 2: Runtime-constant comparison (Grover + structured)
# ---------------------------------------------------------------------------


def verify_claim2() -> None:
    print("=" * 72)
    print("CLAIM 2: Quantitative prefactor comparison")
    print("=" * 72)
    print()

    a_norm = 2.0

    # Grover at N=1024
    n_dim = 1024
    a1_g = (n_dim - 1.0) / n_dim
    a2_g = a1_g
    d0_g = 1.0
    c_mu_g = 1.0  # exact Grover measure constant
    gmin_g = 1.0 / math.sqrt(n_dim)
    ghat_g = ghat_from_params(a1_g, a2_g, d0_g, n_dim)
    i_exact_g = n_dim / math.sqrt(n_dim - 1.0) * math.atan(math.sqrt(n_dim - 1.0))
    one_minus_s0 = n_dim / (2.0 * n_dim - 1.0)
    i_bound_g = (
        3.0 * a2_g / (a1_g * (a1_g + 1.0))
        + 900.0 * one_minus_s0 * one_minus_s0 * a1_g * (a1_g + 1.0) / a2_g
    )

    b_g = b_jrs_prefactor_p32_closed(a_norm, c_mu_g)
    t_jrs_coeff = b_g / gmin_g
    t_rc_exact_coeff = a_norm * i_exact_g / ghat_g
    t_rc_bound_coeff = a_norm * i_bound_g / ghat_g

    print("  Grover (N=1024, C_mu=1):")
    print(f"    B_JRS(3/2) = {b_g:.6f}")
    print(f"    T_JRS coeff (eps=1): {t_jrs_coeff:.6f}")
    print(f"    T_RC exact coeff (eps=1): {t_rc_exact_coeff:.6f}")
    print(f"    T_RC bound coeff (eps=1): {t_rc_bound_coeff:.6f}")
    print(f"    Ratio T_JRS/T_RC_exact: {t_jrs_coeff / t_rc_exact_coeff:.6f}")
    print(f"    Ratio T_JRS/T_RC_bound: {t_jrs_coeff / t_rc_bound_coeff:.6f}")

    # Structured instance from Experiment 11 Remark J.
    a1_s = 1.5848010225
    a2_s = 2.8410286701
    d0_s = 1.0
    n_dim_s = 1024
    c_mu_s = 157.4491589643
    gmin_s = 0.0227184465
    ghat_s = ghat_from_params(a1_s, a2_s, d0_s, n_dim_s)
    i_bound_s = 34807.9388418623

    b_s = b_jrs_prefactor_p32_closed(a_norm, c_mu_s)
    t_jrs_coeff_s = b_s / gmin_s
    t_rc_coeff_s = a_norm * i_bound_s / ghat_s

    print()
    print("  Structured instance (n=10 open-chain ferromagnetic Ising):")
    print(f"    B_JRS(3/2) = {b_s:.6f}")
    print(f"    T_JRS coeff (eps=1): {t_jrs_coeff_s:.6f}")
    print(f"    T_RC bound coeff (eps=1): {t_rc_coeff_s:.6f}")
    print(f"    Ratio T_JRS/T_RC_bound: {t_jrs_coeff_s / t_rc_coeff_s:.6f}")

    # Stability checks against recorded values.
    assert abs(b_g - 268.0) < 1e-9
    assert abs(t_jrs_coeff / t_rc_exact_coeff - 2.7186373572131677) < 1e-9
    assert abs(t_jrs_coeff / t_rc_bound_coeff - 0.29664353118638015) < 1e-9
    assert abs(t_jrs_coeff_s / t_rc_coeff_s - 89.83782486467271) < 1e-7

    print()


# ---------------------------------------------------------------------------
# Claim 3: Non-power-law exponential slowdown schedule
# ---------------------------------------------------------------------------


def gap_linear_cusp(s: float, gmin: float, c_slope: float, s_star: float = 0.5) -> float:
    return max(gmin, c_slope * abs(s - s_star))


def i_rc_model(gmin: float, c_slope: float) -> float:
    # Exact for g(s)=max(gmin, c|s-1/2|), assuming gmin < c/2.
    return 4.0 / (c_slope * gmin) - 4.0 / (c_slope * c_slope)


def i_exp_model_closed(gmin: float, beta: float, c_slope: float) -> float:
    if beta <= 0.0:
        raise ValueError("beta must be > 0")
    # Exact integral of exp(beta/g(s))/g(s)^2 over [0,1] for the linear-cusp model.
    return (
        math.exp(beta / gmin) * (2.0 / (c_slope * gmin) + 2.0 / (beta * c_slope))
        - 2.0 * math.exp(2.0 * beta / c_slope) / (beta * c_slope)
    )


def i_exp_model_numerical(gmin: float, beta: float, c_slope: float) -> float:
    f = lambda s: math.exp(beta / gap_linear_cusp(s, gmin, c_slope)) / (gap_linear_cusp(s, gmin, c_slope) ** 2)
    return simpson_integral(f, 0.0, 1.0, n=200000)


def verify_claim3() -> None:
    print("=" * 72)
    print("CLAIM 3: Non-power-law exponential slowdown overhead")
    print("=" * 72)
    print()

    c_slope = 1.0
    beta = 0.05
    gvals = [0.1, 0.05, 0.02, 0.01, 0.005]

    print(f"  Model: g(s)=max(gmin, c|s-1/2|), c={c_slope}, beta={beta}")
    print()
    print(f"  {'gmin':>10s}  {'I_exp/I_RC':>12s}  {'0.5*exp(beta/gmin)':>20s}  {'Rel Err(closed vs num)':>22s}")
    print(f"  {'-'*10}  {'-'*12}  {'-'*20}  {'-'*22}")

    prev = None
    for gmin in gvals:
        i_rc = i_rc_model(gmin, c_slope)
        i_exp_closed = i_exp_model_closed(gmin, beta, c_slope)
        i_exp_num = i_exp_model_numerical(gmin, beta, c_slope)

        ratio = i_exp_closed / i_rc
        lower_bound = 0.5 * math.exp(beta / gmin)
        rel_err = abs(i_exp_closed - i_exp_num) / i_exp_closed

        print(f"  {gmin:>10.4f}  {ratio:>12.6f}  {lower_bound:>20.6f}  {rel_err:>22.2e}")

        # Closed form matches numerical quadrature.
        assert rel_err < 1e-10
        # Rigorous lower bound from window contribution.
        assert ratio > lower_bound
        # Overhead increases as gap shrinks.
        if prev is not None:
            assert ratio > prev
        prev = ratio

    print()
    print("  Exponential slowdown incurs overhead >= 0.5*exp(beta/gmin),")
    print("  so it is asymptotically worse than O(1/gmin) schedules.")
    print()


# ---------------------------------------------------------------------------
# Claim 4: Class-level non-power-law penalty theorem (proof3/main3)
# ---------------------------------------------------------------------------


def i_phi_model_numerical(gmin: float, c_slope: float, phi_func) -> float:
    f = lambda s: phi_func(gap_linear_cusp(s, gmin, c_slope)) / (gap_linear_cusp(s, gmin, c_slope) ** 2)
    return simpson_integral(f, 0.0, 1.0, n=120000)


def verify_claim4() -> None:
    print("=" * 72)
    print("CLAIM 4: Class-level penalty theorem (window lower bound)")
    print("=" * 72)
    print()

    c_slope = 1.0

    families = [
        (
            "log",
            lambda g: 1.0 + 0.7 * math.log(1.0 / g),
            [0.2, 0.1, 0.05, 0.02],
        ),
        (
            "power",
            lambda g: 1.0 + 0.2 * (g ** (-0.75)),
            [0.2, 0.1, 0.05, 0.02],
        ),
        (
            "stretched_exp",
            lambda g: math.exp(0.03 / (g ** 1.2)),
            [0.2, 0.1, 0.05, 0.03],
        ),
    ]

    for family_name, phi_func, gvals in families:
        print(f"  Family: {family_name}")
        print(f"  {'gmin':>10s}  {'I_phi/I_RC':>12s}  {'exact LB':>12s}  {'coarse LB':>12s}")
        print(f"  {'-'*10}  {'-'*12}  {'-'*12}  {'-'*12}")

        prev = None
        for gmin in gvals:
            i_rc = i_rc_model(gmin, c_slope)
            i_phi = i_phi_model_numerical(gmin, c_slope, phi_func)
            ratio = i_phi / i_rc

            phi_gmin = phi_func(gmin)
            lower_exact = phi_gmin / (2.0 * (1.0 - gmin / c_slope))
            lower_coarse = 0.5 * phi_gmin

            print(f"  {gmin:>10.4f}  {ratio:>12.6f}  {lower_exact:>12.6f}  {lower_coarse:>12.6f}")

            # proof3 Theorem P bounds
            assert ratio >= lower_exact * (1.0 - 5e-7)
            assert ratio >= lower_coarse * (1.0 - 5e-7)

            # overhead should grow as gmin decreases for these chosen families.
            if prev is not None:
                assert ratio > prev
            prev = ratio

        print()

    print("  Class-level bound verified for representative penalty families.")
    print()


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main() -> None:
    print()
    print("Numerical Verification: Experiment 11 Open Threads (proof2/main2/main3)")
    print()

    verify_claim1()
    verify_claim2()
    verify_claim3()
    verify_claim4()

    print("=" * 72)
    print("All open-thread claims verified.")
    print("=" * 72)


if __name__ == "__main__":
    main()
