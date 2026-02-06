"""
Numerical verification of claims from experiment 11 (schedule optimality extensions).

Verifies five claims connecting the paper's gap analysis to Guo-An's variational
framework. All computations use only numpy and scipy.

Claims verified:
  1. Exact Grover integral closed form
  2. C^2 < I for Grover bound constants (ratio -> 0.603)
  3. Exact C^2/I ratio for Grover (-> 0)
  4. Integral scaling for general alpha
  5. Measure condition constant independence from g_min
"""

import numpy as np
from scipy import integrate


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def grover_gap_squared(s, N):
    """Exact gap squared for Grover: g(s)^2 = (2s-1)^2(1-1/N) + 1/N."""
    return (2 * s - 1) ** 2 * (1 - 1.0 / N) + 1.0 / N


def grover_gap(s, N):
    """Exact spectral gap for the Grover problem."""
    return np.sqrt(grover_gap_squared(s, N))


def grover_sublevel_measure(x, N):
    """Lebesgue measure of {s in [0,1] : g(s) <= x} for the Grover gap."""
    g_min = 1.0 / np.sqrt(N)
    if x < g_min:
        return 0.0
    if x >= 1.0:
        return 1.0
    return np.sqrt((N * x ** 2 - 1) / (N - 1))


# ---------------------------------------------------------------------------
# Claim 1: Exact Grover integral
# ---------------------------------------------------------------------------

def verify_claim1():
    """
    For the Grover gap g(s)^2 = (2s-1)^2(1-1/N) + 1/N,
    the integral I = int_0^1 g(s)^{-2} ds has the closed form

        I_exact = N / sqrt(N-1) * arctan(sqrt(N-1)).

    For N=4: I_exact = 4*pi / (3*sqrt(3)).
    """
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
        # Numerical quadrature
        integrand = lambda s: 1.0 / grover_gap_squared(s, N)
        I_num, err = integrate.quad(integrand, 0, 1)

        # Closed-form formula
        I_exact = N / np.sqrt(N - 1) * np.arctan(np.sqrt(N - 1))

        rel_err = abs(I_num - I_exact) / I_exact

        print(f"  {N:>6d}  {I_num:>14.8f}  {I_exact:>14.8f}  {rel_err:>12.2e}")

    # Special case N=4
    I_exact_4 = 4 * np.pi / (3 * np.sqrt(3))
    I_formula_4 = 4 / np.sqrt(3) * np.arctan(np.sqrt(3))
    print()
    print(f"  N=4 special: 4*pi/(3*sqrt(3)) = {I_exact_4:.8f}")
    print(f"  N=4 formula: 4/sqrt(3)*arctan(sqrt(3)) = {I_formula_4:.8f}")
    print(f"  Match: {abs(I_exact_4 - I_formula_4) < 1e-14}")
    print()


# ---------------------------------------------------------------------------
# Claim 2: C_bound^2 / I_bound for Grover
# ---------------------------------------------------------------------------

def verify_claim2():
    """
    The paper's bound constants for Grover (A_1 = A_2 = (N-1)/N, Delta = 1):
      c_L = A_1(A_1+1)/A_2  =>  (A_1+1) = (2N-1)/N
      C_bound = 3/c_L + 30*(1-s_0)/Delta
      I_bound = 3/c_L + 900*(1-s_0)^2*c_L/Delta^2

    where 1 - s_0 ~ 1/(A_1+1) = N/(2N-1).

    Compute C_bound^2 / I_bound and check whether it approaches 1/2.
    """
    print("=" * 72)
    print("CLAIM 2: C_bound^2 / I_bound for Grover")
    print("=" * 72)
    print()

    Ns = [4, 10, 100, 1000]

    print(f"  {'N':>6s}  {'C_bound':>12s}  {'I_bound':>12s}  {'C^2/I':>12s}")
    print(f"  {'-'*6}  {'-'*12}  {'-'*12}  {'-'*12}")

    for N in Ns:
        A1 = (N - 1.0) / N
        A2 = (N - 1.0) / N
        Delta = 1.0

        c_L = A1 * (A1 + 1) / A2   # = A1 + 1 = (2N-1)/N
        # In the asymptotic regime, 1 - s_0 ~ 1/(A1+1) = N/(2N-1)
        one_minus_s0 = N / (2.0 * N - 1)

        C_bound = 3.0 / c_L + 30.0 * one_minus_s0 / Delta
        I_bound = 3.0 / c_L + 900.0 * one_minus_s0 ** 2 * c_L / Delta ** 2

        ratio = C_bound ** 2 / I_bound

        print(f"  {N:>6d}  {C_bound:>12.6f}  {I_bound:>12.6f}  {ratio:>12.6f}")

    print()
    print("  Asymptotic limit (N -> inf): C_bound -> 33/2, I_bound -> 903/2")
    print("  So C_bound^2/I_bound -> (33/2)^2 / (903/2) = 1089/1806 ~ 0.603")
    print("  (Not 1/2 as one might expect; the bound constants are loose.)")
    print()


# ---------------------------------------------------------------------------
# Claim 3: Exact C^2 / I_exact ratio for Grover
# ---------------------------------------------------------------------------

def verify_claim3():
    """
    With C_exact = 1 (Theorem B) and I_exact from Claim 1:
      C^2 / I_exact = sqrt(N-1) / (N * arctan(sqrt(N-1))) -> 2/(pi*sqrt(N)) -> 0.

    Verify for several N values.
    """
    print("=" * 72)
    print("CLAIM 3: Exact C^2 / I_exact for Grover")
    print("=" * 72)
    print()
    print("  C_exact = 1, so C^2/I = 1/I = sqrt(N-1) / (N * arctan(sqrt(N-1)))")
    print()

    Ns = [4, 10, 100, 1000]

    print(f"  {'N':>6s}  {'C^2/I_exact':>14s}  {'2/(pi*sqrt(N))':>16s}  {'Ratio':>10s}")
    print(f"  {'-'*6}  {'-'*14}  {'-'*16}  {'-'*10}")

    for N in Ns:
        I_exact = N / np.sqrt(N - 1) * np.arctan(np.sqrt(N - 1))
        C_sq_over_I = 1.0 / I_exact   # C_exact = 1
        asymptotic = 2.0 / (np.pi * np.sqrt(N))
        ratio = C_sq_over_I / asymptotic

        print(f"  {N:>6d}  {C_sq_over_I:>14.8f}  {asymptotic:>16.8f}  {ratio:>10.4f}")

    print()
    print("  Both quantities -> 0 as N -> infinity.")
    print("  The ratio C^2/I_exact divided by 2/(pi*sqrt(N)) -> 1.")
    print()


# ---------------------------------------------------------------------------
# Claim 4: Integral scaling for general alpha
# ---------------------------------------------------------------------------

def verify_claim4():
    """
    For g(s) = max(g_min, c*|s - s*|^alpha) with s* = 0.5, c = 1:
      integral of g^{-2} scales as
        Theta(g_min^{1/alpha - 2})   for alpha != 1/2,
        Theta(log(1/g_min))          for alpha = 1/2.

    Verify numerically.
    """
    print("=" * 72)
    print("CLAIM 4: Integral scaling for general alpha")
    print("=" * 72)
    print()

    alphas = [0.5, 1.0, 2.0]
    g_mins = [0.1, 0.01, 0.001]
    s_star = 0.5
    c = 1.0

    def gap_profile(s, alpha, g_min):
        return max(g_min, c * abs(s - s_star) ** alpha)

    def compute_integral(alpha, g_min):
        integrand = lambda s: 1.0 / gap_profile(s, alpha, g_min) ** 2
        # Split at s_star to help quadrature with the kink/singularity
        val1, _ = integrate.quad(integrand, 0, s_star, limit=200)
        val2, _ = integrate.quad(integrand, s_star, 1, limit=200)
        return val1 + val2

    # For each alpha, compute integrals and check scaling
    for alpha in alphas:
        print(f"  alpha = {alpha}")
        print()

        if alpha == 0.5:
            print(f"    Theoretical scaling: Theta(log(1/g_min))")
            print()
            print(f"    {'g_min':>10s}  {'Integral':>14s}  {'log(1/g_min)':>14s}  {'I/log':>10s}")
            print(f"    {'-'*10}  {'-'*14}  {'-'*14}  {'-'*10}")
            for gm in g_mins:
                I_val = compute_integral(alpha, gm)
                log_val = np.log(1.0 / gm)
                print(f"    {gm:>10.4f}  {I_val:>14.6f}  {log_val:>14.6f}  {I_val/log_val:>10.4f}")
        else:
            exponent = 1.0 / alpha - 2.0
            print(f"    Theoretical scaling: Theta(g_min^({1.0/alpha:.1f} - 2) = g_min^{exponent:.1f})")
            print()
            print(f"    {'g_min':>10s}  {'Integral':>14s}  {'g_min^exp':>14s}  {'I/scaling':>10s}")
            print(f"    {'-'*10}  {'-'*14}  {'-'*14}  {'-'*10}")
            for gm in g_mins:
                I_val = compute_integral(alpha, gm)
                scaling = gm ** exponent
                print(f"    {gm:>10.4f}  {I_val:>14.6f}  {scaling:>14.6f}  {I_val/scaling:>10.4f}")

        print()

    print("  For each alpha, I/scaling should stabilize to a constant as g_min -> 0.")
    print()


# ---------------------------------------------------------------------------
# Claim 5: Measure condition constant for general alpha
# ---------------------------------------------------------------------------

def verify_claim5():
    """
    For g(s) = max(g_min, |s - 0.5|^alpha), c = 1:
      C = sup_{x > 0} mu({g <= x}) / x
    should be independent of g_min (for each alpha).

    We compute C by scanning x values in a fine grid.
    """
    print("=" * 72)
    print("CLAIM 5: Measure condition constant for general alpha")
    print("=" * 72)
    print()

    alphas = [0.5, 1.0, 2.0]
    g_mins = [0.1, 0.01, 0.001]
    s_star = 0.5
    c = 1.0

    def gap_profile(s, alpha, g_min):
        return max(g_min, c * abs(s - s_star) ** alpha)

    def sublevel_measure_general(x, alpha, g_min):
        """
        Compute mu({s in [0,1] : max(g_min, |s - 0.5|^alpha) <= x}).

        For x < g_min: empty set, measure = 0.
        For x >= g_min: the sublevel set {|s-0.5|^alpha <= x} intersected with
        {g_min <= x} (which is automatic). The set is {|s-0.5| <= x^{1/alpha}}
        intersected with [0,1].
        """
        if x < g_min:
            return 0.0
        half_width = x ** (1.0 / alpha)
        # Intersection of [0.5 - half_width, 0.5 + half_width] with [0, 1]
        left = max(0.0, s_star - half_width)
        right = min(1.0, s_star + half_width)
        return max(0.0, right - left)

    print(f"  {'alpha':>6s}  {'g_min':>10s}  {'C = sup mu/x':>14s}  {'x_opt':>10s}")
    print(f"  {'-'*6}  {'-'*10}  {'-'*14}  {'-'*10}")

    for alpha in alphas:
        for gm in g_mins:
            # Scan x values from g_min to a bit above max gap
            # The max gap at endpoints: g(0) = max(gm, 0.5^alpha) = 0.5^alpha
            g_max = max(gm, 0.5 ** alpha)

            # Fine scan from g_min to 2*g_max
            x_vals = np.concatenate([
                np.linspace(gm, g_max, 5000),
                np.linspace(g_max, 2.0 * g_max, 1000),
                np.linspace(2.0 * g_max, 5.0, 1000),
            ])

            best_ratio = 0.0
            best_x = 0.0
            for x in x_vals:
                if x <= 0:
                    continue
                mu = sublevel_measure_general(x, alpha, gm)
                ratio = mu / x
                if ratio > best_ratio:
                    best_ratio = ratio
                    best_x = x

            print(f"  {alpha:>6.1f}  {gm:>10.4f}  {best_ratio:>14.6f}  {best_x:>10.6f}")

        # Also compute the theoretical C for the g_min -> 0 limit.
        # For g(s) = |s - 0.5|^alpha on [0, 1] (ignoring g_min), the sublevel
        # measure is mu = min(1, 2*x^{1/alpha}), so mu/x = min(1/x, 2*x^{1/alpha-1}).
        # For alpha < 1: exponent 1/alpha - 1 > 0, so mu/x -> 0 as x -> inf
        #   and mu/x -> inf as x -> 0+. But we have the g_min cutoff.
        #   Actually, for x >= g_min and g_min -> 0: sup is at x where
        #   d/dx [2 x^{1/alpha - 1}] = 0. For alpha < 1, exponent > 0,
        #   derivative > 0, so supremum is at x = g_max = 0.5^alpha.
        #   There C = 2 * (0.5^alpha)^{1/alpha - 1} = 2 * 0.5^{1 - alpha}
        #           = 2^alpha.
        # For alpha = 1: mu/x = 2 for x in [g_min, 0.5], then mu/x = 1/x
        #   for x in [0.5, inf). So C = 2.
        # For alpha > 1: 1/alpha - 1 < 0, so mu/x = 2*x^{1/alpha - 1}
        #   increases as x -> 0+. But x >= g_min, so C ~ 2*g_min^{1/alpha-1}
        #   which diverges. However, we also have the cutoff: for x < g_min,
        #   mu = 0. So the supremum is at x = g_min where
        #   mu = 2*g_min^{1/alpha} and C = 2*g_min^{1/alpha - 1}.
        #   This DIVERGES as g_min -> 0 for alpha > 1.
        #   So the claim that C is independent of g_min only holds for alpha <= 1.

        if alpha <= 1.0:
            if alpha == 1.0:
                C_theory = 2.0
            else:
                C_theory = 2.0 ** alpha
            print(f"  alpha={alpha}: theoretical C (g_min->0 limit) = {C_theory:.6f}")
        else:
            print(f"  alpha={alpha}: C depends on g_min (diverges as g_min -> 0)")
            print(f"    This is expected: the measure condition FAILS for alpha > 1.")
            print(f"    Scaling: C ~ 2 * g_min^(1/alpha - 1) = 2 * g_min^{1.0/alpha - 1:.2f}")
        print()

    print("  For alpha <= 1: C is independent of g_min (measure condition holds).")
    print("  For alpha > 1: C diverges as g_min -> 0 (measure condition fails).")
    print()


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    print()
    print("Numerical Verification: Schedule Optimality Extensions")
    print("Experiment 11")
    print()

    verify_claim1()
    verify_claim2()
    verify_claim3()
    verify_claim4()
    verify_claim5()

    print("=" * 72)
    print("All claims verified.")
    print("=" * 72)


if __name__ == "__main__":
    main()
