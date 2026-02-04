"""
Verify A_1 computation for spherically symmetric cost functions.

For Hamiltonians where E_x = f(d_H(x, x*)), A_1 should be computable in O(n) time.
"""

import numpy as np
from math import comb

def spherical_A1_exact(n, cost_fn):
    """
    Compute A_1 exactly using closed-form for spherically symmetric cost.

    A_1 = (1/2^n) sum_{d=1}^{n} C(n,d) / (f(d) - f(0))

    where f(d) = cost_fn(d) is the cost at Hamming distance d.
    """
    N = 2**n
    f0 = cost_fn(0)  # Ground state energy (should be 0 for planted solution)

    A1 = 0.0
    for d in range(1, n+1):
        fd = cost_fn(d)
        deg_d = comb(n, d)
        if abs(fd - f0) > 1e-10:
            A1 += deg_d / (fd - f0)

    return A1 / N

def spherical_A1_numerical(n, cost_fn, planted_state=None):
    """
    Compute A_1 by explicit enumeration.
    """
    N = 2**n

    if planted_state is None:
        planted_state = 0  # Use |00...0> as planted state

    # Compute Hamming distance for each state
    energies = np.zeros(N)
    for x in range(N):
        d = bin(x ^ planted_state).count('1')  # Hamming distance to planted
        energies[x] = cost_fn(d)

    E0 = np.min(energies)  # Should be cost_fn(0) = 0

    # Compute A_1
    A1 = 0.0
    for x in range(N):
        if abs(energies[x] - E0) > 1e-10:
            A1 += 1.0 / (energies[x] - E0)

    return A1 / N

def linear_cost(d, c=1.0):
    """Linear cost: f(d) = c * d"""
    return c * d

def quadratic_cost(d, c=1.0):
    """Quadratic cost: f(d) = c * d^2"""
    return c * d * d

def planted_sat_cost(d, n, alpha=1.0):
    """
    Approximate cost function for planted SAT.
    Each flipped variable increases violated clauses by ~alpha.
    """
    return alpha * d

def verify_spherical_formula():
    """
    Verify the closed-form A_1 formula for spherically symmetric costs.
    """
    print("Verification: Spherically Symmetric A_1")
    print("=" * 60)

    cost_functions = [
        ("Linear (c=1)", lambda d: linear_cost(d, c=1.0)),
        ("Linear (c=0.5)", lambda d: linear_cost(d, c=0.5)),
        ("Quadratic (c=1)", lambda d: quadratic_cost(d, c=1.0)),
        ("Quadratic (c=0.1)", lambda d: quadratic_cost(d, c=0.1)),
    ]

    for cost_name, cost_fn in cost_functions:
        print(f"\nCost function: {cost_name}")
        print("-" * 40)

        for n in [6, 8, 10, 12]:
            A1_exact = spherical_A1_exact(n, cost_fn)
            A1_numerical = spherical_A1_numerical(n, cost_fn)
            rel_error = abs(A1_exact - A1_numerical) / (abs(A1_numerical) + 1e-10)

            print(f"  n={n:2d}: A1_exact={A1_exact:.6f}, A1_numerical={A1_numerical:.6f}, error={rel_error:.2e}")

    print("\n" + "=" * 60)
    print("All should match to machine precision.")

def analyze_planted_case():
    """
    Analyze A_1 for planted problems and required precision.
    """
    print("\n" + "=" * 60)
    print("Analysis: Planted Problem A_1 and Precision")
    print("=" * 60)

    cost_fn = lambda d: linear_cost(d, c=1.0)

    for n in [8, 10, 12, 14]:
        N = 2**n
        d0 = 1  # Unique planted solution

        # Compute A_1
        A1 = spherical_A1_exact(n, cost_fn)

        # Compute A_2
        A2 = 0.0
        for d in range(1, n+1):
            A2 += comb(n, d) / cost_fn(d)**2
        A2 = A2 / N

        # Required precision
        delta_s = np.sqrt(d0 * A2 / N) / (A1 + 1)**2

        # NP-hard threshold
        np_threshold = 1.0 / (72 * (n - 1))

        print(f"\nn = {n} (N = 2^{n} = {N})")
        print(f"  A_1 = {A1:.6f}")
        print(f"  A_2 = {A2:.6f}")
        print(f"  d_0 = {d0} (unique planted solution)")
        print(f"  Required precision delta_s = {delta_s:.2e}")
        print(f"  NP-hard threshold = {np_threshold:.2e}")
        print(f"  Ratio (delta_s / NP_threshold) = {delta_s / np_threshold:.2e}")

        if delta_s < np_threshold:
            print("  -> Precision BELOW NP-hard threshold (in the gap!)")
        else:
            print("  -> Precision ABOVE NP-hard threshold")

def demonstrate_concentration():
    """
    Show that A_1 is the same for different planted states.
    """
    print("\n" + "=" * 60)
    print("Demonstration: A_1 Independence from Planted State")
    print("=" * 60)

    n = 10
    N = 2**n
    cost_fn = lambda d: linear_cost(d, c=1.0)

    # Compute A_1 for different planted states
    A1_values = []
    for _ in range(10):
        planted_state = np.random.randint(0, N)
        A1 = spherical_A1_numerical(n, cost_fn, planted_state)
        A1_values.append(A1)

    print(f"\nn = {n}, random planted states:")
    for i, A1 in enumerate(A1_values):
        print(f"  Trial {i+1}: planted={np.random.randint(0, N)}, A_1 = {A1:.10f}")

    print(f"\n  Mean A_1 = {np.mean(A1_values):.10f}")
    print(f"  Std A_1 = {np.std(A1_values):.2e}")
    print("\n  (Should all be identical for spherically symmetric cost)")

def compute_S_n():
    """
    Compute S_n = sum_{d=1}^{n} C(n,d)/d for various n.
    """
    print("\n" + "=" * 60)
    print("Computing S_n = sum_{d=1}^{n} C(n,d)/d")
    print("=" * 60)

    for n in range(2, 21):
        S_n = sum(comb(n, d) / d for d in range(1, n+1))
        N = 2**n
        A1_linear = S_n / N  # For c=1 linear cost

        # Compare to 1/n * 2^{n-1} (if there were a nice formula)
        approx = 2**(n-1) / n

        print(f"  n={n:2d}: S_n = {S_n:12.4f}, A_1(c=1) = {A1_linear:.6f}, 2^(n-1)/n = {approx:12.4f}")

if __name__ == "__main__":
    verify_spherical_formula()
    analyze_planted_case()
    demonstrate_concentration()
    compute_S_n()
