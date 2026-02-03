"""
Verify A_1 tractability for complete graph Ising model.

The antiferromagnetic Ising model on K_n has spectrum depending only on magnetization.
We verify that our closed-form expression for A_1 matches numerical diagonalization.
"""

import numpy as np
from math import comb, factorial

def complete_graph_energy(n, m, J=1.0):
    """
    Energy of configuration with m up-spins on complete graph.
    E(m) = J/2 * [(2m-n)^2 - n]
    """
    return J/2 * ((2*m - n)**2 - n)

def complete_graph_A1_exact(n, J=1.0):
    """
    Compute A_1 exactly using closed-form expression.

    A_1 = (1/2^n) sum_{m != n/2} C(n,m) / (E(m) - E_0)

    For antiferromagnetic case, E_0 = E(n/2) = -Jn/2
    """
    N = 2**n
    E0 = complete_graph_energy(n, n//2, J)

    A1 = 0.0
    for m in range(n+1):
        if m == n//2:
            continue
        Em = complete_graph_energy(n, m, J)
        dm = comb(n, m)
        A1 += dm / (Em - E0)

    return A1 / N

def complete_graph_A1_numerical(n, J=1.0):
    """
    Compute A_1 by explicit diagonalization.
    """
    N = 2**n

    # Build the Hamiltonian (diagonal)
    H = np.zeros(N)
    for x in range(N):
        # Count up-spins (1s in binary representation)
        m = bin(x).count('1')
        H[x] = complete_graph_energy(n, m, J)

    # Find ground state energy
    E0 = np.min(H)

    # Compute A_1
    A1 = 0.0
    for x in range(N):
        if abs(H[x] - E0) > 1e-10:
            A1 += 1.0 / (H[x] - E0)

    return A1 / N

def verify_complete_graph():
    """
    Verify exact formula matches numerical computation.
    """
    print("Verification: Complete Graph Ising Model A_1")
    print("=" * 60)

    results = []

    for n in [4, 6, 8, 10, 12]:
        A1_exact = complete_graph_A1_exact(n)
        A1_numerical = complete_graph_A1_numerical(n)
        rel_error = abs(A1_exact - A1_numerical) / abs(A1_numerical)

        results.append({
            'n': n,
            'A1_exact': A1_exact,
            'A1_numerical': A1_numerical,
            'rel_error': rel_error
        })

        print(f"\nn = {n} qubits (N = 2^{n} = {2**n})")
        print(f"  A1 (closed-form):  {A1_exact:.10f}")
        print(f"  A1 (numerical):    {A1_numerical:.10f}")
        print(f"  Relative error:    {rel_error:.2e}")

    print("\n" + "=" * 60)
    print("Summary:")
    all_match = all(r['rel_error'] < 1e-10 for r in results)
    if all_match:
        print("VERIFIED: Closed-form expression matches numerical result exactly.")
    else:
        print("WARNING: Some results don't match!")

    return results

def analyze_precision_requirement(n, J=1.0):
    """
    Analyze what precision is needed for AQO on complete graph.
    """
    N = 2**n

    # Compute spectral parameters
    A1 = complete_graph_A1_exact(n, J)

    # Compute A2
    E0 = complete_graph_energy(n, n//2, J)
    A2 = 0.0
    for m in range(n+1):
        if m == n//2:
            continue
        Em = complete_graph_energy(n, m, J)
        dm = comb(n, m)
        A2 += dm / (Em - E0)**2
    A2 = A2 / N

    # Ground state degeneracy
    d0 = comb(n, n//2)

    # Required precision
    delta_s = np.sqrt(d0 * A2 / N) / (A1 + 1)**2

    # Compare to NP-hard threshold
    np_threshold = 1.0 / (72 * (n - 1))

    print(f"\nPrecision Analysis for n = {n}:")
    print(f"  A1 = {A1:.6f}")
    print(f"  A2 = {A2:.6f}")
    print(f"  d0 = {d0} (ground state degeneracy)")
    print(f"  Required precision delta_s = {delta_s:.2e}")
    print(f"  NP-hard threshold = {np_threshold:.2e}")
    print(f"  Ratio (delta_s / NP_threshold) = {delta_s / np_threshold:.2e}")

    if delta_s > np_threshold:
        print("  -> Required precision is ABOVE NP-hard threshold")
        print("     (might still be easy for this structured case)")
    else:
        print("  -> Required precision is BELOW NP-hard threshold")
        print("     (but we computed A1 exactly anyway!)")

    return A1, A2, d0, delta_s

def compute_time_complexity():
    """
    Demonstrate polynomial-time computation of A_1.
    """
    print("\n" + "=" * 60)
    print("Time Complexity Demonstration")
    print("=" * 60)

    import time

    for n in [10, 12, 14, 16, 18, 20]:
        N = 2**n

        # Time the closed-form computation
        start = time.time()
        A1 = complete_graph_A1_exact(n)
        elapsed = time.time() - start

        print(f"n = {n:2d}, N = 2^{n} = {N:10d}: A1 = {A1:.8f}, time = {elapsed:.6f}s")

    print("\nNote: Closed-form computation is O(n), not O(2^n)!")

if __name__ == "__main__":
    # Verify the closed-form expression
    verify_complete_graph()

    # Analyze precision requirements
    for n in [6, 8, 10]:
        analyze_precision_requirement(n)

    # Show polynomial-time complexity
    compute_time_complexity()
