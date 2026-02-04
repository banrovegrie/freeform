"""
Analyze A_1 for planted MAX-CUT and compare to spherically symmetric approximation.

Planted MAX-CUT: G(n, p, q) model
- n vertices split into two groups A, B of size n/2
- Edge probability p within groups, q between groups
- Ground state is the planted partition (for q > p)

Key question: Is A_1 approximately determined by the cost structure?
"""

import numpy as np
from math import comb
from itertools import combinations

def planted_maxcut_graph(n, p, q, seed=None):
    """
    Generate a planted MAX-CUT instance.

    Returns: adjacency matrix, planted partition (as set of vertices in group A)
    """
    if seed is not None:
        np.random.seed(seed)

    # Planted partition: first n/2 vertices in group A
    group_A = set(range(n // 2))
    group_B = set(range(n // 2, n))

    # Generate edges
    adj = np.zeros((n, n))
    for i in range(n):
        for j in range(i + 1, n):
            # Determine edge probability
            same_group = (i in group_A and j in group_A) or (i in group_B and j in group_B)
            edge_prob = p if same_group else q

            if np.random.random() < edge_prob:
                adj[i, j] = adj[j, i] = 1

    return adj, group_A

def maxcut_value(adj, partition):
    """Compute cut value for a given partition."""
    n = adj.shape[0]
    cut = 0
    for i in range(n):
        for j in range(i + 1, n):
            if adj[i, j] == 1:
                i_side = i in partition
                j_side = j in partition
                if i_side != j_side:
                    cut += 1
    return cut

def hamming_distance(x, y, n):
    """Compute Hamming distance between two states represented as integers."""
    return bin(x ^ y).count('1')

def partition_to_int(partition, n):
    """Convert partition (set of vertices) to integer representation."""
    x = 0
    for v in partition:
        x |= (1 << v)
    return x

def int_to_partition(x, n):
    """Convert integer to partition (set of vertices)."""
    return {v for v in range(n) if (x >> v) & 1}

def compute_maxcut_A1_exact(adj, planted_partition):
    """
    Compute A_1 exactly by enumerating all 2^n partitions.
    """
    n = adj.shape[0]
    N = 2**n
    planted_int = partition_to_int(planted_partition, n)

    # Compute cut value for all partitions
    cut_values = np.zeros(N)
    for x in range(N):
        partition = int_to_partition(x, n)
        cut_values[x] = maxcut_value(adj, partition)

    # Ground state is maximum cut (we negate for minimization)
    E0 = -np.max(cut_values)
    energies = -cut_values  # Negate so ground state has lowest energy

    # Check that planted partition is ground state
    planted_energy = energies[planted_int]
    if planted_energy != E0:
        # Find actual ground state
        ground_states = np.where(energies == E0)[0]
        print(f"  Warning: planted partition not optimal. E0={E0}, planted={planted_energy}")
        print(f"  Number of ground states: {len(ground_states)}")

    # Compute A_1
    A1 = 0.0
    for x in range(N):
        if abs(energies[x] - E0) > 1e-10:
            A1 += 1.0 / (energies[x] - E0)

    return A1 / N, E0, energies

def compute_spherical_A1(n, mean_cost_fn):
    """
    Compute A_1 assuming spherically symmetric cost.

    mean_cost_fn(d) = expected cost at Hamming distance d from optimum
    """
    N = 2**n
    f0 = mean_cost_fn(0)  # Should be 0 for optimal partition

    A1 = 0.0
    for d in range(1, n+1):
        fd = mean_cost_fn(d)
        deg_d = comb(n, d)
        if abs(fd - f0) > 1e-10:
            A1 += deg_d / (fd - f0)

    return A1 / N

def expected_cost_planted_maxcut(n, p, q, d):
    """
    Compute expected cost (energy) at Hamming distance d from planted partition.

    When we flip d vertices from their planted group:
    - Expected edges lost from cut ≈ d * q * n/2
    - Expected edges gained in cut ≈ d * p * n/2
    - Net change ≈ d * (p - q) * n/2

    For q > p (good planted partition), flipping increases cost (decreases cut).
    """
    if d == 0:
        return 0.0

    # Approximate: linear in d
    # The maximum cut has value ≈ q * (n/2)^2 + p * 2 * C(n/2, 2)
    # For q > p, cost at distance d is approximately d * (q - p) * n / 2

    return d * (q - p) * n / 2

def test_planted_maxcut():
    """
    Test whether A_1 for planted MAX-CUT is well-approximated by spherical formula.
    """
    print("Testing A_1 for Planted MAX-CUT")
    print("=" * 70)

    # Parameters
    p = 0.3  # Within-group edge probability
    q = 0.7  # Between-group edge probability

    for n in [8, 10, 12]:
        print(f"\nn = {n}, p = {p}, q = {q}")
        print("-" * 50)

        # Generate multiple random instances
        A1_exact_values = []

        for trial in range(5):
            adj, planted = planted_maxcut_graph(n, p, q, seed=trial * 1000)
            A1_exact, E0, energies = compute_maxcut_A1_exact(adj, planted)
            A1_exact_values.append(A1_exact)
            print(f"  Trial {trial+1}: A1_exact = {A1_exact:.6f}")

        # Compute spherical approximation
        mean_cost_fn = lambda d: expected_cost_planted_maxcut(n, p, q, d)
        A1_spherical = compute_spherical_A1(n, mean_cost_fn)

        print(f"\n  Spherical approximation: A1_spherical = {A1_spherical:.6f}")
        print(f"  Mean exact A1: {np.mean(A1_exact_values):.6f} +/- {np.std(A1_exact_values):.6f}")

        rel_error = abs(np.mean(A1_exact_values) - A1_spherical) / abs(np.mean(A1_exact_values))
        print(f"  Relative error: {rel_error:.2%}")

def analyze_cost_structure():
    """
    Analyze the actual cost structure of planted MAX-CUT.
    """
    print("\n" + "=" * 70)
    print("Analyzing Cost Structure of Planted MAX-CUT")
    print("=" * 70)

    n = 10
    p = 0.3
    q = 0.7

    adj, planted = planted_maxcut_graph(n, p, q, seed=42)
    planted_int = partition_to_int(planted, n)

    # Compute energy at each Hamming distance
    N = 2**n

    # Group by Hamming distance
    energies_by_distance = {d: [] for d in range(n+1)}

    for x in range(N):
        partition = int_to_partition(x, n)
        cut = maxcut_value(adj, partition)
        d = hamming_distance(x, planted_int, n)
        energies_by_distance[d].append(-cut)

    print(f"\nn = {n}, p = {p}, q = {q}")
    print("\nHamming distance | Count | Mean energy | Std energy | Expected (spherical)")
    print("-" * 80)

    E0 = np.mean(energies_by_distance[0])

    for d in range(n+1):
        energies = energies_by_distance[d]
        expected = expected_cost_planted_maxcut(n, p, q, d)

        print(f"       {d:2d}         | {len(energies):4d}  | {np.mean(energies) - E0:8.3f}   | {np.std(energies):7.3f}     | {expected:8.3f}")

def final_assessment():
    """
    Final assessment of the planted MAX-CUT A_1 approximation.
    """
    print("\n" + "=" * 70)
    print("Final Assessment: Planted MAX-CUT A_1 Approximation")
    print("=" * 70)

    n = 10
    p = 0.3
    q = 0.7

    # Generate 20 instances
    A1_values = []
    for seed in range(20):
        adj, planted = planted_maxcut_graph(n, p, q, seed=seed)
        A1, _, _ = compute_maxcut_A1_exact(adj, planted)
        A1_values.append(A1)

    # Spherical approximation
    A1_spherical = compute_spherical_A1(n, lambda d: expected_cost_planted_maxcut(n, p, q, d))

    print(f"\nn = {n}, p = {p}, q = {q}, 20 random instances")
    print(f"\nExact A_1 values:")
    print(f"  Mean:   {np.mean(A1_values):.6f}")
    print(f"  Std:    {np.std(A1_values):.6f}")
    print(f"  Min:    {np.min(A1_values):.6f}")
    print(f"  Max:    {np.max(A1_values):.6f}")

    print(f"\nSpherical approximation: {A1_spherical:.6f}")
    print(f"Relative error of approximation: {abs(np.mean(A1_values) - A1_spherical) / np.mean(A1_values):.2%}")

    # What precision does this give?
    # Required precision for AQO
    N = 2**n
    d0 = 1  # Assume unique optimal (approximate)
    A2_approx = compute_spherical_A1(n, lambda d: expected_cost_planted_maxcut(n, p, q, d)**2 if d > 0 else 1e10)
    delta_s = np.sqrt(d0 / N) / (np.mean(A1_values) + 1)**2

    print(f"\nRequired precision for AQO: delta_s ≈ {delta_s:.2e}")
    print(f"A_1 variance: {np.std(A1_values):.2e}")
    print(f"Ratio (variance / delta_s): {np.std(A1_values) / delta_s:.2f}")

    if np.std(A1_values) < delta_s:
        print("\n-> A_1 variance is SMALLER than required precision!")
        print("   Using ensemble A_1 is SUFFICIENT for optimal AQO.")
    else:
        print("\n-> A_1 variance is LARGER than required precision.")
        print("   Instance-specific A_1 may be needed.")

if __name__ == "__main__":
    test_planted_maxcut()
    analyze_cost_structure()
    final_assessment()
