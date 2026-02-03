"""
Refined analysis: find where the 50-50 split occurs and verify gap scaling.
"""

import numpy as np


def generate_instance(n, M, seed=42):
    """Generate a random problem instance."""
    np.random.seed(seed)
    N = 2**n

    energies = np.sort(np.random.uniform(0, 1, M))
    energies[0] = 0
    min_gap = 0.05
    for k in range(1, M):
        if energies[k] - energies[k-1] < min_gap:
            energies[k] = energies[k-1] + min_gap
    if energies.max() > 0:
        energies = energies / energies.max()

    probs = np.random.dirichlet(np.ones(M) * 2)
    degeneracies = np.floor(probs * N).astype(int)
    degeneracies = np.maximum(degeneracies, 1)
    remaining = N - degeneracies.sum()
    if remaining > 0:
        for _ in range(remaining):
            degeneracies[np.random.randint(0, M)] += 1
    elif remaining < 0:
        for _ in range(-remaining):
            idx = np.argmax(degeneracies)
            if degeneracies[idx] > 1:
                degeneracies[idx] -= 1

    A_1 = sum(degeneracies[k] / (energies[k] - energies[0])
              for k in range(1, M)) / N
    A_2 = sum(degeneracies[k] / (energies[k] - energies[0])**2
              for k in range(1, M)) / N

    return {
        'n': n, 'N': N, 'M': M,
        'energies': energies,
        'degeneracies': degeneracies,
        'A_1': A_1, 'A_2': A_2,
        'd_0': degeneracies[0],
    }


def spectral_analysis(inst, r):
    """Get eigenvalues, eigenvectors, and overlaps at parameter r."""
    N = inst['N']
    psi_0 = np.sqrt(inst['degeneracies'] / N)
    H_r = r * np.diag(inst['energies']) - np.outer(psi_0, psi_0)
    eigenvalues, eigenvectors = np.linalg.eigh(H_r)

    phi_0, phi_1 = eigenvectors[:, 0], eigenvectors[:, 1]
    gap = eigenvalues[1] - eigenvalues[0]
    overlap_phi0 = np.abs(np.vdot(psi_0, phi_0))**2
    overlap_phi1 = np.abs(np.vdot(psi_0, phi_1))**2

    return gap, overlap_phi0, overlap_phi1


def scan_resonance(inst, r_min=0.1, r_max=5.0, num_points=2000):
    """Scan to find gap minimum and 50-50 split point."""
    r_values = np.linspace(r_min, r_max, num_points)

    gaps = []
    splits = []  # overlap_phi0 / (overlap_phi0 + overlap_phi1)

    for r in r_values:
        gap, ov0, ov1 = spectral_analysis(inst, r)
        gaps.append(gap)
        splits.append(ov0 / (ov0 + ov1) if (ov0 + ov1) > 0 else 0.5)

    gaps = np.array(gaps)
    splits = np.array(splits)

    # Find minimum gap
    idx_min_gap = np.argmin(gaps)
    r_min_gap = r_values[idx_min_gap]
    g_min = gaps[idx_min_gap]

    # Find 50-50 split point (where split crosses 0.5)
    # Split starts near 1 (phi_0 dominated by psi_0) and decreases
    # Find where it crosses 0.5
    idx_fifty = np.argmin(np.abs(splits - 0.5))
    r_fifty = r_values[idx_fifty]
    split_at_fifty = splits[idx_fifty]
    gap_at_fifty = gaps[idx_fifty]

    return {
        'r_values': r_values,
        'gaps': gaps,
        'splits': splits,
        'r_min_gap': r_min_gap,
        'g_min': g_min,
        'r_fifty': r_fifty,
        'split_at_fifty': split_at_fifty,
        'gap_at_fifty': gap_at_fifty
    }


def main():
    print("=== Refined Resonance Analysis ===\n")
    print("Looking for two phenomena:")
    print("  1. Minimum gap position (r_min_gap)")
    print("  2. 50-50 split position (r_fifty) - where Loschmidt echo should dip\n")

    for n in [8, 10, 12]:
        print(f"\n{'='*60}")
        print(f"n = {n} qubits")

        inst = generate_instance(n, M=10, seed=42)
        N, d_0, A_1, A_2 = inst['N'], inst['d_0'], inst['A_1'], inst['A_2']

        print(f"N={N}, d_0={d_0}, A_1={A_1:.4f}, A_2={A_2:.4f}")

        results = scan_resonance(inst)

        # Predicted values
        # Gap formula for H(r) should include factor (A_1+1) compared to adiabatic
        g_min_predicted = 2 * A_1 * np.sqrt(d_0 / (A_2 * N))

        print(f"\nResults:")
        print(f"  Minimum gap:")
        print(f"    r_min_gap = {results['r_min_gap']:.4f}")
        print(f"    g_min = {results['g_min']:.6f}")
        print(f"    Predicted g_min = {g_min_predicted:.6f}")
        print(f"    Ratio = {results['g_min']/g_min_predicted:.2f}")

        print(f"  50-50 split:")
        print(f"    r_fifty = {results['r_fifty']:.4f}")
        print(f"    gap_at_fifty = {results['gap_at_fifty']:.6f}")
        print(f"    split = {results['split_at_fifty']:.4f}")

        print(f"  Comparison:")
        print(f"    A_1 = {A_1:.4f}")
        print(f"    r_min_gap / A_1 = {results['r_min_gap']/A_1:.4f}")
        print(f"    r_fifty / A_1 = {results['r_fifty']/A_1:.4f}")

        # The key insight: where does Loschmidt echo dip to minimum?
        # It should be near r_fifty, not r_min_gap
        print(f"\n  => For calibration, use r_fifty ≈ {results['r_fifty']:.3f}")
        print(f"     which gives A_1_est ≈ r_fifty = {results['r_fifty']:.3f}")
        print(f"     Error: {abs(results['r_fifty'] - A_1)/A_1 * 100:.1f}%")


if __name__ == "__main__":
    main()
