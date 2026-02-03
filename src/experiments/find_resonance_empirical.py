"""
Empirically find the resonance structure in H(r) = -|psi_0><psi_0| + r*H_z.

This explores the actual behavior to calibrate our theoretical predictions.
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
            idx = np.random.randint(0, M)
            degeneracies[idx] += 1
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
        'Delta': energies[1] - energies[0]
    }


def spectral_analysis(inst, r):
    """Get eigenvalues and eigenvectors at parameter r."""
    N = inst['N']
    psi_0 = np.sqrt(inst['degeneracies'] / N)
    H_r = r * np.diag(inst['energies']) - np.outer(psi_0, psi_0)
    eigenvalues, eigenvectors = np.linalg.eigh(H_r)
    return eigenvalues, eigenvectors, psi_0


def find_avoided_crossing(inst, r_min=0.1, r_max=10.0, num_points=1000):
    """Find the position and width of the avoided crossing."""
    r_values = np.linspace(r_min, r_max, num_points)
    gaps = []
    for r in r_values:
        eigenvalues, _, _ = spectral_analysis(inst, r)
        gap = eigenvalues[1] - eigenvalues[0]
        gaps.append(gap)
    gaps = np.array(gaps)

    # Find minimum
    min_idx = np.argmin(gaps)
    r_min_gap = r_values[min_idx]
    g_min_actual = gaps[min_idx]

    return r_min_gap, g_min_actual, r_values, gaps


def analyze_eigenvector_overlaps(inst, r_values):
    """Analyze how eigenvectors overlap with |psi_0> and |ground>."""
    overlaps_psi0_phi0 = []
    overlaps_psi0_phi1 = []
    overlaps_ground_phi0 = []
    overlaps_ground_phi1 = []

    N = inst['N']
    d_0 = inst['d_0']
    psi_0 = np.sqrt(inst['degeneracies'] / N)
    ground = np.zeros(inst['M'])
    ground[0] = 1.0  # |ground> = |0> in symmetric subspace

    for r in r_values:
        eigenvalues, eigenvectors, _ = spectral_analysis(inst, r)
        phi_0 = eigenvectors[:, 0]  # Lowest eigenstate
        phi_1 = eigenvectors[:, 1]  # Second lowest

        overlaps_psi0_phi0.append(np.abs(np.vdot(psi_0, phi_0))**2)
        overlaps_psi0_phi1.append(np.abs(np.vdot(psi_0, phi_1))**2)
        overlaps_ground_phi0.append(np.abs(np.vdot(ground, phi_0))**2)
        overlaps_ground_phi1.append(np.abs(np.vdot(ground, phi_1))**2)

    return (np.array(overlaps_psi0_phi0), np.array(overlaps_psi0_phi1),
            np.array(overlaps_ground_phi0), np.array(overlaps_ground_phi1))


def main():
    print("=== Empirical Resonance Analysis ===\n")

    for n in [8, 10, 12]:
        print(f"\n{'='*50}")
        print(f"n = {n} qubits")
        print('='*50)

        inst = generate_instance(n, M=10, seed=42)

        print(f"\nSpectral parameters:")
        print(f"  N = {inst['N']}")
        print(f"  d_0 = {inst['d_0']}")
        print(f"  A_1 = {inst['A_1']:.4f}")
        print(f"  A_2 = {inst['A_2']:.4f}")
        print(f"  Delta = {inst['Delta']:.4f}")

        # Predicted from adiabatic theory (with various scalings)
        s_star_adiabatic = inst['A_1'] / (inst['A_1'] + 1)
        r_star_formula1 = inst['A_1']  # r = s/(1-s) at s*
        r_star_formula2 = inst['A_1'] + 1  # Alternative
        g_min_adiabatic = (2 * inst['A_1'] / (inst['A_1'] + 1) *
                          np.sqrt(inst['d_0'] / (inst['A_2'] * inst['N'])))

        print(f"\nPredictions from adiabatic theory:")
        print(f"  s* = {s_star_adiabatic:.4f}")
        print(f"  r* (formula 1: A_1) = {r_star_formula1:.4f}")
        print(f"  r* (formula 2: A_1+1) = {r_star_formula2:.4f}")
        print(f"  g_min (adiabatic) = {g_min_adiabatic:.6f}")

        # Find actual resonance
        r_crossing, g_min_actual, r_vals, gaps = find_avoided_crossing(inst)

        print(f"\nActual (empirical):")
        print(f"  r at min gap = {r_crossing:.4f}")
        print(f"  g_min actual = {g_min_actual:.6f}")
        print(f"  Ratio (actual/predicted) = {g_min_actual/g_min_adiabatic:.2f}")

        # Analyze eigenvector structure at crossing
        overlaps = analyze_eigenvector_overlaps(inst, [r_crossing])
        print(f"\nAt r = {r_crossing:.4f}:")
        print(f"  |<psi_0|phi_0>|^2 = {overlaps[0][0]:.4f}")
        print(f"  |<psi_0|phi_1>|^2 = {overlaps[1][0]:.4f}")
        print(f"  |<ground|phi_0>|^2 = {overlaps[2][0]:.4f}")
        print(f"  |<ground|phi_1>|^2 = {overlaps[3][0]:.4f}")

        # Check if |psi_0> is 50-50 split at crossing (signature of resonance)
        split_ratio = overlaps[0][0] / (overlaps[0][0] + overlaps[1][0])
        print(f"  Split ratio: {split_ratio:.4f} (should be ~0.5 at resonance)")

    print("\n" + "="*50)
    print("ANALYSIS COMPLETE")
    print("="*50)


if __name__ == "__main__":
    main()
