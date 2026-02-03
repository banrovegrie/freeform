"""
Minimal validation of the quantum calibration theory using only numpy.
"""

import numpy as np


def generate_instance(n, M, seed=42):
    """Generate a random problem instance."""
    np.random.seed(seed)
    N = 2**n

    # Energy levels in [0, 1] with minimum gap
    energies = np.sort(np.random.uniform(0, 1, M))
    energies[0] = 0

    # Ensure minimum gap of 0.05 between levels
    min_gap = 0.05
    for k in range(1, M):
        if energies[k] - energies[k-1] < min_gap:
            energies[k] = energies[k-1] + min_gap

    # Normalize to [0, 1]
    if energies.max() > 0:
        energies = energies / energies.max()

    # Degeneracies - ensure they sum to N and are all positive
    probs = np.random.dirichlet(np.ones(M) * 2)  # Larger alpha for smoother distribution
    degeneracies = np.floor(probs * N).astype(int)
    degeneracies = np.maximum(degeneracies, 1)  # At least 1 per level

    # Distribute remaining to match N exactly
    remaining = N - degeneracies.sum()
    if remaining > 0:
        # Add to random levels
        for _ in range(remaining):
            idx = np.random.randint(0, M)
            degeneracies[idx] += 1
    elif remaining < 0:
        # Remove from largest levels
        for _ in range(-remaining):
            idx = np.argmax(degeneracies)
            if degeneracies[idx] > 1:
                degeneracies[idx] -= 1

    # Spectral parameters
    A_1 = sum(degeneracies[k] / (energies[k] - energies[0])
              for k in range(1, M)) / N
    A_2 = sum(degeneracies[k] / (energies[k] - energies[0])**2
              for k in range(1, M)) / N

    d_0 = degeneracies[0]

    # The resonance point: from the paper's discussion
    # H(r) = -|psi_0><psi_0| + r*H_z has avoided crossing at r = A_1
    # This corresponds to s* = A_1/(A_1+1) via r = s/(1-s)
    r_star = A_1

    # The minimum gap at this point
    # g_min scales as sqrt(d_0 / (A_2 * N))
    # The exact prefactor needs more careful derivation
    g_min = np.sqrt(d_0 / (A_2 * N))

    return {
        'n': n, 'N': N, 'M': M,
        'energies': energies,
        'degeneracies': degeneracies,
        'A_1': A_1, 'A_2': A_2, 'd_0': d_0,
        'r_star': r_star, 'g_min': g_min
    }


def matrix_exp(A, t):
    """Compute e^{At} using eigendecomposition."""
    eigenvalues, eigenvectors = np.linalg.eigh(A)
    return eigenvectors @ np.diag(np.exp(eigenvalues * t)) @ eigenvectors.T


def loschmidt_echo(inst, r, t):
    """Compute the Loschmidt echo."""
    M = inst['M']
    N = inst['N']

    # |psi_0> in symmetric subspace
    psi_0 = np.sqrt(inst['degeneracies'] / N)

    # H(r) = r * diag(E_k) - |psi_0><psi_0|
    H_r = r * np.diag(inst['energies']) - np.outer(psi_0, psi_0)

    # Time evolution: e^{-iHt}
    # Use eigendecomposition
    eigenvalues, eigenvectors = np.linalg.eigh(H_r)
    phases = np.exp(-1j * eigenvalues * t)
    U = eigenvectors @ np.diag(phases) @ eigenvectors.T.conj()

    # Evolved state and overlap
    psi_t = U @ psi_0
    overlap = np.vdot(psi_0, psi_t)

    return np.abs(overlap)**2


def spectral_gap(inst, r):
    """Compute spectral gap at parameter r."""
    N = inst['N']
    psi_0 = np.sqrt(inst['degeneracies'] / N)
    H_r = r * np.diag(inst['energies']) - np.outer(psi_0, psi_0)
    eigenvalues = np.sort(np.linalg.eigvalsh(H_r))
    return eigenvalues[1] - eigenvalues[0]


def run_experiment(n=10, M=10, seed=42):
    """Run the validation experiment."""
    print(f"=== Quantum Calibration Validation ===")
    print(f"n = {n} qubits, M = {M} energy levels\n")

    inst = generate_instance(n, M, seed)

    print(f"Parameters:")
    print(f"  N = {inst['N']}")
    print(f"  d_0 = {inst['d_0']}")
    print(f"  A_1 = {inst['A_1']:.4f}")
    print(f"  r* = {inst['r_star']:.4f}")
    print(f"  g_min = {inst['g_min']:.6f}")
    print()

    # Test: Loschmidt echo at various r
    T_star = np.pi / inst['g_min']
    r_values = np.linspace(0.5, 2 * inst['r_star'], 100)

    print("Scanning Loschmidt echo...")
    L_values = [loschmidt_echo(inst, r, T_star) for r in r_values]

    # Find minimum
    min_idx = np.argmin(L_values)
    r_min = r_values[min_idx]
    L_min = L_values[min_idx]

    print(f"  Minimum L = {L_min:.6f} at r = {r_min:.4f}")
    print(f"  True r* = {inst['r_star']:.4f}")
    print(f"  Error = {abs(r_min - inst['r_star']):.6f}")
    print()

    # Test: Spectral gap
    print("Verifying spectral gap...")
    gap_values = [spectral_gap(inst, r) for r in r_values]
    gap_min_idx = np.argmin(gap_values)
    gap_min = gap_values[gap_min_idx]

    print(f"  Min gap = {gap_min:.6f} at r = {r_values[gap_min_idx]:.4f}")
    print(f"  Predicted g_min = {inst['g_min']:.6f}")
    print(f"  Ratio = {gap_min / inst['g_min']:.3f}")
    print()

    # Key validation: at resonance, echo should be near 0
    L_at_resonance = loschmidt_echo(inst, inst['r_star'], T_star)
    print(f"Resonance test:")
    print(f"  L(r*, T*) = {L_at_resonance:.6f}")
    print(f"  Expected: close to 0")

    # Away from resonance, echo should be > 0.5
    r_away = inst['r_star'] + 5 * inst['g_min']
    L_away = loschmidt_echo(inst, r_away, T_star)
    print(f"  L(r* + 5*g_min, T*) = {L_away:.6f}")
    print(f"  Expected: > 0.5")

    # Summary
    print("\n=== VALIDATION RESULT ===")
    if L_at_resonance < 0.1 and L_away > 0.5:
        print("SUCCESS: Loschmidt echo shows clear resonance signature")
        print("The quantum calibration protocol should work!")
    else:
        print("WARNING: Results do not match predictions")
        print("Check parameters or implementation")

    return inst, r_values, L_values, gap_values


if __name__ == "__main__":
    # Run for several system sizes
    for n in [6, 8, 10, 12]:
        print("\n" + "="*50)
        run_experiment(n=n, M=10, seed=42)
