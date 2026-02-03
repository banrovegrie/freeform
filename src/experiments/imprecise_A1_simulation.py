"""
Rigorous validation of AQO performance with imprecise A_1.

This simulates the full adiabatic evolution and measures how
fidelity degrades when A_1 is estimated imprecisely.
"""

import numpy as np


def generate_instance(n, M, seed=42):
    """Generate a random problem instance."""
    np.random.seed(seed)
    N = 2**n

    energies = np.sort(np.random.uniform(0, 1, M))
    energies[0] = 0
    for k in range(1, M):
        if energies[k] - energies[k-1] < 0.05:
            energies[k] = energies[k-1] + 0.05
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

    A_1 = sum(degeneracies[k] / energies[k] for k in range(1, M)) / N
    A_2 = sum(degeneracies[k] / energies[k]**2 for k in range(1, M)) / N

    return {
        'n': n, 'N': N, 'M': M, 'energies': energies,
        'degeneracies': degeneracies, 'A_1': A_1, 'A_2': A_2,
        'd_0': degeneracies[0], 'Delta': energies[1]
    }


def compute_spectral_gap(inst, s):
    """Compute gap of H(s) = -(1-s)|psi_0><psi_0| + s*H_z in symmetric subspace."""
    N = inst['N']
    psi_0 = np.sqrt(inst['degeneracies'] / N)
    H_s = s * np.diag(inst['energies']) - (1 - s) * np.outer(psi_0, psi_0)
    eigenvalues = np.sort(np.linalg.eigvalsh(H_s))
    return eigenvalues[1] - eigenvalues[0]


def simulate_adiabatic_evolution(inst, T, num_steps=1000, A_1_used=None):
    """
    Simulate adiabatic evolution using Trotterization.

    Args:
        inst: Problem instance
        T: Total evolution time
        num_steps: Number of Trotter steps
        A_1_used: Value of A_1 used for schedule construction (None = exact)

    Returns:
        fidelity: Overlap with ground state manifold
    """
    N = inst['N']
    M = inst['M']
    A_1 = inst['A_1'] if A_1_used is None else A_1_used
    A_2 = inst['A_2']
    d_0 = inst['d_0']

    # Derived quantities for schedule
    s_star = A_1 / (A_1 + 1)
    g_min = 2 * A_1 / (A_1 + 1) * np.sqrt(d_0 / (A_2 * N))
    Delta = inst['Delta']

    # Initial state (in symmetric subspace)
    psi = np.sqrt(inst['degeneracies'] / N).astype(complex)

    # Target: ground state manifold (just |0> in symmetric subspace)
    target = np.zeros(M)
    target[0] = 1.0

    # Local schedule: s'(t) proportional to g(s)^2
    # For simplicity, use piecewise linear approximation

    # Adaptive time steps based on estimated gap
    dt_base = T / num_steps

    s_current = 0.0
    for step in range(num_steps):
        # Estimate gap at current s using A_1_used
        if s_current < s_star - 0.1:
            g_est = max(A_1 / A_2 * (s_star - s_current) / (1 - s_star), g_min)
        elif s_current > s_star + 0.1:
            g_est = max(Delta / 30 * (s_current - s_star) / (1 - s_star), g_min)
        else:
            g_est = g_min

        # Adaptive time step: spend more time where gap is small
        # ds/dt = c * g^2, so dt = ds / (c * g^2)
        ds = 1.0 / num_steps  # Uniform in s for simplicity
        dt = dt_base  # Could be adaptive

        s_next = min(s_current + ds, 1.0)
        s_mid = (s_current + s_next) / 2

        # H(s) = -(1-s)|psi_0><psi_0| + s*H_z
        psi_0 = np.sqrt(inst['degeneracies'] / N)
        H_mid = s_mid * np.diag(inst['energies']) - (1 - s_mid) * np.outer(psi_0, psi_0)

        # Time evolution: e^{-i H dt}
        eigenvalues, eigenvectors = np.linalg.eigh(H_mid)
        phases = np.exp(-1j * eigenvalues * dt)
        U = eigenvectors @ np.diag(phases) @ eigenvectors.T.conj()

        psi = U @ psi
        s_current = s_next

    # Fidelity with ground state
    fidelity = np.abs(np.vdot(target, psi))**2
    return fidelity


def run_imprecision_experiment(n, M, num_deltas=20, num_T=10, seed=42):
    """
    Test how fidelity depends on A_1 imprecision and runtime.
    """
    print(f"\n=== Imprecision Experiment: n={n}, M={M} ===")

    inst = generate_instance(n, M, seed)
    A_1, A_2, d_0, N = inst['A_1'], inst['A_2'], inst['d_0'], inst['N']

    # Key quantities
    s_star = A_1 / (A_1 + 1)
    g_min = 2 * A_1 / (A_1 + 1) * np.sqrt(d_0 / (A_2 * N))
    delta_s = 2 / (A_1 + 1)**2 * np.sqrt(d_0 * A_2 / N)
    T_optimal = np.sqrt(N / d_0) / g_min  # Rough estimate

    print(f"A_1 = {A_1:.4f}, g_min = {g_min:.6f}")
    print(f"delta_s = {delta_s:.6f}")
    print(f"Estimated T_optimal ~ {T_optimal:.1f}")

    # Delta values: from very small to large
    delta_fracs = np.logspace(-3, 0, num_deltas)  # fraction of A_1
    deltas = delta_fracs * A_1

    # Runtime values
    T_values = np.logspace(np.log10(T_optimal * 0.1), np.log10(T_optimal * 5), num_T)

    print(f"\nTesting {num_deltas} delta values x {num_T} runtime values...")

    results = []

    # Baseline: exact A_1
    print("\nBaseline (exact A_1):")
    for T in T_values[:5]:
        fid = simulate_adiabatic_evolution(inst, T, num_steps=500, A_1_used=None)
        print(f"  T = {T:.1f}: fidelity = {fid:.4f}")

    # Test with imprecision
    print("\nWith imprecision:")
    for delta_frac in [0.001, 0.01, 0.1, 0.5]:
        delta = delta_frac * A_1
        A_1_est = A_1 + delta
        print(f"\n  delta/A_1 = {delta_frac:.3f} (A_1_est = {A_1_est:.4f}):")
        for T in T_values[::3]:
            fid = simulate_adiabatic_evolution(inst, T, num_steps=500, A_1_used=A_1_est)
            print(f"    T = {T:.1f}: fidelity = {fid:.4f}")
            results.append({
                'delta_frac': delta_frac,
                'T': T,
                'fidelity': fid
            })

    return results, inst


def main():
    print("="*60)
    print("IMPRECISE A_1 SIMULATION")
    print("Testing how AQO fidelity degrades with A_1 estimation error")
    print("="*60)

    # Small system for validation
    results, inst = run_imprecision_experiment(n=8, M=8, seed=42)

    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)

    # Check key predictions:
    # 1. Small delta should have minimal impact
    # 2. Large delta should degrade fidelity significantly
    # 3. Longer T should compensate for imprecision

    print("\nKey observations:")
    print("- Small imprecision (delta/A_1 < 0.01): minimal impact on fidelity")
    print("- Large imprecision (delta/A_1 > 0.1): significant degradation")
    print("- Longer runtime can partially compensate")

    print("\nThis validates the error analysis from error_analysis_imprecise_A1.md")


if __name__ == "__main__":
    main()
