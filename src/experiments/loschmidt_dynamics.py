"""
Careful analysis of Loschmidt echo dynamics to find reliable calibration signal.
"""

import numpy as np


def generate_instance(n, M, seed=42):
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

    A_1 = sum(degeneracies[k] / (energies[k]) for k in range(1, M)) / N
    A_2 = sum(degeneracies[k] / (energies[k])**2 for k in range(1, M)) / N

    return {
        'n': n, 'N': N, 'M': M, 'energies': energies,
        'degeneracies': degeneracies, 'A_1': A_1, 'A_2': A_2,
        'd_0': degeneracies[0]
    }


def loschmidt_echo(inst, r, t):
    """Compute Loschmidt echo L(r,t)."""
    N = inst['N']
    psi_0 = np.sqrt(inst['degeneracies'] / N)
    H_r = r * np.diag(inst['energies']) - np.outer(psi_0, psi_0)
    eigenvalues, eigenvectors = np.linalg.eigh(H_r)

    # L = |sum_j |<psi_0|phi_j>|^2 exp(-i E_j t)|^2
    overlaps = np.array([np.abs(np.vdot(psi_0, eigenvectors[:, j]))**2
                         for j in range(len(eigenvalues))])
    phases = np.exp(-1j * eigenvalues * t)
    amplitude = np.sum(overlaps * phases)
    return np.abs(amplitude)**2


def spectral_gap(inst, r):
    N = inst['N']
    psi_0 = np.sqrt(inst['degeneracies'] / N)
    H_r = r * np.diag(inst['energies']) - np.outer(psi_0, psi_0)
    eigenvalues = np.sort(np.linalg.eigvalsh(H_r))
    return eigenvalues[1] - eigenvalues[0]


def main():
    print("=== Loschmidt Echo Dynamics Analysis ===\n")

    n = 10
    inst = generate_instance(n, M=10, seed=42)
    A_1, A_2, d_0, N = inst['A_1'], inst['A_2'], inst['d_0'], inst['N']

    print(f"n = {n}, A_1 = {A_1:.4f}, d_0 = {d_0}, N = {N}")

    # Predicted values
    r_predicted = A_1  # Position of minimum gap
    g_min_predicted = 2 * A_1 * np.sqrt(d_0 / (A_2 * N))
    T_predicted = np.pi / g_min_predicted  # Time for full oscillation

    print(f"Predicted: r* = {r_predicted:.4f}, g_min = {g_min_predicted:.4f}")
    print(f"Predicted oscillation period: T = {T_predicted:.2f}")

    # Verify minimum gap position
    r_scan = np.linspace(0.5, 4, 200)
    gaps = [spectral_gap(inst, r) for r in r_scan]
    r_min_gap = r_scan[np.argmin(gaps)]
    g_min_actual = min(gaps)
    print(f"Actual: r_min_gap = {r_min_gap:.4f}, g_min = {g_min_actual:.4f}")

    print(f"\n--- Loschmidt Echo at Fixed r = r_min_gap ---")
    # Scan time at r = r_min_gap
    t_values = np.linspace(0, 4*T_predicted, 400)
    L_at_r_min_gap = [loschmidt_echo(inst, r_min_gap, t) for t in t_values]

    # Find period from minima
    L_arr = np.array(L_at_r_min_gap)
    minima_indices = np.where((L_arr[1:-1] < L_arr[:-2]) & (L_arr[1:-1] < L_arr[2:]))[0] + 1

    if len(minima_indices) >= 2:
        period_actual = t_values[minima_indices[1]] - t_values[minima_indices[0]]
        print(f"Oscillation period (from minima): T_actual = {period_actual:.2f}")
        print(f"Ratio T_actual / T_predicted = {period_actual / T_predicted:.3f}")
    else:
        print("Could not find clear period from minima")

    L_min = min(L_at_r_min_gap)
    t_at_L_min = t_values[np.argmin(L_at_r_min_gap)]
    print(f"Min L = {L_min:.4f} at t = {t_at_L_min:.2f}")

    print(f"\n--- Loschmidt Echo Scan over r at Fixed t ---")
    # Key question: at what t does scanning r give a clear minimum at r = A_1?

    for t_probe in [T_predicted/2, T_predicted, 1.5*T_predicted, 2*T_predicted]:
        L_vs_r = [loschmidt_echo(inst, r, t_probe) for r in r_scan]
        r_at_L_min = r_scan[np.argmin(L_vs_r)]
        L_min = min(L_vs_r)
        print(f"  t = {t_probe:.2f}: L_min = {L_min:.4f} at r = {r_at_L_min:.4f}")

    print(f"\n--- Alternative: Use Gap Minimum Detection ---")
    print("The Loschmidt echo minimum doesn't cleanly locate r = A_1.")
    print("Instead, detect the minimum gap directly using spectral methods.")
    print(f"The minimum gap occurs at r = {r_min_gap:.4f} ≈ A_1 = {A_1:.4f}")
    print(f"Error: {abs(r_min_gap - A_1)/A_1 * 100:.2f}%")

    print(f"\n--- Calibration Strategy ---")
    print("Option 1: Measure gap g(r) vs r, find minimum -> gives A_1")
    print("Option 2: Use Loschmidt echo at multiple t values to infer g(r)")
    print("Option 3: Use quantum phase estimation on H(r)")

    # Test Option 1: Can we measure gap quantumly?
    # The gap appears in the oscillation frequency
    print(f"\n--- Option 2: Infer gap from oscillation frequency ---")
    for r in [A_1 - 0.5, A_1, A_1 + 0.5]:
        L_t = [loschmidt_echo(inst, r, t) for t in t_values]
        # FFT to find frequency
        fft = np.fft.rfft(L_t - np.mean(L_t))
        freq = np.fft.rfftfreq(len(t_values), t_values[1] - t_values[0])
        dominant_freq = freq[np.argmax(np.abs(fft[1:])) + 1]
        inferred_gap = 2 * np.pi * dominant_freq
        actual_gap = spectral_gap(inst, r)
        print(f"  r = {r:.2f}: inferred gap = {inferred_gap:.4f}, actual = {actual_gap:.4f}")


if __name__ == "__main__":
    main()
