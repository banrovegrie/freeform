"""
Properly implements local adiabatic schedule and tests A_1 sensitivity.
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


def gap_estimate(s, A_1, A_2, d_0, N, Delta):
    """
    Estimate spectral gap at schedule position s using A_1.

    This is the key function that depends on A_1 and determines
    where the schedule slows down.
    """
    s_star = A_1 / (A_1 + 1)
    g_min = 2 * A_1 / (A_1 + 1) * np.sqrt(d_0 / (A_2 * N))
    delta_s = 2 / (A_1 + 1)**2 * np.sqrt(d_0 * A_2 / N)

    if s < s_star - delta_s:
        # Left of crossing
        g = A_1 / A_2 * (s_star - s) / (1 - s_star)
    elif s > s_star + delta_s:
        # Right of crossing
        g = Delta / 30 * (s - s_star) / (1 - s_star)
    else:
        # In crossing region
        g = g_min

    return max(g, g_min * 0.5)  # Don't let it go below half g_min


def build_local_schedule(A_1, A_2, d_0, N, Delta, num_points=1000):
    """
    Build local schedule s(t) such that ds/dt ~ g(s)^2.

    Returns: array of s values at uniform t points
    """
    # Sample s values
    s_vals = np.linspace(0, 1, num_points)
    gaps = [gap_estimate(s, A_1, A_2, d_0, N, Delta) for s in s_vals]

    # dt/ds = 1/g(s)^2 (slower where gap is small)
    dt_ds = [1.0 / g**2 for g in gaps]

    # Integrate to get t(s)
    t_vals = np.cumsum(dt_ds) * (s_vals[1] - s_vals[0])

    # Normalize so t goes from 0 to 1
    t_vals = t_vals / t_vals[-1]

    # Invert to get s(t)
    # s_of_t[i] = s such that t(s) = i/num_points
    t_uniform = np.linspace(0, 1, num_points)
    s_of_t = np.interp(t_uniform, t_vals, s_vals)

    return s_of_t


def actual_gap(inst, s):
    """Compute actual gap at schedule position s."""
    N = inst['N']
    psi_0 = np.sqrt(inst['degeneracies'] / N)
    H_s = s * np.diag(inst['energies']) - (1 - s) * np.outer(psi_0, psi_0)
    eigenvalues = np.sort(np.linalg.eigvalsh(H_s))
    return eigenvalues[1] - eigenvalues[0]


def simulate_with_schedule(inst, T, schedule, num_steps=500):
    """
    Simulate adiabatic evolution with given schedule.

    Args:
        inst: Problem instance
        T: Total evolution time
        schedule: Array of s values at uniform t points
        num_steps: Number of Trotter steps

    Returns:
        fidelity with ground state
    """
    M = inst['M']
    N = inst['N']

    # Initial state
    psi = np.sqrt(inst['degeneracies'] / N).astype(complex)

    # Target
    target = np.zeros(M)
    target[0] = 1.0

    dt = T / num_steps
    psi_0_vec = np.sqrt(inst['degeneracies'] / N)

    for step in range(num_steps):
        # Get s from schedule
        t_frac = step / num_steps
        idx = min(int(t_frac * len(schedule)), len(schedule) - 1)
        s = schedule[idx]

        # H(s)
        H_s = s * np.diag(inst['energies']) - (1 - s) * np.outer(psi_0_vec, psi_0_vec)

        # Time evolution
        eigenvalues, eigenvectors = np.linalg.eigh(H_s)
        phases = np.exp(-1j * eigenvalues * dt)
        U = eigenvectors @ np.diag(phases) @ eigenvectors.T.conj()

        psi = U @ psi

    return np.abs(np.vdot(target, psi))**2


def main():
    print("="*60)
    print("LOCAL SCHEDULE SIMULATION")
    print("Testing A_1 sensitivity with proper local schedule")
    print("="*60)

    n, M = 10, 10
    inst = generate_instance(n, M, seed=42)
    A_1, A_2, d_0, N, Delta = inst['A_1'], inst['A_2'], inst['d_0'], inst['N'], inst['Delta']

    print(f"\nn = {n}, N = {N}, d_0 = {d_0}")
    print(f"A_1 = {A_1:.4f}, A_2 = {A_2:.4f}, Delta = {Delta:.4f}")

    # Compute key quantities
    s_star = A_1 / (A_1 + 1)
    g_min = 2 * A_1 / (A_1 + 1) * np.sqrt(d_0 / (A_2 * N))

    print(f"s* = {s_star:.4f}, g_min = {g_min:.6f}")

    # Compare schedules: exact A_1 vs. imprecise A_1
    print("\n--- Building schedules ---")

    # Exact schedule
    schedule_exact = build_local_schedule(A_1, A_2, d_0, N, Delta)

    # Check where the schedules spend their time
    s_star_exact = A_1 / (A_1 + 1)

    print(f"\nSchedule with exact A_1 (s* = {s_star_exact:.4f}):")
    print(f"  Time in [0, s*-0.1]: {np.mean(schedule_exact < s_star_exact - 0.1)*100:.1f}%")
    print(f"  Time in [s*-0.1, s*+0.1]: {np.mean((schedule_exact >= s_star_exact - 0.1) & (schedule_exact <= s_star_exact + 0.1))*100:.1f}%")
    print(f"  Time in [s*+0.1, 1]: {np.mean(schedule_exact > s_star_exact + 0.1)*100:.1f}%")

    # Test with various A_1 imprecisions
    print("\n--- Testing fidelity with imprecise A_1 ---")

    # Estimate T_optimal
    T_optimal = np.pi * np.sqrt(N / d_0) / 2  # Rough

    for delta_frac in [0, 0.01, 0.05, 0.1, 0.2, 0.5]:
        A_1_est = A_1 * (1 + delta_frac)

        # Build schedule with imprecise A_1
        schedule = build_local_schedule(A_1_est, A_2, d_0, N, Delta)

        s_star_est = A_1_est / (A_1_est + 1)
        print(f"\ndelta/A_1 = {delta_frac:.2f} (A_1_est = {A_1_est:.3f}, s*_est = {s_star_est:.4f}):")

        for T_mult in [0.5, 1.0, 2.0, 5.0]:
            T = T_optimal * T_mult
            fid = simulate_with_schedule(inst, T, schedule, num_steps=500)
            print(f"  T = {T_mult:.1f} * T_opt = {T:.1f}: fidelity = {fid:.4f}")

    # Compare: uniform schedule
    print("\n--- Comparison: Uniform schedule (s(t) = t) ---")
    schedule_uniform = np.linspace(0, 1, 1000)
    for T_mult in [0.5, 1.0, 2.0, 5.0, 10.0]:
        T = T_optimal * T_mult
        fid = simulate_with_schedule(inst, T, schedule_uniform, num_steps=500)
        print(f"  T = {T_mult:.1f} * T_opt = {T:.1f}: fidelity = {fid:.4f}")


if __name__ == "__main__":
    main()
