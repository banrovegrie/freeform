"""
Check if the value-of-information result scales to larger systems.
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


def build_wide_slow_schedule(s_low, s_high, g_min_ratio=0.02, num_points=1000):
    """Build instance-independent schedule."""
    s_vals = np.linspace(0.001, 0.999, num_points)
    gaps = []
    for s in s_vals:
        if s_low <= s <= s_high:
            g = g_min_ratio
        else:
            dist = min(abs(s - s_low), abs(s - s_high))
            g = g_min_ratio + 0.5 * dist
        gaps.append(g)

    dt_ds = [1.0 / (g**2 + 1e-10) for g in gaps]
    t_vals = np.cumsum(dt_ds) * (s_vals[1] - s_vals[0])
    t_vals = t_vals / t_vals[-1]
    t_uniform = np.linspace(0, 1, num_points)
    s_of_t = np.interp(t_uniform, t_vals, s_vals)
    return s_of_t


def simulate(inst, T, schedule, num_steps=500):
    """Simulate adiabatic evolution."""
    M = inst['M']
    N = inst['N']

    psi = np.sqrt(inst['degeneracies'] / N).astype(complex)
    target = np.zeros(M)
    target[0] = 1.0

    dt = T / num_steps
    psi_0_vec = np.sqrt(inst['degeneracies'] / N)

    for step in range(num_steps):
        t_frac = step / num_steps
        idx = min(int(t_frac * len(schedule)), len(schedule) - 1)
        s = schedule[idx]

        H_s = s * np.diag(inst['energies']) - (1 - s) * np.outer(psi_0_vec, psi_0_vec)
        eigenvalues, eigenvectors = np.linalg.eigh(H_s)
        phases = np.exp(-1j * eigenvalues * dt)
        U = eigenvectors @ np.diag(phases) @ eigenvectors.T.conj()
        psi = U @ psi

    return np.abs(np.vdot(target, psi))**2


def scaling_analysis():
    """Check how the value-of-information scales with n."""
    print("="*75)
    print("SCALING ANALYSIS: Value of A_1 Knowledge vs. System Size")
    print("="*75)

    # Test at different system sizes
    system_sizes = [8, 10, 12]  # Limited by exponential Hilbert space
    num_instances = 10  # Per system size
    T_mult = 5.0

    results = {}

    for n in system_sizes:
        M = n  # Number of distinct energy levels
        print(f"\n{'='*40}")
        print(f"n = {n} qubits (N = 2^{n} = {2**n})")
        print(f"{'='*40}")

        fids_uniform = []
        fids_wide = []
        fids_centered = []

        for seed in range(num_instances):
            inst = generate_instance(n, M, seed=seed)
            T_opt = np.pi * np.sqrt(inst['N'] / inst['d_0']) / 2
            T = T_opt * T_mult

            # Schedules
            sched_uniform = np.linspace(0, 1, 1000)
            sched_wide = build_wide_slow_schedule(0.4, 0.8)

            s_star = inst['A_1'] / (inst['A_1'] + 1)
            sched_centered = build_wide_slow_schedule(s_star - 0.15, s_star + 0.15)

            # Simulate
            fids_uniform.append(simulate(inst, T, sched_uniform))
            fids_wide.append(simulate(inst, T, sched_wide))
            fids_centered.append(simulate(inst, T, sched_centered))

        results[n] = {
            'uniform': np.mean(fids_uniform),
            'wide': np.mean(fids_wide),
            'centered': np.mean(fids_centered)
        }

        # Compute improvements
        imp_wide = (results[n]['wide'] - results[n]['uniform']) / results[n]['uniform'] * 100
        imp_centered = (results[n]['centered'] - results[n]['uniform']) / results[n]['uniform'] * 100
        A1_value = imp_centered - imp_wide

        print(f"\nResults ({num_instances} instances):")
        print(f"  Uniform:              {results[n]['uniform']:.4f}")
        print(f"  Wide [0.4, 0.8]:      {results[n]['wide']:.4f} ({imp_wide:+.1f}%)")
        print(f"  Centered [s*±0.15]:   {results[n]['centered']:.4f} ({imp_centered:+.1f}%)")
        print(f"  Additional A_1 value: {A1_value:+.1f}%")

    # Summary
    print("\n" + "="*75)
    print("SUMMARY: Value of A_1 Knowledge by System Size")
    print("="*75)
    print(f"\n{'n':<6} | {'Uniform':>10} | {'Wide':>10} | {'Centered':>10} | {'II Imp':>10} | {'A_1 Value':>10}")
    print("-"*75)

    for n in system_sizes:
        r = results[n]
        imp_ii = (r['wide'] - r['uniform']) / r['uniform'] * 100
        imp_a1 = (r['centered'] - r['wide']) / r['uniform'] * 100
        print(f"{n:<6} | {r['uniform']:>10.4f} | {r['wide']:>10.4f} | {r['centered']:>10.4f} | {imp_ii:>+9.1f}% | {imp_a1:>+9.1f}%")

    print("\nII Imp = Instance-Independent Improvement over Uniform")
    print("A_1 Value = Additional Improvement from knowing A_1")


if __name__ == "__main__":
    scaling_analysis()
