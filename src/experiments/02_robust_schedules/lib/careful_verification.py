"""
Careful verification of the robust schedule finding.

Use the proper local schedule from the paper's theory and compare
with instance-independent schedules.
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


def compute_actual_gap(inst, s):
    """Compute the actual spectral gap at schedule position s."""
    N = inst['N']
    psi_0 = np.sqrt(inst['degeneracies'] / N)

    # H(s) = s * H_z - (1-s) * |psi_0><psi_0|
    H_s = s * np.diag(inst['energies']) - (1 - s) * np.outer(psi_0, psi_0)

    eigenvalues = np.sort(np.linalg.eigvalsh(H_s))
    return eigenvalues[1] - eigenvalues[0]


def build_local_schedule_actual(inst, num_points=1000):
    """
    Build local schedule using ACTUAL computed gaps.
    This is the gold standard - uses exact spectrum information.
    """
    s_vals = np.linspace(0.001, 0.999, num_points)  # Avoid endpoints

    # Compute actual gaps
    gaps = [compute_actual_gap(inst, s) for s in s_vals]

    # dt/ds = 1/g(s)^2
    dt_ds = [1.0 / (g**2 + 1e-10) for g in gaps]

    # Integrate
    t_vals = np.cumsum(dt_ds) * (s_vals[1] - s_vals[0])
    t_vals = t_vals / t_vals[-1]

    # Invert
    t_uniform = np.linspace(0, 1, num_points)
    s_of_t = np.interp(t_uniform, t_vals, s_vals)

    return s_of_t


def build_local_schedule_theory(A_1, A_2, d_0, N, Delta, num_points=1000):
    """
    Build local schedule using theoretical gap formula from the paper.
    """
    s_star = A_1 / (A_1 + 1)
    g_min = 2 * A_1 / (A_1 + 1) * np.sqrt(d_0 / (A_2 * N))
    delta_s = 2 / (A_1 + 1)**2 * np.sqrt(d_0 * A_2 / N)

    s_vals = np.linspace(0.001, 0.999, num_points)

    gaps = []
    for s in s_vals:
        if s < s_star - delta_s:
            g = A_1 / A_2 * (s_star - s) / (1 - s_star)
        elif s > s_star + delta_s:
            g = Delta / 30 * (s - s_star) / (1 - s_star)
        else:
            g = g_min
        gaps.append(max(g, g_min * 0.5))

    dt_ds = [1.0 / (g**2 + 1e-10) for g in gaps]
    t_vals = np.cumsum(dt_ds) * (s_vals[1] - s_vals[0])
    t_vals = t_vals / t_vals[-1]
    t_uniform = np.linspace(0, 1, num_points)
    s_of_t = np.interp(t_uniform, t_vals, s_vals)

    return s_of_t


def build_wide_slow_schedule(s_low, s_high, g_min_ratio=0.02, num_points=1000):
    """
    Build an instance-independent schedule that slows down over [s_low, s_high].
    """
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


def main():
    print("="*75)
    print("CAREFUL VERIFICATION: Comparing Schedule Strategies")
    print("="*75)

    # Generate instances
    num_instances = 20
    instances = [generate_instance(n=10, M=10, seed=seed) for seed in range(num_instances)]

    # Report instance statistics
    A1_vals = [inst['A_1'] for inst in instances]
    s_star_vals = [inst['A_1'] / (inst['A_1'] + 1) for inst in instances]

    print(f"\n{num_instances} instances generated:")
    print(f"  A_1 range: [{min(A1_vals):.3f}, {max(A1_vals):.3f}]")
    print(f"  s* range: [{min(s_star_vals):.3f}, {max(s_star_vals):.3f}]")

    # Test different schedules
    T_mult = 5.0

    print(f"\nTesting at T = {T_mult} * T_optimal")
    print("-"*75)

    results = {
        'Uniform': [],
        'Local (theory)': [],
        'Local (actual gap)': [],
        'Wide [0.4, 0.8]': [],
        'Wide [0.3, 0.9]': [],
        'Wide [s*-0.15, s*+0.15]': [],  # Instance-specific but simple
    }

    for i, inst in enumerate(instances):
        T_opt = np.pi * np.sqrt(inst['N'] / inst['d_0']) / 2
        T = T_opt * T_mult

        # Build schedules
        sched_uniform = np.linspace(0, 1, 1000)
        sched_theory = build_local_schedule_theory(
            inst['A_1'], inst['A_2'], inst['d_0'], inst['N'], inst['Delta']
        )
        sched_actual = build_local_schedule_actual(inst)
        sched_wide_48 = build_wide_slow_schedule(0.4, 0.8)
        sched_wide_39 = build_wide_slow_schedule(0.3, 0.9)

        # Instance-specific but simple: center on s* with fixed width
        s_star = inst['A_1'] / (inst['A_1'] + 1)
        sched_centered = build_wide_slow_schedule(s_star - 0.15, s_star + 0.15)

        # Simulate
        results['Uniform'].append(simulate(inst, T, sched_uniform))
        results['Local (theory)'].append(simulate(inst, T, sched_theory))
        results['Local (actual gap)'].append(simulate(inst, T, sched_actual))
        results['Wide [0.4, 0.8]'].append(simulate(inst, T, sched_wide_48))
        results['Wide [0.3, 0.9]'].append(simulate(inst, T, sched_wide_39))
        results['Wide [s*-0.15, s*+0.15]'].append(simulate(inst, T, sched_centered))

        if (i + 1) % 5 == 0:
            print(f"  Completed {i+1}/{num_instances} instances")

    # Report results
    print("\n" + "="*75)
    print("RESULTS")
    print("="*75)
    print(f"\n{'Schedule':<25} | {'Mean':>8} | {'Std':>8} | {'Min':>8} | {'Max':>8}")
    print("-"*75)

    for name, fids in results.items():
        print(f"{name:<25} | {np.mean(fids):8.4f} | {np.std(fids):8.4f} | {np.min(fids):8.4f} | {np.max(fids):8.4f}")

    # Analysis
    print("\n" + "="*75)
    print("ANALYSIS")
    print("="*75)

    baseline = np.mean(results['Uniform'])
    best_ii = max(['Wide [0.4, 0.8]', 'Wide [0.3, 0.9]'],
                  key=lambda k: np.mean(results[k]))
    best_exact = max(['Local (theory)', 'Local (actual gap)', 'Wide [s*-0.15, s*+0.15]'],
                     key=lambda k: np.mean(results[k]))

    print(f"\nBaseline (Uniform): {baseline:.4f}")
    print(f"Best instance-independent: {best_ii} with {np.mean(results[best_ii]):.4f}")
    print(f"Best using A_1/s*: {best_exact} with {np.mean(results[best_exact]):.4f}")

    ii_improvement = (np.mean(results[best_ii]) - baseline) / baseline * 100
    exact_improvement = (np.mean(results[best_exact]) - baseline) / baseline * 100

    print(f"\nImprovement over uniform:")
    print(f"  Instance-independent: {ii_improvement:+.1f}%")
    print(f"  Using A_1 knowledge: {exact_improvement:+.1f}%")

    print(f"\nAdditional benefit from knowing A_1:")
    print(f"  {exact_improvement - ii_improvement:+.1f}% over best instance-independent")

    print("\n" + "="*75)
    if exact_improvement - ii_improvement < 10:
        print("CONCLUSION: Knowing A_1 provides MARGINAL additional benefit (<10%)")
        print("over a good instance-independent schedule.")
    else:
        print("CONCLUSION: Knowing A_1 provides SIGNIFICANT additional benefit (>10%)")
        print("over instance-independent schedules.")
    print("="*75)


if __name__ == "__main__":
    main()
