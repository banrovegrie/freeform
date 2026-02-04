"""
Robust AQO Schedule Analysis

Key question: Can we design schedules that work well without knowing A_1 exactly?

Strategy: If A_1 is known to be in [A_min, A_max], find schedule that minimizes
worst-case performance loss.
"""

import numpy as np
from math import sqrt


def generate_instance(n, M, seed=42):
    """Generate a random problem instance."""
    np.random.seed(seed)
    N = 2**n

    # Generate distinct energy levels
    energies = np.sort(np.random.uniform(0, 1, M))
    energies[0] = 0
    for k in range(1, M):
        if energies[k] - energies[k-1] < 0.05:
            energies[k] = energies[k-1] + 0.05
    if energies.max() > 0:
        energies = energies / energies.max()

    # Generate degeneracies
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
    """Estimate spectral gap at schedule position s using A_1."""
    s_star = A_1 / (A_1 + 1)
    g_min = 2 * A_1 / (A_1 + 1) * np.sqrt(d_0 / (A_2 * N))
    delta_s = 2 / (A_1 + 1)**2 * np.sqrt(d_0 * A_2 / N)

    if s < s_star - delta_s:
        g = A_1 / A_2 * (s_star - s) / (1 - s_star)
    elif s > s_star + delta_s:
        g = Delta / 30 * (s - s_star) / (1 - s_star)
    else:
        g = g_min

    return max(g, g_min * 0.5)


def build_local_schedule(A_1, A_2, d_0, N, Delta, num_points=1000):
    """Build local schedule s(t) such that ds/dt ~ g(s)^2."""
    s_vals = np.linspace(0, 1, num_points)
    gaps = [gap_estimate(s, A_1, A_2, d_0, N, Delta) for s in s_vals]
    dt_ds = [1.0 / g**2 for g in gaps]
    t_vals = np.cumsum(dt_ds) * (s_vals[1] - s_vals[0])
    t_vals = t_vals / t_vals[-1]
    t_uniform = np.linspace(0, 1, num_points)
    s_of_t = np.interp(t_uniform, t_vals, s_vals)
    return s_of_t


def build_robust_schedule(A_min, A_max, A_2, d_0, N, Delta, num_points=1000):
    """
    Build a robust schedule that hedges between A_min and A_max.

    Strategy: Average the schedules for A_min and A_max.
    This ensures we spend enough time near BOTH possible avoided crossing positions.
    """
    schedule_min = build_local_schedule(A_min, A_2, d_0, N, Delta, num_points)
    schedule_max = build_local_schedule(A_max, A_2, d_0, N, Delta, num_points)

    # Average the two schedules
    schedule_robust = (schedule_min + schedule_max) / 2

    return schedule_robust


def build_cautious_schedule(A_min, A_max, A_2, d_0, N, Delta, num_points=1000):
    """
    Build a cautious schedule that slows down over the entire range [s*_min, s*_max].

    This ensures we handle ANY A_1 in the given range.
    """
    s_star_min = A_min / (A_min + 1)
    s_star_max = A_max / (A_max + 1)

    s_vals = np.linspace(0, 1, num_points)

    # In the "danger zone" [s*_min - margin, s*_max + margin], use minimum gap
    g_min_worst = 2 * A_min / (A_min + 1) * np.sqrt(d_0 / (A_2 * N))
    margin = 0.05

    gaps = []
    for s in s_vals:
        if s_star_min - margin <= s <= s_star_max + margin:
            # In danger zone - assume worst-case gap
            g = g_min_worst
        elif s < s_star_min - margin:
            # Safe region before crossing
            g = gap_estimate(s, A_max, A_2, d_0, N, Delta)  # Conservative
        else:
            # Safe region after crossing
            g = gap_estimate(s, A_min, A_2, d_0, N, Delta)  # Conservative
        gaps.append(max(g, g_min_worst * 0.5))

    # Build schedule
    dt_ds = [1.0 / g**2 for g in gaps]
    t_vals = np.cumsum(dt_ds) * (s_vals[1] - s_vals[0])
    t_vals = t_vals / t_vals[-1]
    t_uniform = np.linspace(0, 1, num_points)
    s_of_t = np.interp(t_uniform, t_vals, s_vals)

    return s_of_t


def simulate_with_schedule(inst, T, schedule, num_steps=500):
    """Simulate adiabatic evolution with given schedule."""
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


def test_robust_schedules():
    """
    Test robust schedules against exact and uniform schedules.
    """
    print("="*70)
    print("ROBUST SCHEDULE ANALYSIS")
    print("Testing schedules that work without knowing A_1 exactly")
    print("="*70)

    # Generate test instances
    instances = []
    for seed in range(5):
        inst = generate_instance(n=10, M=10, seed=seed)
        instances.append(inst)

    # Compute A_1 range across instances
    A_1_values = [inst['A_1'] for inst in instances]
    A_1_min, A_1_max = min(A_1_values), max(A_1_values)
    A_1_mean = np.mean(A_1_values)

    print(f"\nGenerated {len(instances)} instances:")
    print(f"  A_1 range: [{A_1_min:.4f}, {A_1_max:.4f}]")
    print(f"  A_1 mean: {A_1_mean:.4f}")

    # Test different schedules on each instance
    schedules = {
        'Uniform': lambda inst: np.linspace(0, 1, 1000),
        'Exact A_1': lambda inst: build_local_schedule(
            inst['A_1'], inst['A_2'], inst['d_0'], inst['N'], inst['Delta']
        ),
        'Mean A_1': lambda inst: build_local_schedule(
            A_1_mean, inst['A_2'], inst['d_0'], inst['N'], inst['Delta']
        ),
        'Robust (avg)': lambda inst: build_robust_schedule(
            A_1_min, A_1_max, inst['A_2'], inst['d_0'], inst['N'], inst['Delta']
        ),
        'Cautious': lambda inst: build_cautious_schedule(
            A_1_min, A_1_max, inst['A_2'], inst['d_0'], inst['N'], inst['Delta']
        ),
    }

    # Test at different evolution times
    T_multipliers = [1.0, 2.0, 5.0, 10.0]

    print("\n" + "-"*70)
    print("Results: Fidelity at different evolution times")
    print("-"*70)

    for T_mult in T_multipliers:
        print(f"\nT = {T_mult} * T_optimal:")
        print(f"{'Schedule':<15} | {'Inst 0':>8} {'Inst 1':>8} {'Inst 2':>8} {'Inst 3':>8} {'Inst 4':>8} | {'Mean':>8}")
        print("-"*80)

        for sched_name, sched_fn in schedules.items():
            fids = []
            for inst in instances:
                T_opt = np.pi * np.sqrt(inst['N'] / inst['d_0']) / 2
                T = T_opt * T_mult
                schedule = sched_fn(inst)
                fid = simulate_with_schedule(inst, T, schedule, num_steps=500)
                fids.append(fid)

            fid_str = ' '.join(f'{f:8.4f}' for f in fids)
            print(f"{sched_name:<15} | {fid_str} | {np.mean(fids):8.4f}")


def analyze_A1_uncertainty():
    """
    Analyze how A_1 uncertainty affects optimal schedule choice.
    """
    print("\n" + "="*70)
    print("ANALYSIS: A_1 Uncertainty vs. Performance")
    print("="*70)

    # Fix one instance
    inst = generate_instance(n=10, M=10, seed=42)
    A_1_true = inst['A_1']
    T_opt = np.pi * np.sqrt(inst['N'] / inst['d_0']) / 2

    print(f"\nFixed instance: A_1 = {A_1_true:.4f}")

    # Test schedules with different A_1 estimates
    uncertainties = [0.0, 0.05, 0.1, 0.2, 0.3, 0.5, 0.75, 1.0]

    print("\n" + "-"*70)
    print("Performance vs. A_1 Uncertainty (T = 5 * T_optimal)")
    print("-"*70)
    print(f"{'Uncertainty':<12} | {'Local(true)':>12} {'Local(est)':>12} {'Uniform':>12} {'Robust':>12}")

    T = T_opt * 5

    for unc in uncertainties:
        # A_1 estimate is wrong by factor (1 + unc)
        A_1_est = A_1_true * (1 + unc)

        # Build schedules
        sched_true = build_local_schedule(A_1_true, inst['A_2'], inst['d_0'], inst['N'], inst['Delta'])
        sched_est = build_local_schedule(A_1_est, inst['A_2'], inst['d_0'], inst['N'], inst['Delta'])
        sched_uniform = np.linspace(0, 1, 1000)
        sched_robust = build_robust_schedule(
            A_1_true * 0.5, A_1_true * 2.0,  # Wide range
            inst['A_2'], inst['d_0'], inst['N'], inst['Delta']
        )

        # Compute fidelities
        fid_true = simulate_with_schedule(inst, T, sched_true)
        fid_est = simulate_with_schedule(inst, T, sched_est)
        fid_uniform = simulate_with_schedule(inst, T, sched_uniform)
        fid_robust = simulate_with_schedule(inst, T, sched_robust)

        print(f"{unc*100:>10.0f}%   | {fid_true:12.4f} {fid_est:12.4f} {fid_uniform:12.4f} {fid_robust:12.4f}")


def key_finding():
    """
    Summarize key finding: When is knowing A_1 worth the computational cost?
    """
    print("\n" + "="*70)
    print("KEY FINDING: Value of Knowing A_1")
    print("="*70)

    # Test on multiple instances
    results = {'exact': [], 'uniform': [], 'robust': []}

    for seed in range(20):
        inst = generate_instance(n=10, M=10, seed=seed)
        T_opt = np.pi * np.sqrt(inst['N'] / inst['d_0']) / 2
        T = T_opt * 5  # Generous time budget

        # Build schedules
        sched_exact = build_local_schedule(inst['A_1'], inst['A_2'], inst['d_0'], inst['N'], inst['Delta'])
        sched_uniform = np.linspace(0, 1, 1000)

        # For robust, assume A_1 is in [0.1, 10] (very wide range)
        sched_robust = build_robust_schedule(0.1, 10.0, inst['A_2'], inst['d_0'], inst['N'], inst['Delta'])

        # Compute fidelities
        fid_exact = simulate_with_schedule(inst, T, sched_exact)
        fid_uniform = simulate_with_schedule(inst, T, sched_uniform)
        fid_robust = simulate_with_schedule(inst, T, sched_robust)

        results['exact'].append(fid_exact)
        results['uniform'].append(fid_uniform)
        results['robust'].append(fid_robust)

    print("\nAcross 20 random instances (T = 5 * T_optimal):")
    print(f"\n{'Schedule':<15} | {'Mean Fidelity':>14} | {'Std':>8} | {'Min':>8} | {'Max':>8}")
    print("-"*70)

    for name, fids in results.items():
        print(f"{name:<15} | {np.mean(fids):14.4f} | {np.std(fids):8.4f} | {np.min(fids):8.4f} | {np.max(fids):8.4f}")

    # Compute the "value" of knowing A_1
    improvement = np.mean(results['exact']) - np.mean(results['uniform'])
    relative_improvement = improvement / np.mean(results['uniform']) * 100

    print(f"\n{'='*70}")
    print(f"Improvement from knowing A_1 exactly:")
    print(f"  Absolute: {improvement:.4f}")
    print(f"  Relative: {relative_improvement:.1f}%")
    print(f"{'='*70}")

    if relative_improvement < 20:
        print("\nCONCLUSION: The benefit of knowing A_1 exactly is MODEST (<20%).")
        print("For practical purposes, a robust schedule may be sufficient.")
    else:
        print("\nCONCLUSION: Knowing A_1 provides SIGNIFICANT benefit (>20%).")
        print("Exact calibration is important for optimal performance.")


if __name__ == "__main__":
    test_robust_schedules()
    analyze_A1_uncertainty()
    key_finding()
