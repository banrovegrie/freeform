"""
Verify the robust schedule finding and check if it's truly instance-independent.

Key question: The robust schedule seems to outperform exact A_1 schedule.
Is this real, or an artifact of using instance-specific parameters?
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


def gap_function(s, s_star, g_min, width):
    """
    Simplified gap model: Lorentzian-like minimum at s_star.
    """
    return g_min + (1 - g_min) * min(abs(s - s_star), width) / width


def build_schedule_from_gap(gap_fn, num_points=1000):
    """Build schedule s(t) such that ds/dt ~ g(s)^2."""
    s_vals = np.linspace(0, 1, num_points)
    gaps = [gap_fn(s) for s in s_vals]
    dt_ds = [1.0 / g**2 for g in gaps]
    t_vals = np.cumsum(dt_ds) * (s_vals[1] - s_vals[0])
    t_vals = t_vals / t_vals[-1]
    t_uniform = np.linspace(0, 1, num_points)
    s_of_t = np.interp(t_uniform, t_vals, s_vals)
    return s_of_t


def build_truly_instanceindependent_schedules():
    """
    Build schedules that don't use ANY instance-specific information.
    """
    schedules = {}

    # 1. Uniform (trivial baseline)
    schedules['Uniform'] = np.linspace(0, 1, 1000)

    # 2. "Slow middle" - slow down around s = 0.5 (generic)
    def gap_slow_middle(s):
        s_center = 0.5
        width = 0.2
        g_min = 0.01
        return g_min + (1 - g_min) * min(abs(s - s_center), width) / width

    schedules['Slow Middle (s=0.5)'] = build_schedule_from_gap(gap_slow_middle)

    # 3. "Slow high" - slow down around s = 0.7 (typical A_1 gives s* ~ 0.6-0.8)
    def gap_slow_high(s):
        s_center = 0.7
        width = 0.2
        g_min = 0.01
        return g_min + (1 - g_min) * min(abs(s - s_center), width) / width

    schedules['Slow High (s=0.7)'] = build_schedule_from_gap(gap_slow_high)

    # 4. "Wide slow" - slow down over [0.4, 0.8] (hedge across typical range)
    def gap_wide_slow(s):
        s_low, s_high = 0.4, 0.8
        g_min = 0.02
        if s_low <= s <= s_high:
            return g_min
        else:
            return g_min + 0.5 * min(abs(s - s_low), abs(s - s_high))

    schedules['Wide Slow [0.4,0.8]'] = build_schedule_from_gap(gap_wide_slow)

    # 5. "Very wide slow" - slow down over [0.3, 0.9]
    def gap_very_wide(s):
        s_low, s_high = 0.3, 0.9
        g_min = 0.03
        if s_low <= s <= s_high:
            return g_min
        else:
            return g_min + 0.3 * min(abs(s - s_low), abs(s - s_high))

    schedules['Very Wide [0.3,0.9]'] = build_schedule_from_gap(gap_very_wide)

    return schedules


def test_instance_independent_schedules():
    """
    Test truly instance-independent schedules.
    """
    print("="*75)
    print("TESTING TRULY INSTANCE-INDEPENDENT SCHEDULES")
    print("="*75)

    # Generate test instances with varying parameters
    instances = []
    for seed in range(20):
        inst = generate_instance(n=10, M=10, seed=seed)
        instances.append(inst)

    # Get instance-independent schedules
    ii_schedules = build_truly_instanceindependent_schedules()

    # Also compute exact A_1 schedule for each instance (for comparison)
    print("\nInstance statistics:")
    A1_vals = [inst['A_1'] for inst in instances]
    s_star_vals = [inst['A_1'] / (inst['A_1'] + 1) for inst in instances]
    print(f"  A_1 range: [{min(A1_vals):.3f}, {max(A1_vals):.3f}]")
    print(f"  s* range: [{min(s_star_vals):.3f}, {max(s_star_vals):.3f}]")

    # Test at T = 5 * T_optimal
    T_mult = 5.0

    print(f"\nResults at T = {T_mult} * T_optimal:")
    print("-"*75)

    results = {}

    for sched_name, schedule in ii_schedules.items():
        fids = []
        for inst in instances:
            T_opt = np.pi * np.sqrt(inst['N'] / inst['d_0']) / 2
            T = T_opt * T_mult
            fid = simulate_with_schedule(inst, T, schedule)
            fids.append(fid)
        results[sched_name] = fids
        print(f"{sched_name:<25} | Mean: {np.mean(fids):.4f} | Std: {np.std(fids):.4f}")

    # Exact A_1 schedule (cheating - uses instance info)
    exact_fids = []
    for inst in instances:
        s_star = inst['A_1'] / (inst['A_1'] + 1)
        g_min_est = 0.01  # Can't compute exactly without instance info
        width = 0.1

        def gap_exact(s, s_star=s_star, g_min=g_min_est, w=width):
            return g_min + (1 - g_min) * min(abs(s - s_star), w) / w

        schedule = build_schedule_from_gap(gap_exact)
        T_opt = np.pi * np.sqrt(inst['N'] / inst['d_0']) / 2
        T = T_opt * T_mult
        fid = simulate_with_schedule(inst, T, schedule)
        exact_fids.append(fid)

    results['Exact s* (cheating)'] = exact_fids
    print(f"{'Exact s* (cheating)':<25} | Mean: {np.mean(exact_fids):.4f} | Std: {np.std(exact_fids):.4f}")

    # Best instance-independent schedule
    best_ii = max(ii_schedules.keys(), key=lambda k: np.mean(results[k]))
    print(f"\nBest instance-independent: {best_ii}")
    print(f"  Improvement over uniform: {(np.mean(results[best_ii]) - np.mean(results['Uniform'])) / np.mean(results['Uniform']) * 100:.1f}%")
    print(f"  Gap vs exact s*: {(np.mean(exact_fids) - np.mean(results[best_ii])) / np.mean(exact_fids) * 100:.1f}%")

    return results


def main_finding():
    """
    Establish the main finding about robust schedules.
    """
    print("\n" + "="*75)
    print("MAIN FINDING")
    print("="*75)

    results = test_instance_independent_schedules()

    print("\n" + "-"*75)
    print("SUMMARY")
    print("-"*75)

    uniform_mean = np.mean(results['Uniform'])
    best_ii_name = max([k for k in results.keys() if k != 'Exact s* (cheating)'],
                       key=lambda k: np.mean(results[k]))
    best_ii_mean = np.mean(results[best_ii_name])
    exact_mean = np.mean(results['Exact s* (cheating)'])

    print(f"\n1. Uniform schedule: {uniform_mean:.4f} mean fidelity")
    print(f"2. Best instance-independent ({best_ii_name}): {best_ii_mean:.4f}")
    print(f"3. Exact s* schedule (requires A_1): {exact_mean:.4f}")

    ii_improvement = (best_ii_mean - uniform_mean) / uniform_mean * 100
    exact_improvement = (exact_mean - uniform_mean) / uniform_mean * 100
    gap = (exact_mean - best_ii_mean) / exact_mean * 100

    print(f"\nImprovement over uniform:")
    print(f"  - Instance-independent: {ii_improvement:.1f}%")
    print(f"  - Exact A_1 knowledge: {exact_improvement:.1f}%")
    print(f"\nGap between instance-independent and exact: {gap:.1f}%")

    print("\n" + "="*75)
    if gap < 15:
        print("CONCLUSION: Instance-independent schedules achieve MOST of the benefit")
        print("of knowing A_1 exactly. The practical value of exact calibration is limited.")
    else:
        print("CONCLUSION: Knowing A_1 provides significant additional benefit.")
        print("Exact calibration is important for optimal performance.")
    print("="*75)


if __name__ == "__main__":
    main_finding()
