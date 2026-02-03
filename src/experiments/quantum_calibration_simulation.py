"""
Quantum Calibration Simulation

Validates the Loschmidt echo-based resonance detection protocol
for estimating A_1 in adiabatic quantum optimization.

Author: Alapan Chaudhuri (thesis work)
"""

import numpy as np
from scipy.linalg import eigh, expm
import matplotlib.pyplot as plt
from dataclasses import dataclass
from typing import Tuple, List, Optional


@dataclass
class ProblemInstance:
    """Stores a problem Hamiltonian and its spectral properties."""
    n: int  # number of qubits
    energies: np.ndarray  # M distinct eigenvalues
    degeneracies: np.ndarray  # degeneracies d_k
    A_1: float
    A_2: float
    d_0: int
    Delta: float  # spectral gap E_1 - E_0

    @property
    def N(self) -> int:
        return 2**self.n

    @property
    def M(self) -> int:
        return len(self.energies)

    @property
    def r_star(self) -> float:
        """Resonance point r* = A_1 + 1"""
        return self.A_1 + 1

    @property
    def g_min(self) -> float:
        """Minimum gap at avoided crossing"""
        return 2 * self.A_1 / (self.A_1 + 1) * np.sqrt(self.d_0 / (self.A_2 * self.N))


def generate_random_instance(n: int, M: int, seed: int = None) -> ProblemInstance:
    """
    Generate a random problem instance with M energy levels.

    The Hamiltonian is diagonal in the computational basis with
    eigenvalues E_0 < E_1 < ... < E_{M-1} in [0, 1].
    """
    rng = np.random.default_rng(seed)
    N = 2**n

    # Generate M distinct energy levels in [0, 1]
    energies = np.sort(rng.uniform(0, 1, M))
    energies[0] = 0  # Ground state energy = 0

    # Ensure minimum gap
    min_gap = 0.1  # Reasonable lower bound
    for k in range(1, M):
        if energies[k] - energies[k-1] < min_gap:
            energies[k] = energies[k-1] + min_gap
    energies = energies / energies.max()  # Renormalize to [0, 1]

    # Distribute degeneracies
    # Use Dirichlet distribution for smooth random allocation
    alpha = rng.uniform(0.5, 2.0, M)
    probs = rng.dirichlet(alpha)
    degeneracies = np.round(probs * N).astype(int)
    degeneracies = np.maximum(degeneracies, 1)  # At least 1 per level

    # Adjust to sum exactly to N
    diff = N - degeneracies.sum()
    degeneracies[0] += diff

    # Compute spectral parameters
    E_0 = energies[0]
    d_0 = degeneracies[0]

    A_1 = sum(degeneracies[k] / (energies[k] - E_0)
              for k in range(1, M)) / N
    A_2 = sum(degeneracies[k] / (energies[k] - E_0)**2
              for k in range(1, M)) / N

    Delta = energies[1] - energies[0]

    return ProblemInstance(
        n=n,
        energies=energies,
        degeneracies=degeneracies,
        A_1=A_1,
        A_2=A_2,
        d_0=d_0,
        Delta=Delta
    )


def construct_symmetric_hamiltonian(instance: ProblemInstance, r: float) -> np.ndarray:
    """
    Construct H(r) = -|psi_0><psi_0| + r * H_z in the symmetric subspace.

    The symmetric subspace has dimension M (number of distinct energy levels).
    """
    M = instance.M
    N = instance.N

    # |psi_0> in symmetric subspace: coefficients sqrt(d_k/N)
    psi_0 = np.sqrt(instance.degeneracies / N)

    # H(r) = -|psi_0><psi_0| + r * diag(E_k)
    H_r = r * np.diag(instance.energies) - np.outer(psi_0, psi_0)

    return H_r


def compute_loschmidt_echo(instance: ProblemInstance, r: float, t: float) -> float:
    """
    Compute the Loschmidt echo L(r, t) = |<psi_0|e^{-iH(r)t}|psi_0>|^2
    """
    H_r = construct_symmetric_hamiltonian(instance, r)
    psi_0 = np.sqrt(instance.degeneracies / instance.N)

    # Time evolution operator
    U = expm(-1j * H_r * t)

    # Evolved state
    psi_t = U @ psi_0

    # Loschmidt echo
    overlap = np.vdot(psi_0, psi_t)
    L = np.abs(overlap)**2

    return L


def compute_gap_curve(instance: ProblemInstance, r_values: np.ndarray) -> np.ndarray:
    """Compute the spectral gap as a function of r."""
    gaps = []
    for r in r_values:
        H_r = construct_symmetric_hamiltonian(instance, r)
        eigenvalues = np.linalg.eigvalsh(H_r)
        gap = eigenvalues[1] - eigenvalues[0]
        gaps.append(gap)
    return np.array(gaps)


def binary_search_resonance(
    instance: ProblemInstance,
    r_low: float = 0.5,
    r_high: float = None,
    T_probe: float = None,
    tol: float = None,
    max_iters: int = 50,
    verbose: bool = False
) -> Tuple[float, List[Tuple[float, float]]]:
    """
    Binary search for the resonance point r* using Loschmidt echo.

    Returns:
        r_estimate: Estimated value of r* = A_1 + 1
        history: List of (r, L) pairs from the search
    """
    if r_high is None:
        r_high = instance.n + 1  # Conservative upper bound

    if T_probe is None:
        # Initial estimate: use g_min with crude A_1 guess
        A_1_guess = (r_low + r_high) / 2 - 1
        g_min_guess = A_1_guess / (A_1_guess + 1) * np.sqrt(instance.d_0 / instance.N)
        T_probe = np.pi / max(g_min_guess, 0.01)

    if tol is None:
        tol = instance.g_min / 10  # Target precision

    history = []

    for iteration in range(max_iters):
        r_mid = (r_low + r_high) / 2

        # Probe at r_mid
        L_mid = compute_loschmidt_echo(instance, r_mid, T_probe)
        history.append((r_mid, L_mid))

        if verbose:
            print(f"Iter {iteration}: r={r_mid:.4f}, L={L_mid:.4f}, "
                  f"r*_true={instance.r_star:.4f}")

        if r_high - r_low < tol:
            break

        if L_mid < 0.5:
            # Near resonance - need finer search
            # Probe both sides to determine direction
            L_left = compute_loschmidt_echo(instance, r_mid - (r_high - r_low)/4, T_probe)
            L_right = compute_loschmidt_echo(instance, r_mid + (r_high - r_low)/4, T_probe)

            if L_left < L_right:
                r_high = r_mid
            else:
                r_low = r_mid
        else:
            # Far from resonance - determine which side
            # Resonance has LOWER echo
            L_left = compute_loschmidt_echo(instance, r_low + (r_high - r_low)/4, T_probe)
            L_right = compute_loschmidt_echo(instance, r_high - (r_high - r_low)/4, T_probe)

            if L_left < L_right:
                r_high = r_mid
            else:
                r_low = r_mid

    r_estimate = (r_low + r_high) / 2
    return r_estimate, history


def run_validation_experiment(n: int = 10, M: int = 10, seed: int = 42):
    """
    Full validation experiment for the quantum calibration protocol.
    """
    print(f"=== Quantum Calibration Validation ===")
    print(f"n = {n} qubits, M = {M} energy levels, seed = {seed}\n")

    # Generate instance
    instance = generate_random_instance(n, M, seed)

    print(f"Problem parameters:")
    print(f"  N = 2^{n} = {instance.N}")
    print(f"  d_0 = {instance.d_0} (number of solutions)")
    print(f"  Delta = {instance.Delta:.4f} (spectral gap)")
    print(f"  A_1 = {instance.A_1:.4f}")
    print(f"  A_2 = {instance.A_2:.4f}")
    print(f"  r* = A_1 + 1 = {instance.r_star:.4f}")
    print(f"  g_min = {instance.g_min:.6f}")
    print()

    # Experiment 1: Loschmidt echo vs r
    print("Experiment 1: Loschmidt echo at T = pi/g_min")
    T_star = np.pi / instance.g_min
    r_values = np.linspace(0.5, 2*instance.r_star, 200)
    L_values = [compute_loschmidt_echo(instance, r, T_star) for r in r_values]

    # Find minimum
    min_idx = np.argmin(L_values)
    r_min_empirical = r_values[min_idx]
    L_min = L_values[min_idx]

    print(f"  Minimum echo: L = {L_min:.6f} at r = {r_min_empirical:.4f}")
    print(f"  True resonance: r* = {instance.r_star:.4f}")
    print(f"  Error: |r_min - r*| = {abs(r_min_empirical - instance.r_star):.6f}")
    print()

    # Experiment 2: Binary search
    print("Experiment 2: Binary search for resonance")
    r_estimate, history = binary_search_resonance(
        instance,
        r_low=0.5,
        r_high=instance.r_star * 2,
        T_probe=T_star,
        verbose=True
    )

    A_1_estimate = r_estimate - 1
    print(f"\nResult:")
    print(f"  Estimated r* = {r_estimate:.6f}")
    print(f"  True r* = {instance.r_star:.6f}")
    print(f"  Estimated A_1 = {A_1_estimate:.6f}")
    print(f"  True A_1 = {instance.A_1:.6f}")
    print(f"  Relative error: {abs(A_1_estimate - instance.A_1) / instance.A_1 * 100:.2f}%")
    print(f"  Iterations: {len(history)}")

    # Experiment 3: Gap curve
    print("\nExperiment 3: Spectral gap verification")
    gaps = compute_gap_curve(instance, r_values)
    gap_min_idx = np.argmin(gaps)

    print(f"  Minimum gap: g = {gaps[gap_min_idx]:.6f} at r = {r_values[gap_min_idx]:.4f}")
    print(f"  Predicted g_min = {instance.g_min:.6f}")
    print(f"  Ratio: {gaps[gap_min_idx] / instance.g_min:.3f}")

    return instance, r_values, L_values, gaps, history


def create_figures(instance, r_values, L_values, gaps, history):
    """Create visualization figures."""
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))

    # Plot 1: Loschmidt echo vs r
    ax = axes[0, 0]
    ax.plot(r_values, L_values, 'b-', linewidth=1.5)
    ax.axvline(instance.r_star, color='r', linestyle='--', label=f'r* = {instance.r_star:.3f}')
    ax.axhline(0.5, color='gray', linestyle=':', alpha=0.5)
    ax.set_xlabel('r')
    ax.set_ylabel('Loschmidt Echo L(r, T*)')
    ax.set_title('Resonance Detection via Loschmidt Echo')
    ax.legend()
    ax.grid(True, alpha=0.3)

    # Plot 2: Spectral gap vs r
    ax = axes[0, 1]
    ax.semilogy(r_values, gaps, 'g-', linewidth=1.5)
    ax.axvline(instance.r_star, color='r', linestyle='--', label=f'r* = {instance.r_star:.3f}')
    ax.axhline(instance.g_min, color='orange', linestyle=':', label=f'g_min = {instance.g_min:.4f}')
    ax.set_xlabel('r')
    ax.set_ylabel('Spectral Gap g(r)')
    ax.set_title('Avoided Crossing in r-space')
    ax.legend()
    ax.grid(True, alpha=0.3)

    # Plot 3: Binary search convergence
    ax = axes[1, 0]
    r_history = [h[0] for h in history]
    L_history = [h[1] for h in history]
    iterations = range(len(history))

    ax.plot(iterations, r_history, 'bo-', label='r estimate')
    ax.axhline(instance.r_star, color='r', linestyle='--', label=f'r* = {instance.r_star:.3f}')
    ax.set_xlabel('Iteration')
    ax.set_ylabel('r estimate')
    ax.set_title('Binary Search Convergence')
    ax.legend()
    ax.grid(True, alpha=0.3)

    # Plot 4: Echo during search
    ax = axes[1, 1]
    ax.plot(iterations, L_history, 'mo-')
    ax.axhline(0.5, color='gray', linestyle=':', alpha=0.5, label='threshold')
    ax.set_xlabel('Iteration')
    ax.set_ylabel('Loschmidt Echo')
    ax.set_title('Echo Values During Search')
    ax.legend()
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    return fig


def scaling_study(n_values: List[int] = [6, 8, 10, 12],
                  M: int = 10,
                  num_seeds: int = 5):
    """
    Study how the protocol scales with system size n.
    """
    print("\n=== Scaling Study ===\n")

    results = []

    for n in n_values:
        print(f"n = {n}...")
        errors = []
        iterations_list = []

        for seed in range(num_seeds):
            instance = generate_random_instance(n, M, seed)
            T_star = np.pi / instance.g_min

            r_estimate, history = binary_search_resonance(
                instance,
                r_low=0.5,
                r_high=instance.r_star * 2,
                T_probe=T_star,
                verbose=False
            )

            A_1_estimate = r_estimate - 1
            rel_error = abs(A_1_estimate - instance.A_1) / instance.A_1
            errors.append(rel_error)
            iterations_list.append(len(history))

        mean_error = np.mean(errors)
        std_error = np.std(errors)
        mean_iters = np.mean(iterations_list)

        results.append({
            'n': n,
            'N': 2**n,
            'mean_error': mean_error,
            'std_error': std_error,
            'mean_iterations': mean_iters
        })

        print(f"  Mean relative error: {mean_error*100:.2f}% +/- {std_error*100:.2f}%")
        print(f"  Mean iterations: {mean_iters:.1f}")

    return results


if __name__ == "__main__":
    # Run validation experiment
    instance, r_values, L_values, gaps, history = run_validation_experiment(n=10, M=10, seed=42)

    # Create figures
    fig = create_figures(instance, r_values, L_values, gaps, history)
    plt.savefig('quantum_calibration_validation.png', dpi=150, bbox_inches='tight')
    print("\nFigure saved to quantum_calibration_validation.png")

    # Run scaling study
    results = scaling_study(n_values=[6, 8, 10, 12], M=10, num_seeds=5)

    print("\n=== Summary ===")
    print("n\tN\tMean Error\tIterations")
    for r in results:
        print(f"{r['n']}\t{r['N']}\t{r['mean_error']*100:.2f}%\t\t{r['mean_iterations']:.1f}")
