# Numerical Experiments Framework

This document outlines computational experiments to validate theoretical results and build intuition about adiabatic quantum optimization.


## Objectives

1. Verify spectral gap bounds from the paper
2. Study the distribution of A_1 for random problem instances
3. Measure runtime scaling empirically
4. Validate the error analysis for imprecise A_1
5. Compare AQO with alternative approaches (QAOA, uniform schedule)


## Computational Environment

### System Requirements
- Python 3.10+
- NumPy for linear algebra
- SciPy for eigensolvers and ODE integration
- Matplotlib for visualization
- Optional: QuTiP for open system dynamics

### Limitations
- Exact diagonalization: n <= 20 qubits (2^20 = 1M dimensional Hilbert space)
- Time evolution: n <= 16 qubits for dense simulation
- Memory: approximately 8*(2^n)^2 bytes for full Hamiltonian


## Experiment 1: Spectral Gap Verification

### Goal
Compare the actual spectral gap g(s) to the theoretical bounds from the paper.

### Setup
For the Hamiltonian H(s) = -(1-s)|psi_0><psi_0| + s*H_z:

1. Construct H_z as a random diagonal Hamiltonian
2. For s in linspace(0, 1, 1000), compute full spectrum
3. Extract g(s) = lambda_1(s) - lambda_0(s)
4. Compute theoretical bounds:
   - Left of crossing: g_lower(s) = (A_1/A_2)*(s*-s)/(1-s*)
   - Crossing region: g_lower(s) = g_min (constant)
   - Right of crossing: g_lower(s) = (Delta/30)*(s-s_0)/(1-s_0)

### Implementation Sketch

```python
import numpy as np
from scipy.linalg import eigh

def construct_problem_hamiltonian(n, M, seed=None):
    """
    Construct H_z with M distinct energy levels.

    Returns:
        energies: array of M distinct eigenvalues
        degeneracies: array of M degeneracies (sum to 2^n)
        H_z: diagonal of the Hamiltonian
    """
    rng = np.random.default_rng(seed)
    N = 2**n

    # Generate M distinct energy levels in [0, 1]
    energies = np.sort(rng.uniform(0, 1, M))
    energies[0] = 0  # Ground state at E_0 = 0

    # Distribute degeneracies (random multinomial)
    deg_probs = rng.dirichlet(np.ones(M))
    degeneracies = rng.multinomial(N, deg_probs)
    degeneracies = np.maximum(degeneracies, 1)  # At least 1 per level

    # Adjust to sum to N
    diff = N - degeneracies.sum()
    degeneracies[0] += diff

    # Build diagonal
    H_z_diag = np.repeat(energies, degeneracies)

    return energies, degeneracies, H_z_diag


def spectral_parameters(energies, degeneracies, N):
    """Compute A_1, A_2, A_3 from the spectrum."""
    E_0 = energies[0]
    d_0 = degeneracies[0]

    A = np.zeros(4)
    for p in range(1, 4):
        A[p] = sum(d / (E - E_0)**p for E, d in zip(energies[1:], degeneracies[1:])) / N

    return A[1], A[2], A[3], d_0


def construct_adiabatic_hamiltonian(s, H_z_diag, psi_0):
    """
    Construct H(s) in the symmetric subspace.

    Note: For efficiency, we work in the M-dimensional symmetric subspace.
    """
    # This is a dense M x M matrix
    # H(s) = -(1-s)|psi_0><psi_0| + s*diag(E_k)
    pass  # Implementation depends on representation


def compute_gap_curve(n, M, num_s=1000, seed=None):
    """
    Compute the spectral gap g(s) for s in [0, 1].
    """
    energies, degeneracies, H_z_diag = construct_problem_hamiltonian(n, M, seed)
    N = 2**n

    A_1, A_2, A_3, d_0 = spectral_parameters(energies, degeneracies, N)

    # Derived quantities
    s_star = A_1 / (A_1 + 1)
    delta_s = 2 / (A_1 + 1)**2 * np.sqrt(d_0 * A_2 / N)
    g_min = 2 * A_1 / (A_1 + 1) * np.sqrt(d_0 / (A_2 * N))
    Delta = energies[1] - energies[0]

    # Work in symmetric subspace (dimension M)
    sqrt_d = np.sqrt(degeneracies / N)

    s_vals = np.linspace(0, 1, num_s)
    gaps = np.zeros(num_s)

    for i, s in enumerate(s_vals):
        # H(s) in symmetric subspace
        H_s = s * np.diag(energies) - (1 - s) * np.outer(sqrt_d, sqrt_d)
        eigenvalues = np.linalg.eigvalsh(H_s)
        gaps[i] = eigenvalues[1] - eigenvalues[0]

    return s_vals, gaps, {
        's_star': s_star,
        'delta_s': delta_s,
        'g_min': g_min,
        'Delta': Delta,
        'A_1': A_1,
        'A_2': A_2,
        'd_0': d_0
    }


def theoretical_gap_bounds(s_vals, params):
    """Compute theoretical lower bounds on g(s)."""
    s_star = params['s_star']
    delta_s = params['delta_s']
    g_min = params['g_min']
    Delta = params['Delta']
    A_1 = params['A_1']
    A_2 = params['A_2']

    bounds = np.zeros_like(s_vals)

    for i, s in enumerate(s_vals):
        if s < s_star - delta_s:
            # Left of crossing
            bounds[i] = (A_1 / A_2) * (s_star - s) / (1 - s_star)
        elif s > s_star + delta_s:
            # Right of crossing
            k = 0.25
            a = 4 * k**2 * Delta / 3
            s_0 = s_star - k * g_min * (1 - s_star) / (a - k * g_min)
            bounds[i] = Delta / 30 * (s - s_0) / (1 - s_0)
        else:
            # In crossing region
            bounds[i] = 0.8 * g_min  # Approximate

    return bounds
```

### Expected Output
- Plot showing g(s) vs theoretical bounds
- Table of tightness ratios: g_actual(s) / g_bound(s) for various s


## Experiment 2: Distribution of A_1

### Goal
Understand how A_1 varies across random instances of specific problem classes.

### Problem Classes

**Class 1: Random Ising Model**
```
H_sigma = sum_{i<j} J_ij * sigma_z^i * sigma_z^j + sum_i h_i * sigma_z^i
```
where J_ij, h_i are uniform in [-1, 1].

**Class 2: MAX-CUT**
For a random graph G = (V, E):
```
H_cut = (1/2) * sum_{(i,j) in E} (I - sigma_z^i * sigma_z^j)
```

**Class 3: Random k-SAT**
Encode a random k-SAT formula as an Ising Hamiltonian using the standard reduction.

### Implementation Sketch

```python
def random_ising(n, density=0.5, seed=None):
    """Generate random Ising Hamiltonian (diagonal in computational basis)."""
    rng = np.random.default_rng(seed)
    N = 2**n

    # Random couplings
    J = np.zeros((n, n))
    h = rng.uniform(-1, 1, n)
    for i in range(n):
        for j in range(i+1, n):
            if rng.random() < density:
                J[i, j] = rng.uniform(-1, 1)
                J[j, i] = J[i, j]

    # Compute diagonal
    H_diag = np.zeros(N)
    for z in range(N):
        bits = [(z >> i) & 1 for i in range(n)]
        spins = [2*b - 1 for b in bits]  # 0 -> -1, 1 -> +1

        energy = sum(h[i] * spins[i] for i in range(n))
        energy += sum(J[i,j] * spins[i] * spins[j] for i in range(n) for j in range(i+1, n))
        H_diag[z] = energy

    return H_diag


def compute_A1_from_diagonal(H_diag):
    """Compute A_1 from the diagonal of H_z."""
    N = len(H_diag)

    # Find distinct energy levels
    unique_energies = np.unique(H_diag)
    M = len(unique_energies)

    E_0 = unique_energies[0]
    d_0 = np.sum(H_diag == E_0)

    A_1 = 0
    for E in unique_energies[1:]:
        d = np.sum(H_diag == E)
        A_1 += d / (E - E_0)
    A_1 /= N

    return A_1, d_0, M


def sample_A1_distribution(n, num_samples, problem_class='ising', **kwargs):
    """Sample the distribution of A_1 across random instances."""
    A1_values = []
    d0_values = []

    for seed in range(num_samples):
        if problem_class == 'ising':
            H_diag = random_ising(n, seed=seed, **kwargs)
        elif problem_class == 'maxcut':
            H_diag = random_maxcut(n, seed=seed, **kwargs)
        # Add other classes...

        # Normalize to [0, 1]
        H_diag = H_diag - H_diag.min()
        if H_diag.max() > 0:
            H_diag = H_diag / H_diag.max()

        A_1, d_0, M = compute_A1_from_diagonal(H_diag)
        A1_values.append(A_1)
        d0_values.append(d_0)

    return np.array(A1_values), np.array(d0_values)
```

### Expected Output
- Histogram of A_1 values
- Statistics: mean, std, min, max
- Correlation between A_1 and d_0 (number of solutions)


## Experiment 3: Runtime Scaling

### Goal
Measure empirical runtime of AQO vs problem size n.

### Approach
Simulate the adiabatic evolution via Schrodinger equation:
```
i * d|psi>/dt = H(s(t)) |psi>
```
where s(t) is the local schedule.

### Implementation Sketch

```python
from scipy.integrate import solve_ivp

def simulate_aqo(H_z_diag, T, num_steps=1000, schedule='local'):
    """
    Simulate adiabatic evolution.

    Args:
        H_z_diag: diagonal of problem Hamiltonian
        T: total evolution time
        num_steps: number of time steps
        schedule: 'local' (optimal) or 'linear' (uniform)

    Returns:
        fidelity: overlap with ground state
    """
    N = len(H_z_diag)
    n = int(np.log2(N))

    # Initial state |psi_0> = |+>^n
    psi_0 = np.ones(N) / np.sqrt(N)

    # Ground state of H_z
    E_0 = H_z_diag.min()
    ground_indices = np.where(H_z_diag == E_0)[0]
    d_0 = len(ground_indices)
    psi_target = np.zeros(N)
    psi_target[ground_indices] = 1 / np.sqrt(d_0)

    # Schedule function s(t)
    if schedule == 'linear':
        s_func = lambda t: t / T
    else:
        # Local schedule requires precomputed gap curve
        # s'(t) = c * g(s)^2
        # For now, use linear as placeholder
        s_func = lambda t: t / T

    def schrodinger_rhs(t, psi_flat):
        psi = psi_flat[:N] + 1j * psi_flat[N:]
        s = s_func(t)

        # H(s)|psi> = -(1-s)<psi_0|psi>|psi_0> + s*H_z|psi>
        overlap = np.dot(psi_0, psi)
        H_psi = -(1 - s) * overlap * psi_0 + s * H_z_diag * psi

        # d|psi>/dt = -i * H|psi>
        dpsi_dt = -1j * H_psi

        return np.concatenate([dpsi_dt.real, dpsi_dt.imag])

    # Initial condition
    psi_init = np.concatenate([psi_0.real, psi_0.imag])

    # Solve ODE
    sol = solve_ivp(schrodinger_rhs, [0, T], psi_init,
                    method='RK45', t_eval=[T])

    psi_final = sol.y[:N, -1] + 1j * sol.y[N:, -1]
    fidelity = np.abs(np.dot(psi_target.conj(), psi_final))**2

    return fidelity


def find_runtime(H_z_diag, target_fidelity=0.9, schedule='local'):
    """
    Binary search for runtime T to achieve target fidelity.
    """
    T_low, T_high = 1, 1e6

    while T_high - T_low > 1:
        T_mid = (T_low + T_high) / 2
        fid = simulate_aqo(H_z_diag, T_mid, schedule=schedule)

        if fid >= target_fidelity:
            T_high = T_mid
        else:
            T_low = T_mid

    return T_high
```

### Expected Output
- Plot of runtime vs n for various problem classes
- Comparison: local schedule vs uniform schedule
- Verification of T = O(sqrt(N/d_0)) scaling


## Experiment 4: Imprecise A_1 Validation

### Goal
Test the error analysis predictions about performance degradation with imprecise A_1.

### Approach
1. Compute exact A_1
2. Perturb to A_1_est = A_1 + delta
3. Construct schedule using A_1_est
4. Simulate AQO and measure fidelity
5. Vary delta and runtime to map the fidelity landscape

### Implementation Sketch

```python
def experiment_imprecise_A1(n, num_deltas=20, num_runtimes=20, seed=0):
    """
    Map fidelity as a function of A_1 error and runtime.
    """
    H_diag = random_ising(n, seed=seed)

    # Normalize
    H_diag = H_diag - H_diag.min()
    H_diag = H_diag / H_diag.max()

    A_1_exact, d_0, M = compute_A1_from_diagonal(H_diag)

    # Delta values: logarithmically spaced from 10^-4 to 10^0
    deltas = np.logspace(-4, 0, num_deltas)

    # Runtime values: from 1 to optimal*10
    T_optimal = estimate_optimal_runtime(H_diag)  # Helper function
    runtimes = np.logspace(0, np.log10(T_optimal * 10), num_runtimes)

    fidelities = np.zeros((num_deltas, num_runtimes))

    for i, delta in enumerate(deltas):
        A_1_est = A_1_exact + delta
        # Construct schedule with A_1_est

        for j, T in enumerate(runtimes):
            fidelities[i, j] = simulate_aqo_with_schedule(H_diag, T, A_1_est)

    return deltas, runtimes, fidelities
```

### Expected Output
- Heatmap: fidelity(delta, T)
- Contour lines showing iso-fidelity curves
- Comparison to theoretical predictions


## Experiment 5: Comparison with QAOA

### Goal
Compare AQO performance to QAOA for the same problem instances.

### QAOA Implementation

```python
def qaoa_circuit(H_diag, p, betas, gammas):
    """
    Simulate p-layer QAOA.

    |psi_p> = prod_{l=1}^p [e^{-i*beta_l*H_mixer} * e^{-i*gamma_l*H_problem}] |+>
    """
    N = len(H_diag)
    n = int(np.log2(N))

    # Initial state
    psi = np.ones(N) / np.sqrt(N)

    for l in range(p):
        # Apply e^{-i*gamma_l*H_problem}
        psi = np.exp(-1j * gammas[l] * H_diag) * psi

        # Apply e^{-i*beta_l*H_mixer}
        # H_mixer = sum_i X_i, which acts on each qubit
        # In computational basis: mixing couples |...0...> <-> |...1...>
        psi = apply_mixer(psi, n, betas[l])

    return psi


def apply_mixer(psi, n, beta):
    """Apply e^{-i*beta*sum_i X_i} via tensor structure."""
    # e^{-i*beta*X} = cos(beta)*I - i*sin(beta)*X
    c, s = np.cos(beta), np.sin(beta)

    psi_new = psi.copy()
    for i in range(n):
        # Apply to qubit i
        mask = 1 << i
        for z in range(len(psi)):
            z_flipped = z ^ mask
            if z < z_flipped:
                a, b = psi_new[z], psi_new[z_flipped]
                psi_new[z] = c * a - 1j * s * b
                psi_new[z_flipped] = c * b - 1j * s * a

    return psi_new


def optimize_qaoa(H_diag, p, num_iters=100):
    """Find optimal QAOA parameters."""
    from scipy.optimize import minimize

    def cost(params):
        betas = params[:p]
        gammas = params[p:]
        psi = qaoa_circuit(H_diag, p, betas, gammas)
        return np.real(np.dot(psi.conj(), H_diag * psi))

    # Random initial parameters
    x0 = np.random.uniform(-np.pi, np.pi, 2*p)
    result = minimize(cost, x0, method='COBYLA')

    return result.fun, result.x
```

### Expected Output
- For fixed problem instance: AQO fidelity vs QAOA fidelity (varying p)
- Runtime comparison accounting for optimization cost
- Instances where one method outperforms the other


## Data Storage and Reproducibility

### File Structure
```
src/experiments/
    data/
        spectral_gaps/
            n{n}_M{M}_seed{seed}.npz
        A1_distributions/
            {problem_class}_n{n}_samples{num}.npz
        runtime_scaling/
            {schedule}_{problem_class}.npz
        imprecise_A1/
            n{n}_seed{seed}.npz
        qaoa_comparison/
            p{p}_{problem_class}_n{n}.npz
```

### Metadata
Each .npz file should include:
- Timestamp
- Code version/git hash
- All parameters used
- Random seeds


## Execution Plan

### Phase 1: Validation (Week 1)
- Implement spectral gap computation
- Verify against paper examples
- Ensure code is correct before scaling

### Phase 2: Data Collection (Weeks 2-3)
- Run all experiments for n = 8, 10, 12, 14
- Store results systematically
- Begin visualization

### Phase 3: Analysis (Week 4)
- Statistical analysis of results
- Compare to theoretical predictions
- Identify interesting phenomena

### Phase 4: Extension (Weeks 5-6)
- Push to larger n if feasible
- Investigate anomalies
- Prepare figures for thesis/paper


## Notes on Optimization

### Symmetric Subspace
For the exact spectrum, work in the M-dimensional symmetric subspace instead of the full 2^n space. This reduces diagonalization from O(2^{3n}) to O(M^3).

### Sparse Methods
The initial Hamiltonian -|psi_0><psi_0| is rank-1. Use Sherman-Morrison or Lanczos methods instead of full diagonalization.

### Parallelization
Distribution of A_1 experiment is embarrassingly parallel. Use multiprocessing for speedup.

### Numerical Precision
For large n, use extended precision (np.longdouble) when computing A_1 to avoid overflow in degeneracy sums.
