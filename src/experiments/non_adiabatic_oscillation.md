# Non-Adiabatic Oscillation Algorithm: Self-Calibration via Quantum Experiments

This document develops Proposal 5 from the research proposals. The goal is to explore whether quantum experiments can estimate A_1 more efficiently than classical computation, thereby circumventing the NP-hardness barrier.


## Background: The Continuous-Time Algorithm

The paper's discussion section mentions an alternative to AQO: evolve under the time-independent Hamiltonian

```
H_r = -|psi_0><psi_0| + r * H_z
```

where r is a parameter. When r is chosen appropriately, the system exhibits oscillatory behavior between |psi_0> and the ground state of H_z.


## Physics of the Oscillation

### Resonance Condition

The key insight is that for r close to A_1, there is a near-degeneracy between two states that have large overlap with both |psi_0> and the target ground state.

In the symmetric subspace, H_r has eigenvalues determined by:
```
1 = (1/N) * sum_k d_k / (r*E_k - lambda)
```

When r = A_1 + 1, the ground state eigenvalue crosses through lambda = 0 (similar to the avoided crossing at s* = A_1/(A_1+1)).


### Two-Level Approximation

Near the resonance, the dynamics are approximately governed by a 2x2 effective Hamiltonian:
```
H_eff = [   E_+        g_eff/2  ]
        [ g_eff/2       E_-     ]
```

where:
- E_+ and E_- are the two lowest energy levels of H_r
- g_eff is the effective coupling (related to g_min)

The oscillation frequency is:
```
Omega = sqrt((E_+ - E_-)^2 + g_eff^2)
```


### Overlap Dynamics

Starting from |psi_0>, the overlap with the ground state of H_z oscillates as:
```
F(t) = |<ground|e^{-i*H_r*t}|psi_0>|^2 = sin^2(Omega*t/2) * (4*g_eff^2 / Omega^2)
```

Maximum amplitude occurs when E_+ = E_-, i.e., at the resonance.


## The Self-Calibration Idea

### Key Observation

The oscillation behavior depends sensitively on r:
- r << A_1 + 1: No resonance, F(t) stays small
- r = A_1 + 1: Maximum amplitude oscillation
- r >> A_1 + 1: No resonance, F(t) stays small

This creates a "signature" that identifies the correct value of r.


### Algorithm Sketch

```
Algorithm: Self-Calibrating Continuous-Time Optimization

Input: H_z (problem Hamiltonian), epsilon (error tolerance)
Output: Approximate ground state of H_z

1. Binary search for resonance:
   a. Initialize r_low = 0, r_high = n (upper bound on A_1 + 1)
   b. While r_high - r_low > delta_r:
      i.   r_mid = (r_low + r_high) / 2
      ii.  Perform quantum evolution under H_{r_mid} for time T_probe
      iii. Measure overlap with |psi_0> (or some observable)
      iv.  Based on measurement, update r_low or r_high

2. Use r* from step 1 to run full oscillation
   a. Evolve under H_{r*} for time T = pi/(2*Omega)
   b. Measure in computational basis

3. Return measured state
```


### Key Questions

Q1: What is T_probe - how long must each probe evolution be?

Q2: How many iterations of binary search are needed?

Q3: What observable should be measured to identify resonance?


## Detailed Analysis

### Observable for Resonance Detection

**Option A: Ground state overlap**
Measure F(t) = |<ground|psi(t)>|^2 directly.
Problem: requires knowing the ground state.

**Option B: Loschmidt echo**
Measure L(t) = |<psi_0|psi(t)>|^2 = |<psi_0|e^{-i*H_r*t}|psi_0>|^2

At resonance, L(t) oscillates with large amplitude.
Away from resonance, L(t) stays close to 1.

This is measurable without knowing the ground state!

**Option C: Energy variance**
Measure <H_z^2> - <H_z>^2 during evolution.
At resonance, this should show distinctive behavior.


### Loschmidt Echo Analysis

The Loschmidt echo for H_r = -|psi_0><psi_0| + r*H_z is:
```
L(t) = |<psi_0|e^{-i*H_r*t}|psi_0>|^2
```

In the symmetric subspace, |psi_0> = sum_k sqrt(d_k/N) |k>.

Using the spectral decomposition H_r = sum_j E_j |phi_j><phi_j|:
```
L(t) = |sum_j |<psi_0|phi_j>|^2 * e^{-i*E_j*t}|^2
```


### Near-Resonance Behavior

When r = A_1 + 1 + epsilon for small epsilon:

The two lowest eigenvalues are approximately:
```
E_0 = -g_eff/2 * sqrt(1 + (epsilon/g_eff)^2)
E_1 = +g_eff/2 * sqrt(1 + (epsilon/g_eff)^2)
```

The overlaps are:
```
|<psi_0|phi_0>|^2 approx 1/2 + epsilon/(2*g_eff*sqrt(...))
|<psi_0|phi_1>|^2 approx 1/2 - epsilon/(2*g_eff*sqrt(...))
```

At exact resonance (epsilon = 0):
```
L(t) = |1/2 * e^{i*g_eff*t/2} + 1/2 * e^{-i*g_eff*t/2}|^2 = cos^2(g_eff*t/2)
```

Full oscillation from L = 1 to L = 0 to L = 1 with period 2*pi/g_eff.


### Off-Resonance Behavior

When |epsilon| >> g_eff:

One eigenstate dominates:
```
L(t) approx 1 - small oscillation
```

The echo barely dips below 1.


### Binary Search Protocol

The Loschmidt echo provides a clear signature:
- At resonance: L(T_probe) can reach close to 0
- Off resonance: L(T_probe) stays close to 1

**Decision rule**: For probe time T_probe = pi/g_eff:
- If L(T_probe) < 0.5: resonance is near r_mid
- If L(T_probe) > 0.5: resonance is away from r_mid (need to determine which side)


### Determining Direction

To know whether to search left or right, measure L(t) for two values:
- r_mid - delta and r_mid + delta

The one with smaller L(T_probe) is closer to resonance.


## Complexity Analysis

### Number of Binary Search Iterations

To achieve precision delta_r in r, we need O(log(n/delta_r)) iterations.

For optimal AQO, we need delta_r such that the induced error in s* is O(delta_s).
```
delta_r approx delta_s * (A_1 + 1) = O(sqrt(d_0*A_2/N))
```

This is exponentially small, so we need O(n) iterations.


### Probe Time per Iteration

Each probe requires evolution time T_probe = O(1/g_eff) = O(sqrt(N*A_2/d_0) / A_1).

For typical Ising Hamiltonians: T_probe = O(sqrt(N/d_0)).


### Total Quantum Complexity

```
Total time = (# iterations) * T_probe = O(n * sqrt(N/d_0))
```

Compare to AQO optimal runtime: T_AQO = O(sqrt(N/d_0)).

The self-calibration adds a factor of O(n) overhead!


### Classical vs Quantum Calibration

**Classical**: Computing A_1 to precision delta_r is NP-hard for delta_r = 1/poly(n).
Cannot do it in time O(2^{n/2}) unless NP subset of BQP.

**Quantum**: O(n) iterations of O(2^{n/2}) evolution = O(n * 2^{n/2}).

The quantum calibration adds only polynomial overhead to the optimal runtime.


## Main Result (Theorem Sketch)

**Theorem**: There exists a quantum algorithm that:
1. Does not require prior knowledge of A_1
2. Achieves ground state fidelity 1 - epsilon
3. Runs in total time O(n * sqrt(N/d_0) * log(1/epsilon))

**Proof sketch**:
- Use Loschmidt echo binary search to find r* = A_1 + 1 to precision O(g_eff)
- Run oscillation evolution for time T = O(sqrt(N/d_0))
- Apply amplitude amplification to boost success probability

This circumvents the classical hardness by using quantum experiments for calibration.


## Challenges and Open Questions

### Challenge 1: Measurement Noise

Real quantum measurements have finite shot noise. To distinguish L(T) = 0.3 from L(T) = 0.7, we need O(1/epsilon^2) shots.

This adds an O(1/epsilon^2) multiplicative factor to the complexity.


### Challenge 2: Decoherence

If decoherence time T2 < T_probe, the oscillation is damped and the binary search fails.

This sets a constraint: T2 > O(sqrt(N/d_0)).


### Challenge 3: Higher Excited States

The two-level approximation neglects higher excited states. Their contribution can cause additional oscillation frequencies that complicate the signal.


### Challenge 4: Unique Ground State

For d_0 = 1 (unique solution), the oscillation amplitude is largest. For d_0 >> 1, amplitude decreases as sqrt(d_0/N), making detection harder.


## Connection to Quantum Phase Estimation

The binary search is reminiscent of quantum phase estimation (QPE):
- QPE extracts eigenvalue information via controlled evolution
- Our method extracts resonance information via Loschmidt echo

Could QPE provide a more efficient calibration?


### QPE-Based Alternative

Apply QPE to H_r with |psi_0> as input:
- If r is far from resonance, |psi_0> is close to an eigenstate
- If r is at resonance, |psi_0> is a superposition of two eigenstates with eigenvalue difference O(g_eff)

QPE with precision delta requires evolution time O(1/delta). To resolve the g_eff gap, we need T = O(sqrt(N/d_0)), same as the Loschmidt approach.


## Experimental Considerations

### Required Capabilities

1. Prepare |psi_0> = |+>^n (easy)
2. Implement H_z = diagonal Hamiltonian (depends on encoding)
3. Implement H_r = -|psi_0><psi_0| + r*H_z (challenge: projector term)
4. Measure in computational basis (easy)


### Implementing the Projector Term

The term -|psi_0><psi_0| is non-local. Implementation options:

**Option A: Ancilla-assisted**
Add an ancilla qubit and implement:
```
H' = -|0><0|_anc tensor |psi_0><psi_0| + I_anc tensor r*H_z
```

Initialize ancilla in |+>, measure at the end.

**Option B: Trotterization**
Decompose evolution into:
```
e^{-i*H_r*dt} approx e^{i*dt*|psi_0><psi_0|} * e^{-i*r*dt*H_z}
```

The first term is a reflection about |psi_0>, implementable via:
```
e^{i*theta*|psi_0><psi_0|} = I + (e^{i*theta} - 1)|psi_0><psi_0|
                          = 2|psi_0><psi_0| - I  (for theta = pi)
```

This is just the Grover diffusion operator!


### Connection to Grover's Algorithm

The oscillation algorithm is structurally similar to Grover:
- Grover: alternate between oracle and diffusion
- Oscillation: evolve under H_r which combines oracle-like H_z and diffusion-like |psi_0><psi_0|

The continuous-time version smoothly interpolates, potentially with better noise resilience.


## Summary of Novel Contributions

1. **Self-calibrating algorithm**: First quantum algorithm for optimization that finds its own optimal parameters via quantum experiments.

2. **Circumventing classical hardness**: Demonstrates that quantum experiments can extract information (A_1) that is NP-hard to compute classically.

3. **Loschmidt echo protocol**: Practical protocol for resonance detection without knowing the target state.

4. **Complexity analysis**: Total runtime O(n * sqrt(N/d_0)), only polynomial overhead over optimal AQO.


## Next Steps

1. **Rigorous proof**: Formalize the two-level approximation and bound errors from higher levels.

2. **Numerical validation**: Simulate the binary search protocol for small n and verify convergence.

3. **Noise analysis**: Incorporate realistic noise models and determine tolerance thresholds.

4. **Comparison**: Benchmark against AQO with imprecise A_1 from the error analysis.


## Potential Paper Outline

**Title**: Self-Calibrating Quantum Optimization via Continuous-Time Evolution

**Abstract**: We present a quantum algorithm for ground state preparation that does not require prior knowledge of spectral parameters. By using quantum experiments (Loschmidt echo measurements) to identify a resonance condition, the algorithm self-calibrates before running the main optimization. The total runtime is O(n * sqrt(N/d_0)), achieving near-optimal complexity without solving the NP-hard classical preprocessing problem.

**Sections**:
1. Introduction: AQO hardness barrier, motivation for self-calibration
2. Continuous-time oscillation algorithm: Physics and analysis
3. Self-calibration protocol: Loschmidt echo and binary search
4. Complexity analysis: Runtime bounds, comparison to AQO
5. Numerical experiments: Validation for small instances
6. Discussion: Noise tolerance, experimental feasibility
