# Quantum Calibration via Phase Estimation

After the Loschmidt echo approach failed numerical validation, we develop an alternative based on quantum phase estimation (QPE).


## The Core Insight

The minimum spectral gap of H(r) = -|psi_0><psi_0| + r*H_z occurs at r ≈ A_1 (validated numerically with <2% error).

If we can measure the gap g(r) for various r values, we can find A_1 by binary search for the minimum.


## QPE-Based Gap Measurement

### Standard QPE

QPE on a Hamiltonian H with eigenstate |phi_j> and eigenvalue E_j:
- Prepare |phi_j> (or close approximation)
- Apply controlled e^{-iHt} operations
- Measure to get E_j with precision delta in time O(1/delta)


### Gap Measurement Protocol

To measure the gap g(r) = E_1(r) - E_0(r):

1. Prepare |psi_0> (the initial state, easy)
2. Apply QPE with H(r) to get eigenvalue samples
3. The two dominant eigenvalues in the sample are E_0 and E_1
4. Compute g(r) = E_1 - E_0

**Issue**: |psi_0> is not an eigenstate of H(r). It's a superposition with overlap ~1/2 on each of the two lowest eigenstates (at resonance).

**Resolution**: Multiple shots. With probability ~1/2, measure E_0; with probability ~1/2, measure E_1. After O(1) shots, recover both.


### Precision Requirement

To distinguish g(r) from g(r + dr), need precision:
```
precision = |dg/dr| * dr
```

Near the minimum, |dg/dr| = 0, so we need second-order analysis:
```
g(r) = g_min + c * (r - r_min)^2 + O((r - r_min)^3)
```

To resolve the minimum to precision delta_r, need:
```
precision < c * delta_r^2
```

For the typical scaling c = O(1) and delta_r = O(g_min), we need precision O(g_min^2).


### Complexity

**Per probe**: O(1/precision) = O(1/g_min^2) evolution time
**Number of probes**: O(log(1/delta_r)) = O(n) for binary search
**Total**: O(n / g_min^2) evolution time

Substituting g_min = O(sqrt(d_0/N)):
```
Total time = O(n * N / d_0) = O(n * 2^n / d_0)
```

**This is worse than optimal AQO by a factor of sqrt(N/d_0)!**


## The Problem: QPE Requires Eigenstates

Standard QPE gives the eigenvalue of the state you feed in. To measure BOTH E_0 and E_1, you need superposition over both eigenstates.

|psi_0> IS such a superposition near the resonance (overlap ~1/2 on each). But away from resonance, one eigenvalue dominates, making gap measurement harder.


## Alternative: Variational Gap Estimation

Instead of QPE, use variational quantum eigensolver (VQE) ideas:

1. For fixed r, prepare approximate ground state |phi_0(r)> via adiabatic evolution from small r
2. Measure energy E_0 = <phi_0|H(r)|phi_0>
3. Prepare approximate first excited state |phi_1(r)> via orthogonalized search
4. Measure E_1
5. Compute g = E_1 - E_0

This is more heuristic but might work in practice.


## Honest Complexity Assessment

Let T_AQO = O(sqrt(N/d_0)) be the optimal AQO runtime.

| Method | Time to estimate A_1 | Total optimization time |
|--------|---------------------|------------------------|
| Classical | NP-hard | N/A |
| QPE-based | O(n * N/d_0) | O(n * N/d_0) + T_AQO |
| Loschmidt (failed) | ??? | ??? |

The QPE approach has complexity O(n * sqrt(N/d_0)^2) = O(n * N/d_0), which is WORSE than just running uniform-schedule AQO.


## Conclusion

**The quantum calibration idea does not provide significant speedup** in its current form.

The core issue: measuring the gap to precision g_min requires time O(1/g_min^2), which is as bad as the uncalibrated AQO runtime.

This is a **negative result**: there is no obvious way to use quantum experiments to estimate A_1 faster than just running a suboptimal AQO schedule.


## Salvage: What IS Novel Here?

1. **The gap formula for H(r)**: g_min = 2*A_1*sqrt(d_0/(A_2*N)) is new and validated.

2. **The negative result itself**: Showing that quantum calibration (at least via QPE) doesn't help is informative.

3. **The question is clarified**: The paper's hardness applies to classical computation. We've shown that naive quantum approaches don't obviously circumvent this.


## Open Question (Genuine)

Is there ANY quantum protocol that can estimate A_1 to precision delta_s = O(sqrt(d_0/N)) in time O(poly(n) * sqrt(N/d_0))?

If not, this would be a new hardness result: even quantum experiments cannot efficiently determine the optimal AQO schedule.

If yes, it would circumvent the NP-hardness.

This remains an open question worthy of further investigation.
