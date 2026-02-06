# Structured Tractability: When is A_1 Easy?

## Problem Statement

The paper proves A_1 is #P-hard to compute for general Hamiltonians (even
approximation to constant factor is NP-hard). It leaves open the question: are there
interesting problem classes where A_1 can be computed efficiently?

**Central Question**: Characterize the boundary between hard and easy A_1 computation.
The key insight is that A_1 hardness comes from *counting complexity* (computing
degeneracies d_k), not optimization hardness. Simple spectra give easy A_1; complex
spectra give hard A_1. NP-hard problems can have simple spectra.


## Why Novel

The paper proves hardness for general Hamiltonians but says:
> "We leave open the question of whether this limitation may be overcome... by a
> suitable modification of the adiabatic Hamiltonian... so that the position of the
> avoided crossing does not depend on the spectrum of the problem Hamiltonian."

This experiment resolves the three natural conjectures about the tractability boundary
and identifies the precise structural property (spectral complexity) that controls it.


## Conjectures and Resolutions

### Conjecture 1 (Unique Solution Tractability) -- FALSE

**Conjecture.** For d_0 = 1 and Delta >= 1/poly(n): A_1 = 1/Delta + O(1).

**Resolution.** Counterexample with three energy levels: E_0=0 (d_0=1), E_1=1/n
(d_1=1), E_2=1 (d_2=N-2). Then A_1 -> 1 while 1/Delta -> infinity. The tail of N-2
strings at energy 1 dominates the single string at the gap edge. The counterexample
is valid but contrived; whether the conjecture fails for natural problem spectra
remains open. See Proposition 1 in proof.md.

### Conjecture 2 (Bounded Degeneracy) -- VACUOUS

**Conjecture.** If d_k <= poly(n) for all k >= 1 and M <= poly(n), then A_1 is
computable in poly(n) time.

**Resolution.** Technically true but uninteresting. The hypothesis forces
d_0 >= N - poly(n)^2, so d_0/N -> 1 (for sufficiently large n) and the problem is
trivially solvable by random sampling. See Proposition 2 in proof.md.

### Conjecture 3 (Structure-Hardness Tradeoff) -- FALSE IN BOTH DIRECTIONS

**Conjecture.** A_1 is efficiently computable iff the optimization problem is in P.

**Resolution.** (a) 2-SAT is in P but #2-SAT is #P-complete, so A_1 for 2-SAT
clause-violation Hamiltonians is #P-hard. (b) Grover search requires
Omega(sqrt(N/d_0)) queries, but A_1 = (N-d_0)/N is O(1)-computable given d_0 (promise
model). Optimization hardness and A_1 hardness are independent because A_1 tracks
counting complexity while optimization tracks decision complexity. See Proposition 6.


## Results

**Status**: RESOLVED

### Complete Results

| Result | Statement | Status |
|--------|-----------|--------|
| Prop 1 | Conjecture 1 is false (counterexample) | Proved |
| Prop 2 | Conjecture 2 is vacuous | Proved |
| Prop 3 | Sufficient condition: poly levels + known d_k + known E_k | Proved |
| Prop 4 | CSPs with #P-hard counting: A_1 is #P-hard | Proved |
| Prop 5 | Grover (promise model): hard search + O(1) A_1 | Proved |
| Prop 6 | Conjecture 3 fails both directions | Proved |
| Remark | Planted instances: A_1 as O(n)-bit advice | Observation |
| Prop 7 | Hamming distance: A_1 = f(n) only | Proved |

### Key Conclusions

A_1 tractability is determined by spectral/counting complexity, not optimization
hardness. Proposition 3 gives sufficient conditions (poly levels + known d_k + known
E_k), but these are not necessary: the Grover Hamiltonian has easy A_1 without
individually known d_k (the sum collapses when M=2).

The Grover Hamiltonian is the canonical "sweet spot": hard search with trivially
computable A_1 in the promise model. But this relies on knowing d_0. Without that
promise, even Grover's A_1 requires Theta(sqrt(N)) quantum queries to determine.


## Remaining Open Questions

1. **Necessary conditions for easy A_1.** Proposition 3 gives sufficient conditions.
   What is the weakest structural assumption that makes A_1 tractable? The Grover
   case shows individual d_k need not be known if the sum collapses.

2. **Natural NP-hard problems with simple spectra.** Grover is the only known example
   of a hard search problem with easy A_1. Do natural combinatorial NP-hard problems
   (not oracle search) ever have simple enough spectra?

3. **Approximate A_1.** The paper shows A_1 computation is #P-hard for CSPs with hard counting. Perhaps
   constant-factor approximation suffices for near-optimal schedules.

4. **Quantum computation of A_1.** Phase estimation on H_z could estimate A_1
   quantumly. Classical hardness does not rule out efficient quantum computation.


## Connection to Other Experiments

- Supersedes the original 03_structured_tractability
- Proposition 3 connects to 07 (partial information): knowing partial spectrum
  contributes to the sufficient condition for A_1 tractability
- Proposition 4 strengthens the hardness barrier narrative for CSP-based AQO


## Numerical Verification

All claims verified in `lib/verify_a1.py`. Key checks:
- Grover N=4, d_0=1: A_1 = 3/4, s* = 3/7
- Grover N=4, d_0=2: A_1 = 1/2, s* = 1/3
- Proposition 1 (n=4, N=16): A_1 = 9/8 = 1.125, vs 1/Delta = 4
- Hamming n=4: A_1 = 103/192 = 0.537
- Hamming asymptotic: A_1 * n/2 -> 1 (verified to n=128)


## References

1. Original paper -- Section 4 (hardness), Theorem 12
2. Valiant 1979 -- #P-completeness of counting
3. Bennett, Bernstein, Brassard, Vazirani 1997 -- query lower bounds
4. Grover 1996 -- quantum search


## Status

**Phase**: Resolved

All conjectures resolved. All results are propositions (no unjustified "theorem"
labels). Sufficient conditions established; necessary conditions remain open. Numerics
verified. Honest about caveats (contrived counterexample, promise model for Grover).
