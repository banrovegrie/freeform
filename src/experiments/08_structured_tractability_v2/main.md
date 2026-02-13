# Structured Tractability: When is $A_1$ Easy?

## Problem Statement

The paper proves $A_1$ is #P-hard to compute for general Hamiltonians (even
approximation to constant factor is NP-hard). It leaves open the question: are there
interesting problem classes where $A_1$ can be computed efficiently?

**Central Question**: Characterize the boundary between hard and easy $A_1$ computation.
The key insight is that $A_1$ hardness comes from *counting complexity* (computing
degeneracies $d_k$), not optimization hardness. Simple spectra give easy $A_1$; complex
spectra give hard $A_1$. NP-hard problems can have simple spectra.


## Why Novel

The paper proves hardness for general Hamiltonians but says:
> "We leave open the question of whether this limitation may be overcome... by a
> suitable modification of the adiabatic Hamiltonian... so that the position of the
> avoided crossing does not depend on the spectrum of the problem Hamiltonian."

This experiment resolves the three natural conjectures about the tractability boundary
and identifies the precise structural property (spectral complexity) that controls it.

**What is new vs the paper and Guo-An (2025).**
- The paper's hardness results show $A_1$ is hard in the worst case. This experiment
  adds *positive structure*: $A_1$ can be computed exactly for bounded-treewidth local
  energy functions via a partition-function DP (Prop 8) and approximated via
  partition-function evaluation over a temperature window (Props 10-15).
- Propositions 10-13 make a new bridge explicit: additive approximation of $A_1$ can
  avoid computing $d_0$ (the counting-hard quantity) by anchoring at $Z(\varepsilon)$
  or $Z(B)$, turning "estimate $A_1$" into "estimate $Z$ on a grid" with explicit
  truncation/quadrature error bounds.
- Proposition 15 adds a new boundary theorem: the bridge is one-way. Even exact
  $A_1$ with matched coarse drivers $(\rho_0,\Delta_{\min},R)$ does not determine
  low-temperature $Z(\beta)$.
- Guo-An (2025) studies schedule optimality under gap-measure conditions. These
  results are complementary: they take the gap profile as a given object, while this
  experiment isolates and formalizes the *information* needed to obtain that profile
  (via $A_1$) and how structure/promises can make it tractable (or not) at different
  precision regimes.


## Conjectures and Resolutions

### Conjecture 1 (Unique Solution Tractability) -- FALSE

**Conjecture.** For $d_0 = 1$ and $\Delta \geq 1/\text{poly}(n)$: $A_1 = 1/\Delta + O(1)$.

**Resolution.** Counterexample with three energy levels: $E_0 = 0$ ($d_0 = 1$), $E_1 = 1/n$
($d_1 = 1$), $E_2 = 1$ ($d_2 = N - 2$). Then $A_1 \to 1$ while $1/\Delta \to \infty$. The tail of $N - 2$
strings at energy 1 dominates the single string at the gap edge. The counterexample
is valid but contrived; whether the conjecture fails for natural problem spectra
remains open. See Proposition 1 in proof.md.

### Conjecture 2 (Bounded Degeneracy) -- VACUOUS

**Conjecture.** If $d_k \leq \text{poly}(n)$ for all $k \geq 1$ and $M \leq \text{poly}(n)$, then $A_1$ is
computable in $\text{poly}(n)$ time.

**Resolution.** Technically true but uninteresting. The hypothesis forces
$d_0 \geq N - \text{poly}(n)^2$, so $d_0/N \to 1$ (for sufficiently large n) and the problem is
trivially solvable by random sampling. See Proposition 2 in proof.md.

### Conjecture 3 (Structure-Hardness Tradeoff) -- FALSE IN BOTH DIRECTIONS

**Conjecture.** $A_1$ is efficiently computable iff the optimization problem is in P.

**Resolution.** (a) 2-SAT is in P but #2-SAT is #P-complete, so $A_1$ for 2-SAT
clause-violation Hamiltonians is #P-hard. (b) Grover search requires
$\Omega(\sqrt{N/d_0})$ queries, but $A_1 = (N - d_0)/N$ is $O(1)$-computable given $d_0$ (promise
model). Optimization hardness and $A_1$ hardness are independent because $A_1$ tracks
counting complexity while optimization tracks decision complexity. See Proposition 6.


## Results

**Status**: RESOLVED

### Complete Results

| Result | Statement | Status |
|--------|-----------|--------|
| Prop 1 | Conjecture 1 is false (counterexample) | Proved |
| Prop 2 | Conjecture 2 is vacuous | Proved |
| Prop 3 | Sufficient condition: poly levels + known $d_k$ + known $E_k$ | Proved |
| Prop 4 | CSPs with #P-hard counting: $A_1$ is #P-hard | Proved |
| Prop 5 | Grover (promise model): hard search + $O(1)$ $A_1$ | Proved |
| Prop 6 | Conjecture 3 fails both directions | Proved |
| Remark | Planted instances: $A_1$ as $O(n)$-bit advice | Observation |
| Prop 7 | Hamming distance: $A_1 = f(n)$ only | Proved |
| Prop 8 | Bounded treewidth: exact $A_1$ via partition-function DP | Proved |
| Prop 9 | Coarse $A_1$ approximation is easy when $E_0$ is known | Proved |
| Prop 10 | Approximate $A_1$ from $Z(t)$ without $d_0$ | Proved |
| Prop 11 | Laplace proxy: approximate $A_1$ from $Z(\beta)$ without $d_0$ | Proved |
| Prop 12 | Oracle reduction: approximate $Z$ on a grid $\Rightarrow$ additive $A_1$ | Proved |
| Prop 13 | Ferromagnetic Ising + multiplicative $Z$ approximation $\Rightarrow$ additive $A_1$ (explicit error drivers) | Proved |
| Prop 14 | Schedule-level $A_1$ sufficient condition: $\eta_{A_1} \leq \min\{(1 + A_1)/2, \sqrt{d_0 A_2/N}\}$; worst-case target $\Theta(2^{-n/2})$ | Proved |
| Prop 15 | Reverse-bridge obstruction: exact $A_1$ does not determine low-temperature $Z(\beta)$ even with matched $(\rho_0, \Delta_{\min}, R)$ | Proved |

### Key Conclusions

$A_1$ tractability is determined by spectral/counting complexity, not optimization
hardness. Proposition 3 gives sufficient conditions (poly levels + known $d_k$ + known
$E_k$), but these are not necessary: the Grover Hamiltonian has easy $A_1$ without
individually known $d_k$ (the sum collapses when $M = 2$).

The Grover Hamiltonian is the canonical "sweet spot": hard search with trivially
computable $A_1$ in the promise model. But this relies on knowing $d_0$. Without that
promise, even Grover's $A_1$ requires $\Theta(\sqrt{N})$ quantum queries to determine.

The partition-function bridge is now family-level concrete: for ferromagnetic Ising
with consistent fields, multiplicative approximation of $Z$ on a temperature window
implies additive approximation of $A_1$ with explicit dependence on energy scale $R$,
minimum excitation $\Delta_{\min}$, and ground mass $d_0/N$ (Prop 13).

Precision is the real boundary: to place the crossing at window scale, $A_1$ must be
estimated to additive precision at least on the scale
$\eta_{A_1} \leq \min\{(1 + A_1)/2, \sqrt{d_0 A_2/N}\}$ (Prop 14), with worst-case target
$\Theta(2^{-n/2})$. Coarse inverse-polynomial precision can be tractable while
schedule-level precision can still be intractable.

The reverse direction is provably blocked: low-temperature partition information is
not identifiable from $A_1$ alone (Prop 15), so "recover hard $Z$ from easy $A_1$" is
not a valid generic reduction route.


## Remaining Open Questions

1. **Natural NP-hard problems with simple spectra.** Grover is the only known example
   of a hard search problem with easy $A_1$. Do natural combinatorial NP-hard problems
   (not oracle search) ever have simple enough spectra?

2. **Boundary at schedule precision.** We now know the target precision scale
   $\eta_{A_1} \leq \min\{(1 + A_1)/2, \sqrt{d_0 A_2/N}\}$, with worst-case
   $\Theta(2^{-n/2})$ (Prop 14). Which natural families still admit polynomial-time
   approximation at that schedule-relevant scale, not just at inverse-polynomial error?

3. **Tight converse conditions for partition data.** Proposition 15 shows a
   non-identifiability obstruction for recovering $Z(\beta)$ from $A_1$. What minimal
   additional statistics (for example a short list of moments or proxy values) are
   sufficient to make a reverse reconstruction possible on natural families?

4. **Quantum computation of $A_1$.** Phase estimation on $H_z$ could estimate $A_1$
   quantumly. Classical hardness does not rule out efficient quantum computation.


## Connection to Other Experiments

- Supersedes the original 03_structured_tractability
- Proposition 3 connects to 07 (partial information): knowing partial spectrum
  contributes to the sufficient condition for $A_1$ tractability
- Proposition 4 strengthens the hardness barrier narrative for CSP-based AQO


## Numerical Verification

Quantitative sanity checks verified in `lib/verify_a1.py` and
`lib/verify_ising_bridge.py`. Key checks:
- Grover $N = 4$, $d_0 = 1$: $A_1 = 3/4$, $s^* = 3/7$
- Grover $N = 4$, $d_0 = 2$: $A_1 = 1/2$, $s^* = 1/3$
- Proposition 1 ($n = 4$, $N = 16$): $A_1 = 9/8 = 1.125$, vs $1/\Delta = 4$
- Hamming $n = 4$: $A_1 = 103/192 = 0.537$
- Hamming asymptotic: $A_1 \cdot n/2 \to 1$ (verified to $n = 128$)
- Proposition 15 families: matched $A_1$ but $|Z_U(B) - Z_S(B)|/N > 1/100$ for $B \geq 3$

Structured-family demo (bounded width): `lib/variable_elimination_a1.py` computes
$Z(t)$ and $A_1$ exactly by variable elimination and checks against brute force on toy
instances.

Coarse approximation demo: `lib/estimate_a1_sampling.py` estimates $A_1$ by Monte
Carlo sampling (Proposition 9) and compares to an exact computation for a toy
structured instance.

Partition-function quadrature demo: `lib/approx_a1_from_partition_function.py`
implements a log-grid midpoint rule for $A_1^{(\varepsilon)}$ (Propositions 10-12) and
compares to an exact computation on a toy structured instance.

Laplace-side quadrature demo: `lib/approx_a1_from_laplace_partition_function.py`
implements the anchored proxy $A_1^{[B]}$ (Proposition 11) via midpoint quadrature and
compares to the exact value for a toy structured instance.

Ferromagnetic bridge verification: `lib/verify_ising_bridge.py` checks the full
Proposition 13 bound numerically (tail + oracle + quadrature terms) and validates the
Proposition 14 crossing-sensitivity identity and min-condition criterion.

Reverse-bridge obstruction verification: `lib/verify_a1.py` checks Proposition 15
analytically and by brute force on a toy $n$.

Lean formal verification: `lean/StructuredTractability08/Prop13.lean`,
`lean/StructuredTractability08/Prop14.lean`, and
`lean/StructuredTractability08/Prop15.lean` machine-check key deterministic identities
and bound lemmas for Propositions 13-15, including Proposition 13's error-budget core
plus tail/oracle/quadrature aggregation lemmas, and the Proposition 15 quantitative
gap core;
`cd lean && lake build` succeeds.


## References

1. Original paper -- Section 4 (hardness), Theorem 12
2. Valiant 1979 -- #P-completeness of counting
3. Bennett, Bernstein, Brassard, Vazirani 1997 -- query lower bounds
4. Grover 1996 -- quantum search
5. Jerrum, Sinclair (ferromagnetic Ising partition-function approximation regime)


## Status

**Phase**: Resolved

All conjectures resolved. All results are propositions (no unjustified "theorem"
labels). Positive structure, precision bridge, and a nontrivial boundary obstruction
are established. Numerics verified. Honest caveats remain (promise model for Grover;
no full hardness converse from $A_1$-approximation to $Z$-approximation). Key identities
and quantitative bound cores for Props 13-15 are additionally Lean-checked.
Full absolute formalization would still require importing/formalizing external
results used as assumptions (notably the Ising FPRAS guarantee and the paper's
Section-4 schedule framework).

**Next:** see `todo.md` (task tree + progress) for publication-grade directions
beyond the current theorem set.
