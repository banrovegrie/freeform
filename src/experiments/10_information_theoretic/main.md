# Information-Theoretic Limits: Beyond the Adiabatic Framework

## Problem Statement

The paper proves that fixed-schedule AQO needs precise crossing information
($A_1$ / $s^*$), and computing that information is classically hard.
This experiment asks whether that barrier is fundamental to the computational task
or specific to the adiabatic model.

**Central question.**
For ground-state finding of diagonal Hamiltonians, is the $A_1$ barrier an
information-theoretic limit across all algorithms?

**Answer.**
No. The only universal lower bound is the Grover scale
$\Omega(\sqrt{N/d_0})$. The $A_1$ barrier is model-specific.

**Scope.**
All results here are for ground-state finding of diagonal $n$-qubit Hamiltonians.
For other tasks (energy estimation, full-spectrum reconstruction, thermal-state
preparation), spectral information can remain necessary even in circuit settings.


## Novelty Assessment

The statement "AQO has an $A_1$ barrier while circuits do not" appears informally in
the paper discussion. The novelty in this experiment is the formal and complete
landscape:

1. **$A_1$-blindness theorem layer (Part VII).**
   Circuit output carries negligible information about $A_1$:
   $I(X_{\mathrm{DH}};A_1\mid S_0,E_0)\le 2^{-\Omega(n)}$, and exactly zero when
   conditioned on success.

2. **Precision-aware bridge (Part VIII, Proposition 9).**
   Combining Experiment 07 and Experiment 13 yields:
   quantum estimate-$A_1$-then-evolve runs in $O(2^{n/2}p(n))$,
   classical estimate-$A_1$-then-evolve is $\Omega(2^n)$.
   This identifies the information gap scale with the quantum speedup scale.

3. **Complete model comparison theorem (Part X, Theorem 8).**
   One theorem now unifies Experiments 08, 10, 12, and 13 into a single table with
   explicit assumptions, runtime bounds, information sources, and barrier status.

4. **Continuous-time barrier resolution split across `proof.md` and `proof2.md`.**
   A constant-control rank-one protocol on the two-level family
   $H_z=\mathbb{I}-P_0$ reaches the ground space in
   $\Theta(\sqrt{N/d_0})$ time without $A_1$ input.
   The normalized worst-case reformulation is then proved in `proof2.md` (Theorem 10).


## Conjectures

### Conjecture 1 (Oracle Lower Bound) -- PROVED
Ground-state finding needs $\Omega(\sqrt{N/d_0})$ queries.
Resolved via BBBV reduction and Farhi et al. consistency check.

### Conjecture 2 (Information-Complexity Tradeoff) -- REFINED AND SOLVED
Original formulation was not well-posed for quantum algorithms.
Correct statement is model-specific: fixed AQO obeys the bit-runtime law
$T(C)=T_{\mathrm{inf}}\Theta(\max(1,2^{n/2-C}))$.

### Conjecture 3 (Adiabatic Limitation) -- PROVED (Corrected Framing)
Fixed AQO needs $n/2$ bits at schedule precision; circuit algorithms do not.
The right statement is "circuits do not need $A_1$", not "circuits get $A_1$ for free."

### Conjecture 4 (No Free Lunch) -- REFUTED
Durr-Hoyer is a direct counterexample: optimal scaling without computing spectral
aggregates such as $A_1$.

### Conjecture 5 (Continuous-Time $A_1$ Barrier) -- RESOLVED (SPLIT FORM)
Literal form is refuted in `proof.md` Part IX.
Normalized worst-case reformulation is proved in `proof2.md` (Theorem 10).


## Results

| ID | Statement | Status |
|---|---|---|
| Thm 1 | Universal lower bound $\Omega(\sqrt{N/d_0})$ | Proved |
| Thm 2 | Durr-Hoyer achieves $O(\sqrt{N/d_0})$ with no spectral inputs | Proved |
| Thm 3 | Model separation: circuit vs fixed AQO vs adaptive AQO | Proved |
| Thm 4 | Communication complexity formalization | Proved |
| Thm 5 | Conjecture 4 refuted | Proved |
| Props 6-8 | $A_1$-blindness of circuit algorithm | Proved |
| Thm 6 | Interpolation import from Exp 07 | Imported and integrated |
| Thm 7 | Bit-runtime information law | Proved |
| Prop 9 | Quantum pre-computation tradeoff (Exp 07 + Exp 13) | Proved by citation chain |
| Thm 8 | Complete model comparison theorem (Exps 08, 10, 12, 13) | Proved by citation chain |
| Prop 10 | Constant-control rank-one protocol on two-level family | Proved |
| Thm 9 | Conjecture 5 (literal form) refuted by counterexample | Proved |
| Thm 10 (proof2) | Normalized worst-case continuous-time lower bound | Proved |

**Main theorem of the experiment.**
For the scoped task (ground-state finding of diagonal Hamiltonians), the only
universal query barrier is Grover/BBBV. The AQO $A_1$ barrier is model-dependent.


## Main Insight

The AQO crossing parameter
$$A_1 = \frac{1}{N}\sum_{k\ge 1}\frac{d_k}{E_k-E_0}$$
controls one specific path family.
Algorithms that do not rely on that path do not pay that information cost.

The complete comparison now has two layers:

1. **Worst-case unstructured layer (Part X table).**
   Fixed AQO needs spectrum bits; circuit and adaptive models can avoid prior
   classical communication.

2. **Structured-family layer (import from Exp 08).**
   On bounded-treewidth and partition-function-tractable families
   (Exp 08, Props 8-12), $A_1$ can be estimated/computed in polynomial time.
   Then the gap-informed AQO row changes qualitatively from "hard pre-step" to
   "polynomial pre-step."


## Open Questions

1. **Unnormalized control/action formulations.**
   Worst-case barrier is proved under normalized controls (`proof2.md`, Theorem 10).
   Remaining work is to characterize equivalent formulations when control amplitude is
   unbounded and complexity is measured by oracle action instead of raw time.

2. **Classical communication lower bounds.**
   Query complexity is tight; communication-complexity lower bounds outside the fixed
   schedule model remain less sharp.

3. **Beyond ground-state finding.**
   Identify the precise task boundary where spectral information becomes unavoidable
   in every model.


## Connection to Other Experiments

- **Experiment 04 (Separation Theorem):** supplies the fixed-schedule uninformed AQO
  penalty used in this experiment's model separation.
- **Experiment 05 (Adaptive Schedules):** supplies the adaptive bypass row in the
  model table.
- **Experiment 07 (Partial Information):** supplies interpolation theorem imported as
  Theorem 6 and used to derive Theorem 7 and Proposition 9.
- **Experiment 08 (Structured Tractability v2):** supplies Propositions 8-12, which
  modify the gap-informed rows on structured families.
- **Experiment 12 (Circumventing Barrier):** supplies Theorem 5 no-go for rank-one
  instance-independent modified Hamiltonians.
- **Experiment 13 (Intermediate Hardness):** supplies Theorems 2-5 used in
  Proposition 9 and Theorem 8.


## References

1. Bennett, Bernstein, Brassard, Vazirani (1997) -- query lower bound.
2. Farhi, Goldstone, Gutmann, Nagaj (2008) -- rank-one adiabatic lower bound instance.
3. Durr, Hoyer (1996) -- quantum minimum finding.
4. Boyer, Brassard, Hoyer, Tapp (1998) -- search with unknown number of marked items.
5. Paper Section 3 -- NP-hard and #P-hard hardness of $A_1$.
6. Experiment 08 -- structured tractability (Props 8-12 import).
7. Experiment 12 -- rank-one no-go (Thm 5 import).
8. Experiment 13 -- precision $2^{-n/2}$ estimation complexity (Thms 2-5 import).
9. Lee, Mittal, Reichardt, Spalek, Szegedy (2011) -- bounded-error equivalence of
   discrete and continuous-time query models used for the tight transfer in `proof2.md`.
10. Brandeho, Roland (2015) -- continuous-time adversary lower-bound framework used
    in `proof2.md`.
11. Cleve, Gottesman, Mosca, Somma, Yonge-Mallo (2009) -- near-linear simulation
    of continuous-time queries by discrete queries (`O(T log T / log log T)`), giving a
    weaker transferred lower bound.


## Status

**Phase:** Extended-complete (core and synthesis complete; Conjecture 5 resolved in split form)

- Conjecture 1: PROVED
- Conjecture 2: REFINED AND SOLVED
- Conjecture 3: PROVED (corrected framing)
- Conjecture 4: REFUTED
- Conjecture 5: RESOLVED IN SPLIT FORM (literal refuted; normalized worst-case proved in `proof2.md`)
- New in this pass: Proposition 9, Proposition 10, Theorem 9, Theorem 10, and Theorem 8
- Numerics: `lib/verify.py` now runs 8 tests including Part IX and addendum scaling checks
- Lean: algebraic core, Part IX identities, and addendum scaling identity verified (18 checks)

## Addendum Files

- `main2.md`: open-item resolution summary and interpretation.
- `proof2.md`: normalized worst-case theorem and proof details.
