# Experiment 08: Structured Tractability (v2) - `todo.md`

Purpose: maintain a single consolidated place for open threads, partial results, and
next actions while the experiment is evolving.


## Plans

### A. Partition-function route (turn "spectral complexity" into theorems)

**A0. Identity hygiene**
- [x] Add an "assumptions + interchange justification" note for the Laplace identity
      (when swapping sum/integral is valid).
- [x] Add a corollary: if $Z(\beta)$ is efficiently computable/approximable on a
      grid, then $A_1$ is efficiently approximable (state the model precisely).

**A1. Approximation theorem (core publishable lemma)**
- [x] Pick approximation model: additive $\eta$ vs relative error; oracle access to
      $Z(\cdot)$ vs explicit algorithm for $Z(\cdot)$; define input size.
- [x] Prove a deterministic quadrature bound for
      $\frac{1}{N}\int_0^1 (Z(t)-d_0)/t\,dt$ (integer-spectrum case).
- [x] Prove an analogous bound for the Laplace form
      $\frac{1}{N}\int_0^\infty (Z(\beta)-d_0)\,d\beta$ with truncation at
      $\beta_{\max}$ and tail control.
- [x] Make error parameters explicit (energy normalization, minimum excited energy,
      mass near the ground, etc.).

**A2. Structured-family positive theorem**
- [x] Choose 1-2 families where $Z$ is tractable and derive a polynomial-time
      algorithm for approximating $A_1$ (to a specified precision regime).
- [x] Choose a *second* family where $Z$ is nontrivially approximable (e.g. a known
      FPRAS regime for a spin system / matching polynomial) and write a clean corollary.
- [x] Write as a theorem + proof, not just an observation.

**A3. Structured-family negative theorem**
- [x] Add a nontrivial boundary theorem for the reverse direction
      ($A_1 \Rightarrow Z$) on an explicit structured family.
- [x] Ensure it is not a restatement of the paper's interpolation reduction.


### B. No-go theorem for "natural NP-hard with easy $A_1$" (high risk/high reward)

**B0. Make the statement precise first**
- [x] Fix input model: diagonal $k$-local Hamiltonians, bounded weights, bit
      complexity, and what the input/oracle access is.
- [x] Fix approximation: additive precision $\eta(n)$ (candidates:
      $\eta=2^{-n/2}$ or $\eta=1/\mathrm{poly}(n)$).
- [x] Write a conjecture/theorem template: "If $A_1$ is polytime computable for all
      instances in family $\mathcal{F}$, then ...".

**B1. Attempt reductions not relying on exponentially accurate interpolation**
- [x] Try reverse partition-function bridge directly; outcome: non-identifiability
      obstruction (Prop 15) for recovering low-temperature $Z(\beta)$ from $A_1$.
- [x] Evaluate decision-to-$A_1$ signal amplification path; current status:
      superseded by Prop 15 obstruction for this version, left as follow-on work.

**B2. If it fails**
- [x] Document the obstruction crisply (can still be publishable if it reveals a
      genuine barrier and motivates Target A/C).


### C. Precision-aware story (bridge to Chapter 9 + Experiment 13)

**C0. Map precisions to "what AQO needs"**
- [x] Extract from the paper: the required $\delta_{A_1}$ scale for schedule
      correctness; restate it in this experiment's notation.
- [x] Decide which precision regimes are worth targeting for "structured
      tractability" results.

**C1. Connect the structured-family theorem(s) to algorithmic precision**
- [x] For the chosen structured family, determine whether we can compute/estimate
      $A_1$ to $\eta=2^{-n/2}$ (or the correct derived scale) in polytime /
      quasi-poly / etc.
- [x] If only constant-factor or inverse-poly additive error is feasible, determine
      whether that is meaningful for near-optimal schedules.

**C2. Integration**
- [x] Draft a "Chapter 9 insertion outline": where 08 fits, and which theorems from
      A/B/C become section-level content.


### D. Structured family selection (choose a motivating class)

Selection criteria:
- Natural/recognizable for quantum optimization or classical complexity.
- Has a nontrivial partition-function story (tractable or provably hard).
- Lets us say something new about $A_1$ beyond "counting is hard".

Candidates:
- [ ] **Bounded treewidth CSPs / factor graphs**: exact dynamic programming for
      partition functions $\Rightarrow$ exact/approx $A_1$.
- [x] **Ferromagnetic Ising / monotone systems**: known FPRAS regimes for partition
      functions in some parameter ranges.
- [ ] **XOR-SAT / linear codes**: counting is in P $\Rightarrow$ exact $Z(t)$;
      check if it yields a clean, nontrivial $A_1$ theorem.
- [ ] **Horn-SAT / monotone CNF**: possible clean theorems in restricted regimes.
- [ ] **Submodular energies / cut functions**: if $Z$ or related transforms are
      tractable, could yield a strong positive theorem.

Immediate action:
- [x] Choose the "main family" and write a 1-page mini-brief: input model, known
      $Z$ facts, target precision, likely theorem statement.


### E. Paper-grade checklist (what "done" looks like)

- [x] 1-2 main theorems (new) + 2-4 supporting lemmas.
- [x] Clear model definition (input encoding + approximation notion).
- [x] At least one positive structured-family theorem.
- [x] At least one negative/boundary theorem OR a sharp barrier lemma not already in
      the original paper.
- [x] Small computational appendix: scripts validating toy cases / identities.
- [x] "Novelty positioning" paragraph: explicitly state what is new vs the original
      paper and Guo-An 2025.


## Progress

- 2026-02-06: added partition-function identities in `proof.md`; consolidated the
  running plan/progress here; hardened CSP hardness proof to satisfiable-only
  reduction; fixed `lib/verify_a1.py` vacuity print for small $n$; created this
  `todo.md`.
- 2026-02-06: added Proposition 8 (bounded treewidth / variable elimination route) and
  a correctness-checked demo in `lib/variable_elimination_a1.py`; removed redundant
  `notes/roadmap.md`.
- 2026-02-06: added Proposition 9 (Monte Carlo additive approximation when $E_0$ is
  known) and a demo in `lib/estimate_a1_sampling.py`.
- 2026-02-06: added Proposition 10 (additive $A_1$ approximation from $Z(t)$ without
  computing $d_0$) as a bridge from partition-function algorithms to $A_1$.
- 2026-02-06: added Proposition 11 (Laplace-side anchored proxy without $d_0$) and
  Proposition 12 (oracle reduction $Z$-approx $\Rightarrow$ additive $A_1$); added
  numerical sanity checks for the bounds in `lib/verify_a1.py` and a Laplace-side
  quadrature demo in `lib/approx_a1_from_laplace_partition_function.py`.
- 2026-02-06: selected ferromagnetic Ising with consistent fields as the main
  approximation family (`notes/family_selection.md`); added Proposition 13
  (multiplicative-$Z$ to additive-$A_1$ with explicit $(R,\Delta_{\min},\rho_0)$ error
  drivers) and Proposition 14 (schedule-relevant precision
  $\eta_{A_1}=\Theta(\sqrt{d_0A_2/N})$); added `lib/verify_ising_bridge.py` and
  verified all checks pass.
- 2026-02-06: added Proposition 15 (reverse-bridge obstruction): explicit 4-local
  families with identical $(A_1,\rho_0,\Delta_{\min},R)$ but order-one separated
  low-temperature partition values $Z(B)$; updated `lib/verify_a1.py` with analytic
  and brute-force checks.
- 2026-02-06: added Lean project in `lean/` with Mathlib dependency; machine-checked
  algebraic cores for Proposition 14 (`crossing_shift_identity`,
  `crossing_shift_abs_bound`, `crossing_shift_target_bound`,
  `scale_substitution_identity`) and Proposition 15 (`prop15_a1_match`,
  `cB_between`);
  `cd lean && lake build` passes.
- 2026-02-06: tightened Proposition 14 statement in `proof.md` to an explicit
  min-condition ($|\varepsilon|\le \min\{(1+A_1)/2,\sqrt{d_0A_2/N}\}$) and aligned
  `main.md` wording with this exact sufficient condition; extended
  `lib/verify_ising_bridge.py` to test the min-condition criterion numerically; widened
  the Proposition 15 sweep in `lib/verify_a1.py` to $B=3,\ldots,5000$.
- 2026-02-06: strengthened Lean verification for Proposition 15 by adding a full
  machine-checked proof of the quantitative gap core
  $\frac{e^{-1}}{16}-\frac{7}{16}\exp(-7B^2/(B^2+6))>1/100$ for $B\ge 3$, including
  the transcendental constant bound $\exp(-21/5)<3/200$, in
  `lean/StructuredTractability08/Prop15.lean`.
- 2026-02-06: added `lean/StructuredTractability08/Prop13.lean` to machine-check the
  deterministic Proposition 13 cores: three-term error decomposition, midpoint-oracle
  bound, and the $\eta/3+\eta/3+\eta/3$ parameter-budget implication.
- 2026-02-06: extended `lean/StructuredTractability08/Prop13.lean` with a generic
  minimum-gap tail suppression lemma matching the core inequality used in
  Proposition 13.
- 2026-02-06: added a Lean midpoint quadrature-aggregation theorem in
  `lean/StructuredTractability08/Prop13.lean` formalizing the algebraic
  `K`-interval to `LB^2/(2K)` scaling step used in Proposition 13.


## Findings

### Solid (already correct)

- Counterexamples: $\Delta$ and $d_0=1$ do not determine $A_1$.
- Optimization hardness and $A_1$-hardness are independent (counting vs decision).
- Sufficient condition: poly levels + efficiently computable $(E_k,d_k)$
  $\Rightarrow$ polytime $A_1$.
- CSP clause-violation Hamiltonians inherit \#P-hardness for computing $A_1$.
- Structural lemma: $A_1$ can be expressed as a transform of the partition function
  $Z$, connecting tractability/hardness of $A_1$ to tractability/hardness of $Z$.
- Additive $A_1$ approximation can avoid computing $d_0$ via anchoring at
  $Z(\varepsilon)$ (ordinary) or $Z(B)$ (Laplace), with explicit truncation bounds.
- In structured ferromagnetic Ising regimes, multiplicative approximation of
  partition functions on a temperature window yields additive approximation of $A_1$
  with explicit decomposition into tail, oracle, and quadrature terms (Prop 13).
- Crossing-position sensitivity gives an explicit sufficient condition
  $\eta_{A_1}\le \min\{(1+A_1)/2,\sqrt{d_0A_2/N}\}$, recovering the worst-case
  $2^{-n/2}$ regime from the paper's $\delta_s$ formula (Prop 14).
- Reverse bridge obstruction: even exact $A_1$ with matched
  $(\rho_0,\Delta_{\min},R)$ does not determine low-temperature $Z(\beta)$; this
  blocks generic converse reductions and gives a concrete negative boundary result
  (Prop 15).
- Lean formal checks now cover deterministic cores for Props 13-15, including
  Prop 13 tail/oracle/quadrature aggregation/budget lemmas and Prop 15's
  quantitative gap inequality,
  reducing risk of symbolic manipulation errors in the core equations and bounds.

### Residual formalization boundary (explicit)

- External approximation-theory inputs remain assumptions rather than in-project Lean
  proofs: specifically, the invoked ferromagnetic Ising partition-function FPRAS
  guarantee in the stated parameter regime.
- Chapter-9 schedule interpretation relies on the paper's Section-4 setup
  ($\delta_s$ construction and crossing-window semantics), which is cited and
  propagated consistently here but not re-formalized end-to-end in Lean.

### Resolved (novelty targets)

- Positive structured-family theorem: ferromagnetic Ising multiplicative-$Z$ route to
  additive $A_1$ with explicit error drivers (Prop 13).
- Precision-aware bridge to schedule relevance:
  $\eta_{A_1}\le \min\{(1+A_1)/2,\sqrt{d_0A_2/N}\}$, with worst-case
  $2^{-n/2}$ scale (Prop 14).
- Negative/boundary theorem beyond interpolation: reverse-bridge non-identifiability
  obstruction (Prop 15).

### Chapter 9 insertion outline (draft)

- **Motivation:** predicting the avoided crossing requires $A_1$ to precision
  $O(\delta_s)$; by Prop 14 this is equivalent to additive
  $\eta_{A_1}\le \min\{(1+A_1)/2,\sqrt{d_0A_2/N}\}$, with worst-case
  $2^{-n/2}$.
- **Key structural lemma:** $A_1$ as a partition-function transform (Laplace + ordinary
  generating function).
- **Positive structure:** bounded treewidth gives exact $Z(t)$ coefficients and exact
  $A_1$ (Prop 8); more generally, approximate $Z$ over a temperature window implies
  additive $A_1$ (Props 10-13), including ferromagnetic Ising FPRAS regimes.
- **Precision-aware message:** coarse $A_1$ is often "moderate temperature", but the
  schedule-relevant regime $\eta_{A_1}\approx 2^{-n/2}$ is "low temperature", and
  Prop 13 shows this pushes required multiplicative $Z$ accuracy into effectively
  exponential effort for $1/\mu$-polynomial oracles.
- **Boundary message:** Prop 15 proves the bridge is one-way in general; matching
  $A_1$ and coarse spectral drivers does not pin down low-temperature partition mass.
