# Correctness Audit of Chapter 9 (Information Gap)

## Context

Chapter 9 is the thesis's primary original contribution, built from 10 experiment files (src/experiments/02-13) rather than the published paper. The user wants absolute mathematical correctness verified. Six verification agents cross-referenced Chapter 9 against all experiment sources, Chapters 5-8, the published paper, AND verified the experiment proof files themselves for internal correctness. This plan addresses every issue found.

## Three-Layer Audit

1. Chapter 9 proofs — verified line-by-line against experiment sources
2. Experiment proof files — verified internally for algebraic correctness, sanity-checked with N=4
3. Chapter 9 vs experiments — cross-checked for divergences in statements, constants, and proof mechanisms

## Audit Summary

Overall verdict: Chapter 9 is largely correct. 30 of 33 numbered results verified CORRECT. The experiment sources are internally sound (all 10 files verified CORRECT with no mathematical errors). Three issues require fixes: one critical error, one factual error in a proof sketch, and one proof gap.

### CRITICAL (mathematical error)

**C1. Lemma 9.3 (Precision propagation, line 91-96): Factor-of-2 bound unjustified.**
- Chapter 9 claims: $|s^*_{\rm est} - s^*| \leq 2\varepsilon/(A_1+1)^2$
- The justification "$\varepsilon < A_1$ ensures $A_1 - \varepsilon + 1 \geq (A_1+1)/\sqrt{2}$" is **FALSE** for $A_1 > \sqrt{2}-1 \approx 0.414$
- For Grover ($A_1 = 3/4$): LHS $= 3/4 - 3/4 + 1 = 1$, RHS $= (7/4)/\sqrt{2} \approx 1.24$. Already fails.
- Experiment 07 (proof.md line 32) gives the correct bound: $\varepsilon/(A_1+1)^2 \cdot (1 + O(\varepsilon/A_1))$
- Experiment 08 (Prop 14) gives the exact identity: $\hat{s}^* - s^* = \varepsilon/((1+A_1)(1+A_1+\varepsilon))$
- Fix: Use the exact identity from Exp 08 Prop 14. Under $|\varepsilon| \leq (1+A_1)/2$, the denominator $(1+A_1+\varepsilon) \geq (1+A_1)/2$, giving the clean bound $|s^*_{\rm est} - s^*| \leq 2|\varepsilon|/(1+A_1)^2$.
- Downstream impact: Theorem 9.2 (interpolation) uses $\Theta$ notation, so it absorbs the constant. Unaffected.

### MODERATE (factual error or proof gap)

**M1. Theorem 9.16 (ETH, line 541-543): WRONG reduction mechanism cited.**
- Chapter 9 says: "The paper's reduction from #P-hard counting to A_1 evaluation (Theorem 8.2) uses Lagrange interpolation..."
- Experiment 13 Theorem 5 (lines 704-717) uses a completely different mechanism: the NP-hardness reduction from the paper's Theorem 2 (3-SAT reduction, Section 3.1), NOT the #P-hardness Lagrange interpolation
- The ETH argument: NP-hardness of A_1 at 1/poly(n) precision (from 3-SAT) implies hardness at $2^{-n/2}$ by monotonicity (finer oracle trivially solves coarser problem). Under ETH, 3-SAT on $\Omega(n)$ variables requires $2^{\Omega(n)}$ time.
- Fix: Replace lines 541-543 with the correct proof sketch citing the 3-SAT reduction and monotonicity argument

**M2. Theorem 9.3 (Hedging, line 139-146): Error functional not derived from JRS bound.**
- The proof states the error functional decomposition without connecting to the JRS integral
- Fix: Add one sentence: "The JRS error integral of \autoref{eq:jrs-bound} decomposes as $\eta = (1/T)(v_{\rm slow} I_{\rm slow} + v_{\rm fast} I_{\rm fast})$ when the schedule has piecewise-constant velocity."

**M3. Theorem 9.7 (Scaling spectrum, line 308): Convergence condition not justified.**
- Both integrals converge when $1/\alpha < p < 3 - 1/\alpha$
- Fix: Add: "where $p$ is chosen in $(1/\alpha, 3-1/\alpha)$; for $p = 3/2$ this holds for all $\alpha > 2/3$."

**M4. Theorem 9.8 (Measure condition, line 337): Missing spectral condition assumption.**
- The crossing window bound requires $\eta \leq 1/6$
- Fix: Add "under the spectral condition of Chapter~5" to theorem statement

### MINOR (notation/clarity, no math impact)

**m1.** Line 28: Window width notation. Says $O(\Delta_*)$, should say $O(\delta_s)$ with note $\delta_s = \Theta(\Delta_*)$ for paper's gap profile.

**m2.** Lemma 9.6 (line ~290): Convergence label swap. "Convergent at $u=0$" should be "convergent as $u \to \infty$."

**m3.** Theorem 9.1: Notation inconsistency — clean $\geq$ in statement but $\Theta$ in proof conclusion.

## Experiment Source Verification (Internal Correctness)

All 10 experiment proof files verified for internal mathematical correctness:

| Experiment File | Verdict | Notes |
|---|---|---|
| 04_separation_theorem/proof.md | CORRECT | Error model is acknowledged heuristic simplification |
| 07_partial_information/proof.md | CORRECT | No issues |
| 02_robust_schedules/proof.md | CORRECT | Minor intermediate expression error in subdominant term; final result unaffected |
| 05_adaptive_schedules/proof.md | CORRECT* | *Cost analysis counts only phase estimation, not adiabatic evolution. Chapter 9 FIXES this by using direct phase estimation on $\lvert\psi_0\rangle$ |
| 06_measure_condition/proof.md | CORRECT | Thm 1 proof for $\alpha < 1$ assumes local gap model globally; correct for physical instances |
| 08_structured_tractability_v2/proof.md | CORRECT | Midpoint rule constant loose by factor 2 (harmless upper bound) |
| 10_information_theoretic/proof.md | CORRECT | Slightly imprecise Pinsker invocation; conclusion unaffected |
| 11_schedule_optimality/proof.md | CORRECT | Minor concern about exact constant in $\eta \leq 1/6$ condition |
| 12_circumventing_barrier/proof.md | CORRECT | One compressed derivation ($C_{\rm ground}$ formula) |
| 13_intermediate_hardness/proof.md | CORRECT | No issues found |

Key finding: The experiment sources are mathematically sound. Chapter 9's only real errors are introduced in the translation from experiments to chapter (C1 bad justification, M1 wrong reduction cited), not inherited from incorrect source material.

Note on Exp 05 adaptive protocol: The experiment source has a cost accounting gap (step 102 says "evolve adiabatically to s_mid" but the cost analysis only counts phase estimation). Chapter 9 intentionally addresses this by removing the adiabatic evolution step — it applies phase estimation directly to $|\psi_0\rangle$, relying on the overlap argument of lines 160-162. This is a genuine improvement over the experiment source.

## Chapter 9 vs Experiments: Cross-Check Summary

| Ch 9 Result | Verdict | Detail |
|---|---|---|
| Lemma 9.3 | DIVERGENCE | Factor 2 vs factor $(1+O(\varepsilon/A_1))$ — C1 |
| Def 9.4 (Adaptive protocol) | INTENTIONAL DIVERGENCE | Ch 9 omits adiabatic evolution (improvement) |
| Thm 9.16 (ETH proof sketch) | DIVERGENCE | Cites wrong reduction — M1 |
| Prop 9.5 | MINOR CONCERN | $O(1/\Delta_{\min})$ vs exact $1/\Delta_{\min}$ |
| All other 29 results | MATCH | Statements, proofs, and constants consistent |

## Completeness Check

| Experiment | Key Result | In Ch 9? | Status |
|---|---|---|---|
| 04 | Separation theorem | Yes (Thm 9.1) | Complete |
| 05 | Adaptive protocol | Yes (Thm 9.4) | Complete |
| 02 | Hedging | Yes (Thm 9.3) | Complete |
| 07 | Interpolation | Yes (Thm 9.2) | Complete |
| 06 | Geometric char + Scaling spectrum | Yes (Thms 9.6-9.7) | Complete |
| 11 | Measure condition + Bridge | Yes (Thms 9.8-9.9, Cor 9.2) | Complete |
| 12 | No-go chain (Thms 1-5) | Yes (Thms 9.10-9.14) | Complete |
| 12 | Rank-k Props | Yes (Props 9.1-9.2) | Condensed but present |
| 08 | Treewidth tractability | Yes (Prop 9.4) | Complete |
| 08 | Reverse bridge | Yes (Prop 9.5) | Complete |
| 08 | Counting hardness + False conjectures | Yes (Props 9.3, 9.6-9.8) | Complete |
| 10 | A1-blindness + Bit-runtime law | Yes (Prop 9.9, Thm 9.18) | Complete |
| 13 | Quantum query + ETH + Structure irrel. | Yes (Thms 9.15-9.17) | Complete |

Verdict: Chapter 9 is complete. All major experiment results present. Condensation and omissions are appropriate.

## Implementation Plan

### Fix C1: Precision propagation bound (CRITICAL)

File: src/chapters/chapter9.tex lines 89-96

Action: Replace the incorrect intermediate inequality with the exact identity from Exp 08 Prop 14:
- State: $f(A_1 + \varepsilon) - f(A_1) = \varepsilon/((1+A_1)(1+A_1+\varepsilon))$
- Under $|\varepsilon| \leq (1+A_1)/2$: denominator $\geq (1+A_1)^2/2$, giving $\leq 2|\varepsilon|/(1+A_1)^2$
- This justification is now algebraically rigorous (no false intermediate claim)
- Update line 98 ($W(\varepsilon)$ definition) correspondingly

### Fix M1: ETH proof sketch (MODERATE — factual error)

File: src/chapters/chapter9.tex lines 541-543

Action: Replace the #P/Lagrange interpolation citation with the correct argument:
- "The paper's Theorem~2 reduces 3-SAT on $n_{\rm var}$ variables to $A_1$ estimation at precision $1/\mathrm{poly}(n)$, where $n = O(n_{\rm var})$ qubits. An oracle at precision $2^{-n/2} < 1/\mathrm{poly}(n)$ is strictly more powerful, so it also solves 3-SAT. Under ETH, this requires $2^{\Omega(n_{\rm var})} = 2^{\Omega(n)}$ time."

### Fix M2: Hedging error functional derivation (MODERATE)

File: src/chapters/chapter9.tex line 144

Action: Add one sentence connecting to JRS bound

### Fix M3: Scaling spectrum convergence (MODERATE)

File: src/chapters/chapter9.tex line 308

Action: Add convergence range note

### Fix M4: Spectral condition assumption (MODERATE)

File: src/chapters/chapter9.tex line 337

Action: Add "under the spectral condition of Chapter~5"

### Fix m1: Window width notation (MINOR)

File: src/chapters/chapter9.tex line 28

### Fix m2: Convergence condition label (MINOR)

File: src/chapters/chapter9.tex line ~290

## Verification

1. Build: `cd src && pdflatex main.tex && bibtex main && pdflatex main.tex && pdflatex main.tex`
2. Grover sanity check (N=4):
   - C1 fix: $\varepsilon = 0.1$, $A_1 = 3/4$. Exact: $0.1/((7/4)(7/4+0.1)) = 0.1/(7/4 \cdot 37/20) = 0.1/(259/80) = 8/259 \approx 0.031$. Bound: $2 \cdot 0.1/(7/4)^2 = 0.2/(49/16) = 3.2/49 \approx 0.065$. Both valid.
3. Reference check: Verify no undefined references after edits
