# Experiment 11: Schedule Optimality - todo.md

Purpose: consolidated tracker for completion status, integration mapping, and remaining
publication-grade threads.


## Plans

### P1. Core closure (required)
- [x] Add partial-information schedule comparison connecting to Exp 07.
- [x] Add structured-family constant comparison connecting to Exp 08.
- [x] Update numerical verification for all new claims.
- [x] Update `main.md` with cross-experiment synthesis and practical guidance.

### P2. Chapter 9 integration (required)
- [x] Produce explicit insertion outline for Chapter 9 placement.
- [x] Map experiment results to section-level Chapter 9 content.
- [x] Mark what stays in main text versus appendix remarks.

### P3. Formal rigor extension (optional)
- [x] Extend Lean formalization with Proposition I algebraic overhead identity.
- [x] Add Lean-side placeholders for structured-instance constant comparison inputs.

### P4. Open technical depth (optional)
- [x] Compute explicit JRS prefactor certificate for this Hamiltonian class.
- [x] Compare a concrete non-power-law schedule family against $p=2$ and $p=3/2$.

### P5. Continuation integration (required for archive readiness)
- [x] Add `main2.md` and `proof2.md` for continuation-only open-thread closure.
- [x] Add `lib/verify_open_threads.py` and run it successfully.
- [x] Update `src/experiments/README.md` so continuation files are indexed and held
  to the same standards as `main.md`/`proof.md`.

### P6. Round-3 class-level closure (required for residual depth)
- [x] Add `main3.md` and `proof3.md` to generalize non-power-law results from
  single-family to class-level.
- [x] Extend `lib/verify_open_threads.py` with class-level checks across
  logarithmic, polynomial, and stretched-exponential penalties.
- [x] Integrate Round-3 status into `main.md`/`main2.md` and experiment conventions.


## Progress

- 2026-02-06: Re-read all required files for experiment 11 and neighboring experiments
  06, 07, 08, 10, plus experiment conventions (`src/experiments/README.md`,
  `src/experiments/CLAUDE.md`, root `CLAUDE.md`).
- 2026-02-06: Added `Proposition I` to `proof.md` (partial-information RC vs JRS
  degradation, importing Exp 07 Theorem 3).
- 2026-02-06: Added `Remark J` to `proof.md` (structured ferromagnetic Ising
  instance from Exp 08 Prop 13 family, explicit $C$, $I$, and $C^2/I$ comparison).
- 2026-02-06: Replaced `lib/verify_extensions.py` with pure-standard-library
  verification and added Claims 6-7 for the new results.
- 2026-02-06: Updated `main.md` with new results, cross-experiment integration, and
  revised status/open-question framing.
- 2026-02-06: Numerical verification executed successfully (`python3
  src/experiments/11_schedule_optimality/lib/verify_extensions.py`).
- 2026-02-07: Added `lean/ScheduleOptimality/PartialInfo.lean` with formal proofs of
  RC overhead baseline and the exact JRS overhead identity used in Proposition I.
- 2026-02-07: Updated legacy Experiment 11 Lean files for toolchain compatibility
  (`Basic.lean`, `Theorems.lean`, `ScheduleOptimality.lean`) and re-ran Lean checks.
- 2026-02-07: Added Corollary I.1 (explicit $A_1$-propagation formulas) and
  extended numerical verification with deterministic identity/bound checks.
- 2026-02-07: Hardened Theorem E phrasing to the exact criterion
  $C^2<I \iff (c_L-1)r^2-2ar+a(1-a)>0$, added field-strength robustness scans
  ($h \in \{1,2,3,4\}$ at $n=10$), and added Lean theorem `c2_lt_i_iff`.
- 2026-02-07: Added continuation files `main2.md` and `proof2.md` to resolve the
  two remaining open threads without rewriting closed core results.
- 2026-02-07: Added `lib/verify_open_threads.py` and validated all continuation
  claims (explicit JRS prefactor algebra, constant-level comparisons, non-power-law
  exponential slowdown overhead).
- 2026-02-07: Ran `python3 src/experiments/11_schedule_optimality/lib/verify_extensions.py`
  and `python3 src/experiments/11_schedule_optimality/lib/verify_open_threads.py`
  (both PASS), and checked Lean for Experiment 11 modules with
  `LEAN_PATH=\"11_schedule_optimality/lean:$LEAN_PATH\" lake env lean 11_schedule_optimality/lean/ScheduleOptimality.lean`.
- 2026-02-07: Updated `src/experiments/README.md` to formally index optional
  `main2.md`/`proof2.md` continuation files and enforce same rigor standards.
- 2026-02-07: Added `lean/ScheduleOptimality/StructuredInputs.lean` placeholder
  bundle for structured-instance constants and integrated it into
  `lean/ScheduleOptimality.lean` checks.
- 2026-02-07: Added Round-3 continuation files `main3.md` and `proof3.md` with a
  class-level window-dominance theorem for multiplicative penalty schedules.
- 2026-02-07: Extended `lib/verify_open_threads.py` with Claim 4 and validated
  class-level bounds for logarithmic, polynomial, and stretched-exponential
  penalty families (PASS).
- 2026-02-07: Updated `main.md` and `main2.md` to reference Round-3 closure and
  updated `src/experiments/README.md` to support continuation layers beyond
  `main2.md`/`proof2.md`.


## Findings

### F1. Partial-information schedule comparison (Gap 1)

- Imported exactly from Exp 07 Theorem 3:
  $$T_{\mathrm{RC}}(\epsilon_{A_1})
  = T_{\mathrm{RC},\infty}\cdot
  \Theta\!\left(\max\!\left(1,\frac{\epsilon_{A_1}}{\delta_{A_1}}\right)\right),
  \quad \delta_{A_1}=2\sqrt{d_0A_2/N}.$$ 
- Derived explicit JRS sensitivity:
  $$\frac{T_{\mathrm{JRS}}(\delta_C,\delta_g)}{T_{\mathrm{JRS},\infty}}
  = \frac{(1+\delta_C/C)^2}{1-\delta_g/g_{\min}}
  = 1 + 2\delta_C/C + \delta_g/g_{\min} + \text{higher-order terms}.$$
- Added Corollary I.1 with explicit $A_1$-error propagation identities:
  $$\frac{g_{\mathrm{mod}}(A+e)}{g_{\mathrm{mod}}(A)}-1=\frac{e}{A(A+e+1)},$$
  $$\frac{C_{\mathrm{mod}}(A+e)-\rho}{C_{\mathrm{mod}}(A)-\rho}-1
  =-\frac{(2A+1)e+e^2}{(A+e)(A+e+1)},$$
  giving explicit certified bounds for JRS overhead under $|e|\le\epsilon<A$.
- Lean formalization now includes these algebraic identities in
  `lean/ScheduleOptimality/PartialInfo.lean`.
- Practical recommendation from Proposition I:
  - Coarse $A_1$ knowledge ($\epsilon_{A_1} \gg \delta_{A_1}$): prefer JRS-style
    scheduling with conservative $(C_+, g_-)$.
  - High-precision regime ($\epsilon_{A_1} \lesssim \delta_{A_1}$): both frameworks
    are constant-factor optimal; compare constants via $I$ versus $C^2$.

### F2. Structured-family constant comparison (Gap 2)

- Concrete instance: open ferromagnetic Ising chain, $n=10$, $J_{i,i+1}=1$,
  $h_i=1$, normalized to $E \in [0,1]$.
- Computed parameters:
  $$A_1=1.5848010225,\; A_2=2.8410286701,\; \Delta=1/7,\; d_0=1,$$
  $$g_{\min}=0.0227184465,\; s_0=0.2601498656.$$
- Constants:
  $$C=157.4491589643,\quad I=34807.9388418623,\quad C^2/I=0.7122006784.$$
- Comparison to Grover bound ratio at same $N=1024$:
  $$0.7122 > 0.6033.$$
  Interpretation: JRS remains tighter ($C^2 < I$), but the relative advantage is
  weaker than in Grover.
- Family-level robustness check (same model, $n \in \{8,10,12\}$) preserves
  $C^2/I < 1$ and keeps the structured ratio above the Grover benchmark at matching
  $N$.
- Additional field-strength robustness at fixed $n=10$ and $h \in \{1,2,3,4\}$
  also preserves $0.6033 < C^2/I < 1$.

### F3. Chapter 9 insertion outline (Gap 3)

Placement: within or immediately after Chapter 9 "Measure Condition and Scaling"
section (currently sourced from Exp 06), as a schedule-selection subsection.

Proposed subsection order:
1. **Measure Condition for the Paper's Gap (Exp 11 Theorem A + B)**
   - State explicit $C$ bound and Grover exact constant $C=1$.
2. **Runtime Recovery Across Frameworks (Exp 11 Theorem C + D)**
   - Show both $p=2$ and $p=3/2$ recover
     $T = O(\sqrt{NA_2/d_0}/\epsilon)$.
3. **Constant-Level Comparison (Exp 11 Theorem E + Remark J)**
   - Present $C^2/I$ logic, Grover benchmark, and structured Ising contrast.
4. **Schedule Choice Under Partial Information (Exp 11 Proposition I + Exp 07 Thm 3)**
   - Translate asymptotic equivalence into practical regime guidance.
5. **Geometry Map (Exp 11 Theorems F, G, Proposition H)**
   - Clarify the $\alpha=1$ boundary role and when each framework wins/fails.

Main-text versus appendix split:
- Main text: Theorems A-C, E, Proposition I, brief Remark J numeric table.
- Appendix/remarks: detailed derivations for D, F-H, full structured-instance
  computation details, and extended numeric tables.

### F4. Continuation-thread closure

- Open thread 1 (explicit JRS prefactor): resolved at certificate level in
  `proof2.md` Theorem K and Corollary K.1 with
  $$B_{\mathrm{JRS}}(3/2)=8A_HC_\mu+63A_H^2C_\mu^2.$$
- Open thread 2 (non-power-law comparison): resolved for an explicit RC-safe
  exponential slowdown family in `proof2.md` Theorem N with
  $$T_{\exp}/T_{\mathrm{RC}} \geq \tfrac12 e^{\beta/g_{\min}}.$$
- All continuation numerics are reproducible in
  `lib/verify_open_threads.py` (PASS).

### F5. Residual optional depth (not blocking completion)

- Replace placeholder-level structured constants with fully proven in-Lean bounds
  if full formal-numeric integration is later required.
- Extend class-level penalty results beyond the alpha=1 model to broader
  gap geometries.

### F6. Round-3 class-level non-power-law closure

- `proof3.md` Theorem P proves, for schedules
  $$\frac{ds}{dt}
  =
  \frac{\epsilon_{\mathrm{ad}}}{A_H}\frac{g(s)^2}{\Phi(g(s))},\quad \Phi\ge 1,$$
  on the canonical alpha=1 model:
  $$\frac{T_{\Phi}}{T_{\mathrm{RC}}}
  \ge
  \frac{\Phi(g_{\min})}{2(1-g_{\min}/c)}
  >
  \frac12\Phi(g_{\min}).$$
- This strictly generalizes the exponential-only result from `proof2.md`
  (Corollary P.1).
- Corollary taxonomy now covers logarithmic, polynomial, and exponential penalty
  regimes in one framework.
- Proposition Q adds the bounded-penalty complement:
  `1 <= T_Phi/T_RC <= K` when `1 <= Phi <= K`.
- Claim 4 in `lib/verify_open_threads.py` validates these bounds numerically for
  all three representative families (PASS).
