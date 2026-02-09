# Claim-by-Claim Ledger (Chapters 5-9)

## Scope
- This ledger indexes formal mathematical anchors in Chapters 5-9: theorem-like environments and math labels (`eq:`, `lem:`, `thm:`, `def:`, `prop:`, `cor:`).
- Inline assertions without labels are tracked separately in the Action-Required table.

## Action-Required Items (Explicit Fixes)

| Severity | Location | Issue | Required change |
|---|---|---|---|
| Major | `src/chapters/chapter7.tex:208` | Theorem statement is generic, but proof uses AQO-specific constants (`g_0(1)=\\Delta/30`, fixed `b`) not in hypotheses. | Either (A) add these assumptions to theorem statement, or (B) refactor proof to avoid special constants and prove fully generic claim. |
| Major | `src/chapters/chapter6.tex:284` | Hypothesis propagation gap: right-gap proof assumes `A_1 \\geq 1/2` (`chapter6.tex:146`), but complete-profile and downstream runtime statements are presented without this extra condition. | Either remove the `A_1 \\geq 1/2` restriction by strengthening the proof, or add an explicit equivalent hypothesis (e.g. `s^* \\geq 1/3`) to `chapter5.tex:362`, `chapter6.tex:284`, and downstream theorems that rely on `thm:complete-profile`. |
| Major | `src/chapters/chapter9.tex:708` | “Structure irrelevance” theorem is stronger than the proof provided (proof is heuristic sensitivity argument, not a full worst-case reduction). | Either downgrade claim to a proposition/insight, or add a rigorous reduction proving worst-case equivalence to `M=2` approximate counting. |
| Major | `src/chapters/chapter9.tex:664` | Query-complexity statement overstates precision range: theorem claims `Θ(1/\varepsilon)` for general precision, but cited upper bound (\autoref{thm:quantum-A1}) is `O(\sqrt{N} + 1/(\varepsilon\Delta_1))` unless additional assumptions (e.g., known `E_0` or `\varepsilon \lesssim 1/\sqrt{N}`) are imposed. | Restrict theorem/proposition to the schedule-relevant regime (e.g., `\varepsilon = \Theta(2^{-n/2})` or `\varepsilon \le c/\sqrt{N}`), or explicitly add assumptions under which `\sqrt{N}` is absorbed. |
| Major | `src/chapters/chapter9.tex:282` | Measurement lower-bound proof assumes each measurement gives only binary/`O(1)` information (“ground vs excited”), but theorem quantifies over any adaptive algorithm. This is stronger than what is proved. | Either restrict theorem/model to binary decision probes (as used in the protocol) or provide a formal per-measurement information bound for the broader adaptive measurement model. |
| Major | `src/chapters/chapter9.tex:64` | Separation theorem is stated for all gap functions in the abstract class `\mathcal{G}(s_L,s_R,\Delta_*)`, but the proof step for `T_{\mathrm{inf}}` uses rank-one-specific structure (`\delta_s=\Theta(\Delta_*)`, linear approach near crossing, and `\autoref{thm:aqo-runtime}`). This does not follow for a generic `\mathcal{G}` instance. | Narrow theorem scope to rank-one (or add explicit geometric assumptions on the informed profile that imply `T_{\mathrm{inf}}=\Theta(\Delta_*/v_{\mathrm{slow}})`), and remove the “applied to any gap profile in the class” over-claim. |
| Minor | `src/chapters/chapter8.tex:263` | Generic extrapolation barrier uses a strong quantifier (“incurs error at least …”) while the proof establishes a worst-case amplification bound via the Lebesgue constant. | Rephrase theorem/proof to “can incur” or “worst-case error is at least …” to align quantifiers with the argument. |
| Minor | `src/chapters/chapter9.tex:706` | Incorrect justification of the distance hypothesis for `\autoref{thm:generic-barrier}`: `x^*=\Theta(2^{-n/2})` with nodes in `[0,1/\mathrm{poly}(n)]` does not imply `\mathrm{dist}(x^*,[a,b]) \ge b-a` (typically `x^*` is inside/near the interval). | Remove or correct the parenthetical claim; state the barrier condition explicitly and tie it to the actual interpolation geometry used in Chapter 8 (evaluation outside the sampled interval). |

## Resolved in Execution Pass

| Location | Status | Resolution summary |
|---|---|---|
| `src/chapters/chapter5.tex:204` | Resolved | Removed invalid global bound `g(s) < s\Delta`; replaced with a safe non-quantitative statement. |
| `src/chapters/chapter6.tex:15` | Resolved | Removed repeated invalid bound `g(s) < s\Delta`; kept only safe ordering statement. |
| `src/chapters/chapter8.tex:9` | Resolved | Replaced `A_2 \ge 1` by global bound `A_2 \ge 1 - d_0/N` (via `eq:A2-lower-bound`). |
| `src/chapters/chapter7.tex:412` | Resolved | Replaced `A_2 \ge 1` by `A_2 \ge 1 - d_0/N` in runtime discussion. |
| `src/chapters/chapter9.tex:254` | Resolved | Replaced false `d_{i+1} \ge d_i/2` step with a valid recurrence-based shell-occupancy argument. |
| `src/chapters/chapter9.tex:311` | Resolved | Replaced invalid MI-vs-TV step with a chain-rule entropy bound via failure indicator decomposition. |
| `src/chapters/chapter9.tex:348` | Resolved | Added explicit boundary case `\beta=1/\alpha` with logarithmic scaling. |

## Non-Blocker / Excluded Items

| Location | Status | Reason |
|---|---|---|
| `src/chapters/chapter7.tex:385` | Excluded (thesis-safe variant) | `A_1(A_1+1)` vs paper's `A_1^2` is explicitly footnoted and internally consistent; no fix required. |
| `src/chapters/chapter9.tex:526` | Excluded (not a correctness failure) | Proposition is concise and follows the preceding determinant-branch derivation; proof expansion is optional exposition work. |
| `src/chapters/chapter9.tex:533` | Excluded (not a correctness failure) | Proposition statement already contains the core trace/continuity argument; adding a separate proof is optional formalization. |
| `src/chapters/chapter9.tex:651` | Excluded (not a correctness failure) | This is an expository complexity-landscape claim with inline examples; more formal proof is optional. |
| `src/chapters/chapter9.tex:32` | Excluded (wording-level only) | Running-example `s^*=3/7` is a first-order/rank-one parameter illustration; exact-vs-approx qualifier is editorial, not a blocker. |
| `src/chapters/chapter9.tex:299` | Excluded (wording-level only) | Same as line 32; clarification is optional and not correctness-critical. |

## Reconciliation Notes (Chapter 9 Audit Alignment)

The following items were flagged in `run/chap9_pass0.md` but were not explicitly reflected in the original ledger draft. They are now tracked here for audit continuity.

| Source finding | Location | Current status | Reconciliation note |
|---|---|---|---|
| C1 precision-propagation bound justification | `src/chapters/chapter9.tex:101` | Resolved | Proof now uses exact identity `eq:precision-exact` and the denominator lower bound under `|\varepsilon| \le (1+A_1)/2`. |
| M1 ETH reduction mechanism citation | `src/chapters/chapter9.tex:688` | Resolved | Proof sketch now cites NP-hardness reduction route (`thm:np-hard-A1`) plus monotonicity from finer to coarser precision. |
| M2 Hedging error-functional derivation | `src/chapters/chapter9.tex:161` | Resolved | Theorem proof now explicitly derives the objective from JRS bound normalization. |
| M3 Scaling-spectrum convergence condition | `src/chapters/chapter9.tex:355` | Resolved | Proof now states integrability window `1/\alpha < p < 3 - 1/\alpha` and checks `p=3/2` for `\alpha > 2/3`. |
| M4 Missing spectral-condition assumption | `src/chapters/chapter9.tex:408` | Resolved | Theorem statement now includes “Under the spectral condition of Chapter~5”. |
| m1 Window-width notation clarity | `src/chapters/chapter9.tex:273` | Resolved | Runtime proof now states `O(2^{-n/2}) = O(\delta_s)`. |
| m2 Gap-integral convergence wording | `src/chapters/chapter9.tex:352` | Resolved | Proof now distinguishes convergence at `u \to \infty` and at `u=0`. |
| m3 Theorem 9.1 notation consistency | `src/chapters/chapter9.tex:64` | No blocker | Statement/proof remain asymptotically consistent (`\Omega` lower bound with matching scaling context). |


## Chapter 5 Formal-Claim Checklist

| Item | Type | Location | Anchor | Status | Action |
|---|---|---|---|---|---|
| 1 | label | `src/chapters/chapter5.tex:28` | `eq:Hz-def` | Pass | - |
| 2 | label | `src/chapters/chapter5.tex:35` | `eq:eigenvalues-ordered` | Pass | - |
| 3 | label | `src/chapters/chapter5.tex:40` | `eq:Omega-k-def` | Pass | - |
| 4 | label | `src/chapters/chapter5.tex:47` | `eq:Ising-Ham` | Pass | - |
| 5 | label | `src/chapters/chapter5.tex:56` | `eq:H0-def` | Pass | - |
| 6 | label | `src/chapters/chapter5.tex:63` | `eq:H(s)-def` | Pass | - |
| 7 | definition | `src/chapters/chapter5.tex:80` | `\begin{definition}[Spectral parameters]` | Pass | - |
| 8 | label | `src/chapters/chapter5.tex:81` | `def:spectral-parameters` | Pass | - |
| 9 | label | `src/chapters/chapter5.tex:84` | `eq:Ap-def` | Pass | - |
| 10 | label | `src/chapters/chapter5.tex:93` | `eq:Ap-grover` | Pass | - |
| 11 | label | `src/chapters/chapter5.tex:104` | `eq:A2-lower-bound` | Pass | - |
| 12 | definition | `src/chapters/chapter5.tex:111` | `\begin{definition}[Spectral condition]` | Pass | - |
| 13 | label | `src/chapters/chapter5.tex:112` | `def:spectral-condition` | Pass | - |
| 14 | label | `src/chapters/chapter5.tex:115` | `eq:spectral-condition` | Pass | - |
| 15 | label | `src/chapters/chapter5.tex:132` | `eq:symmetric-state` | Pass | - |
| 16 | label | `src/chapters/chapter5.tex:137` | `eq:HS-def` | Pass | - |
| 17 | label | `src/chapters/chapter5.tex:143` | `eq:Hz-symmetric` | Pass | - |
| 18 | label | `src/chapters/chapter5.tex:148` | `eq:psi0-symmetric` | Pass | - |
| 19 | label | `src/chapters/chapter5.tex:155` | `eq:fourier-basis` | Pass | - |
| 20 | label | `src/chapters/chapter5.tex:160` | `eq:HS-perp` | Pass | - |
| 21 | label | `src/chapters/chapter5.tex:171` | `eq:H(s)-restricted` | Pass | - |
| 22 | lemma | `src/chapters/chapter5.tex:176` | `\begin{lemma}[Eigenvalue equation]` | Pass | - |
| 23 | label | `src/chapters/chapter5.tex:177` | `lem:eigenvalue-equation` | Pass | - |
| 24 | label | `src/chapters/chapter5.tex:180` | `eq:eigenvalue-equation` | Pass | - |
| 25 | label | `src/chapters/chapter5.tex:192` | `eq:alpha-k-expression` | Pass | - |
| 26 | label | `src/chapters/chapter5.tex:212` | `eq:grover-eigenvalues` | Pass | - |
| 27 | label | `src/chapters/chapter5.tex:217` | `eq:grover-gap` | Pass | - |
| 28 | label | `src/chapters/chapter5.tex:230` | `eq:delta-equation` | Pass | - |
| 29 | label | `src/chapters/chapter5.tex:239` | `eq:delta-pm-formula` | Pass | - |
| 30 | label | `src/chapters/chapter5.tex:244` | `eq:s-star-def` | Pass | - |
| 31 | lemma | `src/chapters/chapter5.tex:253` | `\begin{lemma}[Validity of approximation]` | Pass | - |
| 32 | label | `src/chapters/chapter5.tex:254` | `lem:validity-approximation` | Pass | - |
| 33 | label | `src/chapters/chapter5.tex:257` | `eq:delta-s-def` | Pass | - |
| 34 | label | `src/chapters/chapter5.tex:272` | `eq:gap-formula-window` | Pass | - |
| 35 | label | `src/chapters/chapter5.tex:277` | `eq:gmin-formula` | Pass | - |
| 36 | label | `src/chapters/chapter5.tex:284` | `eq:gmin-deltas-relation` | Pass | - |
| 37 | label | `src/chapters/chapter5.tex:291` | `eq:three-regions` | Pass | - |
| 38 | lemma | `src/chapters/chapter5.tex:296` | `\begin{lemma}[Gap within the crossing window]` | Pass | - |
| 39 | label | `src/chapters/chapter5.tex:297` | `lem:gap-in-window` | Pass | - |
| 40 | label | `src/chapters/chapter5.tex:300` | `eq:kappa-prime` | Pass | - |
| 41 | label | `src/chapters/chapter5.tex:305` | `eq:gap-window-bounds` | Pass | - |
| 42 | label | `src/chapters/chapter5.tex:334` | `eq:grover-s-star` | Pass | - |
| 43 | label | `src/chapters/chapter5.tex:335` | `eq:grover-gmin` | Pass | - |
| 44 | label | `src/chapters/chapter5.tex:336` | `eq:grover-deltas` | Pass | - |
| 45 | lemma | `src/chapters/chapter5.tex:346` | `\begin{lemma}[Gap to the left of the crossing]` | Pass | - |
| 46 | label | `src/chapters/chapter5.tex:347` | `lem:gap-left-preview` | Pass | - |
| 47 | label | `src/chapters/chapter5.tex:350` | `eq:gap-left-bound` | Pass | - |
| 48 | label | `src/chapters/chapter5.tex:357` | `eq:variational-ansatz` | Pass | - |
| 49 | lemma | `src/chapters/chapter5.tex:362` | `\begin{lemma}[Gap to the right of the crossing]` | Review-needed | Propagate the `A_1 \geq 1/2` (or equivalent) hypothesis used in Chapter 6 right-gap proof, unless proof is strengthened to remove it. |
| 50 | label | `src/chapters/chapter5.tex:363` | `lem:gap-right-preview` | Pass | - |
| 51 | label | `src/chapters/chapter5.tex:366` | `eq:s0-def` | Pass | - |
| 52 | label | `src/chapters/chapter5.tex:371` | `eq:gap-right-bound` | Pass | - |
| 53 | label | `src/chapters/chapter5.tex:386` | `eq:runtime-integral-preview` | Pass | - |
| 54 | label | `src/chapters/chapter5.tex:403` | `eq:runtime-preview` | Pass | - |

## Chapter 6 Formal-Claim Checklist

| Item | Type | Location | Anchor | Status | Action |
|---|---|---|---|---|---|
| 1 | lemma | `src/chapters/chapter6.tex:19` | `\begin{lemma}[Gap to the left of the crossing]` | Pass | - |
| 2 | label | `src/chapters/chapter6.tex:20` | `lem:gap-left` | Pass | - |
| 3 | label | `src/chapters/chapter6.tex:23` | `eq:gap-left` | Pass | - |
| 4 | label | `src/chapters/chapter6.tex:33` | `eq:ansatz-left` | Pass | - |
| 5 | label | `src/chapters/chapter6.tex:56` | `eq:variational-bound` | Pass | - |
| 6 | label | `src/chapters/chapter6.tex:61` | `eq:lambda0-upper` | Pass | - |
| 7 | label | `src/chapters/chapter6.tex:103` | `eq:resolvent-def` | Pass | - |
| 8 | label | `src/chapters/chapter6.tex:108` | `eq:resolvent-norm` | Pass | - |
| 9 | label | `src/chapters/chapter6.tex:113` | `eq:gap-resolvent` | Pass | - |
| 10 | label | `src/chapters/chapter6.tex:126` | `eq:sherman-morrison` | Pass | - |
| 11 | label | `src/chapters/chapter6.tex:139` | `eq:s0-definition` | Pass | - |
| 12 | lemma | `src/chapters/chapter6.tex:144` | `\begin{lemma}[Gap to the right of the crossing]` | Pass | - |
| 13 | label | `src/chapters/chapter6.tex:145` | `lem:gap-right` | Pass | - |
| 14 | label | `src/chapters/chapter6.tex:148` | `eq:gap-right` | Pass | - |
| 15 | label | `src/chapters/chapter6.tex:158` | `eq:resolvent-SM` | Pass | - |
| 16 | label | `src/chapters/chapter6.tex:172` | `eq:numerator-bound` | Pass | - |
| 17 | label | `src/chapters/chapter6.tex:183` | `eq:denominator-bound` | Pass | - |
| 18 | label | `src/chapters/chapter6.tex:189` | `eq:resolvent-f` | Pass | - |
| 19 | label | `src/chapters/chapter6.tex:194` | `eq:f-definition` | Pass | - |
| 20 | label | `src/chapters/chapter6.tex:207` | `eq:gap-via-f` | Pass | - |
| 21 | label | `src/chapters/chapter6.tex:214` | `eq:uv-def` | Pass | - |
| 22 | label | `src/chapters/chapter6.tex:222` | `eq:u-prime` | Pass | - |
| 23 | label | `src/chapters/chapter6.tex:228` | `eq:upv-uvp` | Pass | - |
| 24 | label | `src/chapters/chapter6.tex:237` | `eq:domination-argument` | Pass | - |
| 25 | label | `src/chapters/chapter6.tex:246` | `eq:a-constraint` | Pass | - |
| 26 | label | `src/chapters/chapter6.tex:257` | `eq:f-at-sstar` | Pass | - |
| 27 | theorem | `src/chapters/chapter6.tex:284` | `\begin{theorem}[Complete gap profile]` | Review-needed | Right-gap input lemma is currently proved under `A_1 \geq 1/2`; theorem hypotheses should match or proof should be generalized. |
| 28 | label | `src/chapters/chapter6.tex:285` | `thm:complete-profile` | Pass | - |
| 29 | label | `src/chapters/chapter6.tex:288` | `eq:piecewise-bound` | Pass | - |

## Chapter 7 Formal-Claim Checklist

| Item | Type | Location | Anchor | Status | Action |
|---|---|---|---|---|---|
| 1 | label | `src/chapters/chapter7.tex:22` | `eq:jrs-bound` | Pass | - |
| 2 | label | `src/chapters/chapter7.tex:27` | `eq:jrs-runtime` | Pass | - |
| 3 | label | `src/chapters/chapter7.tex:34` | `eq:roland-cerf-runtime` | Pass | - |
| 4 | label | `src/chapters/chapter7.tex:39` | `eq:roland-cerf-integral` | Pass | - |
| 5 | label | `src/chapters/chapter7.tex:53` | `eq:reparametrized-evolution` | Pass | - |
| 6 | label | `src/chapters/chapter7.tex:60` | `eq:error-def` | Pass | - |
| 7 | label | `src/chapters/chapter7.tex:65` | `eq:pseudoinverse-def` | Pass | - |
| 8 | lemma | `src/chapters/chapter7.tex:70` | `\begin{lemma}[Adiabatic error bound {\cite{braida2024unstructured, cunningham2024eigenpath}}]` | Pass | - |
| 9 | label | `src/chapters/chapter7.tex:71` | `lem:error-bound` | Pass | - |
| 10 | label | `src/chapters/chapter7.tex:74` | `eq:error-bound` | Pass | - |
| 11 | lemma | `src/chapters/chapter7.tex:110` | `\begin{lemma}[Projector derivative bounds {\cite{braida2024unstructured}}]` | Pass | - |
| 12 | label | `src/chapters/chapter7.tex:111` | `lem:derivative-bounds` | Pass | - |
| 13 | label | `src/chapters/chapter7.tex:114` | `eq:P-prime-bound` | Pass | - |
| 14 | label | `src/chapters/chapter7.tex:116` | `eq:commutator-bound` | Pass | - |
| 15 | label | `src/chapters/chapter7.tex:118` | `eq:commutator-deriv-bound` | Pass | - |
| 16 | label | `src/chapters/chapter7.tex:142` | `eq:pseudoinverse-derivative` | Pass | - |
| 17 | label | `src/chapters/chapter7.tex:147` | `eq:pseudoinverse-deriv-bound` | Pass | - |
| 18 | label | `src/chapters/chapter7.tex:157` | `eq:P-double-prime-bound` | Pass | - |
| 19 | theorem | `src/chapters/chapter7.tex:173` | `\begin{theorem}[Constant-rate runtime]` | Pass | - |
| 20 | label | `src/chapters/chapter7.tex:174` | `thm:constant-rate` | Pass | - |
| 21 | label | `src/chapters/chapter7.tex:177` | `eq:constant-rate-formula` | Pass | - |
| 22 | label | `src/chapters/chapter7.tex:192` | `eq:constant-rate-window` | Pass | - |
| 23 | theorem | `src/chapters/chapter7.tex:208` | `\begin{theorem}[Adaptive rate {\cite{braida2024unstructured}}]` | Review-needed | Align theorem hypotheses with proof constants or generalize proof. |
| 24 | label | `src/chapters/chapter7.tex:209` | `thm:adaptive-rate` | Review-needed | Same as theorem at line 208. |
| 25 | label | `src/chapters/chapter7.tex:212` | `eq:B1-condition` | Pass | - |
| 26 | label | `src/chapters/chapter7.tex:217` | `eq:c-constant` | Pass | - |
| 27 | label | `src/chapters/chapter7.tex:222` | `eq:adaptive-schedule` | Pass | - |
| 28 | label | `src/chapters/chapter7.tex:227` | `eq:adaptive-runtime` | Pass | - |
| 29 | label | `src/chapters/chapter7.tex:235` | `eq:adaptive-error-expanded` | Pass | - |
| 30 | label | `src/chapters/chapter7.tex:248` | `eq:proof-term-H-prime` | Pass | - |
| 31 | label | `src/chapters/chapter7.tex:252` | `eq:proof-term-H-double-prime` | Pass | - |
| 32 | label | `src/chapters/chapter7.tex:259` | `eq:proof-schedule-variation` | Pass | - |
| 33 | corollary | `src/chapters/chapter7.tex:276` | `\begin{corollary}` | Pass | - |
| 34 | label | `src/chapters/chapter7.tex:277` | `cor:ideal-case` | Pass | - |
| 35 | lemma | `src/chapters/chapter7.tex:285` | `\begin{lemma}[Grover gap integral]` | Pass | - |
| 36 | label | `src/chapters/chapter7.tex:286` | `lem:grover-integral` | Pass | - |
| 37 | label | `src/chapters/chapter7.tex:289` | `eq:grover-integral-bound` | Pass | - |
| 38 | label | `src/chapters/chapter7.tex:319` | `eq:g0-def` | Pass | - |
| 39 | label | `src/chapters/chapter7.tex:328` | `eq:b-def` | Pass | - |
| 40 | label | `src/chapters/chapter7.tex:342` | `eq:B1-left` | Pass | - |
| 41 | label | `src/chapters/chapter7.tex:346` | `eq:B1-window` | Pass | - |
| 42 | label | `src/chapters/chapter7.tex:354` | `eq:B1-right` | Pass | - |
| 43 | label | `src/chapters/chapter7.tex:360` | `eq:B1-result` | Pass | - |
| 44 | label | `src/chapters/chapter7.tex:366` | `eq:B2-result` | Pass | - |
| 45 | label | `src/chapters/chapter7.tex:376` | `eq:c-result` | Pass | - |
| 46 | theorem | `src/chapters/chapter7.tex:380` | `\begin{theorem}[Runtime of AQO --- Main Result 1 {\cite{braida2024unstructured}}]` | Review-needed | If `thm:complete-profile` keeps an extra `A_1 \geq 1/2`-type hypothesis, propagate it here (or remove by strengthening upstream proof). |
| 47 | label | `src/chapters/chapter7.tex:381` | `thm:aqo-runtime` | Pass | - |
| 48 | label | `src/chapters/chapter7.tex:384` | `eq:main-runtime` | Pass | - |

## Chapter 8 Formal-Claim Checklist

| Item | Type | Location | Anchor | Status | Action |
|---|---|---|---|---|---|
| 1 | label | `src/chapters/chapter8.tex:23` | `eq:modified-ham` | Pass | - |
| 2 | lemma | `src/chapters/chapter8.tex:28` | `\begin{lemma}[Disambiguation {\cite{braida2024unstructured}}]` | Pass | - |
| 3 | label | `src/chapters/chapter8.tex:29` | `lem:disambiguation` | Pass | - |
| 4 | label | `src/chapters/chapter8.tex:32` | `eq:disambiguation-bound` | Pass | - |
| 5 | label | `src/chapters/chapter8.tex:54` | `eq:A1-decomposition` | Pass | - |
| 6 | label | `src/chapters/chapter8.tex:64` | `eq:disambiguation-gap` | Pass | - |
| 7 | theorem | `src/chapters/chapter8.tex:79` | `\begin{theorem}[NP-hardness of $A_1$ estimation {\cite{braida2024unstructured}}]` | Pass | - |
| 8 | label | `src/chapters/chapter8.tex:80` | `thm:np-hard-A1` | Pass | - |
| 9 | label | `src/chapters/chapter8.tex:98` | `eq:clause-ham` | Pass | - |
| 10 | label | `src/chapters/chapter8.tex:102` | `eq:3sat-ham` | Pass | - |
| 11 | label | `src/chapters/chapter8.tex:109` | `eq:precision-arithmetic` | Pass | - |
| 12 | label | `src/chapters/chapter8.tex:131` | `eq:param-ham` | Pass | - |
| 13 | label | `src/chapters/chapter8.tex:138` | `eq:f-function` | Pass | - |
| 14 | lemma | `src/chapters/chapter8.tex:143` | `\begin{lemma}[Exact degeneracy extraction {\cite{braida2024unstructured}}]` | Pass | - |
| 15 | label | `src/chapters/chapter8.tex:144` | `lem:exact-degeneracy` | Pass | - |
| 16 | label | `src/chapters/chapter8.tex:153` | `eq:recon-poly` | Pass | - |
| 17 | label | `src/chapters/chapter8.tex:160` | `eq:degeneracy-extraction` | Pass | - |
| 18 | lemma | `src/chapters/chapter8.tex:170` | `\begin{lemma}[Paturi {\cite{paturi1992}}]` | Pass | - |
| 19 | label | `src/chapters/chapter8.tex:171` | `lem:paturi` | Pass | - |
| 20 | lemma | `src/chapters/chapter8.tex:177` | `\begin{lemma}[Approximate degeneracy extraction {\cite{braida2024unstructured}}]` | Pass | - |
| 21 | label | `src/chapters/chapter8.tex:178` | `lem:approx-degeneracy` | Pass | - |
| 22 | theorem | `src/chapters/chapter8.tex:196` | `\begin{theorem}[$\#$P-hardness of $A_1$ estimation {\cite{braida2024unstructured}}]` | Pass | - |
| 23 | label | `src/chapters/chapter8.tex:197` | `thm:sharp-P-hard-A1` | Pass | - |
| 24 | theorem | `src/chapters/chapter8.tex:213` | `\begin{theorem}[Interpolation barrier]` | Pass | - |
| 25 | label | `src/chapters/chapter8.tex:214` | `thm:interpolation-barrier` | Pass | - |
| 26 | label | `src/chapters/chapter8.tex:223` | `eq:sample-error` | Pass | - |
| 27 | label | `src/chapters/chapter8.tex:229` | `eq:interp-error` | Pass | - |
| 28 | label | `src/chapters/chapter8.tex:234` | `eq:lebesgue-bound` | Pass | - |
| 29 | label | `src/chapters/chapter8.tex:239` | `eq:total-error` | Pass | - |
| 30 | label | `src/chapters/chapter8.tex:246` | `eq:rounding-condition` | Pass | - |
| 31 | theorem | `src/chapters/chapter8.tex:261` | `\begin{theorem}[Generic extrapolation barrier]` | Review-needed | Quantifier wording should reflect worst-case amplification, not universal per-instance lower bound. |
| 32 | label | `src/chapters/chapter8.tex:262` | `thm:generic-barrier` | Pass | - |
| 33 | theorem | `src/chapters/chapter8.tex:280` | `\begin{theorem}[Quantum algorithm for $A_1$]` | Pass | - |
| 34 | label | `src/chapters/chapter8.tex:281` | `thm:quantum-A1` | Pass | - |
| 35 | label | `src/chapters/chapter8.tex:284` | `eq:quantum-complexity` | Pass | - |
| 36 | theorem | `src/chapters/chapter8.tex:314` | `\begin{theorem}[Classical lower bound for $A_1$ estimation]` | Pass | - |
| 37 | label | `src/chapters/chapter8.tex:315` | `thm:classical-lower-A1` | Pass | - |
| 38 | corollary | `src/chapters/chapter8.tex:339` | `\begin{corollary}[Quadratic quantum-classical separation]` | Pass | - |
| 39 | label | `src/chapters/chapter8.tex:340` | `cor:quadratic-separation` | Pass | - |

## Chapter 9 Formal-Claim Checklist

| Item | Type | Location | Anchor | Status | Action |
|---|---|---|---|---|---|
| 1 | definition | `src/chapters/chapter9.tex:27` | `\begin{definition}[Gap class]` | Pass | - |
| 2 | label | `src/chapters/chapter9.tex:28` | `def:gap-class` | Pass | - |
| 3 | lemma | `src/chapters/chapter9.tex:42` | `\begin{lemma}[Adversarial gap construction]` | Pass | - |
| 4 | label | `src/chapters/chapter9.tex:43` | `lem:adversarial-gap` | Pass | - |
| 5 | lemma | `src/chapters/chapter9.tex:51` | `\begin{lemma}[Velocity bound for uninformed schedules]` | Pass | - |
| 6 | label | `src/chapters/chapter9.tex:52` | `lem:velocity-bound` | Pass | - |
| 7 | theorem | `src/chapters/chapter9.tex:64` | `\begin{theorem}[Separation]` | Review-needed | Theorem scope is generic `\mathcal{G}`, but proof of `T_{\mathrm{inf}}` uses rank-one-specific assumptions (`chapter9.tex:78`); align statement and proof scope. |
| 8 | label | `src/chapters/chapter9.tex:65` | `thm:separation` | Pass | - |
| 9 | label | `src/chapters/chapter9.tex:68` | `eq:separation-ratio` | Pass | - |
| 10 | corollary | `src/chapters/chapter9.tex:84` | `\begin{corollary}[Unstructured search]` | Pass | - |
| 11 | label | `src/chapters/chapter9.tex:85` | `cor:separation-grover` | Pass | - |
| 12 | lemma | `src/chapters/chapter9.tex:101` | `\begin{lemma}[$A_1$-to-$s^*$ precision propagation]` | Pass | C1 reconciled: exact-identity proof now present. |
| 13 | label | `src/chapters/chapter9.tex:102` | `lem:precision-propagation` | Pass | - |
| 14 | label | `src/chapters/chapter9.tex:109` | `eq:precision-exact` | Pass | - |
| 15 | theorem | `src/chapters/chapter9.tex:120` | `\begin{theorem}[Interpolation]` | Pass | - |
| 16 | label | `src/chapters/chapter9.tex:121` | `thm:interpolation` | Pass | - |
| 17 | label | `src/chapters/chapter9.tex:124` | `eq:interpolation` | Pass | - |
| 18 | label | `src/chapters/chapter9.tex:133` | `eq:precision-identity` | Pass | - |
| 19 | theorem | `src/chapters/chapter9.tex:161` | `\begin{theorem}[Hedging]` | Pass | M2 reconciled: JRS-derived error functional now explicit. |
| 20 | label | `src/chapters/chapter9.tex:162` | `thm:hedging` | Pass | - |
| 21 | definition | `src/chapters/chapter9.tex:206` | `\begin{definition}[Adaptive adiabatic protocol]` | Pass | - |
| 22 | label | `src/chapters/chapter9.tex:207` | `def:adaptive-protocol` | Pass | - |
| 23 | lemma | `src/chapters/chapter9.tex:227` | `\begin{lemma}[Phase estimation cost]` | Pass | - |
| 24 | label | `src/chapters/chapter9.tex:228` | `lem:phase-estimation-cost` | Pass | - |
| 25 | lemma | `src/chapters/chapter9.tex:236` | `\begin{lemma}[Phase 1 cost]` | Pass | Recurrence-based shell occupancy argument now replaces the invalid midpoint-distance inequality. |
| 26 | label | `src/chapters/chapter9.tex:237` | `lem:phase1-cost` | Pass | - |
| 27 | label | `src/chapters/chapter9.tex:244` | `eq:gap-lower-bound` | Pass | - |
| 28 | label | `src/chapters/chapter9.tex:249` | `eq:pe-cost` | Pass | - |
| 29 | theorem | `src/chapters/chapter9.tex:267` | `\begin{theorem}[Adaptive adiabatic optimality]` | Pass | - |
| 30 | label | `src/chapters/chapter9.tex:268` | `thm:adaptive` | Pass | - |
| 31 | theorem | `src/chapters/chapter9.tex:276` | `\begin{theorem}[Measurement lower bound]` | Review-needed | The proof at `chapter9.tex:282` assumes binary/O(1)-bit measurement outcomes; restrict theorem scope or prove this information cap in the stated adaptive model. |
| 32 | label | `src/chapters/chapter9.tex:277` | `thm:measurement-lower` | Pass | - |
| 33 | proposition | `src/chapters/chapter9.tex:305` | `\begin{proposition}[$A_1$-blindness]` | Pass | Proof now uses a valid chain-rule/entropy decomposition with explicit failure-event control. |
| 34 | label | `src/chapters/chapter9.tex:306` | `prop:A1-blindness` | Pass | - |
| 35 | theorem | `src/chapters/chapter9.tex:326` | `\begin{theorem}[Geometric characterization]` | Pass | - |
| 36 | label | `src/chapters/chapter9.tex:327` | `thm:geometric-char` | Pass | - |
| 37 | lemma | `src/chapters/chapter9.tex:341` | `\begin{lemma}[Gap integral]` | Pass | Statement and proof now separate `\beta>1/\alpha`, `\beta=1/\alpha`, `\beta<1/\alpha`. |
| 38 | label | `src/chapters/chapter9.tex:342` | `lem:gap-integral` | Pass | - |
| 39 | label | `src/chapters/chapter9.tex:345` | `eq:gap-integral` | Pass | - |
| 40 | theorem | `src/chapters/chapter9.tex:355` | `\begin{theorem}[Scaling spectrum]` | Pass | M3 reconciled: convergence window and `p=3/2` condition explicit. |
| 41 | label | `src/chapters/chapter9.tex:356` | `thm:scaling-spectrum` | Pass | - |
| 42 | label | `src/chapters/chapter9.tex:359` | `eq:scaling-spectrum` | Pass | - |
| 43 | remark | `src/chapters/chapter9.tex:391` | `\begin{remark}` | Pass | - |
| 44 | proposition | `src/chapters/chapter9.tex:395` | `\begin{proposition}[Structural $\alpha = 1$]` | Pass | - |
| 45 | label | `src/chapters/chapter9.tex:396` | `prop:structural-alpha` | Pass | - |
| 46 | theorem | `src/chapters/chapter9.tex:408` | `\begin{theorem}[Measure condition for the rank-one gap profile]` | Pass | M4 reconciled: spectral-condition hypothesis explicit. |
| 47 | label | `src/chapters/chapter9.tex:409` | `thm:measure-paper` | Pass | - |
| 48 | label | `src/chapters/chapter9.tex:412` | `eq:measure-constant` | Pass | - |
| 49 | corollary | `src/chapters/chapter9.tex:422` | `\begin{corollary}[Grover measure constant]` | Pass | - |
| 50 | label | `src/chapters/chapter9.tex:423` | `cor:grover-C` | Pass | - |
| 51 | theorem | `src/chapters/chapter9.tex:435` | `\begin{theorem}[Constant comparison]` | Pass | - |
| 52 | label | `src/chapters/chapter9.tex:436` | `thm:constant-comparison` | Pass | - |
| 53 | remark | `src/chapters/chapter9.tex:444` | `\begin{remark}` | Pass | - |
| 54 | theorem | `src/chapters/chapter9.tex:462` | `\begin{theorem}[Product ancilla invariance]` | Pass | - |
| 55 | label | `src/chapters/chapter9.tex:463` | `thm:product-ancilla` | Pass | - |
| 56 | remark | `src/chapters/chapter9.tex:471` | `\begin{remark}` | Pass | - |
| 57 | theorem | `src/chapters/chapter9.tex:475` | `\begin{theorem}[Universality of uniform superposition]` | Pass | - |
| 58 | label | `src/chapters/chapter9.tex:476` | `thm:universality` | Pass | - |
| 59 | corollary | `src/chapters/chapter9.tex:490` | `\begin{corollary}` | Pass | - |
| 60 | label | `src/chapters/chapter9.tex:491` | `cor:universality` | Pass | - |
| 61 | theorem | `src/chapters/chapter9.tex:495` | `\begin{theorem}[Coupled ancilla limitation]` | Pass | - |
| 62 | label | `src/chapters/chapter9.tex:496` | `thm:coupled-ancilla` | Pass | - |
| 63 | theorem | `src/chapters/chapter9.tex:504` | `\begin{theorem}[Multi-segment rigidity]` | Pass | - |
| 64 | label | `src/chapters/chapter9.tex:505` | `thm:multi-segment` | Pass | - |
| 65 | theorem | `src/chapters/chapter9.tex:513` | `\begin{theorem}[No-go]` | Pass | - |
| 66 | label | `src/chapters/chapter9.tex:514` | `thm:no-go` | Pass | - |
| 67 | proposition | `src/chapters/chapter9.tex:526` | `\begin{proposition}[Rank-$k$ two-level obstruction]` | Pass | Concise proposition backed by the preceding determinant-branch derivation; proof expansion is optional. |
| 68 | label | `src/chapters/chapter9.tex:527` | `prop:rank-k-obstruction` | Pass | - |
| 69 | proposition | `src/chapters/chapter9.tex:533` | `\begin{proposition}[Trace no-go]` | Pass | Core trace/continuity reasoning is already present in the proposition statement; separate proof is optional formalization. |
| 70 | label | `src/chapters/chapter9.tex:534` | `prop:trace-nogo` | Pass | - |
| 71 | remark | `src/chapters/chapter9.tex:538` | `\begin{remark}` | Pass | - |
| 72 | proposition | `src/chapters/chapter9.tex:544` | `\begin{proposition}[Constant-control optimality on two-level family]` | Pass | - |
| 73 | label | `src/chapters/chapter9.tex:545` | `prop:constant-control` | Pass | - |
| 74 | proposition | `src/chapters/chapter9.tex:567` | `\begin{proposition}[Normalized-control lower bound]` | Pass | - |
| 75 | label | `src/chapters/chapter9.tex:568` | `prop:normalized-control` | Pass | - |
| 76 | proposition | `src/chapters/chapter9.tex:588` | `\begin{proposition}[$A_1$ hardness is counting hardness]` | Pass | - |
| 77 | label | `src/chapters/chapter9.tex:589` | `prop:counting-hardness` | Pass | - |
| 78 | label | `src/chapters/chapter9.tex:599` | `eq:A1-laplace` | Pass | - |
| 79 | label | `src/chapters/chapter9.tex:604` | `eq:A1-proxy` | Pass | - |
| 80 | proposition | `src/chapters/chapter9.tex:609` | `\begin{proposition}[Bounded treewidth tractability]` | Pass | - |
| 81 | label | `src/chapters/chapter9.tex:610` | `prop:treewidth` | Pass | - |
| 82 | proposition | `src/chapters/chapter9.tex:622` | `\begin{proposition}[Reverse bridge obstruction]` | Pass | - |
| 83 | label | `src/chapters/chapter9.tex:623` | `prop:reverse-bridge` | Pass | - |
| 84 | proposition | `src/chapters/chapter9.tex:633` | `\begin{proposition}[Unique solution does not imply easy $A_1$]` | Pass | - |
| 85 | label | `src/chapters/chapter9.tex:634` | `prop:conjecture-unique` | Pass | - |
| 86 | proposition | `src/chapters/chapter9.tex:642` | `\begin{proposition}[Bounded degeneracy is vacuous]` | Pass | - |
| 87 | label | `src/chapters/chapter9.tex:643` | `prop:conjecture-bounded` | Pass | - |
| 88 | proposition | `src/chapters/chapter9.tex:651` | `\begin{proposition}[Hard optimization does not imply hard $A_1$]` | Pass | Expository claim supported by standard examples (`2`-SAT vs `\#2`-SAT, promised Grover family); formal expansion is optional. |
| 89 | label | `src/chapters/chapter9.tex:652` | `prop:conjecture-hard-opt` | Pass | - |
| 90 | theorem | `src/chapters/chapter9.tex:664` | `\begin{theorem}[Tight quantum query complexity]` | Review-needed | Clarify precision regime/assumptions so `\sqrt{N}` term from `thm:quantum-A1` is not silently dropped. |
| 91 | label | `src/chapters/chapter9.tex:665` | `thm:tight-quantum` | Pass | - |
| 92 | proposition | `src/chapters/chapter9.tex:679` | `\begin{proposition}[Precision phase diagram]` | Review-needed | “Every precision scale” claim should be aligned with theorem assumptions or narrowed to schedule-relevant precision range. |
| 93 | label | `src/chapters/chapter9.tex:680` | `prop:precision-phase` | Pass | - |
| 94 | theorem | `src/chapters/chapter9.tex:688` | `\begin{theorem}[ETH computational complexity]` | Pass | M1 reconciled: reduction mechanism/citation corrected. |
| 95 | label | `src/chapters/chapter9.tex:689` | `thm:eth` | Pass | - |
| 96 | corollary | `src/chapters/chapter9.tex:699` | `\begin{corollary}[Quantum pre-computation cost]` | Pass | - |
| 97 | label | `src/chapters/chapter9.tex:700` | `cor:quantum-precomp` | Pass | - |
| 98 | theorem | `src/chapters/chapter9.tex:708` | `\begin{theorem}[Structure irrelevance]` | Review-needed | Strength of statement exceeds current proof rigor; add reduction or weaken claim. |
| 99 | label | `src/chapters/chapter9.tex:709` | `thm:structure-irrelevance` | Review-needed | Same as theorem at line 708. |
| 100 | theorem | `src/chapters/chapter9.tex:723` | `\begin{theorem}[Bit-runtime information law]` | Pass | - |
| 101 | label | `src/chapters/chapter9.tex:724` | `thm:bit-runtime` | Pass | - |

## Inline Math Assertions (Unlabeled)

| Location | Status | Assertion | Action |
|---|---|---|---|
| `src/chapters/chapter9.tex:282` | Warning | Claims each measurement yields only `O(1)` bits via an “effectively binary” outcome without model restrictions. | Restrict to binary probe model or supply a formal information bound for the stated adaptive setting. |
| `src/chapters/chapter9.tex:78` | Fail | Uses `T_{\mathrm{inf}}=\Theta(\Delta_*/v_{\mathrm{slow}})` via `\autoref{thm:aqo-runtime}` while claiming applicability to any `g \in \mathcal{G}`; this is rank-one-specific, not generic-gap-class justified. | Restrict theorem/proof scope or add explicit assumptions ensuring informed runtime scaling for the stated class. |
| `src/chapters/chapter9.tex:706` | Warning | Claims the generic-barrier distance condition holds from `x^*=\Theta(2^{-n/2})` and nodes in `[0,1/\mathrm{poly}(n)]`; this does not follow. | Replace parenthetical with a correct condition check tied to the concrete interpolation setup. |
