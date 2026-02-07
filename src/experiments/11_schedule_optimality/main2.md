# Schedule Optimality Open Threads (Continuation)

## Problem Statement

This continuation closes the two open threads left in Experiment 11:

1. Can the JRS-side runtime prefactor be made explicit (not hidden in `O(.)`)?
2. Do concrete non-power-law schedules improve over the p=2 and p=3/2 baselines?


## Why This Continuation Exists

`main.md` and `proof.md` resolved the core framework connection (Theorems A--H,
Proposition I, Remark J) but left two explicit open questions. This file and
`proof2.md` provide the next layer without rewriting the already-resolved core.


## Results

**Status**: RESOLVED (for the two stated open threads)

### Result 1: Explicit JRS Prefactor (Theorem K, Corollary K.1)

Using JRS Theorem 3 (`references/mds/jansen2007bounds.md`) plus the measure-condition
integral bounds used by Guo-An, the p-schedule certificate is

$$
T\ge \frac{B_{\mathrm{JRS}}(p)}{\epsilon_{\mathrm{ad}}\,\Delta_*},
$$

with

$$
B_{\mathrm{JRS}}(p)
=
\frac{2A_H C_\mu p}{p-1}
+
2A_H C_\mu
+
\frac{7A_H^2 C_\mu^2 p(3-p)}{(p-1)(2-p)}.
$$

For `p=3/2`:

$$
B_{\mathrm{JRS}}(3/2)=8A_HC_\mu+63A_H^2C_\mu^2.
$$

This is explicit and removes hidden `K`-style ambiguity at the certificate level.

### Result 2: Quantitative Constant Comparison with RC Certificates

At `N=1024` Grover (`A_H=2`, exact `C_mu=1`):
- `T_JRS^{cert}` coefficient (eps=1): `8576`
- `T_RC^{cert}` with exact `I_exact`: `3154.52` (JRS/RC = `2.7186`)
- `T_RC^{cert}` with coarse `I_bound`: `28910.12` (JRS/RC = `0.2966`)

For the structured instance from Remark J (`n=10` chain, `C_mu=157.449...`):
- `T_JRS^{cert}` coefficient: `2.7509e8`
- `T_RC^{cert}` coefficient: `3.0621e6`
- JRS/RC = `89.84`

Takeaway: explicit prefactors materially change "which certificate is tighter".
Structural `C_mu^2/I` alone is not sufficient.

### Result 3: Non-Power-Law Test (Theorem N)

Tested schedule family (RC-safe exponential slowdown):

$$
\frac{ds}{dt}=\frac{\epsilon_{\mathrm{ad}}}{A_H}\frac{g(s)^2}{e^{\beta/g(s)}},\quad \beta>0.
$$

For the canonical `alpha=1` linear-cusp model,

$$
\frac{T_{\exp}}{T_{\mathrm{RC}}}\ge \frac{1}{2}e^{\beta/g_{\min}}.
$$

Hence this explicit non-power-law family is asymptotically worse than both p=2 RC and
p=3/2 JRS certificates (which are `O(1/(epsilon_ad g_min))`).


## Novelty Assessment

This continuation adds genuine new content beyond framework matching:

1. Explicit prefactor extraction with closed form dependence on `(A_H, C_mu, p)`.
2. A quantitative criterion showing when prefactors overturn structural comparisons.
3. A closed-form non-power-law counterexample family with exponential overhead.


## Deliverables

- Full derivations: `src/experiments/11_schedule_optimality/proof2.md`
- Numerical verification: `src/experiments/11_schedule_optimality/lib/verify_open_threads.py`


## Scope Caveat

The non-power-law conclusion is for a specific family (exponential slowdown near the
crossing). It is not a no-go theorem for all non-power-law schedules.
Class-level closure for multiplicative penalty schedules appears in
`main3.md` and `proof3.md`.


## Connection Back to Main Experiment

`proof.md` established asymptotic framework equivalence and structural constants.
`proof2.md` resolves the remaining constant-level and schedule-family open threads.
Together they provide a practical schedule-selection picture with explicit runtime
certificates.
