# Schedule Optimality Open Threads (Round 3): Class-Level Non-Power-Law Closure

## Problem Statement

`main2.md` and `proof2.md` showed one explicit non-power-law family
(`Phi(g)=exp(beta/g)`) is asymptotically worse than RC/JRS baselines.
The residual question was whether this behavior generalizes beyond that single ansatz.


## New Result

**Status**: RESOLVED (for class-level slowdown penalties on the alpha=1 model)

In `proof3.md` we analyze the schedule class

$$
\frac{ds}{dt}
=
\frac{\epsilon_{\mathrm{ad}}}{A_H}\frac{g(s)^2}{\Phi(g(s))},
\quad \Phi(g)\ge 1,
$$

on the canonical alpha=1 linear-cusp model.

Main theorem (`proof3.md`, Theorem P):

$$
\frac{T_{\Phi}}{T_{\mathrm{RC}}}
\ge
\frac{\Phi(g_{\min})}{2(1-g_{\min}/c)}
>
\frac{1}{2}\Phi(g_{\min}).
$$

This is a class-level window-dominance bound and strictly generalizes the
exponential case from `proof2.md`.


## Regime Consequences

From Theorem P:

1. `Phi(g)=1+\lambda\log(1/g)` -> logarithmic overhead.
2. `Phi(g)=1+\lambda g^{-q}` -> polynomial overhead.
3. `Phi(g)=exp(beta/g^r)` -> stretched/exponential overhead.

Complement (`proof3.md`, Proposition Q):
if `Phi` is uniformly bounded (`1 <= Phi <= K`), runtime remains constant-factor
equivalent to RC (`1 <= T_Phi/T_RC <= K`).


## Novelty Delta vs `main2.md`

`main2.md` gave a single-family counterexample.
`main3.md` + `proof3.md` provide:

1. A class theorem with explicit lower bound constant.
2. A unified taxonomy of slowdown overhead regimes.
3. A bounded-penalty complement that closes the classification logic.


## Deliverables

- Theorem-level derivations: `src/experiments/11_schedule_optimality/proof3.md`
- Numerical checks (extended): `src/experiments/11_schedule_optimality/lib/verify_open_threads.py`


## Scope Caveat

This closure is class-level for multiplicative penalty schedules on the alpha=1
model. It is not a no-go theorem for every conceivable non-power-law strategy
outside that model/schedule class.
