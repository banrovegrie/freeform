# Schedule Optimality Open Threads (Round 3): Class-Level Non-Power-Law Penalty Theorem

## Scope

This continuation extends `proof2.md` from a single non-power-law family
(`Phi(g)=exp(beta/g)`) to a class-level statement that covers logarithmic,
polynomial, and exponential slowdown penalties in one theorem.

Notation follows `proof2.md`:
- `A_H`: Hamiltonian derivative norm.
- `epsilon_ad`: adiabatic error parameter in RC-style runtime certificates.
- `g_min`: minimum gap.


## 1. Setup: Penalty-Modified RC Schedules

Work on the canonical alpha=1 model used in Experiment 06 and `proof2.md`:

$$
g_{\mathrm{mod}}(s)=\max\big(g_{\min},\,c|s-1/2|\big),\quad 0<g_{\min}<c/2,\; c>0.
$$

Let
$$
g_{\max}:=\max_{s\in[0,1]} g_{\mathrm{mod}}(s)=\max(g_{\min},c/2)=c/2.
$$

Define a penalty-modified RC-safe schedule class:

$$
\frac{ds}{dt}
=
\frac{\varepsilon_{\mathrm{ad}}}{A_H}\frac{g(s)^2}{\Phi(g(s))},
$$

with measurable penalty `Phi:[g_min,g_max] -> [1,\infty)`.

The runtime is

$$
T_{\Phi}
=
\frac{A_H}{\varepsilon_{\mathrm{ad}}}
I_{\Phi},
\qquad
I_{\Phi}:=\int_0^1\frac{\Phi(g_{\mathrm{mod}}(s))}{g_{\mathrm{mod}}(s)^2}\,ds.
$$

The RC baseline corresponds to `Phi=1`:

$$
T_{\mathrm{RC}}
=
\frac{A_H}{\varepsilon_{\mathrm{ad}}}
I_{\mathrm{RC}},
\qquad
I_{\mathrm{RC}}=\int_0^1 g_{\mathrm{mod}}(s)^{-2}\,ds
=\frac{4}{cg_{\min}}-\frac{4}{c^2}.
$$


## 2. Main Theorem: Universal Window Lower Bound

**Theorem P (Class-level lower bound for slowdown penalties).**
For the schedule class above:

$$
\frac{T_{\Phi}}{T_{\mathrm{RC}}}
\ge
\frac{\Phi(g_{\min})}{2(1-g_{\min}/c)}
>
\frac{1}{2}\Phi(g_{\min}).
$$

In particular, any family with `Phi(g_min) -> infinity` as `g_min -> 0` is
asymptotically worse than RC by at least a diverging multiplicative factor.

*Proof.*
On the central window `|s-1/2|<=g_min/c`, the gap is constant:
`g_mod(s)=g_min`, and window length is `2g_min/c`. Therefore

$$
I_{\Phi}
\ge
\int_{|s-1/2|\le g_{\min}/c}
\frac{\Phi(g_{\min})}{g_{\min}^2}\,ds
=
\frac{2\Phi(g_{\min})}{cg_{\min}}.
$$

Also

$$
I_{\mathrm{RC}}
=
\frac{4}{cg_{\min}}-\frac{4}{c^2}
=
\frac{4}{cg_{\min}}(1-g_{\min}/c).
$$

Hence

$$
\frac{T_{\Phi}}{T_{\mathrm{RC}}}
=
\frac{I_{\Phi}}{I_{\mathrm{RC}}}
\ge
\frac{2\Phi(g_{\min})/(cg_{\min})}
{(4/(cg_{\min}))(1-g_{\min}/c)}
=
\frac{\Phi(g_{\min})}{2(1-g_{\min}/c)}.
$$

Since `0<g_min/c<1/2`, denominator `<2`, giving
`T_Phi/T_RC > (1/2)Phi(g_min)`. QED.


## 3. Corollaries

### 3.1. Recovery of the Exponential Result from `proof2.md`

**Corollary P.1.**
With `Phi(g)=exp(beta/g)` (`beta>0`):

$$
\frac{T_{\Phi}}{T_{\mathrm{RC}}}
>
\frac{1}{2}e^{\beta/g_{\min}}.
$$

This recovers Theorem N in `proof2.md` as a strict subclass case.

### 3.2. Overhead Regime Map by Penalty Class

**Corollary P.2 (taxonomy).**
For the same alpha=1 model:

1. `Phi(g)=1+\lambda\log(1/g)` (`lambda>0`) gives
   `T_Phi/T_RC = Omega(log(1/g_min))`.
2. `Phi(g)=1+\lambda g^{-q}` (`lambda,q>0`) gives
   `T_Phi/T_RC = Omega(g_min^{-q})`.
3. `Phi(g)=exp(beta/g^r)` (`beta,r>0`) gives
   `T_Phi/T_RC = Omega(exp(beta/g_min^r))`.

All follow by direct substitution into Theorem P.


## 4. Complement: Bounded-Penalty Class

**Proposition Q (Bounded penalties remain constant-factor RC).**
If `1 <= Phi(g) <= K` for all `g in [g_min,g_max]`, then

$$
1
\le
\frac{T_{\Phi}}{T_{\mathrm{RC}}}
\le
K.
$$

*Proof.*
Pointwise:
`g^{-2} <= Phi(g)g^{-2} <= K g^{-2}`.
Integrate over `[0,1]` and divide by `I_RC`. QED.

Interpretation:
- Diverging `Phi(g_min)` implies diverging slowdown (Theorem P).
- Uniformly bounded penalties are only constant-factor worse (Proposition Q).


## 5. Practical Consequence

For alpha=1 gaps (the paper's structural regime), multiplicative slowdowns that
target the minimum-gap region via large `Phi(g_min)` are provably expensive:
the central window alone enforces the lower bound in Theorem P.

This gives a class-level answer to the residual open question from `main2.md`:
the non-power-law issue is not specific to one exponential ansatz; it is a
general window-dominance effect for penalty schedules in this class.
