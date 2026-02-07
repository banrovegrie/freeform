# Schedule Optimality Open Threads: Explicit JRS Prefactor and Non-Power-Law Schedules

## Scope

This continuation resolves two open threads left in `proof.md`:

1. Compute an explicit JRS-side runtime prefactor for the paper's Hamiltonian class.
2. Test a concrete non-power-law schedule against the p=2 and p=3/2 baselines.

All symbols here are ASCII and disambiguated from prior notation collisions.

- `C_mu`: measure-condition constant for the spectral gap.
- `A_H`: Hamiltonian derivative norm, `A_H = ||H_1 - H_0||_2`.
- `Delta_*`: minimum spectral gap along the path.
- `epsilon_ad`: target adiabatic error.


## Section 1: Explicit JRS Prefactor

### 1.1. Starting point and notation hygiene

Use Jansen-Ruskai-Seiler (JRS) Theorem 3 (as transcribed in
`references/mds/jansen2007bounds.md`, Theorem 3). For rank-1 target band (`m=1`),
one explicit bound is

$$
\mathcal{A}(1)
\le
\frac{1}{T}
\left[
\left.\frac{||\dot H||}{\Delta^2}\right|_{\mathrm{ub}}
+
\int_0^1\left(\frac{||\dot H||}{\Delta^2}+7\frac{||\dot H||^2}{\Delta^3}\right)ds
\right],
$$

with transition probability bounded by `\mathcal{A}(1)^2`.

Use power-law schedule (`citations/guo2025adiabatic.tex`, Eq. `eq:power_law`):

$$
u'(s)=c_p\,\Delta^p(\nu(s)),\quad p\in(1,2),
$$

with normalization

$$
c_p=\int_0^1\Delta(u)^{-p}du.
$$

Under measure condition with constant `C_mu`, gap-integral control gives

$$
\int_0^1\Delta(u)^{-\alpha}du\le C_\alpha\Delta_*^{-(\alpha-1)},\quad
C_\alpha=\frac{C_\mu\alpha}{\alpha-1},\quad \alpha>1,
$$

hence

$$
c_p\le C_p\Delta_*^{-(p-1)},\quad C_p=\frac{C_\mu p}{p-1}.
$$

Also, for `H(\nu(s))=(1-\nu)H_0+\nu H_1`,

$$
||\dot H||\le A_H\,\nu'(s)=A_H c_p\Delta^p.
$$

### 1.2. Explicit prefactor theorem

**Theorem K (Explicit prefactor for p-schedules).**
For `p in (1,2)`, the runtime certificate

$$
\mathcal{A}(1)\le \epsilon_{\mathrm{ad}}
$$

is satisfied by

$$
T\ge
\frac{B_{\mathrm{JRS}}(p)}{\epsilon_{\mathrm{ad}}\,\Delta_*},
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

*Proof.*
Bound the three contributions in the JRS Theorem 3 inequality.

Boundary term:

$$
\frac{||\dot H||}{\Delta^2}
\le
A_H c_p\Delta^{p-2}
\le
A_H C_p\Delta_*^{-1}.
$$

Both endpoints contribute

$$
2A_H C_p\Delta_*^{-1}.
$$

First integral term:

$$
\int_0^1 \frac{||\dot H||}{\Delta^2}ds
\le
A_H\int_0^1\Delta^{-2}(u)du
\le
A_H C_2\Delta_*^{-1},\quad C_2=2C_\mu.
$$

Second integral term:

$$
7\int_0^1\frac{||\dot H||^2}{\Delta^3}ds
\le
7A_H^2 c_p\int_0^1\Delta^{p-3}(u)du
\le
7A_H^2 C_p C_{3-p}\Delta_*^{-1},
$$

with `C_{3-p}=C_\mu(3-p)/(2-p)`.

Summing all terms yields

$$
\mathcal{A}(1)
\le
\frac{1}{T}
\left(2A_H C_p + A_H C_2 + 7A_H^2 C_p C_{3-p}\right)
\Delta_*^{-1}.
$$

Substitute `C_p`, `C_2`, `C_{3-p}` to get `B_{\mathrm{JRS}}(p)`.
Setting the right-hand side to `<= epsilon_ad` gives the runtime condition. QED.

### 1.3. p=3/2 closed form

**Corollary K.1 (p=3/2).**

$$
B_{\mathrm{JRS}}(3/2)=8A_HC_\mu+63A_H^2C_\mu^2.
$$

For the paper's Hamiltonian class (`A_H<=2`):

$$
B_{\mathrm{JRS}}(3/2)\le 16C_\mu+252C_\mu^2.
$$

This is fully explicit.


## Section 2: Quantitative Comparison with RC Certificates

Use RC certificate in the Experiment 11 notation:

$$
T_{\mathrm{RC}}^{\mathrm{cert}}=\frac{A_H I}{\epsilon_{\mathrm{ad}}\,\hat g},
$$

and JRS certificate from Corollary K.1:

$$
T_{\mathrm{JRS}}^{\mathrm{cert}}=\frac{8A_HC_\mu+63A_H^2C_\mu^2}{\epsilon_{\mathrm{ad}}\,g_{\min}}.
$$

Hence

$$
\frac{T_{\mathrm{JRS}}^{\mathrm{cert}}}{T_{\mathrm{RC}}^{\mathrm{cert}}}
=
\frac{(8A_HC_\mu+63A_H^2C_\mu^2)\hat g}{A_H I g_{\min}}.
$$

This formula exposes a key point: structural comparison by `C_\mu^2/I` alone is not
sufficient once explicit prefactors are unfolded.

### 2.1. Grover and structured instance numbers

All values below are reproduced by
`src/experiments/11_schedule_optimality/lib/verify_open_threads.py`.

- Grover (`N=1024`, `A_H=2`, `C_\mu=1`):
  - `B_JRS(3/2)=268`.
  - `T_JRS^{cert}(eps=1)=8576`.
  - `T_RC^{cert}` with exact `I_exact` is `3154.5215` (ratio `2.7186`).
  - `T_RC^{cert}` with coarse bound `I_bound` is `28910.1197` (ratio `0.2966`).

- Structured instance from Experiment 11 Remark J (`n=10` open-chain ferromagnetic Ising,
  `A_H=2`, `C_\mu=157.4491589643`, `I=34807.9388418623`):
  - `B_JRS(3/2)=6249659.0765`.
  - `T_JRS^{cert}(eps=1)=275091832.3796`.
  - `T_RC^{cert}(eps=1)=3062093.6426`.
  - Ratio `T_JRS/T_RC=89.8378`.

**Interpretation.**
- Explicit-prefactor JRS certificate can beat loose RC bounds.
- Against tighter RC constants (exact Grover integral or structured `I` from Exp 11),
  explicit-prefactor JRS certificate can be worse by large factors.

This resolves the open question "what is the missing prefactor" at the level of an
explicit certificate, with transparent dependence on `(A_H, C_mu)`.


## Section 3: Non-Power-Law Schedule Test

### 3.1. Schedule definition

To test non-power-law behavior with direct comparability to RC safety, define an
RC-safe exponential slowdown schedule:

$$
\frac{ds}{dt}=\frac{\epsilon_{\mathrm{ad}}}{A_H}\,\frac{g(s)^2}{e^{\beta/g(s)}},\quad \beta>0.
$$

Runtime is

$$
T_{\exp}=\frac{A_H}{\epsilon_{\mathrm{ad}}}
\int_0^1\frac{e^{\beta/g(s)}}{g(s)^2}ds.
$$

### 3.2. Canonical alpha=1 model

Use the canonical `alpha=1` gap model from the Experiment 06 geometry class:

$$
g_{\mathrm{mod}}(s)=\max\big(g_{\min},\,c|s-1/2|\big),\quad c>0.
$$

For this model (and `g_min<c/2`), exact integrals are:

$$
I_{\mathrm{RC}}=\int_0^1\frac{ds}{g_{\mathrm{mod}}(s)^2}
=\frac{4}{cg_{\min}}-\frac{4}{c^2},
$$

$$
I_{\exp}=\int_0^1\frac{e^{\beta/g_{\mathrm{mod}}(s)}}{g_{\mathrm{mod}}(s)^2}ds
=e^{\beta/g_{\min}}\left(\frac{2}{cg_{\min}}+\frac{2}{\beta c}\right)
-\frac{2e^{2\beta/c}}{\beta c}.
$$

So

$$
T_{\exp}=\frac{A_H}{\epsilon_{\mathrm{ad}}}I_{\exp},\qquad
T_{\mathrm{RC}}=\frac{A_H}{\epsilon_{\mathrm{ad}}}I_{\mathrm{RC}}.
$$

### 3.3. Exponential overhead theorem

**Theorem N (Exponential penalty).**
For the model above and `beta>0`:

$$
\frac{T_{\exp}}{T_{\mathrm{RC}}}
=\frac{I_{\exp}}{I_{\mathrm{RC}}}
\ge \frac{1}{2}e^{\beta/g_{\min}}.
$$

Hence `T_exp = Omega(e^{beta/g_min}/(epsilon_ad g_min))`, asymptotically worse than
both p=2 RC and p=3/2 JRS certificates, which scale as `O(1/(epsilon_ad g_min))`.

*Proof.*
Window contribution (`|s-1/2|<=g_min/c`) gives

$$
I_{\exp}\ge \frac{2}{cg_{\min}}e^{\beta/g_{\min}}.
$$

Also

$$
I_{\mathrm{RC}}=\frac{4}{cg_{\min}}-\frac{4}{c^2}<\frac{4}{cg_{\min}}.
$$

Divide to obtain

$$
\frac{I_{\exp}}{I_{\mathrm{RC}}}>
\frac{2e^{\beta/g_{\min}}/(cg_{\min})}{4/(cg_{\min})}
=\frac{1}{2}e^{\beta/g_{\min}}.
$$

QED.

### 3.4. Numerical check

For `c=1`, `beta=0.05`:

| `g_min` | `I_exp/I_RC` | `0.5*exp(beta/g_min)` |
|---|---:|---:|
| 0.1   | 1.5199   | 0.8244 |
| 0.05  | 2.2797   | 1.3591 |
| 0.02  | 8.4762   | 6.0912 |
| 0.01  | 89.8357  | 74.2066 |
| 0.005 | 12175.3778 | 11013.2329 |

Closed form and numerical quadrature match to machine precision in
`verify_open_threads.py`.


## Final Status of the Two Open Threads

1. **Explicit JRS constant:** resolved at certificate level by Theorem K/Corollary K.1.
2. **Non-power-law schedule test:** resolved for a concrete family by Theorem N; the
   tested non-power-law class is provably suboptimal in the `alpha=1` regime.

These results close the two open tasks left in `main.md` as stated questions, while
remaining honest about scope: the non-power-law result is for a specific, explicit
family (exponential slowdown), not all conceivable non-power-law schedules.
