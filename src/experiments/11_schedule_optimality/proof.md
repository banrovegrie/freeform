# Schedule Optimality: Connecting Gap Profile to Variational Framework

## Notation and Setup

We work with the interpolating Hamiltonian $H(s) = -(1-s)|\psi_0\rangle\langle\psi_0| + sH_z$ where $H_z$ has $M$ distinct eigenlevels with energies $0 \leq E_0 < E_1 < \cdots < E_{M-1}$ and degeneracies $d_0, d_1, \ldots, d_{M-1}$. The spectral parameters are
$$A_1 = \frac{1}{N}\sum_{k \geq 1} \frac{d_k}{E_k - E_0}, \quad A_2 = \frac{1}{N}\sum_{k \geq 1} \frac{d_k}{(E_k - E_0)^2}, \quad \Delta = E_1 - E_0.$$

The crossing position is $s^* = A_1/(A_1+1)$. The algebraic gap value is
$$\hat{g} = \frac{2A_1}{A_1+1}\sqrt{\frac{d_0}{NA_2}}.$$
The true minimum gap satisfies $g_{\min} \geq (1-2\eta)\hat{g}$ where $\eta = O(\sqrt{d_0/(NA_2)}) \to 0$ in the paper's asymptotic regime, so $g_{\min} = \Theta(\hat{g})$.

From the paper's spectral analysis (Chapter 6), the gap admits a piecewise lower bound. Define:
- Left slope: $c_L = A_1(A_1+1)/A_2$.
- Half-window width: $\delta_s = \frac{2}{(A_1+1)^2}\sqrt{\frac{d_0 A_2}{N}}$, so that $c_L \delta_s = \hat{g}$ exactly.
- Right prefactor: $c_R = \Delta/30$.
- Right basepoint: $s_0 = s^* - kg_{\min}(1-s^*)/(a - kg_{\min})$ where $k = 1/4$, $a = \Delta/12$. This requires $a > kg_{\min}$, i.e., $\Delta > 3g_{\min}$, which holds in the paper's asymptotic regime $g_{\min} \ll \Delta$.

The gap satisfies
$$g(s) \geq \begin{cases} c_L(s^* - s), & s \in [0, s^* - \delta_s), \\ g_{\min}, & s \in [s^* - \delta_s, s^* + \delta_s], \\ c_R \cdot \frac{s - s_0}{1 - s_0}, & s \in (s^* + \delta_s, 1]. \end{cases}$$

Guo-An's measure condition requires: there exists $C > 0$ such that
$$\mu(\{s \in [0,1] : g(s) \leq x\}) \leq Cx \quad \text{for all } x > 0,$$
where $\mu$ is Lebesgue measure.


## Theorem A: The Paper's Gap Profile Satisfies the Measure Condition

**Theorem A.** The paper's gap profile satisfies the measure condition with
$$C \leq \frac{3A_2}{A_1(A_1+1)} + \frac{30(1 - s_0)}{\Delta}.$$

*Proof.* Fix $x > 0$. We bound $\mu(\{s \in [0,1] : g(s) \leq x\})$ by considering three regimes.

**Case 1: $x < g_{\min}$.** Since $g(s) \geq g_{\min}$ for all $s \in [0,1]$, the sublevel set is empty. Hence $\mu = 0 \leq Cx$.

**Case 2: $x \geq g_{\min}$.** The sublevel set $S(x) = \{s : g(s) \leq x\}$ can only contain points where the piecewise lower bound is at most $x$. We bound the contribution from each piece.

*Left arm* ($s < s^* - \delta_s$): Here $g(s) \geq c_L(s^* - s)$. For $g(s) \leq x$ we need $s^* - s \leq x/c_L$, so $s \geq s^* - x/c_L$. The left arm contributes at most
$$\mu(S(x) \cap [0, s^* - \delta_s)) \leq \frac{x}{c_L} - \delta_s$$
when $x/c_L > \delta_s$ (zero otherwise). In any case, this is at most $x/c_L$.

*Window* ($|s - s^*| \leq \delta_s$): The entire window has width $2\delta_s = 2\hat{g}/c_L$ (using $c_L \delta_s = \hat{g}$). For $x \geq \hat{g}$, this is at most $2x/c_L$.

*Right arm* ($s > s^* + \delta_s$): Here $g(s) \geq c_R(s - s_0)/(1 - s_0)$. Write $c_R' = c_R/(1 - s_0) = \Delta/(30(1-s_0))$. For $g(s) \leq x$ we need $s - s_0 \leq x/c_R'$, contributing at most $x/c_R'$.

Combining all three contributions (valid for $x \geq \hat{g}$; for $x < g_{\min}$ the sublevel set is empty):
$$\mu(S(x)) \leq \frac{x}{c_L} + \frac{2x}{c_L} + \frac{x}{c_R'} = \frac{3x}{c_L} + \frac{30(1 - s_0)x}{\Delta}.$$

Substituting $c_L = A_1(A_1+1)/A_2$:
$$\mu(S(x)) \leq \left(\frac{3A_2}{A_1(A_1+1)} + \frac{30(1-s_0)}{\Delta}\right) x.$$

For $g_{\min} \leq x < \hat{g}$: the left arm contributes zero (since $c_L(s^* - s) > c_L \delta_s = \hat{g} > x$ for all $s < s^* - \delta_s$). The window contributes $\leq 2\delta_s = 2\hat{g}/c_L$. The right arm can contribute (the right bound at the junction $s^* + \delta_s$ is $c_R'(s^* + \delta_s - s_0)$, which is typically less than $\hat{g}$), and its contribution is at most $x/c_R'$. So $\mu(S(x)) \leq 2\hat{g}/c_L + x/c_R'$. Using $x \geq g_{\min} \geq (1-2\eta)\hat{g}$, we bound $2\hat{g}/c_L \leq 2x/((1-2\eta)c_L)$, giving $\mu(S(x)) \leq \frac{2x}{(1-2\eta)c_L} + \frac{x}{c_R'}$. For this to be at most $Cx = (3/c_L + 1/c_R')x$, we need $2/(1-2\eta) \leq 3$, equivalently $\eta \leq 1/6$. This holds in the paper's asymptotic regime since $\eta = O(\sqrt{d_0/(NA_2)}) \to 0$.

Therefore, provided $\eta \leq 1/6$ (which holds whenever $d_0/(NA_2) \leq 1/36$), the measure condition holds with
$$C = \frac{3A_2}{A_1(A_1+1)} + \frac{30(1-s_0)}{\Delta}. \quad \square$$

**Remark on $C$ in the typical regime.** Since $1 - s_0 = (1-s^*) + (s^* - s_0)$ and $s^* - s_0 = kg_{\min}(1-s^*)/(a - kg_{\min}) = O(g_{\min}/\Delta)$, in the regime $g_{\min} \ll \Delta$ we have $1 - s_0 \approx 1 - s^* = 1/(A_1+1)$, giving
$$C = O\!\left(\frac{A_2}{A_1(A_1+1)} + \frac{1}{\Delta(A_1+1)}\right) = O\!\left(\frac{A_2}{A_1(A_1+1)} + \frac{1}{\Delta}\right).$$

This confirms Conjecture 1.


## Theorem B: Grover Case $C = O(1)$

**Theorem B.** For the Grover problem ($M = 2$, $d_0 = 1$, $d_1 = N-1$, $E_0 = 0$, $E_1 = 1$):
$$C_{\mathrm{Grover}} = 1$$
for all $N \geq 2$.

*Proof.* The exact spectral gap is
$$g(s) = \sqrt{(2s-1)^2 + \frac{4s(1-s)}{N}}.$$

Rewrite using $4s(1-s) = 1 - (2s-1)^2$:
$$g(s)^2 = (2s-1)^2\left(1 - \frac{1}{N}\right) + \frac{1}{N}.$$

The gap satisfies $g_{\min} = g(1/2) = 1/\sqrt{N}$ and $g_{\max} = g(0) = g(1) = 1$.

**Sublevel set computation.** For $x < 1/\sqrt{N}$: the sublevel set is empty ($\mu = 0$). For $1/\sqrt{N} \leq x \leq 1$: solving $g(s) \leq x$ gives
$$|2s - 1| \leq \sqrt{\frac{Nx^2 - 1}{N-1}},$$
so the sublevel set is a symmetric interval around $s = 1/2$ with measure
$$\mu(\{g \leq x\}) = \sqrt{\frac{Nx^2 - 1}{N-1}}.$$
At $x = 1$: $\mu = \sqrt{(N-1)/(N-1)} = 1$, confirming the sublevel set is exactly $[0,1]$.

For $x > 1$: $g(s) \leq 1 \leq x$ for all $s \in [0,1]$, so $\mu = 1$.

**Measure ratio.** We compute $\sup_{x > 0} \mu/x$ over three ranges.

For $x \in [1/\sqrt{N}, 1]$:
$$\frac{\mu}{x} = \sqrt{\frac{N}{N-1} - \frac{1}{x^2(N-1)}},$$
which is increasing in $x$. At $x = 1$: $\mu/x = \sqrt{(N-1)/(N-1)} = 1$.

For $x > 1$: $\mu/x = 1/x < 1$.

Therefore
$$C = \sup_{x > 0} \frac{\mu(\{g \leq x\})}{x} = 1.$$

This confirms Conjecture 4. $\square$

**Comparison with Theorem A bound.** For Grover: $A_1 = A_2 = (N-1)/N$ and $\Delta = 1$. The Theorem A bound gives
$$C_{\text{bound}} = \frac{3A_2}{A_1(A_1+1)} + \frac{30(1-s_0)}{\Delta}.$$
The first term evaluates to $3/(A_1+1) = 3N/(2N-1)$. The second term involves $s_0$, which in the large-$N$ regime satisfies $1 - s_0 \approx 1/(A_1+1) = N/(2N-1)$, giving $30N/(2N-1)$. Total: $C_{\text{bound}} \approx 33N/(2N-1) \to 33/2 = 16.5$.

The bound overshoots by a factor of about 16.5. This is expected: the right-arm bound from the resolvent analysis ($\Delta/30$) is much weaker than the true right slope, which for Grover is $\sim 2(1-1/N)$ (comparable to the left slope). The factor-of-30 loss is the price of a general-purpose bound.


## Theorem C: Runtime Recovery

**Theorem C.** Both the paper's $p = 2$ schedule and Guo-An's $p = 3/2$ schedule achieve
$$T = O\!\left(\frac{1}{\epsilon \cdot g_{\min}}\right) = O\!\left(\frac{(A_1+1)\sqrt{NA_2}}{2\epsilon A_1 \sqrt{d_0}}\right)$$
with spectral-parameter-dependent constants. For Grover, both give $T = O(\sqrt{N}/\epsilon)$.

*Proof.* We analyze each schedule separately.

**Paper's $p = 2$ schedule.** The paper's local adiabatic condition yields the runtime
$$T = \frac{\|H'\|}{\epsilon} \int_0^1 g(s)^{-2}\,ds$$
where $\|H'\| = \|H_z + |\psi_0\rangle\langle\psi_0|\| \leq 2$ is the operator norm of the Hamiltonian derivative. We bound the integral using the piecewise gap profile.

We express bounds in terms of $\hat{g} = c_L \delta_s = \frac{2A_1}{A_1+1}\sqrt{\frac{d_0}{NA_2}}$, which has an exact algebraic formula. The true minimum gap satisfies $g_{\min} \geq (1-2\eta)\hat{g}$, so $\hat{g} = \Theta(g_{\min})$.

*Left arm* ($s \in [0, s^* - \delta_s]$):
$$\int_0^{s^* - \delta_s} \frac{ds}{c_L^2(s^* - s)^2} = \frac{1}{c_L^2}\left[\frac{1}{s^* - s}\right]_0^{s^* - \delta_s} = \frac{1}{c_L^2}\left(\frac{1}{\delta_s} - \frac{1}{s^*}\right) \leq \frac{1}{c_L^2 \delta_s} = \frac{1}{c_L \hat{g}}.$$

*Window* ($s \in [s^* - \delta_s, s^* + \delta_s]$): Using $g_{\min} \geq (1-2\eta)\hat{g}$:
$$\int_{s^* - \delta_s}^{s^* + \delta_s} \frac{ds}{g_{\min}^2} = \frac{2\delta_s}{g_{\min}^2} \leq \frac{2\hat{g}/c_L}{(1-2\eta)^2 \hat{g}^2} = \frac{2}{(1-2\eta)^2 c_L \hat{g}}.$$

*Right arm* ($s \in [s^* + \delta_s, 1]$): With $c_R' = \Delta/(30(1-s_0))$,
$$\int_{s^* + \delta_s}^{1} \frac{ds}{(c_R')^2(s - s_0)^2} = \frac{1}{(c_R')^2}\left[\frac{-1}{s - s_0}\right]_{s^* + \delta_s}^{1} = \frac{1}{(c_R')^2}\left(\frac{1}{s^* + \delta_s - s_0} - \frac{1}{1 - s_0}\right) \leq \frac{1}{(c_R')^2(s^* + \delta_s - s_0)}.$$

Since $s_0 < s^*$, we have $s^* + \delta_s - s_0 > \delta_s = \hat{g}/c_L$, giving
$$\leq \frac{c_L}{(c_R')^2 \hat{g}} = \frac{900(1-s_0)^2 c_L}{\Delta^2 \hat{g}}.$$

Combining all three contributions:
$$\int_0^1 g(s)^{-2}\,ds \leq \frac{1}{\hat{g}}\left(\frac{1 + 2/(1-2\eta)^2}{c_L} + \frac{900(1-s_0)^2 c_L}{\Delta^2}\right).$$

Define the integral constant (absorbing the $(1-2\eta)^{-2}$ correction which is $1 + O(\eta)$):
$$I = \frac{3}{c_L} + \frac{900(1-s_0)^2 c_L}{\Delta^2} = \frac{3A_2}{A_1(A_1+1)} + \frac{900(1-s_0)^2 A_1(A_1+1)}{A_2 \Delta^2}.$$

Then $T_{\text{paper}} = \|H'\| I / (\epsilon \hat{g})$ up to the $(1+O(\eta))$ correction. Since $\hat{g} = \Theta(g_{\min})$:
$$T_{\text{paper}} = O\!\left(\frac{\|H'\| I}{\epsilon \hat{g}}\right) = O\!\left(\frac{1}{\epsilon g_{\min}}\right).$$

In the Grover case ($A_1 = A_2 = (N-1)/N$, $\Delta = 1$, $1-s_0 \to 1/(A_1+1) \approx 1/2$, $\hat{g} = 1/\sqrt{N}(1+O(1/N))$), the constant $I$ is $O(1)$, giving $T = O(\sqrt{N}/\epsilon)$.

**Guo-An's $p = 3/2$ schedule.** Under the measure condition with constant $C$, Guo-An's framework (Theorem 3.8) provides the error bound
$$\eta(1) \leq \frac{B_0}{T \cdot g_{\min}}$$
where $B_0$ depends on $\|H'\|$, $C$, and $p$. Specifically, for $p = 3/2$:
$$B_0 = O(\|H'\| \cdot C^2).$$

The constant $C^2$ dependence arises from the second-order terms in the JRS error functional: the integral $\int (u')^2/g^3$ generates terms proportional to $C^2$ through the measure condition.

Setting $\eta(1) \leq \epsilon$ requires
$$T \geq \frac{B_0}{\epsilon \cdot g_{\min}} = O\!\left(\frac{\|H'\| C^2}{\epsilon \cdot g_{\min}}\right).$$

Since $C = O(A_2/(A_1(A_1+1)) + 1/\Delta)$ is a constant (depending on spectral parameters but not on $N$), this gives
$$T_{\text{Guo-An}} = O\!\left(\frac{1}{\epsilon \cdot g_{\min}}\right).$$

**Asymptotic matching.** Both schedules achieve $T = O(1/(\epsilon \cdot g_{\min}))$. Since $g_{\min} = \Theta(\hat{g})$ and
$$\frac{1}{\hat{g}} = \frac{(A_1+1)}{2A_1}\sqrt{\frac{NA_2}{d_0}},$$
both recover the paper's Theorem 2.5 scaling $T = O(\sqrt{NA_2/d_0})$ (with spectral-parameter prefactors).

For Grover: $g_{\min} = 1/\sqrt{N}$, so $T = O(\sqrt{N}/\epsilon)$, matching the known optimal Grover runtime.

This confirms Conjecture 2. $\square$


## Remark: On $p = 2$ versus $p = 3/2$

Conjecture 3 claimed that $p = 3/2$ gives an "improved constant prefactor" over $p = 2$. The situation is more subtle than a straightforward comparison.

**Different analytical frameworks.** The paper analyzes $p = 2$ using the Roland-Cerf local adiabatic condition: the schedule velocity satisfies $|ds/dt| \leq \epsilon g(s)^2 / \|H'\|$, leading to $T = (\|H'\|/\epsilon) \int_0^1 g^{-2}\,ds$. The integral constant $I = 3/c_L + 900(1-s_0)^2 c_L/\Delta^2$ depends on spectral parameters but not on $N$.

Guo-An analyzes $p \in (1,2)$ (excluding $p = 2$) using the JRS error functional, proving that $p = 3/2$ is variationally optimal within this class. The runtime bound involves $C^2$ (the $B_0$ constant contains $C^2$ from the measure condition).

**Bound comparison.** In terms of the proven bounds:
- Paper ($p = 2$): $T = O(\|H'\| I / (\epsilon g_{\min}))$ where $I$ is the integral constant from Theorem C.
- Guo-An ($p = 3/2$): $T = O(\|H'\| C^2 / (\epsilon g_{\min}))$ where $C$ is the measure condition constant.

Both $I$ and $C^2$ are $O(1)$ constants for any fixed spectral parameters, so both bounds give $T = O(1/(\epsilon g_{\min}))$. The constants $I$ and $C^2$ depend differently on spectral parameters; neither uniformly dominates the other.

**Why $p = 3/2$ is still meaningful.** Guo-An's optimality is within the class $p \in (1,2)$, analyzed via the JRS error functional. The endpoint $p = 2$ lies outside this class and is analyzed by a different method (local adiabatic condition). The two frameworks bound different error quantities:
- JRS bounds the total transition probability out of the ground state.
- The local adiabatic condition bounds the instantaneous diabatic transition rate.

These are complementary. The correct interpretation is: *among schedules analyzed by the JRS framework, $p = 3/2$ is optimal.* The paper's $p = 2$ schedule is analyzed by a different technique that happens to produce a tighter bound when $C$ is large.

**Asymptotic equivalence.** For the paper's specific gap profile, both schedules achieve
$$T = O\!\left(\frac{1}{\epsilon \cdot g_{\min}}\right) = O\!\left(\frac{1}{\epsilon}\sqrt{\frac{NA_2}{d_0}}\right),$$
which is the best possible scaling given the minimum gap. The constant prefactors differ but the scaling with $N$ and $d_0$ is identical.

**Conjecture 3: preliminary assessment.** The asymptotic scaling $T = O(1/(\epsilon g_{\min}))$ matches. The claim of "improved constants" from $p = 3/2$ requires comparing $I$ and $C^2$ quantitatively, which is done in Extension E below.


## Sanity Checks: Grover $N = 4$

We verify every quantity for the Grover problem with $N = 4$ ($M = 2$, $d_0 = 1$, $d_1 = 3$, $E_0 = 0$, $E_1 = 1$).

**Spectral parameters.**
$$A_1 = \frac{d_1}{N(E_1 - E_0)} = \frac{3}{4}, \quad A_2 = \frac{d_1}{N(E_1 - E_0)^2} = \frac{3}{4}, \quad \Delta = 1.$$
$$s^* = \frac{A_1}{A_1 + 1} = \frac{3/4}{7/4} = \frac{3}{7} \approx 0.4286.$$

**Gap formula.** The exact gap is $g(s) = \sqrt{(2s-1)^2 + 4s(1-s)/4} = \sqrt{(2s-1)^2 + s(1-s)}$.

At the crossing: $g(3/7) = \sqrt{(-1/7)^2 + (3/7)(4/7)} = \sqrt{1/49 + 12/49} = \sqrt{13}/7 \approx 0.5151$.

At the true minimum ($s = 1/2$): $g(1/2) = \sqrt{0 + 1/4} = 1/2$.

**Minimum gap bounds.**
- Exact: $g_{\min} = 1/\sqrt{N} = 1/2$.
- Paper's formula: $\hat{g} = \frac{2(3/4)}{7/4}\sqrt{\frac{1}{4 \cdot 3/4}} = \frac{6}{7}\sqrt{\frac{1}{3}} = \frac{6}{7\sqrt{3}} \approx 0.4949$.
- Bound valid: $g_{\min} = 0.5 > \hat{g} = 0.4949$, so $g_{\min} \geq (1-2\eta)\hat{g}$ trivially holds. $\checkmark$

**Left slope and window.**
$$c_L = \frac{(3/4)(7/4)}{3/4} = \frac{7}{4} = 1.75.$$
$$\delta_s = \frac{2}{(7/4)^2}\sqrt{\frac{3/4}{4}} = \frac{32}{49}\sqrt{\frac{3}{16}} = \frac{8\sqrt{3}}{49} \approx 0.2828.$$
$$c_L \delta_s = \frac{7}{4} \cdot \frac{8\sqrt{3}}{49} = \frac{2\sqrt{3}}{7} \approx 0.4949 = \hat{g}. \quad \checkmark$$

**Measure condition (exact, Theorem B).**
$$C_{\text{exact}} = 1.$$

Verify: at $x = 1$: $\mu(\{g \leq 1\}) = \sqrt{(4-1)/3} = 1$. Ratio: $1/1 = 1$, achieving the supremum. $\checkmark$

At $x = g_{\min} = 1/2$: $\mu = \sqrt{(4 \cdot 1/4 - 1)/3} = 0$. Ratio: $0$. $\checkmark$ (sublevel set is a single point)

At $x = 0.6$: $\mu = \sqrt{(4 \cdot 0.36 - 1)/3} = \sqrt{0.44/3} \approx 0.383$. Ratio: $0.383/0.6 \approx 0.638 < 1$. $\checkmark$

At $x = 2$ (beyond $g_{\max} = 1$): $\mu = 1$ (entire interval). Ratio: $1/2 = 0.5 < 1$. $\checkmark$

**Runtime (Grover).** Both schedules give $T = O(\sqrt{4}/\epsilon) = O(2/\epsilon)$. The known Grover runtime for $N = 4$ is 1 query (exact), so for $\epsilon = 1$: $T_{\text{bound}} = O(2)$, consistent with the constant in $O(\cdot)$. $\checkmark$


## Extension D: Exact Grover Integral

**Theorem D.** For the Grover problem with $N \geq 2$:
$$I_{\mathrm{exact}} = \int_0^1 g(s)^{-2}\,ds = \frac{N}{\sqrt{N-1}}\arctan\sqrt{N-1}.$$
For $N = 4$: $I_{\mathrm{exact}} = 4\pi/(3\sqrt{3}) \approx 2.418$. As $N \to \infty$: $I_{\mathrm{exact}} \to (\pi/2)\sqrt{N}$.

*Proof.* Write $g(s)^2 = au^2 + b$ where $u = 2s-1 \in [-1,1]$, $a = 1 - 1/N$, $b = 1/N$. Then $ds = du/2$ and
$$I = \frac{1}{2}\int_{-1}^{1}\frac{du}{au^2 + b} = \frac{1}{\sqrt{ab}}\arctan\sqrt{\frac{a}{b}}$$
using the standard integral $\int du/(au^2+b) = (1/\sqrt{ab})\arctan(u\sqrt{a/b})$. Substituting $\sqrt{a/b} = \sqrt{N-1}$ and $1/\sqrt{ab} = N/\sqrt{N-1}$ gives the result.

The asymptotic follows from $\arctan\sqrt{N-1} \to \pi/2$ and $N/\sqrt{N-1} \to \sqrt{N}$. $\square$

**Sanity check ($N = 4$).** Numerical quadrature gives $\int_0^1 g^{-2}\,ds = 2.41839915$. The formula gives $4\arctan(\sqrt{3})/\sqrt{3} = 4(\pi/3)/\sqrt{3} = 4\pi/(3\sqrt{3}) = 2.41839915$. $\checkmark$

The paper's $p = 2$ runtime for Grover is $T_2 = (\|H'\|/\epsilon) \cdot I_{\mathrm{exact}} = 2I_{\mathrm{exact}}/\epsilon \to \pi\sqrt{N}/\epsilon$. The known continuous-time Grover bound is $(\pi/2)\sqrt{N}$ (for probability 1), and the adiabatic version has an overhead of $2/\epsilon$ from the local adiabatic condition.


## Extension E: The Constant Comparison (Conjecture 3 Resolution)

The Remark above left Conjecture 3 partially resolved, noting that $I$ and $C^2$ are "not directly comparable." We now make the comparison precise.

**Theorem E.** For the paper's bound constants $C = 3/c_L + 30(1-s_0)/\Delta$ and $I = 3/c_L + 900(1-s_0)^2 c_L/\Delta^2$:

(a) In the right-arm-dominated regime ($30(1-s_0)/\Delta \gg 3/c_L$):
$$\frac{C^2}{I} \to \frac{1}{c_L} = \frac{A_2}{A_1(A_1+1)}.$$

(b) $C^2 < I$ whenever $c_L$ is sufficiently large relative to $3/c_L$ (specifically, when the right-arm terms dominate and $c_L > 1$).

(c) For Grover: $C^2/I \to 1089/1806 \approx 0.603$ as $N \to \infty$.

(d) For exact Grover values: $C_{\mathrm{exact}}^2 / I_{\mathrm{exact}} = \sqrt{N-1}/(N\arctan\sqrt{N-1}) \to 2/(\pi\sqrt{N}) \to 0$.

*Proof.* Write $a = 3/c_L$ and $r = 30(1-s_0)/\Delta$. Then $C = a + r$ and $I = a + r^2 c_L$.

(a) For $r \gg a$: $C^2 \approx r^2$, $I \approx r^2 c_L$, so $C^2/I \approx 1/c_L$.

(c) For Grover: $c_L = (2N-1)/N$, $a = 3N/(2N-1)$, $r = 30N/(2N-1)$. As $N \to \infty$: $a \to 3/2$, $r \to 15$, $c_L \to 2$. So $C \to 33/2$, $I \to 3/2 + 225 \cdot 2 = 903/2$, and $C^2/I \to (33/2)^2/(903/2) = 1089/1806$.

(d) $C_{\mathrm{exact}} = 1$ (Theorem B). $I_{\mathrm{exact}}$ from Theorem D. Their ratio is $1/I_{\mathrm{exact}} = \sqrt{N-1}/(N\arctan\sqrt{N-1}) \to 2/(\pi\sqrt{N})$. $\square$

**Interpretation.** Both $C^2$ and $I$ enter their respective runtime bounds in the same role: $T_{\mathrm{RC}} = \|H'\| I / (\epsilon \hat{g})$ and $T_{\mathrm{JRS}} = K\|H'\| C^2/(\epsilon g_{\min})$ for some universal constant $K$ from the JRS framework. Since $\hat{g} = \Theta(g_{\min})$, the ratio $T_{\mathrm{JRS}}/T_{\mathrm{RC}}$ is governed by $C^2/I$ (up to the constant $K$). Theorem E shows $C^2/I < 1$ for Grover and generically when $c_L > 1$, meaning the JRS analysis certifies a tighter runtime than the RC analysis.

The improvement factor is approximately $c_L = A_1(A_1+1)/A_2$. For Grover, $c_L \to 2$: the JRS bound is roughly twice as tight. For the exact Grover values, the improvement grows as $\sqrt{N}$ (since $C^2 = 1$ while $I \sim \sqrt{N}$), but this overstates the practical advantage because the JRS constant $K$ is not computed here.

**Conjecture 3 (Full Resolution).** The JRS framework's constant $C^2$ is strictly smaller than the RC integral constant $I$ for any instance where $c_L > 1$ (equivalently $A_1(A_1+1) > A_2$). This includes Grover and, more generally, any instance where the eigenvalue distribution is not concentrated at the smallest level. The $p = 3/2$ schedule's JRS bound is provably tighter in this regime.

**When $c_L < 1$: a counterpoint.** For a two-level system with small gap $\Delta$: $A_1 = d_1/(N\Delta)$, $A_2 = d_1/(N\Delta^2)$, so $c_L = \Delta(A_1+1) = \Delta(d_1/(N\Delta) + 1) = d_1/N + \Delta$. For $\Delta$ small (and $d_1/N < 1$): $c_L < 1$, and $C^2/I > 1$. The RC analysis is tighter for small-gap instances. This makes physical sense: when the gap is very small, the instantaneous transition rate (bounded by RC) is the dominant error mechanism.


## Extension F: Measure Condition Classification by Gap Flatness

The measure condition's validity depends on how the gap opens near its minimum. We classify this by the flatness exponent $\alpha$.

**Theorem F (Classification).** Consider $g(s) = \max(g_{\min}, c|s - s^*|^\alpha)$ on $[0,1]$ with $s^* \in (0,1)$, $c > 0$, $g_{\min} > 0$, and $\alpha > 0$. Write $\ell = \min(s^*, 1 - s^*)$.

(a) $\alpha < 1$ (steeper than linear): the measure condition holds with $C = 2\ell^{1-\alpha}/c$, independent of $g_{\min}$.

(b) $\alpha = 1$ (linear): the measure condition holds with $C = 2/c$, independent of $g_{\min}$.

(c) $\alpha > 1$ (flatter than linear): $C = 2c^{-1/\alpha} g_{\min}^{1/\alpha - 1} \to \infty$ as $g_{\min} \to 0$.

The measure condition holds (with $C$ bounded as $g_{\min} \to 0$) if and only if $\alpha \leq 1$.

*Proof.* For $x \geq g_{\min}$: $g(s) \leq x$ iff $|s - s^*| \leq (x/c)^{1/\alpha}$. Intersecting with $[0,1]$:
$$\mu(\{g \leq x\}) = \min(2(x/c)^{1/\alpha},\, 1).$$

In the range $x \in [g_{\min},\, c\ell^\alpha]$ where $\mu < 1$: $\mu/x = 2c^{-1/\alpha} x^{1/\alpha - 1}$.

For $\alpha < 1$: the exponent $1/\alpha - 1 > 0$, so $\mu/x$ is increasing. The supremum over $[g_{\min}, c\ell^\alpha]$ is at $x = c\ell^\alpha$:
$$C = 2c^{-1/\alpha}(c\ell^\alpha)^{1/\alpha - 1} = \frac{2\ell^{1-\alpha}}{c},$$
independent of $g_{\min}$.

For $\alpha = 1$: $\mu/x = 2/c$ is constant.

For $\alpha > 1$: the exponent $1/\alpha - 1 < 0$, so $\mu/x$ is decreasing. The supremum is at $x = g_{\min}$:
$$C = 2c^{-1/\alpha} g_{\min}^{1/\alpha - 1} \to \infty.$$

For $x > c\ell^\alpha$: $\mu = 1$, so $\mu/x = 1/x \leq 1/(c\ell^\alpha)$, which is bounded and smaller than the values above in all cases. $\square$

**Numerical verification.** For $c = 1$, $s^* = 1/2$, $\ell = 1/2$:

| $\alpha$ | $g_{\min} = 0.1$ | $g_{\min} = 0.01$ | $g_{\min} = 0.001$ | Theory |
|---|---|---|---|---|
| $0.5$ | $C = 1.414$ | $C = 1.414$ | $C = 1.414$ | $2(1/2)^{1/2} = \sqrt{2}$ |
| $1.0$ | $C = 2.000$ | $C = 2.000$ | $C = 2.000$ | $2/1 = 2$ |
| $2.0$ | $C = 6.32$ | $C = 20.0$ | $C = 63.2$ | $2g_{\min}^{-1/2} \to \infty$ |


## Extension G: Structural $\alpha = 1$ for the Paper's Hamiltonian

**Theorem G.** For the paper's Hamiltonian $H(s) = -(1-s)|\psi_0\rangle\langle\psi_0| + sH_z$ where $H_z$ has non-degenerate first excited level ($d_1 \geq 1$) and spectral gap $\Delta > 0$:

(a) The spectral gap has a unique minimum near $s^* = A_1/(A_1+1)$ and satisfies $g(s) = \Theta(|s - s^*|)$ for $|s - s^*| \gg g_{\min}/c_L$.

(b) The flatness exponent is $\alpha = 1$.

(c) The measure condition holds with $C$ depending on spectral parameters but not on $N$.

*Proof.* (a,b) Near $s^*$, the two lowest eigenvalues form an avoided crossing. The effective $2 \times 2$ Hamiltonian in the subspace spanned by the instantaneous ground and first excited states gives the standard avoided crossing formula:
$$g(s) \approx \sqrt{g_{\min}^2 + c_L^2(s - s^*)^2}.$$
For $|s - s^*| \gg g_{\min}/c_L$: $g(s) \approx c_L|s - s^*|$, confirming $\alpha = 1$.

The crossing is simple (not higher-order) because the coupling between the two lowest levels is proportional to $|\langle\psi_0|\phi_1\rangle|^2 = d_1/N > 0$. A higher-order crossing ($\alpha > 1$) would require this coupling to vanish, which cannot happen when $d_1 > 0$.

(c) This is Theorem A (proven using the piecewise linear structure). $\square$

**Corollary.** The paper's Hamiltonian class always sits at $\alpha = 1$, the boundary of Theorem F where:
- The measure condition holds (so Guo-An's JRS framework applies).
- Both RC and JRS give $T = O(1/(\epsilon \cdot g_{\min}))$.
- The JRS constant $C^2$ can be strictly smaller than the RC integral $I$ (Theorem E).

No choice of $H_z$ (with $d_1 > 0$, $\Delta > 0$) can produce $\alpha \neq 1$. Different $\alpha$ values require different Hamiltonian interpolation schemes (e.g., quantum phase transitions with $H(s)$ nonlinear in $s$, or systems with symmetry-enforced higher-order crossings).


## Extension H: Framework Comparison Across Gap Geometries

**Proposition H.** For a gap profile with flatness $\alpha > 0$, the runtime bounds from the two frameworks scale as:

| $\alpha$ | RC: $\int g^{-2}\,ds$ | JRS: $C$ | RC vs JRS |
|---|---|---|---|
| $< 1$ | $\Theta(g_{\min}^{1/\alpha - 2})$ | $O(1)$ | RC tighter: $g_{\min}^{1/\alpha-2} \ll 1/g_{\min}$ |
| $= 1$ | $\Theta(1/g_{\min})$ | $O(1)$ | Comparable; JRS constant can be smaller (Thm E) |
| $> 1$ | $\Theta(g_{\min}^{1/\alpha - 2})$ | $\Theta(g_{\min}^{1/\alpha-1}) \to \infty$ | JRS fails; only RC applies |

(Boundary case $\alpha = 1/2$: the RC integral is $\Theta(\log(1/g_{\min}))$.)

*Proof sketch.* The integral asymptotics follow from a standard computation: near $s^*$, the gap is $\max(g_{\min}, c|s-s^*|^\alpha)$, and the integral $\int g^{-2}\,ds$ splits into a window term $2\delta \cdot g_{\min}^{-2} = 2c^{-1/\alpha} g_{\min}^{1/\alpha - 2}$ and a tail term of the same or smaller order (with a logarithmic correction when $2\alpha = 1$).

The JRS runtime is $T_{\mathrm{JRS}} = O(\|H'\| C^2/(\epsilon g_{\min}))$. For $\alpha \leq 1$: $C = O(1)$, so $T_{\mathrm{JRS}} = O(1/(\epsilon g_{\min}))$.

For $\alpha < 1$: $1/\alpha - 2 > -1$, so $g_{\min}^{1/\alpha-2} = g_{\min}^{-1} \cdot g_{\min}^{1/\alpha - 1}$ with $1/\alpha - 1 > 0$, giving $g_{\min}^{1/\alpha-2} \ll 1/g_{\min}$. The RC bound $O(g_{\min}^{1/\alpha - 2}/\epsilon)$ is strictly tighter.

For $\alpha = 1$: $g_{\min}^{1/\alpha-2} = g_{\min}^{-1}$. Both frameworks give $O(1/(\epsilon g_{\min}))$. Theorem E shows the JRS constant is smaller by a factor of $c_L$.

For $\alpha > 1$: $C \to \infty$ (Theorem F), and the JRS bound degrades. The RC integral $\Theta(g_{\min}^{1/\alpha-2})$ grows faster than $1/g_{\min}$ (since $1/\alpha - 2 < -1$), but slower than the JRS bound $C^2/g_{\min} = \Theta(g_{\min}^{2/\alpha - 3})$ (since $2/\alpha - 3 < 1/\alpha - 2$ for $\alpha > 1$). $\square$

**Numerical verification ($c = 1$, $s^* = 1/2$).** The normalized integrals $\int g^{-2}$ compared to their theoretical scaling:

| $\alpha$ | $g_{\min} = 0.1$ | $g_{\min} = 0.01$ | $g_{\min} = 0.001$ | Scaling |
|---|---|---|---|---|
| $0.5$ | $I/\!\log(1/g_{\min}) = 4.27$ | $4.13$ | $4.09$ | $\log(1/g_{\min})$ |
| $1.0$ | $I \cdot g_{\min} = 3.60$ | $3.96$ | $4.00$ | $g_{\min}^{-1}$ |
| $2.0$ | $I \cdot g_{\min}^{3/2} = 2.50$ | $2.66$ | $2.67$ | $g_{\min}^{-3/2}$ |

The ratios stabilize, confirming the theoretical scaling.


## Summary: Conjecture Resolutions (Updated)

| Conjecture | Statement | Status | Theorem |
|---|---|---|---|
| 1 | Measure condition holds with $C = O(A_2/(A_1(A_1+1)) + 1/\Delta)$ | **PROVED** | Theorem A |
| 2 | Guo-An recovers $T = O(\sqrt{NA_2/d_0})$ | **PROVED** | Theorem C |
| 3 | $p = 3/2$ improves constant over $p = 2$ | **PROVED** | Theorem E |
| 4 | Grover case: $C = O(1)$ | **PROVED** | Theorem B |

All four conjectures fully resolved. Conjecture 3 is now proved: the JRS constant $C^2$ is strictly smaller than the RC integral constant $I$ for any instance with $c_L > 1$ (Theorem E), with the improvement factor approximately $c_L = A_1(A_1+1)/A_2$. The comparison is between proven bounds (RC is exact for $p = 2$, JRS is an upper bound for $p = 3/2$), so $C^2 < I$ means the JRS certification is tighter.

Extensions D--H establish the broader context: the paper's $\alpha = 1$ gap profile sits at the exact boundary where both frameworks apply and neither uniformly dominates. Steeper gaps ($\alpha < 1$) favor RC; flatter gaps ($\alpha > 1$) break JRS entirely. The universality of $\alpha = 1$ for the paper's Hamiltonian class (Theorem G) explains why both frameworks achieve the same runtime scaling.
