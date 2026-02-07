# Information-Theoretic Limits: Proof Addendum (Part XI)

## Part XI: Worst-Case Continuous-Time Statement Under Normalized Controls

Part IX of `proof.md` refuted the literal Conjecture 5 and left a worst-case reformulation:
for fixed instance-independent controls, does there exist a diagonal instance that forces
slow runtime? This addendum resolves that reformulation under an explicit normalization
condition.

### Setup

We study continuous-time rank-one algorithms
$$
i\frac{d}{dt}|\psi(t)\rangle
= \left(f(t)|\psi_0\rangle\langle\psi_0| + g(t)H_z\right)|\psi(t)\rangle,
$$
with instance-independent controls $f,g:[0,T]\to\mathbb{R}$ and
$|\psi_0\rangle = N^{-1/2}\sum_x |x\rangle$.

We use the scaled unstructured family
$$
H_z^{(S,\delta)} = \delta\left(\mathbb{I} - P_S\right), \qquad
P_S = \sum_{x\in S}|x\rangle\langle x|, \quad |S|=d_0,
$$
where $\delta\in(0,1]$.
Ground states are exactly $S$.

### Why Normalization Is Necessary

**Proposition 11 (Unnormalized Time Lower Bounds Are Ill-Posed).**
Without a bound on control amplitude (for example $|g(t)|\le 1$ or an oracle-action budget),
nonzero runtime lower bounds in physical time are not meaningful.

*Proof.*
Take any control pair $(f,g)$ on $[0,T]$ and define, for $K>1$,
$$
f_K(t)=Kf(Kt),\qquad g_K(t)=Kg(Kt),\qquad t\in[0,T/K].
$$
Then $U_K(T/K)=U(T)$ by the time-rescaling change of variables.
Success probability is unchanged while runtime scales by $1/K$.
Hence no instance-independent positive lower bound on time can hold without
normalization. $\square$

### Main Result

**Theorem 10 (Normalized Worst-Case Lower Bound).**
Assume normalized controls
$$
|g(t)|\le 1 \quad \text{for all } t\in[0,T].
$$
Fix $N,d_0$ and consider algorithms that must succeed with probability at least $2/3$
on every instance in the family $H_z^{(S,\delta)}$.
Then
$$
T = \Omega\!\left(\frac{\sqrt{N/d_0}}{\delta}\right).
$$
In particular, choosing $\delta = N^{-1/2}$ gives
$$
T = \Omega\!\left(\frac{N}{\sqrt{d_0}}\right).
$$

*Proof.*
For $H_z^{(S,\delta)}$, the oracle-dependent term is
$$
g(t)H_z^{(S,\delta)} = \delta g(t)\mathbb{I} - \delta g(t)P_S.
$$
The identity part contributes only global phase.
Hence instance dependence enters only through $P_S$ with instantaneous strength
$\delta |g(t)|$.

Define oracle action
$$
\mathcal{A} := \int_0^T \delta |g(t)|\,dt.
$$
Under the standard continuous-time query normalization (oracle coefficient bounded by 1,
with total oracle action as query budget), the bounded-error equivalence between
discrete and continuous-time query models via the adversary characterization
(Lee et al. 2011; see also the direct continuous-time adversary lower-bound
discussion in Brandeho and Roland 2015) gives:
an algorithm with success probability $\ge 2/3$ for size-$d_0$ unstructured search requires
$$
\mathcal{A} = \Omega\!\left(\sqrt{\frac{N}{d_0}}\right)
$$
(BBBV/Boyer-BBH-T lower bound in query form, transferred to oracle action).

Using $|g(t)|\le 1$:
$$
\mathcal{A} = \int_0^T \delta |g(t)|\,dt \le \delta T.
$$
Therefore
$$
\delta T = \Omega\!\left(\sqrt{\frac{N}{d_0}}\right)
\;\Longrightarrow\;
T = \Omega\!\left(\frac{\sqrt{N/d_0}}{\delta}\right).
$$
Setting $\delta=N^{-1/2}$ gives
$$
T = \Omega\!\left(\sqrt{\frac{N}{d_0}}\cdot\sqrt{N}\right)
= \Omega\!\left(\frac{N}{\sqrt{d_0}}\right).
$$
$\square$

### Consequence for Experiment 10

**Corollary 11.1 (Open Item Closure Under Normalization).**
The worst-case continuous-time rank-one barrier is proved for normalized controls:
for every instance-independent normalized control law, there exist diagonal instances
forcing $\Omega(N/\sqrt{d_0})$ runtime.

Combined with Part IX of `proof.md`:
1. Literal Conjecture 5 is false (Proposition 10 / Theorem 9 in `proof.md`).
2. The normalized worst-case reformulation is true (Theorem 10 here).

These statements are consistent: fast $\Theta(\sqrt{N/d_0})$ behavior exists on special
families, while worst-case diagonal spectra still force the AQO-scale barrier under
normalized controls.

## References

1. Bennett, Bernstein, Brassard, Vazirani (1997): quantum query lower bounds.
2. Boyer, Brassard, Hoyer, Tapp (1998): search with unknown number of marked items.
3. Lee, Mittal, Reichardt, Spalek, Szegedy (2011): bounded-error equivalence of
   discrete and continuous-time query models via state conversion/adversary framework.
4. Brandeho, Roland (2015): direct continuous-time adversary lower-bound framework.
5. Cleve, Gottesman, Mosca, Somma, Yonge-Mallo (2009): near-linear
   simulation of continuous-time queries by discrete queries
   ($O(T \log T/\log\log T)$ and the corresponding weaker transferred lower bound).
