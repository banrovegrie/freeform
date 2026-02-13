# Structured Tractability: Proofs

## Notation and Setup

Let $H_z$ be a diagonal Hamiltonian on $N = 2^n$ states with eigenvalues
$E_0 < E_1 < \cdots < E_{M-1}$ and degeneracies $d_0, d_1, \ldots, d_{M-1}$
satisfying $\sum_k d_k = N$. The spectral gap is $\Delta = E_1 - E_0$. The key
parameter from the paper is

$$A_1 = \frac{1}{N}\sum_{k=1}^{M-1}\frac{d_k}{E_k - E_0}.$$

The paper shows: the adiabatic runtime with the optimal local schedule is

$$T = O\!\left(\frac{\sqrt{A_2}}{A_1^2\,\Delta^2}\,\sqrt{\frac{N}{d_0}}\right),$$

and this is optimal among all monotone schedules. The schedule itself depends on $A_1$
(through $s^* = A_1/(1 + A_1)$ and the local gap profile), so computing $A_1$ is
necessary to run the optimal schedule.

Throughout, "Grover Hamiltonian" means
$H_z = I - \sum_{z \in S}|z\rangle\langle z|$ with $|S| = d_0$ marked items
($E_0 = 0$, $E_1 = 1$, $d_1 = N - d_0$). In this case $M = 2$ and
$A_1 = (N - d_0)/N$.

### Computational models (used implicitly below)

To keep statements precise, we distinguish a few input/algorithm models:

- **Spectral-list model:** the instance is given explicitly as $(E_k,d_k)_{k=0}^{M-1}$.
  Then computing $A_1$ is just arithmetic (Proposition 3).
- **Local energy model:** the instance is given as an integer-valued local energy
  function $E(x)=\sum_j E_j(x_{S_j})$ with constant locality and polynomially bounded
  range. This covers clause-violation CSP Hamiltonians and Ising-type diagonal
  Hamiltonians. In this model, evaluating $E(x)$ on a given assignment is polynomial
  time.
- **Partition-function oracle model:** the algorithm can query (exactly or
  approximately) $Z(t)=\sum_x t^{E(x)}$ or $Z(\beta)=\sum_x e^{-\beta E(x)}$ at points
  of its choice. Propositions 10-12 explain how such access translates into additive
  approximations of $A_1$.

Approximation guarantees below are **additive** unless stated otherwise.


## Proposition 1: Conjecture 1 is False

**Conjecture 1.** For $d_0 = 1$ and $\Delta \ge 1/\mathrm{poly}(n)$:
$A_1 = 1/\Delta + O(1)$.

**Counterexample.** Take $N = 2^n$, three energy levels:

| Level | Energy | Degeneracy |
|-------|--------|------------|
| 0     | 0      | 1          |
| 1     | $1/n$  | 1          |
| 2     | 1      | $N - 2$    |

Then $\Delta = 1/n = 1/\mathrm{poly}(n)$, and

$$A_1 = \frac{1}{N}\!\left[\frac{1}{1/n} + \frac{N-2}{1}\right]
      = \frac{n}{N} + \frac{N-2}{N}
      = \frac{n}{N} + 1 - \frac{2}{N}.$$

For large $n$, $A_1 \to 1$ because the $n/N$ term vanishes. Meanwhile
$1/\Delta = n \to \infty$. So $A_1 \ne 1/\Delta + O(1)$.

The mechanism is clear: the single string at $E_1 = 1/n$ contributes $n/N$ to $A_1$
(negligible), while the $N - 2$ strings at $E_2 = 1$ contribute $(N-2)/N \approx 1$.
The tail dominates the pole.

**Sanity check ($n = 4$, $N = 16$).** $A_1 = 4/16 + 14/16 = 18/16 = 9/8 = 1.125$.
Conjecture predicts $A_1 \approx 1/\Delta = 4$. The actual value is $1.125$, off by a
factor of $3.6$.

**Remark on naturality.** This spectrum is contrived: it assigns energies to
bit-strings without reference to a combinatorial problem. Any diagonal Hamiltonian on
$N$ states with values in $[0,1]$ is a valid problem Hamiltonian in the paper's
framework (Definition 1), so the counterexample is mathematically valid. But it leaves
open whether Conjecture 1 fails for spectra arising from natural optimization problems
(SAT, Max-Cut, etc.), where the energy landscape is more structured. $\square$


## Proposition 2: Conjecture 2 is Vacuous

**Conjecture 2.** If $d_k \le \mathrm{poly}(n)$ for all $k \ge 1$ and
$M \le \mathrm{poly}(n)$, then $A_1$ is computable in poly time.

The conjecture is technically true but vacuous: its hypothesis forces the problem to
be trivial.

**Proof.** Under the hypothesis, the total number of non-ground-state strings is

$$\sum_{k=1}^{M-1} d_k \le (M-1)\cdot\max_k d_k \le \mathrm{poly}(n)^2.$$

Since $\sum_{k=0}^{M-1} d_k = N = 2^n$, we get

$$d_0 = N - \sum_{k \ge 1} d_k \ge 2^n - \mathrm{poly}(n)^2.$$

For sufficiently large $n$, $\mathrm{poly}(n)^2 \ll 2^n$, so $d_0/N \to 1$. The ground
space is almost the entire Hilbert space: the initial state $|+\rangle^{\otimes n}$
has overlap $\langle +^n | \Pi_0 | +^n \rangle = d_0/N = 1 - o(1)$ with the ground
space. A single random sample lands in the ground space with probability
$1 - \mathrm{poly}(n)^2/2^n$, so the optimization problem is trivially solvable
without any quantum algorithm. $\square$


## Proposition 3: Sufficient Condition for Tractable $A_1$

**Proposition.** If all three conditions hold:

1. $M = \mathrm{poly}(n)$ distinct energy levels,
2. Each degeneracy $d_k$ is efficiently computable,
3. Each energy $E_k$ is efficiently computable,

then $A_1$ is computable in $\mathrm{poly}(n)$ time.

**Proof.** The sum $A_1 = (1/N)\sum_{k=1}^{M-1} d_k/(E_k - E_0)$ has
$M - 1 = \mathrm{poly}(n)$ terms, each requiring one division and one subtraction
with known inputs. The total computation is $\mathrm{poly}(n)$. $\square$

**Remark.** These conditions are sufficient but not necessary. The sum can sometimes
be evaluated without knowing individual $d_k$. For instance, if all non-ground states
share a common energy ($E_k = E_0 + c$ for all $k \ge 1$), then
$A_1 = (N - d_0)/(Nc)$ regardless of how the $N - d_0$ excited strings distribute
among sublevels. The Grover Hamiltonian is exactly this case. More generally, any
closed-form simplification of the sum (telescoping, generating functions, symmetry)
can bypass the need for individual $d_k$.

## Lemma: Partition-Function Representations of $A_1$

This is not a complexity result by itself, but it is a useful *structural* fact: it
re-expresses $A_1$ as a transform of the density of states / partition function. This
often turns "compute $A_1$" into a familiar counting / partition-function task.

Throughout, shift energies so that $E_0 = 0$ (this does not change $A_1$).

### Laplace-transform identity (general nonnegative spectrum)

Let $E(x)\ge 0$ be the energy of basis state $|x\rangle$ and define the Laplace
partition function
$$Z(\beta) \;\defeq\; \sum_x e^{-\beta E(x)}.$$
Then
$$A_1 \;=\; \frac{1}{N}\int_0^\infty \left(Z(\beta)-d_0\right)\,d\beta.$$

**Proof.** For any $a>0$, $\frac{1}{a}=\int_0^\infty e^{-\beta a}\,d\beta$. Apply this
to $a=E(x)$ for every excited state $x$ with $E(x)>0$. Writing
$$Z(\beta)-d_0=\sum_{x:E(x)>0} e^{-\beta E(x)},$$
we have a finite sum of nonnegative terms, so Tonelli's theorem (or simply
finiteness) justifies interchanging sum and integral:
$$\int_0^\infty (Z(\beta)-d_0)\,d\beta
  =\sum_{x:E(x)>0}\int_0^\infty e^{-\beta E(x)}\,d\beta
  =\sum_{x:E(x)>0}\frac{1}{E(x)}.$$
Dividing by $N$ gives $A_1=(1/N)\sum_{x:E(x)>0}1/E(x)$, which is the same as the
level-sum definition. $\square$

### Ordinary generating-function identity (integer spectra)

If the energies are integers $E(x)\in\{0,1,\ldots,m\}$, define the ordinary partition
function / generating function
$$Z(t)\;\defeq\;\sum_x t^{E(x)} \;=\;\sum_{k=0}^m d_k t^k.$$
Then
$$A_1 \;=\; \frac{1}{N}\int_0^1 \frac{Z(t)-d_0}{t}\,dt.$$

**Proof.** Use $\frac{1}{k}=\int_0^1 t^{k-1}\,dt$ for integers $k\ge 1$:
$$A_1=\frac{1}{N}\sum_{k=1}^m \frac{d_k}{k}
     =\frac{1}{N}\int_0^1 \sum_{k=1}^m d_k t^{k-1}\,dt
     =\frac{1}{N}\int_0^1 \frac{Z(t)-d_0}{t}\,dt.$$
$\square$

**Remark (complexity hook).** For clause-violation CSP Hamiltonians, $Z(t)$ is
exactly a weighted counting partition function over assignments. This connects
tractability/hardness of $A_1$ to tractability/hardness of partition functions.


## Proposition 4: CSP Hardness

**Proposition.** For Boolean CSPs where counting satisfying assignments is #P-hard
(this includes $k$-SAT for $k \ge 2$, NAE-SAT, 1-in-3-SAT, and graph coloring with
$\ge 3$ colors), computing $A_1$ of the clause-violation Hamiltonian is #P-hard (even
restricted to satisfiable instances, so that $E_0 = 0$ and $d_0$ counts solutions).

**Proof.** Encode the CSP as $H = \sum_{j=1}^m C_j$ where each $C_j$ is a clause
projector: $C_j(x) = 1$ if assignment $x$ violates clause $j$, else $0$. Then
$E(x) = \sum_j C_j(x)$ counts violated clauses, the energy levels are integers
$0, 1, \ldots, m$, and $d_k$ counts assignments violating exactly $k$ clauses.

To avoid the corner case where the instance is unsatisfiable (so $E_0 > 0$ and $d_0$
does not count satisfying assignments), we reduce from the satisfiable-only counting
problem. For $k$-SAT, this restriction is still \#P-hard: given a CNF $\varphi(x)$ on
$n$ variables, introduce a fresh bit $y$ and replace each clause $C$ by
$(\neg y \lor C)$. The new formula $\varphi'(x,y)$ is always satisfiable (set $y=0$),
and $\#\mathrm{sat}(\varphi') = 2^n + \#\mathrm{sat}(\varphi)$. Thus computing the
solution count remains \#P-hard even on satisfiable instances, and for such instances
we have $E_0 = 0$ and $d_0 = \#\mathrm{sat}(\varphi')$.

The paper (Main Result 3) proves #P-hardness for Ising Hamiltonians via the following
argument. Construct an $(n+1)$-qubit Hamiltonian $H'(x) = H \otimes I - I \otimes
(x/2)\,\sigma_+^{(n+1)}$ where $x > 0$ is a tunable parameter that shifts the energy
gaps. Define $f(x) = 2A_1(H'(x)) - A_1(H)$. Then

$$f(x) = \frac{1}{N}\sum_{k=0}^{M-1}\frac{d_k}{\Delta_k + x/2},$$

where $\Delta_k = E_k - E_0$ are the energy gaps of $H$. This is a rational function
of $x$ with $M$ poles. Multiplying through by $\prod_k (\Delta_k + x/2)$ yields a
polynomial of degree $M - 1$ whose coefficients encode the $d_k$. Evaluating $f$ at $M$
distinct values of $x$ and applying Lagrange interpolation recovers all degeneracies.
In particular, $d_0 = N - \sum_{k \ge 1} d_k$ is recovered.

For CSP Hamiltonians: (a) the energy levels are integers $0, 1, \ldots, m$, so
$M \le m + 1 = \mathrm{poly}(n)$ and the interpolation requires polynomially many
evaluations; (b) computing $d_0$ (counting satisfying assignments) is #P-hard for the
CSP in question (by hypothesis); (c) each evaluation of $f(x)$ requires computing
$A_1$ of an $(n+1)$-qubit Hamiltonian whose structure matches the original CSP. Hence
computing $A_1$ is at least as hard as computing $d_0$.

The argument does not apply to CSPs with easy counting (2-coloring, XOR-SAT, Horn-SAT),
since for these #$d_0$ is in P and the reduction yields no hardness. $\square$


## Proposition 5: Grover as Sweet Spot

**Proposition.** The Grover Hamiltonian $H_z = I - \sum_{z \in S}|z\rangle\langle z|$
(with $|S| = d_0$ marked items) has $A_1 = (N - d_0)/N$. In the promise model where
$d_0$ is given as input alongside $H_z$, $A_1$ is computable in $O(1)$ time while
the search problem (finding any $z \in S$) requires $\Omega(\sqrt{N/d_0})$ quantum
queries and $\Omega(N/d_0)$ classical queries.

**Proof.** The spectrum has $M = 2$ levels: $E_0 = 0$ (degeneracy $d_0$) and $E_1 = 1$
(degeneracy $N - d_0$). Therefore

$$A_1 = \frac{1}{N}\cdot\frac{N - d_0}{1} = 1 - \frac{d_0}{N}.$$

Given $d_0$, this is a single arithmetic operation.

The search lower bounds are standard: $\Omega(\sqrt{N/d_0})$ quantum queries (Bennett
et al. 1997, Grover 1996) and $\Omega(N/d_0)$ classical queries (by a straightforward
adversary argument).

**Caveat.** The tractability of $A_1$ here depends on knowing $d_0$, which is itself a
piece of spectral information. In the standard oracle model where $d_0$ is unknown,
computing $A_1$ reduces to computing $d_0$, which requires $\Theta(\sqrt{N})$ quantum
queries (quantum counting). The sweet spot is genuine but requires the promise that
$d_0$ is given. This is a weaker claim than "search is hard AND $A_1$ is easy from the
same information."

**Sanity checks.**
- $N = 4$, $d_0 = 1$: $A_1 = 3/4$. Crossing at $s^* = A_1/(1 + A_1) = 3/7$.
- $N = 4$, $d_0 = 2$: $A_1 = 1/2$. Crossing at $s^* = 1/3$. $\square$


## Proposition 6: Conjecture 3 Fails in Both Directions

**Conjecture 3.** $A_1$ is efficiently computable if and only if the optimization
problem (finding a ground state of $H_z$) is in P. Equivalently: no "sweet spot" of
hard problem + easy $A_1$ exists.

**Proposition.** The conjecture is false in both directions.

**(a) Easy optimization does not imply easy $A_1$.**

2-SAT is solvable in polynomial time, but #2-SAT (counting satisfying assignments)
is #P-complete (Valiant 1979). The 2-SAT clause-violation Hamiltonian $H = \sum_j C_j$
has degeneracies $d_k$ counting assignments violating exactly $k$ clauses. By
Proposition 4, computing $A_1$ for 2-SAT Hamiltonians is #P-hard.

**(b) Hard search does not imply hard $A_1$ (in the promise model).**

By Proposition 5, the Grover Hamiltonian with known $d_0$ has
$A_1 = (N - d_0)/N$ computable in $O(1)$ time. The search problem requires
$\Omega(\sqrt{N/d_0})$ quantum queries. As noted in Proposition 5, this is a
promise-model result: the solver is given $d_0$ alongside the oracle.

**The corrected picture.** The tractability of $A_1$ is determined by spectral
complexity, not optimization hardness. Optimization hardness and counting hardness
are independent: 2-SAT is easy to optimize but hard to count; Grover search is hard to
solve but trivial to count (given $d_0$). $A_1$ tracks counting complexity, since it is
a weighted sum over the degeneracy spectrum.

Whether NP-hard problems with genuinely easy $A_1$ (without extra information like
$d_0$) exist beyond the Grover family remains open. $\square$


## Remark: Planted Instances with Provided $A_1$

For planted-solution instances, the constructor knows $z^*$ and the full spectrum at
creation time. Publishing $(H_z, A_1)$ alongside the instance lets the solver run the
optimal schedule without computing $A_1$. This is the observation that $A_1$ is a
short advice string ($O(n)$ bits suffice to specify it to the precision needed for the
schedule). The paper's hardness result says this advice cannot be computed efficiently
in general, but it can be provided by a trusted party.

This is not a deep result: anyone with full knowledge of the spectrum can compute any
spectral parameter. The nontrivial content is that $A_1$ alone (rather than the full
spectrum $\{d_k, E_k\}$) suffices to run the optimal schedule, and it is a short
string.


## Proposition 7: Hamming Distance Hamiltonians

**Proposition.** For the Hamming distance Hamiltonian $H_z$ defined by
$E(x) = d_H(x, z^*)$ (Hamming distance from $x$ to a secret string $z^*$), $A_1$
depends only on $n$ and is computable in $O(n)$ time.

**Proof.** The spectrum has $M = n + 1$ levels with $E_k = k$ for $k = 0, 1, \ldots, n$.
The degeneracy of level $k$ is $d_k = \binom{n}{k}$ (the number of strings at Hamming
distance $k$ from $z^*$). Therefore $d_0 = 1$, $\Delta = 1$, and

$$A_1 = \frac{1}{2^n}\sum_{k=1}^{n}\frac{\binom{n}{k}}{k}.$$

Each term depends only on $n$, not on $z^*$. The sum has $n$ terms, each computable in
$O(1)$ arithmetic operations. Total: $O(n)$.

**Integral representation.** $A_1 = 2^{-n}\int_0^1 [(1+x)^n - 1]/x\, dx$, since
$\int_0^1 x^{k-1}\,dx = 1/k$. By Laplace's method: near $x = 1$, substitute
$x = 1 - t/n$ to get $(1+x)^n \approx 2^n e^{-t/2}$ and $dx = dt/n$. The dominant
contribution is

$$A_1 \approx 2^{-n}\cdot\frac{2^n}{n}\int_0^\infty e^{-t/2}\,dt
    = \frac{2}{n}.$$

Numerically: $A_1 \cdot n/2 \to 1$ as $n \to \infty$ ($1.07$ at $n = 4$, $1.08$ at
$n = 16$, $1.008$ at $n = 128$). Convergence is non-monotone.

**Explicit values.**

| $n$ | $A_1$ (exact)  | $A_1$ (decimal) |
|-----|----------------|-----------------|
| 2   | $5/8$          | $0.625$         |
| 3   | $29/48$        | $0.604$         |
| 4   | $103/192$      | $0.537$         |
| 8   | $63253/215040$ | $0.294$         |
| 16  |                | $0.135$         |
| 32  |                | $0.065$         |

**Limitation.** Finding $z^*$ from the Hamming distance oracle requires only $n$
queries (query each $e_i$ to read the $i$-th bit of $z^*$). So the search problem is
easy, and this is not a counterexample to Conjecture 3 -- both optimization and $A_1$
are easy. $\square$


## Proposition 8: Bounded Treewidth (Exact $A_1$ via Partition Functions)

This is the first concrete positive tractability result that goes beyond the
tautological sufficient condition "given all $(E_k,d_k)$, compute the sum".

It formalizes the heuristic: if the spectrum is simple because the *energy function*
has low graphical complexity, then $A_1$ is efficiently computable.

**Setup (local integer energies).** Let $E:\{0,1\}^n\to\{0,1,\ldots,m\}$ be an
integer-valued energy function written as a sum of local terms,
$$E(x) \;=\; \sum_{j=1}^r E_j(x_{S_j}),$$
where each $S_j\subseteq[n]$ has size at most $k=O(1)$ and each $E_j$ is given by its
truth table. Let $G$ be the primal graph on $[n]$ with an edge between variables that
co-occur in some $S_j$.

Define the partition-function polynomial
$$Z(t)\;\defeq\;\sum_{x\in\{0,1\}^n} t^{E(x)} \;=\; \sum_{q=0}^m d_q\,t^q.$$
Let $E_0 \defeq \min\{q : d_q>0\}$ and $d_0 \defeq d_{E_0}$.

**Proposition.** Given a tree decomposition of $G$ of width $w$, the coefficients
$\{d_q\}_{q=0}^m$ (and hence $A_1$) are exactly computable in time
$2^{O(w)}\cdot \mathrm{poly}(n,m)$.

In particular, $A_1$ is computable as
$$A_1 \;=\; \frac{1}{2^n}\sum_{q>E_0}\frac{d_q}{q-E_0}.$$

**Proof.** Write $Z(t)$ in factor-graph form. For each local term
$E_j(x_{S_j})\in\{0,1,\ldots,m\}$ define a factor
$$\phi_j(x_{S_j}) \;\defeq\; t^{E_j(x_{S_j})}.$$
Then
$$Z(t)=\sum_{x\in\{0,1\}^n}\prod_{j=1}^r \phi_j(x_{S_j}).$$

Fix an elimination ordering of the variables of induced width $w$ (equivalently, a
tree decomposition of width $w$). Variable elimination computes $Z(t)$ by repeatedly:
(i) multiplying all factors that contain the next variable $v$ into a single factor
$\Phi$ on at most $w{+}1$ variables, and (ii) summing $v\in\{0,1\}$ out of $\Phi$ to
produce a new factor on the remaining at most $w$ variables. This is the standard
sum-product algorithm; the only difference here is that factor values are *polynomials*
in $t$ whose coefficients count how many partial assignments realize each energy.

Concretely, every factor table entry is a polynomial of degree at most $m$, and:
- multiplying factors multiplies the corresponding polynomials (convolution of degrees);
- summing out $v$ adds the two polynomials corresponding to $v=0$ and $v=1$.

At width $w$, every intermediate factor has scope size at most $w{+}1$, so it has at
most $2^{w+1}$ table entries. Naive polynomial multiplication costs $O(m^2)$ per entry
(or $\widetilde{O}(m)$ via FFT if desired), and additions cost $O(m)$. With $n$ elimination
steps, total runtime is $2^{O(w)}\cdot \mathrm{poly}(n,m)$ and the final scalar factor is
exactly the polynomial $Z(t)=\sum_q d_q t^q$.

From the coefficients we compute $E_0=\min\{q:d_q>0\}$, set $d_0=d_{E_0}$, and evaluate
the finite sum
$$A_1 \;=\; \frac{1}{2^n}\sum_{q>E_0}\frac{d_q}{q-E_0}.$$
$\square$

**Sanity check (code).** `lib/variable_elimination_a1.py` demonstrates the same idea
via variable elimination (equivalent to a tree decomposition) and checks correctness
against brute force on toy low-width instances.


## Proposition 9: Coarse Approximation of $A_1$ is Easy When $E_0$ is Known

The paper's hardness result (Main Result 2) concerns estimating $A_1(H)$ given a
Hamiltonian description **without** being promised the value of $E_0$ (indeed, the
reduction uses an $A_1$-estimator to distinguish whether $E_0 = 0$).

In contrast, if $E_0$ is promised and the minimum excited energy is not too close to
$E_0$, then $A_1$ becomes a bounded mean-estimation problem and admits a simple
Monte Carlo estimator.

**Setup.** Let $H_z$ be diagonal with energies $E(x)\in[0,1]$ and known ground energy
$E_0$. Define
$$G(x)\;\defeq\;\begin{cases}
0,& E(x)=E_0,\\
\frac{1}{E(x)-E_0},& E(x)>E_0.
\end{cases}$$
Then
$$A_1 \;=\; \frac{1}{N}\sum_x G(x) \;=\; \mathbb{E}_{x\sim\mathrm{Unif}(\{0,1\}^n)}[G(x)].$$

Assume there is a known lower bound $\Delta_{\min}>0$ such that
$E(x)\in \{E_0\}\cup [E_0+\Delta_{\min},1]$ for all $x$. Then $0\le G(x)\le 1/\Delta_{\min}$.

**Proposition.** For any $\eta\in(0,1)$ and failure probability $\delta\in(0,1)$, the
empirical mean of $T$ i.i.d. samples of $G(x)$ satisfies
$$\Pr\left[\left|\widehat{A}_1 - A_1\right|>\eta\right]\le \delta$$
provided
$$T \;\ge\; \frac{1}{2\eta^2\,\Delta_{\min}^2}\ln\frac{2}{\delta}.$$
In particular, approximating $A_1$ to additive inverse-polynomial accuracy is in
\textsf{BPP} under the promise that $E_0$ and $\Delta_{\min}$ are known and
inverse-polynomially bounded.

**Proof.** Since $G(x)\in[0,1/\Delta_{\min}]$, Hoeffding's inequality gives
$$\Pr\left[\left|\widehat{A}_1-A_1\right|>\eta\right]\le
2\exp\!\left(-\frac{2T\eta^2}{(1/\Delta_{\min})^2}\right)
 = 2\exp\!\left(-2T\eta^2\Delta_{\min}^2\right).$$
Choosing $T\ge (1/(2\eta^2\Delta_{\min}^2))\ln(2/\delta)$ makes this $\le\delta$.
$\square$

**Remark (clause-violation CSPs).** For an $m$-clause CSP with energy normalized as
$E(x)=\#\mathrm{viol}(x)/m$ and satisfiable promise ($E_0=0$), we have
$\Delta_{\min}=1/m$ and hence sample complexity
$T=O\!\left(m^2\eta^{-2}\log(1/\delta)\right)$.
This gives a polynomial-time coarse approximation of $A_1$ even though exact $A_1$ is
\#P-hard (Proposition 4).

**Remark (algorithmic precision).** The adiabatic schedule requires $A_1$ at
precision on the order of $2^{-n/2}$ in the worst case (via $\delta_s$). In that
regime, the bound becomes $T=\Theta(2^n)$ samples, so Monte Carlo does not circumvent
the information barrier; it only shows that coarse approximation is easy in many
natural promise settings.

**Remark (promise boundary).** Main Result 2 of the paper shows that approximating
$A_1$ to inverse-polynomial additive precision is NP-hard *without* being promised the
ground energy $E_0$. Proposition 9 shows the complementary direction: once $E_0$ and a
lower bound on the minimum excitation $\Delta_{\min}$ are part of the promise, coarse
additive estimation becomes a standard mean-estimation problem in \textsf{BPP}.


## Proposition 10: Approximating $A_1$ from the Partition Function Without $d_0$

The partition-function identity for integer spectra reads
$$A_1 = \frac{1}{N}\int_0^1 \frac{Z(t)-d_0}{t}\,dt,$$
which appears to require knowing $d_0$ (a counting-hard quantity for many CSPs).
However, for **additive** approximation it is enough to replace $d_0$ by a single
evaluation $Z(\varepsilon)$ at a small $\varepsilon>0$.

Assume $E_0=0$ and integer energies $E(x)\in\{0,1,\ldots,m\}$, so
$$Z(t)=\sum_{q=0}^m d_q t^q,\qquad d_0 = Z(0).$$

For $\varepsilon\in(0,1)$ define the "$\varepsilon$-truncated" proxy
$$A_1^{(\varepsilon)} \;\defeq\; \frac{1}{N}\int_{\varepsilon}^1 \frac{Z(t)-Z(\varepsilon)}{t}\,dt.$$

**Proposition.** For all $\varepsilon\in(0,1)$,
$$0 \;\le\; A_1 - A_1^{(\varepsilon)} \;\le\; \varepsilon\left(1+\ln\frac{1}{\varepsilon}\right).$$
Consequently, choosing $\varepsilon \le \eta/\!\left(2(1+\ln(2/\eta))\right)$ gives an
additive $\eta$ approximation to $A_1$ once $A_1^{(\varepsilon)}$ is computed to
additive error $\eta/2$.

**Proof.** Using $Z(t)-d_0=\sum_{q\ge 1} d_q t^q$,
\begin{align}
A_1N &= \int_0^1 \sum_{q\ge 1} d_q t^{q-1}\,dt
     = \sum_{q\ge 1}\frac{d_q}{q}.
\end{align}
Also,
\begin{align}
A_1^{(\varepsilon)}N
&= \int_{\varepsilon}^1 \frac{Z(t)-d_0}{t}\,dt
   - (Z(\varepsilon)-d_0)\int_{\varepsilon}^1 \frac{dt}{t} \\
&= \int_{\varepsilon}^1 \sum_{q\ge 1} d_q t^{q-1}\,dt
   - \left(\sum_{q\ge 1} d_q \varepsilon^q\right)\ln\frac{1}{\varepsilon}.
\end{align}
Subtracting,
\begin{align}
(A_1 - A_1^{(\varepsilon)})N
&= \int_0^{\varepsilon} \sum_{q\ge 1} d_q t^{q-1}\,dt
   + \left(\sum_{q\ge 1} d_q \varepsilon^q\right)\ln\frac{1}{\varepsilon} \\
&= \sum_{q\ge 1} d_q \varepsilon^q\left(\frac{1}{q} + \ln\frac{1}{\varepsilon}\right).
\end{align}
All terms are nonnegative, so the difference is $\ge 0$. For the upper bound, use
$\varepsilon^q \le \varepsilon$ and $1/q \le 1$:
\begin{align}
(A_1 - A_1^{(\varepsilon)})N
&\le \sum_{q\ge 1} d_q\,\varepsilon\left(1+\ln\frac{1}{\varepsilon}\right)
 = (N-d_0)\,\varepsilon\left(1+\ln\frac{1}{\varepsilon}\right)
 \le N\,\varepsilon\left(1+\ln\frac{1}{\varepsilon}\right).
\end{align}
Divide by $N$ to obtain the stated inequality. $\square$

**Remark (algorithmic hook).** The proxy $A_1^{(\varepsilon)}$ depends only on the
values $Z(t)$ for $t\in[\varepsilon,1]$ (plus one baseline value $Z(\varepsilon)$),
not on $d_0=Z(0)$. This creates room for structured positive results: whenever
$Z(t)$ is computable/approximable for moderate $t$ but $d_0$ is hard, one may still
obtain a meaningful additive approximation to $A_1$.

**Remark (tightness).** The truncation bound is essentially tight. For the two-level
Grover spectrum ($E\in\{0,1\}$), one can compute explicitly that
$$A_1-A_1^{(\varepsilon)}=\frac{N-d_0}{N}\,\varepsilon\left(1+\ln\frac{1}{\varepsilon}\right),$$
matching the upper bound up to the factor $(N-d_0)/N\le 1$.


## Proposition 11: Laplace-Side Proxy Without $d_0$ (Truncation + Anchoring)

Proposition 10 used the *ordinary* partition function $Z(t)$ for integer spectra. For
general nonnegative spectra, the Laplace identity
$$A_1 = \frac{1}{N}\int_0^\infty \left(Z(\beta)-d_0\right)\,d\beta,\qquad
Z(\beta)=\sum_x e^{-\beta E(x)}$$
still appears to require knowing $d_0$. The following proxy removes $d_0$ while also
truncating the infinite integration range.

Assume $E_0=0$ and define the minimum excited energy
$$\Delta_{\min}\;\defeq\;\min\{E(x):E(x)>0\}\,>0.$$

For $B>0$ define the anchored proxy
$$A_1^{[B]} \;\defeq\; \frac{1}{N}\int_{0}^{B}\left(Z(\beta)-Z(B)\right)\,d\beta.$$

**Proposition.** For all $B>0$,
$$0 \;\le\; A_1 - A_1^{[B]} \;\le\; e^{-B\Delta_{\min}}\left(B+\frac{1}{\Delta_{\min}}\right).$$
In particular, for integer spectra with $\Delta_{\min}\ge 1$,
$$0 \;\le\; A_1 - A_1^{[B]} \;\le\; e^{-B}(1+B).$$

**Proof.** Write $Z(\beta)-d_0=\sum_{x:E(x)>0}e^{-\beta E(x)}$. Then
\begin{align}
A_1^{[B]}N
&= \int_0^B \sum_{x:E(x)>0}\left(e^{-\beta E(x)}-e^{-B E(x)}\right)\,d\beta\\
&= \sum_{x:E(x)>0}\left(\int_0^B e^{-\beta E(x)}\,d\beta - B e^{-B E(x)}\right)\\
&= \sum_{x:E(x)>0}\left(\frac{1-e^{-B E(x)}}{E(x)} - B e^{-B E(x)}\right).
\end{align}
Subtracting from $A_1N=\sum_{x:E(x)>0}1/E(x)$ gives
$$ (A_1-A_1^{[B]})N
 = \sum_{x:E(x)>0} e^{-B E(x)}\left(\frac{1}{E(x)}+B\right),$$
which is nonnegative. For the upper bound, use $E(x)\ge \Delta_{\min}$, hence
$e^{-B E(x)}\le e^{-B\Delta_{\min}}$ and $1/E(x)\le 1/\Delta_{\min}$:
\begin{align}
(A_1-A_1^{[B]})N
&\le \sum_{x:E(x)>0} e^{-B\Delta_{\min}}\left(B+\frac{1}{\Delta_{\min}}\right)
\le N\, e^{-B\Delta_{\min}}\left(B+\frac{1}{\Delta_{\min}}\right).
\end{align}
Divide by $N$. $\square$

**Remark (precision scaling).** The bound decays essentially as
$B e^{-B\Delta_{\min}}$, so achieving additive error $\eta$ requires
$B=\Theta((1/\Delta_{\min})\log(1/\eta))$. In the AQO-relevant regime
$\eta\approx 2^{-n/2}$, this forces $B=\Theta(n/\Delta_{\min})$, i.e. access to
low-temperature partition functions.

**Remark (tightness).** For the two-level Grover spectrum ($E\in\{0,1\}$),
$$A_1-A_1^{[B]}=\frac{N-d_0}{N}\,e^{-B}(1+B),$$
so the exponential tail bound is again achieved up to the factor $(N-d_0)/N$.


## Proposition 12: Oracle Reduction (Approximate $Z$ $\Rightarrow$ Additive Approximation of $A_1$)

Propositions 10-11 turn $A_1$ into a *log-scale integral* of partition-function
evaluations. This section makes the algorithmic consequence explicit: any method for
(approximately) evaluating $Z$ over a temperature window yields an additive approximation
to $A_1$.

We state the result for the ordinary (integer-spectrum) case; an analogous statement
holds for the Laplace proxy $A_1^{[B]}$ by replacing the $t$-grid with a $\beta$-grid.

Assume integer energies $E(x)\in\{0,1,\ldots,m\}$ and $E_0=0$, so
$Z(t)=\sum_{q=0}^m d_q t^q$ and Proposition 10 applies.

Fix $\varepsilon\in(0,1)$ and write the proxy
$$A_1^{(\varepsilon)}=\frac{1}{N}\int_{\varepsilon}^1\frac{Z(t)-Z(\varepsilon)}{t}\,dt
     =\frac{1}{N}\int_{\ln\varepsilon}^{0}\left(Z(e^u)-Z(\varepsilon)\right)\,du,$$
where $u=\ln t$.

**Proposition.** Suppose we can query an oracle that returns $\widehat{Z}(t)$ for any
$t\in[\varepsilon,1]$ such that
$$\left|\widehat{Z}(t)-Z(t)\right|\le \alpha N.$$
Let $K\ge 1$ and set $h\defeq \ln(1/\varepsilon)/K$. Define midpoints
$u_i\defeq \ln\varepsilon + (i+1/2)h$ and $t_i\defeq e^{u_i}$ for $i=0,\ldots,K-1$,
and compute the midpoint-rule estimator
$$\widehat{A}_1^{(\varepsilon)} \;\defeq\; \frac{h}{N}\sum_{i=0}^{K-1}\left(\widehat{Z}(t_i)-\widehat{Z}(\varepsilon)\right).$$
Then
$$\left|\widehat{A}_1^{(\varepsilon)}-A_1^{(\varepsilon)}\right|
 \;\le\; 2\alpha\ln\frac{1}{\varepsilon} \;+\; \frac{m}{2}\,h\,\ln\frac{1}{\varepsilon}.$$

Consequently, choosing
$$\alpha \le \frac{\eta}{8\ln(1/\varepsilon)},\qquad
K \ge \frac{4m\,\ln(1/\varepsilon)^2}{\eta}$$
ensures $\left|\widehat{A}_1^{(\varepsilon)}-A_1^{(\varepsilon)}\right|\le \eta/2$.
Combining with Proposition 10 yields an overall additive $\eta$ approximation to $A_1$
once $\varepsilon$ is chosen to make $A_1-A_1^{(\varepsilon)}\le \eta/2$.

**Proof.** Split the error into (i) oracle evaluation error and (ii) quadrature error.

*(i) Oracle error.* By triangle inequality,
$$\left|\big(\widehat{Z}(t)-\widehat{Z}(\varepsilon)\big)-\big(Z(t)-Z(\varepsilon)\big)\right|
\le \left|\widehat{Z}(t)-Z(t)\right|+\left|\widehat{Z}(\varepsilon)-Z(\varepsilon)\right|
\le 2\alpha N.$$
Integrating $\frac{dt}{t}$ from $\varepsilon$ to $1$ gives total contribution
$(1/N)\int_{\varepsilon}^1 2\alpha N \,dt/t = 2\alpha\ln(1/\varepsilon)$.

*(ii) Quadrature error.* Define $F(u)\defeq Z(e^u)-Z(\varepsilon)$ on
$u\in[\ln\varepsilon,0]$. Since $Z(t)$ is a degree-$m$ polynomial with nonnegative
coefficients and $t\in[0,1]$,
$$Z'(t)=\sum_{q\ge 1} q d_q t^{q-1} \le \sum_{q\ge 1} q d_q \le m\sum_q d_q = mN.$$
Thus $|F'(u)|=|e^u Z'(e^u)| \le mN$, so $F$ is $mN$-Lipschitz. On an interval of length
$h$, midpoint-rule error is bounded by $\int |F(u)-F(u_{\mathrm{mid}})|\,du \le (mN)h^2/2$.
Summing over $K$ intervals yields total quadrature error at most
$(mN)h^2K/2 = (mN)h\ln(1/\varepsilon)/2$. Dividing by $N$ gives
$(m/2)h\ln(1/\varepsilon)$. $\square$

**Remark (structured families).** Proposition 12 is where partition-function algorithms
enter: whenever a model admits an FPRAS / deterministic approximation scheme for $Z$ on
a temperature window, we immediately obtain an additive approximation scheme for $A_1$.


## Proposition 13: Ferromagnetic Ising via Multiplicative Partition-Function Approximation

We now make the error drivers explicit: energy scale, minimum excitation, and mass
near the ground.

Assume $E_0=0$ and $E(x)\in[0,R]$ for all basis states $x$. Define
$$\rho_0 \defeq d_0/N,\qquad
\Delta_{\min}\defeq \min\{E(x):E(x)>0\}.$$
Let $Z(\beta)=\sum_x e^{-\beta E(x)}$.

Fix $B>0$, $K\ge 1$, and midpoints $\beta_i\defeq(i+1/2)B/K$.
Suppose an oracle returns $\widehat{Z}(\beta)$ such that for every queried
$\beta\in[0,B]$,
$$(1-\mu)Z(\beta)\le \widehat{Z}(\beta)\le (1+\mu)Z(\beta),$$
with failure probability at most $\delta_q$ per query.

Define
$$\widehat{A}_1^{[B]} \defeq \frac{B}{KN}\sum_{i=0}^{K-1}\left(\widehat{Z}(\beta_i)-\widehat{Z}(B)\right).$$
Then, with probability at least $1-(K+1)\delta_q$,
$$\left|A_1-\widehat{A}_1^{[B]}\right|
\le (1-\rho_0)e^{-B\Delta_{\min}}\left(B+\frac{1}{\Delta_{\min}}\right)
   +2\mu B + \frac{R B^2}{2K}.$$

In particular, choosing
$$\mu\le \frac{\eta}{6B},\qquad
K\ge \frac{3RB^2}{2\eta},\qquad
(1-\rho_0)e^{-B\Delta_{\min}}\left(B+\frac{1}{\Delta_{\min}}\right)\le \frac{\eta}{3},$$
and $\delta_q=\delta/(K+1)$ gives an additive-$\eta$ estimator with success
probability at least $1-\delta$.

**Proof.** Write the exact anchored proxy
$$A_1^{[B]}=\frac{1}{N}\int_0^B\left(Z(\beta)-Z(B)\right)\,d\beta.$$
Split
$$|A_1-\widehat{A}_1^{[B]}|
\le |A_1-A_1^{[B]}|
 + |A_1^{[B]}-\widetilde{A}_1^{[B]}|
 + |\widetilde{A}_1^{[B]}-\widehat{A}_1^{[B]}|,$$
where $\widetilde{A}_1^{[B]}$ is the midpoint rule using exact $Z$ values.

Tail term:
\begin{align}
(A_1-A_1^{[B]})N
&= \sum_{x:E(x)>0} e^{-B E(x)}\left(\frac{1}{E(x)}+B\right) \\
&\le (N-d_0)e^{-B\Delta_{\min}}\left(B+\frac{1}{\Delta_{\min}}\right).
\end{align}
Dividing by $N$ gives
$$|A_1-A_1^{[B]}|
\le (1-\rho_0)e^{-B\Delta_{\min}}\left(B+\frac{1}{\Delta_{\min}}\right).$$

Oracle term: whenever all oracle calls succeed,
$$|\widehat{Z}(\beta)-Z(\beta)|\le \mu Z(\beta)\le \mu N$$
for every queried $\beta$ (since $Z(\beta)\le N$ for nonnegative energies).
Hence for each midpoint,
\begin{align}
\left|(\widehat{Z}(\beta_i)-\widehat{Z}(B))-(Z(\beta_i)-Z(B))\right|
\le 2\mu N.
\end{align}
After summing and multiplying by $B/(KN)$,
$$|\widetilde{A}_1^{[B]}-\widehat{A}_1^{[B]}|\le 2\mu B.$$

Quadrature term: let $F(\beta)\defeq Z(\beta)-Z(B)$. Then
\begin{align}
|F'(\beta)|
&= |Z'(\beta)|
 = \left|\sum_x -E(x)e^{-\beta E(x)}\right|
 \le \sum_x E(x) \le RN.
\end{align}
So $F$ is $RN$-Lipschitz on $[0,B]$. For interval length $h=B/K$, midpoint error on
one interval is at most $RN h^2/2$, so total quadrature error is at most
$RN Bh/2 = RN B^2/(2K)$. Dividing by $N$:
$$|A_1^{[B]}-\widetilde{A}_1^{[B]}|\le \frac{R B^2}{2K}.$$

Combining the three bounds gives the claimed inequality.
There are $K+1$ oracle calls ($K$ midpoints plus $\beta=B$), so by union bound the
success probability is at least $1-(K+1)\delta_q$. Substituting
$\delta_q=\delta/(K+1)$ and the parameter choices yields total error at most $\eta$.
$\square$

**Corollary (ferromagnetic Ising with consistent fields).**
Consider the Ising cost function on spins $\sigma\in\{\pm1\}^n$:
$$C(\sigma)=\sum_{(i,j)\in E} J_{ij}\frac{1-\sigma_i\sigma_j}{2}
           +\sum_{i=1}^n h_i\frac{1-\sigma_i}{2},$$
with $J_{ij},h_i\in\mathbb{Z}_{\ge 0}$ (if all external fields are nonpositive,
globally flip all spins first). Let
$$W\defeq \sum_{(i,j)\in E}J_{ij}+\sum_i h_i,\qquad E(\sigma)\defeq C(\sigma)/W.$$
Assume $W>0$.
Then $E(\sigma)\in[0,1]$, $E_0=0$, and $\Delta_{\min}\ge 1/W$. If a multiplicative
FPRAS for $Z(\beta)=\sum_\sigma e^{-\beta E(\sigma)}$ is available on $\beta\in[0,B]$
(as in classical ferromagnetic Ising FPRAS results in this regime), Proposition 13
gives an additive approximation of $A_1$.

For target $\eta$ and failure probability $\delta$, pick any $B$ such that
$e^{-B/W}(B+W)\le \eta/3$ (equivalently $B=O(W\log(W/\eta))$), then choose
$\mu=\Theta(\eta/B)$ and $K=\Theta(B^2/\eta)$. If the FPRAS runtime is
$\mathrm{poly}(n,1/\mu,\log(1/\delta_q))$, the resulting $A_1$ estimator runs in
$\mathrm{poly}(n,W,1/\eta,\log(1/\delta))$ time for inverse-polynomial $\eta$.

At schedule-level precision $\eta=2^{-n/2}$, the same reduction requires
$1/\mu=\Omega(B/\eta)=\Omega(2^{n/2}/\mathrm{poly}(n))$, so the induced runtime is no
longer polynomial. This matches the low-temperature precision barrier.


## Proposition 14: Schedule-Relevant Precision for $A_1$

Let $s^*(A)\defeq A/(1+A)$ for $A>0$. Suppose we estimate $A_1$ by
$\widehat{A}_1=A_1+\varepsilon$ with $\widehat{A}_1>-1$, and define
$\widehat{s}^*=s^*(\widehat{A}_1)$.

Then
$$\widehat{s}^*-s^*=\frac{\varepsilon}{(1+A_1)(1+A_1+\varepsilon)}.$$
In particular, if $|\varepsilon|\le (1+A_1)/2$, then
$$|\widehat{s}^*-s^*|\le \frac{2|\varepsilon|}{(1+A_1)^2}.$$
So a sufficient condition for $|\widehat{s}^*-s^*|\le \delta_s$ is
$$|\varepsilon|\le \min\!\left\{\frac{1+A_1}{2},\;\frac{(1+A_1)^2}{2}\,\delta_s\right\}.$$

Using the paper's crossing-window scale
$$\delta_s=\frac{2}{(1+A_1)^2}\sqrt{\frac{d_0A_2}{N}},$$
it suffices to estimate $A_1$ to additive precision
$$|\varepsilon|\le \min\!\left\{\frac{1+A_1}{2},\;\sqrt{\frac{d_0A_2}{N}}\right\}.$$
Whenever $\sqrt{d_0A_2/N}\le (1+A_1)/2$, this simplifies to
$$|\varepsilon|\le \sqrt{\frac{d_0A_2}{N}}.$$
In the worst case $d_0=\Theta(1)$ and $A_2=\Theta(1)$, this is
$\Theta(2^{-n/2})$.

**Proof.** The identity is direct algebra:
\begin{align}
\frac{A_1+\varepsilon}{1+A_1+\varepsilon}-\frac{A_1}{1+A_1}
=\frac{\varepsilon}{(1+A_1)(1+A_1+\varepsilon)}.
\end{align}
If $|\varepsilon|\le (1+A_1)/2$, then
$1+A_1+\varepsilon\ge (1+A_1)/2$, hence
\begin{align}
|\widehat{s}^*-s^*|
&\le \frac{|\varepsilon|}{(1+A_1)\cdot (1+A_1)/2}
=\frac{2|\varepsilon|}{(1+A_1)^2}.
\end{align}
The sufficient condition follows by requiring the right-hand side be at most
$\delta_s$, and substituting the paper's formula for $\delta_s$ yields the final
expression. $\square$


## Gap 2 Setup (Model and Approximation Target)

For the boundary result below, the input model is diagonal $k$-local Hamiltonians on
$n$ bits, given by an explicit list of local terms with rational coefficients of
bit-complexity $\mathrm{poly}(n)$. Energies satisfy $E(x)\in[0,R]$ with
$R=\mathrm{poly}(n)$, and $A_1$ is approximated in additive error
$|\widehat{A}_1-A_1|\le \eta(n)$.

The attempted reverse strategy in Todo-B1(a) was: recover low-temperature partition
information from accurate $A_1$ estimates. Proposition 15 gives a sharp obstruction.


## Proposition 15: Reverse-Bridge Obstruction (Exact $A_1$ Does Not Determine Low-Temperature $Z$)

Fix integers $B\ge 3$ and $n\ge 4$. Let $N=2^n$ and define two diagonal Hamiltonians
on $x\in\{0,1\}^n$:
\[
E_U(x)\defeq x_1\!\left(B-\left(B-\frac{1}{B}\right)(1-x_2)(1-x_3)\right),
\]
\[
c_B\defeq \frac{7B}{B^2+6},\qquad
E_S(x)\defeq x_1\!\left(c_B-\left(c_B-\frac{1}{B}\right)
(1-x_2)(1-x_3)(1-x_4)\right).
\]
Then:

1. $E_0=0$, $d_0/N=1/2$, $\Delta_{\min}=1/B$, and both families have
   $E(x)\in[0,B]$.
2. $A_1(E_U)=A_1(E_S)=\frac{B^2+3}{8B}$.
3. At inverse temperature $\beta=B$,
   \[
   \frac{|Z_U(B)-Z_S(B)|}{N}\ge \frac{1}{100}.
   \]

Hence even exact knowledge of $A_1$ does not determine low-temperature partition
values. Any reverse reduction "$A_1$ approximation $\Rightarrow$ $Z(\beta)$
approximation" fails on this family without additional information.

**Proof.** Both Hamiltonians are diagonal and at most $4$-local by construction.

For $E_U$:
- $x_1=0$ gives energy $0$ on $2^{n-1}$ states;
- $x_1=1$, $x_2=x_3=0$ gives energy $1/B$ on $2^{n-3}$ states;
- the remaining $3\cdot 2^{n-3}$ excited states have energy $B$.

For $E_S$:
- $x_1=0$ gives energy $0$ on $2^{n-1}$ states;
- $x_1=1$, $x_2=x_3=x_4=0$ gives energy $1/B$ on $2^{n-4}$ states;
- the remaining $7\cdot 2^{n-4}$ excited states have energy $c_B$.

So both have $d_0/N=1/2$ and $\Delta_{\min}=1/B$. Also $c_B\in(1/B,B)$ for $B>1$,
hence both spectra lie in $[0,B]$.

Compute $A_1$:
\[
A_1(E_U)=\frac{1}{N}\!\left(2^{n-3}B+3\cdot 2^{n-3}\frac{1}{B}\right)
=\frac{1}{8}\!\left(B+\frac{3}{B}\right)=\frac{B^2+3}{8B}.
\]
\[
A_1(E_S)=\frac{1}{N}\!\left(2^{n-4}B+7\cdot 2^{n-4}\frac{1}{c_B}\right)
=\frac{1}{16}\!\left(B+7\frac{B^2+6}{7B}\right)
=\frac{1}{8}\!\left(B+\frac{3}{B}\right)=\frac{B^2+3}{8B}.
\]
Hence $A_1(E_U)=A_1(E_S)$ exactly.

Now evaluate partition functions at $\beta=B$:
\[
\frac{Z_U(B)}{N}
=\frac{1}{2}+\frac{1}{8}e^{-1}+\frac{3}{8}e^{-B^2},
\]
\[
\frac{Z_S(B)}{N}
=\frac{1}{2}+\frac{1}{16}e^{-1}
+\frac{7}{16}\exp\!\left(-B\,c_B\right)
=\frac{1}{2}+\frac{1}{16}e^{-1}
+\frac{7}{16}\exp\!\left(-\frac{7B^2}{B^2+6}\right).
\]
Therefore
\[
\frac{Z_U(B)-Z_S(B)}{N}
= \frac{e^{-1}}{16}+\frac{3e^{-B^2}}{8}
-\frac{7}{16}\exp\!\left(-\frac{7B^2}{B^2+6}\right).
\]
For $B\ge 3$,
\[
\frac{7B^2}{B^2+6}\ge \frac{63}{15}=4.2
\quad\Rightarrow\quad
\exp\!\left(-\frac{7B^2}{B^2+6}\right)\le e^{-4.2}<0.015.
\]
Hence
\[
\frac{Z_U(B)-Z_S(B)}{N}
\ge \frac{e^{-1}}{16}-\frac{7}{16}e^{-4.2}
>0.016>\frac{1}{100}.
\]
So $|Z_U(B)-Z_S(B)|/N\ge 1/100$. $\square$

**Remark (precise failure mode of Todo-B1(a)).** Proposition 12 is a one-way map
($Z$-window approximation implies additive $A_1$ approximation). Proposition 15 shows
the reverse direction is non-identifiable from a single $A_1$ value: two instances can
share all coarse drivers $(\rho_0,\Delta_{\min},R)$ and exact $A_1$, yet differ by an
order-one amount in low-temperature partition mass.


## Sanity Checks

All quantitative claims verified numerically (`lib/verify_a1.py`,
`lib/verify_ising_bridge.py`, and auxiliary demos in `lib/`).

**Grover $N = 4$, $d_0 = 1$.**
- $A_1 = (4 - 1)/4 = 3/4$. $\checkmark$
- $s^* = A_1/(1 + A_1) = (3/4)/(7/4) = 3/7$. $\checkmark$

**Grover $N = 4$, $d_0 = 2$.**
- $A_1 = (4 - 2)/4 = 1/2$. $\checkmark$
- $s^* = (1/2)/(3/2) = 1/3$. $\checkmark$

**Proposition 1 counterexample ($n = 4$, $N = 16$).**
- $d_0 = 1$, $d_1 = 1$ (at $E_1 = 1/4$), $d_2 = 14$ (at $E_2 = 1$).
- Total: $1 + 1 + 14 = 16 = N$. $\checkmark$
- $A_1 = (1/16)[4 + 14] = 18/16 = 9/8 = 1.125$. $\checkmark$
- $1/\Delta = 4$. Ratio: $A_1/(1/\Delta) = 0.28$. $\checkmark$ (conjecture off by 3.6x)

**Hamming $n = 4$.**
- Sum: $4 + 3 + 4/3 + 1/4 = 103/12 \approx 8.583$. $\checkmark$
- $A_1 = 103/(12 \cdot 16) = 103/192 \approx 0.5365$. $\checkmark$

**Proposition 13 (Ising multiplicative-$Z$ to additive-$A_1$).**
- Numerical bound check on a ferromagnetic Ising chain with bounded multiplicative
  oracle noise passes: observed errors stay below
  $(1-\rho_0)e^{-B\Delta_{\min}}(B+1/\Delta_{\min})+2\mu B + B^2/(2K)$.
  $\checkmark$ (`lib/verify_ising_bridge.py`)

**Proposition 14 (schedule sensitivity).**
- Direct numerical checks confirm
  $|\widehat{s}^*-s^*|\le 2|\varepsilon|/(1+A_1)^2$ in the stated regime and validate
  the explicit min-condition sufficient criterion. $\checkmark$
  (`lib/verify_ising_bridge.py`)

**Proposition 15 (reverse-bridge obstruction).**
- Explicit families with equal $(A_1,\rho_0,\Delta_{\min},R)$ but order-one separated
  low-temperature partition values satisfy
  $|Z_U(B)-Z_S(B)|/N > 1/100$ for $B\ge 3$. $\checkmark$
  (`lib/verify_a1.py`)

**Lean formalization (Props 13-15 bounds).**
- Proposition 13 deterministic cores are machine-checked in
  `lean/StructuredTractability08/Prop13.lean`:
  minimum-gap tail suppression lemma, three-term absolute-value decomposition,
  midpoint-oracle contribution bound, midpoint quadrature-aggregation algebra, and the explicit
  $\eta/3+\eta/3+\eta/3$ parameter-budget lemma.
- Proposition 14 crossing-shift identity, local absolute-error bound, target-bound
  lemma (with the explicit min-condition), and scale-substitution identity are
  machine-checked in `lean/StructuredTractability08/Prop14.lean`.
- Proposition 15 exact $A_1$ matching identity and the parameter inequality
  $1/B<c_B<B$ are machine-checked in `lean/StructuredTractability08/Prop15.lean`.
- Proposition 15's quantitative gap core
  $\frac{e^{-1}}{16}-\frac{7}{16}\exp\!\left(-\frac{7B^2}{B^2+6}\right)>1/100$ for
  $B\ge 3$ is also machine-checked in
  `lean/StructuredTractability08/Prop15.lean`.
- Project builds successfully with `cd lean && lake build`.


## Summary Table

| Result | Statement | Status |
|--------|-----------|--------|
| Prop 1 | Conjecture 1 ($A_1 = 1/\Delta + O(1)$ for unique solutions) is false | Disproved by counterexample |
| Prop 2 | Conjecture 2 (bounded degeneracy $\Rightarrow$ easy $A_1$) is vacuous | Hypothesis forces $d_0/N \to 1$ |
| Prop 3 | Sufficient condition: poly levels + known $d_k$ + known $E_k$ | Proved (forward direction) |
| Prop 4 | CSPs with #P-hard counting: $A_1$ is #P-hard | Proved (via paper's interpolation) |
| Prop 5 | Grover with known $d_0$: $O(1)$-computable $A_1$, hard search | Proved (promise model) |
| Prop 6 | Conjecture 3 fails both directions | Proved (2-SAT + Grover) |
| Remark | Planted instances: constructor can provide $A_1$ as advice | Observation |
| Prop 7 | Hamming distance: $A_1$ depends only on $n$ | Proved (but problem is easy) |
| Prop 8 | Bounded treewidth: exact $A_1$ via partition-function DP | Proved (variable elimination + code demo) |
| Prop 9 | Coarse $A_1$ approximation is easy when $E_0$ is known | Proved |
| Prop 10 | Approximate $A_1$ from $Z(t)$ without $d_0$ | Proved |
| Prop 11 | Laplace proxy: approximate $A_1$ from $Z(\beta)$ without $d_0$ | Proved |
| Prop 12 | Oracle reduction: approximate $Z$ on a grid $\Rightarrow$ additive $A_1$ | Proved |
| Prop 13 | Ferromagnetic Ising (multiplicative $Z$ approximation) $\Rightarrow$ additive $A_1$ with explicit $(R,\Delta_{\min},\rho_0)$ error drivers | Proved |
| Prop 14 | Schedule-level sufficient condition: $|A_1-\widehat{A}_1|\le \min\{(1+A_1)/2,\sqrt{d_0A_2/N}\}$; worst-case target $\Theta(2^{-n/2})$ | Proved |
| Prop 15 | Reverse-bridge obstruction: exact $A_1$ does not determine low-temperature $Z(\beta)$ even with matched $(\rho_0,\Delta_{\min},R)$ | Proved |


## Information-Gap Interpretation (Chapter 9 hook)

The paper's "information gap" phenomenon can be reframed using Propositions 10--15:

- **Coarse accuracy is a moderate-temperature object.** For additive
  $\eta=1/\mathrm{poly}(n)$ and $\Delta_{\min}\ge 1/\mathrm{poly}(n)$, Proposition 11
  only needs $B=\Theta((1/\Delta_{\min})\log(1/\eta))=\mathrm{polylog}(n)$, and
  Proposition 10 only needs $\varepsilon=\mathrm{poly}(n)^{-1}$. Proposition 13 then
  turns any multiplicative partition-function approximation in that window into a
  randomized polynomial-time additive approximation for $A_1$.

- **Schedule-relevant accuracy is low-temperature.** Proposition 14 makes the required
  scale explicit: a sufficient condition is
  $|A_1-\widehat{A}_1|\le \min\{(1+A_1)/2,\sqrt{d_0A_2/N}\}$, which becomes
  $\Theta(2^{-n/2})$ in the worst case. At that precision:
  - Proposition 11 requires $B=\Theta(n/\Delta_{\min})$;
  - Proposition 10 requires $\varepsilon\approx 2^{-n/2}/\mathrm{poly}(n)$;
  - Proposition 13 requires multiplicative partition-function accuracy
    $\mu=O(2^{-n/2}/B)$, i.e. effectively exponential effort for oracle runtimes
    polynomial in $1/\mu$.

In other words: **the information barrier corresponds to the need for low-temperature
partition-function information** (or equivalently, fine-grained density-of-states
information), even though the adiabatic evolution itself is "zero-temperature".
Proposition 15 shows this is also a one-way phenomenon: $A_1$ alone cannot reconstruct
that low-temperature partition information.


## What Remains Open

1. **Necessary conditions.** Proposition 3 gives sufficient conditions. What are
   necessary conditions for tractable $A_1$? The Grover case shows that known
   individual $d_k$ are not necessary (the sum collapses when $M = 2$). A
   characterization of when $A_1$ admits closed-form evaluation despite unknown $d_k$
   would complete the picture.

2. **Natural NP-hard problems with simple spectra.** Grover is the only known example
   of a hard search problem with easy $A_1$. Do natural NP-hard problems (combinatorial
   optimization, not oracle search) ever have simple enough spectra for $A_1$ to be
   tractable?

3. **Approximate $A_1$.** The paper shows even approximating $A_1$ to $1/\mathrm{poly}(n)$
   precision is NP-hard (Main Result 2), and exact computation is #P-hard (Main Result
   3). But perhaps constant-factor approximation suffices for near-optimal schedules.
   The gap between "exact $A_1$ needed" and "approximate $A_1$
   suffices" is unexplored.

4. **Quantum computation of $A_1$.** A quantum computer could estimate $A_1$ via phase
   estimation on $H_z$. The classical hardness results do not rule out efficient quantum
   computation of $A_1$, which would let a digital quantum computer set up its own
   optimal adiabatic schedule.
