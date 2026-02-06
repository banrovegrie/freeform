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


## Proposition 4: CSP Hardness

**Proposition.** For Boolean CSPs where counting satisfying assignments is #P-hard
(this includes $k$-SAT for $k \ge 2$, NAE-SAT, 1-in-3-SAT, and graph coloring with
$\ge 3$ colors), computing $A_1$ of the clause-violation Hamiltonian is #P-hard.

**Proof.** Encode the CSP as $H = \sum_{j=1}^m C_j$ where each $C_j$ is a clause
projector: $C_j(x) = 1$ if assignment $x$ violates clause $j$, else $0$. Then
$E(x) = \sum_j C_j(x)$ counts violated clauses, the energy levels are integers
$0, 1, \ldots, m$, and $d_k$ counts assignments violating exactly $k$ clauses.

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


## Sanity Checks

All quantitative claims verified numerically (`lib/verify_a1.py`).

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
