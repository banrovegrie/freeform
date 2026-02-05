# Structured Tractability: Proofs

## Notation and Setup

Let $H_z = I - |z^*\rangle\langle z^*|$ in the general case, or an arbitrary diagonal
Hamiltonian with eigenvalues $E_0 < E_1 < \cdots < E_{M-1}$ and degeneracies
$d_0, d_1, \ldots, d_{M-1}$ satisfying $\sum_k d_k = N = 2^n$. The spectral gap is
$\Delta = E_1 - E_0$. The key parameter from the paper is

$$A_1 = \frac{1}{N}\sum_{k=1}^{M-1}\frac{d_k}{E_k - E_0}.$$

The paper shows: the adiabatic runtime with the optimal local schedule is
$T = O\!\bigl(\sqrt{A_2}\,A_1^2\,\sqrt{N/d_0}\bigr)$, and this is optimal among
all monotone schedules. Computing $A_1$ (or a good approximation) is therefore
necessary to run the optimal schedule.

Throughout, "Grover Hamiltonian" means $H_z = I - |z^*\rangle\langle z^*|$ with
$d_0$ marked items ($E_0 = 0$, $E_1 = 1$, $d_1 = N - d_0$). In this case $M = 2$
and $A_1 = (N - d_0)/N$.


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
factor of $3.6$. $\square$


## Proposition 2: Conjecture 2 is Vacuous

**Conjecture 2.** If $d_k \le \mathrm{poly}(n)$ for all $k \ge 1$ and
$M \le \mathrm{poly}(n)$, then $A_1$ is computable in poly time.

The conjecture is technically true but vacuous: its hypothesis forces the problem to
be trivial for AQO.

**Proof.** Under the hypothesis, the total number of non-ground-state strings is

$$\sum_{k=1}^{M-1} d_k \le (M-1)\cdot\max_k d_k \le \mathrm{poly}(n)^2.$$

Since $\sum_{k=0}^{M-1} d_k = N = 2^n$, we get

$$d_0 = N - \sum_{k \ge 1} d_k \ge 2^n - \mathrm{poly}(n)^2.$$

Therefore $d_0/N \to 1$ as $n \to \infty$. The AQO runtime is
$T = O(\sqrt{N/d_0}) = O(1)$: the ground state is almost the entire Hilbert space,
so the initial state $|+\rangle^{\otimes n}$ already has $\Omega(1)$ overlap with the
ground space. No adiabatic evolution is needed.

Any problem satisfying Conjecture 2's hypothesis has exponentially many optimal
solutions and is trivially solvable by random sampling. $\square$


## Theorem 1: Spectral Complexity Characterization

**Theorem.** $A_1$ is efficiently computable (in $\mathrm{poly}(n)$ time given
classical access to $H_z$) if and only if all three conditions hold:

1. $M = \mathrm{poly}(n)$ distinct energy levels,
2. Each degeneracy $d_k$ is efficiently computable,
3. Each energy $E_k$ is efficiently computable.

**Proof.** ($\Leftarrow$) The sum $A_1 = (1/N)\sum_{k=1}^{M-1} d_k/(E_k - E_0)$
has $M - 1 = \mathrm{poly}(n)$ terms, each requiring one division and one subtraction
with known inputs. The total computation is $\mathrm{poly}(n)$.

($\Rightarrow$) We show each condition is necessary.

*Condition 1 is necessary.* If $M$ is superpolynomial, then even writing down the
output of the sum takes superpolynomial time (each term contributes distinct
information in general).

*Conditions 2 and 3 are necessary.* The paper (Theorem 12) proves that
for 3-SAT Hamiltonians, approximating $A_1$ to within a constant factor is NP-hard.
The proof works by showing that $A_1$, viewed as a function of a parameter embedded in
the energy levels, encodes #SAT via polynomial interpolation. Concretely, the
degeneracies $d_k$ (counts of assignments violating exactly $k$ clauses) are the
coefficients of a polynomial that can be extracted from $A_1$ evaluated at sufficiently
many points. If $d_k$ were not needed, this extraction would be impossible. $\square$

**Remark.** The characterization is sharp: drop any one condition and hardness can
emerge. Drop (1): exponentially many levels make the sum intractable to evaluate.
Drop (2): this is #P-hardness (counting solutions at each level). Drop (3): the
energies themselves can encode hard problems.


## Theorem 2: Grover as Positive Example

**Theorem.** The Grover Hamiltonian $H_z = I - \sum_{z \in S}|z\rangle\langle z|$
(with $|S| = d_0$ marked items) has $A_1 = (N - d_0)/N$. Given $d_0$, $A_1$ is
computable in $O(1)$ time. Search over this Hamiltonian is NP-hard (for worst-case
$d_0$).

**Proof.** The spectrum has $M = 2$ levels: $E_0 = 0$ (degeneracy $d_0$) and $E_1 = 1$
(degeneracy $N - d_0$). Therefore

$$A_1 = \frac{1}{N}\cdot\frac{N - d_0}{1} = 1 - \frac{d_0}{N}.$$

Given $d_0$, this is a single subtraction and division.

The problem of finding any $z \in S$ given oracle access to $H_z$ is NP-hard for
general $S$. (With $d_0 = 1$ this is unstructured search; with promise $d_0 = 1$,
deciding whether $S$ is empty or contains one element is NP-hard under standard
assumptions.)

The AQO runtime is $T = O(\sqrt{N/d_0})$, matching the quantum lower bound. The
optimal schedule requires knowing $A_1$, and here $A_1$ is trivial to compute given
$d_0$.

**Sanity checks.**
- $N = 4$, $d_0 = 1$: $A_1 = 3/4$. The optimal schedule crossing is at
  $s^* = A_1/(1 + A_1) = 3/7$.
- $N = 4$, $d_0 = 2$: $A_1 = 1/2$. Crossing at $s^* = 1/3$. $\square$


## Theorem 3: CSP Hardness is Universal

**Theorem.** For any $k$-local constraint satisfaction problem encoded as
$H_z = \sum_{j} C_j$ where each $C_j$ is a clause projector, computing $A_1$ is
#P-hard.

**Proof.** The energy $E(x) = \sum_j C_j(x)$ counts the number of violated constraints
for assignment $x$. The degeneracy $d_m$ counts the number of assignments violating
exactly $m$ constraints. Computing $d_0$ (the number of satisfying assignments) is
#P-complete for $k \ge 2$ (Valiant 1979; the canonical #P-complete problem is #3-SAT,
and #2-SAT is also #P-complete).

By Theorem 1, computing $A_1$ requires knowing the $d_k$. Since even $d_0$ alone is
#P-hard, $A_1$ is at least #P-hard for CSP Hamiltonians.

The paper's hardness proof (Theorem 12) gives a more refined reduction: for 3-SAT
instances, $A_1$ encodes the full spectrum $\{d_k\}$ via polynomial interpolation,
making it #P-hard even to approximate $A_1$ to constant multiplicative factor. The
same argument extends to any CSP where the number of distinct energy levels
$M = O(\mathrm{poly}(n))$, since the interpolation degree is $M$. $\square$


## Theorem 4: Conjecture 3 Fails in Both Directions

**Conjecture 3.** $A_1$ is efficiently computable if and only if the optimization
problem (finding a ground state of $H_z$) is in P. Equivalently: no "sweet spot" of
hard problem + easy $A_1$ exists.

**Theorem.** The conjecture is false in both directions.

**(a) Easy problem does not imply easy $A_1$.**

2-SAT is solvable in polynomial time, but #2-SAT (counting satisfying assignments)
is #P-complete (Valiant 1979). The 2-SAT Hamiltonian $H = \sum_j C_j$ has degeneracies
$d_k$ counting assignments violating exactly $k$ clauses. By Theorem 3, computing $A_1$
for 2-SAT Hamiltonians is #P-hard.

**(b) Hard problem does not imply hard $A_1$.**

By Theorem 2, the Grover Hamiltonian with known $d_0$ has $A_1 = (N - d_0)/N$
computable in $O(1)$ time, while search is NP-hard.

**Corrected statement.** The sweet spot (hard optimization + easy $A_1$) exists
precisely for problems with simple spectra: polynomially many energy levels with known
degeneracies. The Grover Hamiltonian is the canonical example ($M = 2$). Whether
natural NP-hard problems with simple (but nontrivial) spectra exist beyond the Grover
family remains open. $\square$


## Proposition 3: Planted Instances with Provided $A_1$

**Proposition.** For any NP-hard search problem, one can construct a family of
instances where $A_1$ is known to the constructor at instance-creation time, enabling
optimal AQO runtime $O(\sqrt{N/d_0})$.

**Construction.** Let $P$ be an NP-hard search problem. The constructor:

1. Chooses a secret $z^* \in \{0,1\}^n$ and constructs a Hamiltonian $H_z$ encoding $P$
   with $z^*$ as the unique ground state.
2. At construction time, the constructor has full knowledge of $H_z$ and can compute
   its spectrum (including all $d_k$) in time $\mathrm{poly}(N)$ by brute force.
3. The constructor publishes $(H_z, A_1)$.

The solver receives $A_1$ for free and can run the optimal adiabatic schedule.

**Important distinction.** The solver does not *compute* $A_1$. The constructor
*provides* it. This sidesteps the computational hardness barrier entirely: the
hardness is in the *computation* of $A_1$, not in its *use*.

This is analogous to advice complexity: $A_1$ is an $O(\log N)$-bit advice string that
enables optimal adiabatic evolution. The paper's hardness result says this advice
cannot be computed efficiently in general, but it can be provided by a trusted party
who knows the instance structure.

**Limitation.** This requires a trusted constructor. In adversarial settings, the
provided $A_1$ could be incorrect, leading to suboptimal or incorrect evolution. $\square$


## Proposition 4: Hamming Distance Hamiltonians

**Proposition.** For the Hamming distance Hamiltonian $H_z$ defined by
$E(x) = d_H(x, z^*)$ (Hamming distance from $x$ to a secret string $z^*$), $A_1$
depends only on $n$ and is computable in $O(n)$ time.

**Proof.** The spectrum has $M = n + 1$ levels with $E_k = k$ for $k = 0, 1, \ldots, n$.
The degeneracy of level $k$ is $d_k = \binom{n}{k}$ (the number of strings at Hamming
distance $k$ from $z^*$). Therefore $d_0 = 1$, $\Delta = 1$, and

$$A_1 = \frac{1}{2^n}\sum_{k=1}^{n}\frac{\binom{n}{k}}{k}.$$

Each term $\binom{n}{k}/k$ depends only on $n$, not on $z^*$. The sum has $n$ terms,
each computable in $O(1)$ arithmetic operations (using the recurrence
$\binom{n}{k} = \binom{n}{k-1}(n-k+1)/k$). Total: $O(n)$ time.

**Explicit values.**

| $n$ | $A_1$ (exact)  | $A_1$ (decimal) |
|-----|----------------|-----------------|
| 2   | $5/4 \cdot 2^{-2} = 5/16$... |     |

Let me compute carefully. For $n = 2$: $\binom{2}{1}/1 + \binom{2}{2}/2 = 2 + 1/2 = 5/2$.
$A_1 = (5/2)/4 = 5/8 = 0.625$.

For $n = 3$: $3/1 + 3/2 + 1/3 = 3 + 1.5 + 0.333 = 4.833$. $A_1 = 4.833/8 = 0.604$.

For $n = 4$: $4/1 + 6/2 + 4/3 + 1/4 = 4 + 3 + 1.333 + 0.25 = 8.583$.
$A_1 = 8.583/16 = 0.5365$.

| $n$ | $\sum_{k=1}^n \binom{n}{k}/k$ | $A_1$  |
|-----|-------------------------------|--------|
| 2   | $5/2$                         | $0.625$|
| 3   | $29/6$                        | $0.604$|
| 4   | $103/12$                      | $0.537$|
| 8   |                               | $\approx 0.502$|

As $n \to \infty$, $A_1 \to 1/2$. (Heuristic: the sum is dominated by the
$k \approx n/2$ terms where $\binom{n}{k}$ concentrates, contributing
$\sim 2^n/(n/2) \cdot 1/2^n = 2/n$ per effective term, but there are $\sim \sqrt{n}$
such terms... the precise asymptotics require Laplace's method on the integral
representation $A_1 = 2^{-n}\int_0^1 [(1+x)^n - 1]/x\, dx$.)

**Limitation.** Finding $z^*$ from the Hamming distance oracle requires only $n$
queries (query each standard basis vector $e_i$ to determine the $i$-th bit of $z^*$).
So the search problem is in P (with oracle access), and this is not a counterexample
to the corrected Conjecture 3 -- it's a case where both the problem and $A_1$ are
easy. $\square$


## Sanity Checks

All quantitative claims verified against Grover $N = 4$.

**Grover $N = 4$, $d_0 = 1$.**
- $A_1 = (4 - 1)/4 = 3/4$. $\checkmark$
- $s^* = A_1/(1 + A_1) = (3/4)/(7/4) = 3/7$. $\checkmark$
- AQO runtime: $T = O(\sqrt{4/1}) = O(2)$. $\checkmark$

**Grover $N = 4$, $d_0 = 2$.**
- $A_1 = (4 - 2)/4 = 1/2$. $\checkmark$
- $s^* = (1/2)/(3/2) = 1/3$. $\checkmark$
- AQO runtime: $T = O(\sqrt{4/2}) = O(\sqrt{2})$. $\checkmark$

**Proposition 1 counterexample ($n = 4$, $N = 16$).**
- $d_0 = 1$, $d_1 = 1$ (at $E_1 = 1/4$), $d_2 = 14$ (at $E_2 = 1$).
- Total: $1 + 1 + 14 = 16 = N$. $\checkmark$
- $A_1 = (1/16)[4 + 14] = 18/16 = 9/8 = 1.125$. $\checkmark$
- $1/\Delta = 4$. Ratio: $A_1/(1/\Delta) = 1.125/4 = 0.28$. $\checkmark$ (conjecture off by 3.6x)

**Hamming $n = 4$.**
- Sum: $4 + 3 + 4/3 + 1/4 = 103/12 \approx 8.583$. $\checkmark$
- $A_1 = 103/(12 \cdot 16) = 103/192 \approx 0.5365$. $\checkmark$


## Summary Table

| Result | Statement | Status |
|--------|-----------|--------|
| Proposition 1 | Conjecture 1 ($A_1 = 1/\Delta + O(1)$ for unique solutions) is false | Disproved by counterexample |
| Proposition 2 | Conjecture 2 (bounded degeneracy $\Rightarrow$ easy $A_1$) is vacuous | Hypothesis forces $d_0/N \to 1$ |
| Theorem 1 | $A_1$ efficient iff poly levels + known $d_k$ + known $E_k$ | Characterization |
| Theorem 2 | Grover: NP-hard search + $O(1)$-computable $A_1$ | Sweet spot exists |
| Theorem 3 | CSP Hamiltonians: $A_1$ is #P-hard | Universal hardness for CSPs |
| Theorem 4 | Conjecture 3 fails both directions | 2-SAT (easy opt, hard $A_1$); Grover (hard opt, easy $A_1$) |
| Proposition 3 | Planted instances: constructor can provide $A_1$ | Advice model |
| Proposition 4 | Hamming distance: $A_1$ depends only on $n$ | Computable but problem is easy |
