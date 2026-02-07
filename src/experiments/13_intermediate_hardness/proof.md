# Proofs: Intermediate Hardness of $A_1$ at Precision $2^{-n/2}$

## Setup

We work with the notation of the paper throughout. An $n$-qubit diagonal
Hamiltonian $H_z$ has eigenvalues $0 \le E_0 < E_1 < \cdots < E_{M-1}$
with degeneracies $d_0, d_1, \ldots, d_{M-1}$ summing to $N = 2^n$. The
quantity of interest is

$$
A_1(H) \;=\; \frac{1}{N} \sum_{k=1}^{M-1} \frac{d_k}{E_k - E_0}.
$$

Write $\Delta_k = E_k - E_0$ for the gap to excited level $k$, so
$\Delta_1 = E_1 - E_0$ is the spectral gap. The number of distinct energy
levels satisfies $M \in \mathrm{poly}(n)$ for the Hamiltonians arising in
the paper's reductions. For the adiabatic algorithm (Theorem 2) we assume
$0 \le H_z \le I$, so $E_{M-1} \le 1$. For the #P-hardness analysis
(Theorem 1) we follow the paper's Ising reduction where eigenvalues are
integers, potentially with $E_{M-1} = \mathrm{poly}(n)$.

**Known hardness results (paper Section 3).**

1. *NP-hardness at inverse-polynomial precision.* Theorem 2 of the paper
   shows that estimating $A_1$ to additive error $\epsilon < 1/\mathrm{poly}(n)$
   is NP-hard, via a reduction from 3-SAT using a 3-local Hamiltonian on
   $O(n_{\mathrm{var}} + m)$ qubits (where $n_{\mathrm{var}}$ is the number
   of Boolean variables and $m$ the number of clauses; the paper writes $n$
   for the total qubit count). The reduction calls the estimation oracle
   twice: once on $H$ and once on
   $H' = H \otimes [(I + \sigma_z)/2]$, and distinguishes $E_0 = 0$ from
   $E_0 \ge 1/(6m)$ by comparing $A_1(H) - 2A_1(H')$.

2. *#P-hardness at exponentially small precision.* Theorem 3 uses polynomial
   interpolation (via Paturi's lemma) to extract exact degeneracies from
   $O(\mathrm{poly}(n))$ approximate evaluations of $A_1$. This requires
   precision $\epsilon = O(2^{-\mathrm{poly}(n)})$ so that rounding
   recovers exact integer degeneracies.

The adiabatic algorithm's optimal schedule requires $A_1$ to precision
$\epsilon = O(2^{-n/2})$. This precision sits strictly between the two
known hardness regimes. We prove seven results about this intermediate
regime: a barrier for the paper's proof technique (Theorem 1), a quantum
algorithm (Theorem 2), a classical lower bound (Theorem 3), a tight
quantum lower bound (Theorem 4), a computational complexity result
(Theorem 5), a generic extrapolation barrier (Theorem 6), and a
structure irrelevance result (Theorem 7).


## Theorem 1: Polynomial Interpolation Barrier at $2^{-n/2}$

**Theorem 1.** *The polynomial interpolation technique of paper Section 3.2
requires precision $\epsilon = 2^{-n - O(M \log n)}$ to extract exact
degeneracies, where $M = \mathrm{poly}(n)$ is the number of distinct energy
levels. At precision $\epsilon = 2^{-n/2}$, the amplified error exceeds
$1/2$ and rounding fails. Consequently, the #P-hardness argument does not
extend to precision $2^{-n/2}$.*

**Proof.** We trace the paper's construction and track error propagation
explicitly.

**Step 1: Auxiliary Hamiltonian.** For parameter $x > 0$, define the
$(n+1)$-qubit Hamiltonian

$$
H'(x) \;=\; H \otimes I \;-\; \frac{x}{2}\, I \otimes \sigma_+^{(n+1)},
\qquad
\sigma_+^{(n+1)} = \frac{I + \sigma_z^{(n+1)}}{2}.
$$

The eigenvalues of $\sigma_+$ are $1$ (for $|0\rangle$) and $0$ (for
$|1\rangle$). So $H'(x)$ has eigenvalues $E_k - x/2$ (with multiplicity
$d_k$, on the $|0\rangle$ branch) and $E_k$ (with multiplicity $d_k$, on
the $|1\rangle$ branch). The ground energy of $H'(x)$ is $E_0 - x/2$.

The gaps relative to the new ground energy $E_0 - x/2$ are $\Delta_k$ for
the $|0\rangle$ branch and $\Delta_k + x/2$ for the $|1\rangle$ branch.
Computing $A_1(H'(x))$ from these and simplifying (following the paper):

$$
f(x) \;=\; 2\,A_1(H'(x)) - A_1(H)
\;=\; \frac{1}{N} \sum_{k=0}^{M-1} \frac{d_k}{\Delta_k + x/2}.
$$

Here $\Delta_0 = 0$, so the $k = 0$ term contributes $d_0/(x/2) = 2d_0/x$.
The paper evaluates $f$ at positive odd integers, avoiding any divergence.

**Step 2: Reconstruction polynomial.** Define

$$
P(x) \;=\; \prod_{k=0}^{M-1}\!\Bigl(\Delta_k + \frac{x}{2}\Bigr)\; f(x)
\;=\; \frac{1}{N} \sum_{k=0}^{M-1} d_k \prod_{\ell \ne k}
\Bigl(\Delta_\ell + \frac{x}{2}\Bigr).
$$

This is a polynomial of degree at most $M - 1$ in $x$. Following the paper,
evaluate $f$ at $M$ distinct points $x_i \in \{1, 3, 5, \ldots, 2M - 1\}$
(odd integers, so that $\Delta_k + x_i/2 \ge 1/2 > 0$ for all $k$). From
$P(x_i)$ we reconstruct $P$ via Lagrange interpolation (the $M$ values
determine a polynomial of degree $\le M - 1$ uniquely). The degeneracies
are then recovered by evaluating at the poles:

$$
\tilde{d}_k \;=\; \frac{N \cdot P(-2\Delta_k)}
{\prod_{\ell \ne k}(\Delta_\ell - \Delta_k)}.
$$

**Step 3: Error propagation at sample points.** Suppose we have an oracle
$\tilde{A}_1$ with $|\tilde{A}_1(H) - A_1(H)| \le \epsilon$. Then

$$
\tilde{f}(x_i) \;=\; 2\,\tilde{A}_1(H'(x_i)) - \tilde{A}_1(H)
$$

satisfies $|\tilde{f}(x_i) - f(x_i)| \le 3\epsilon$ (triangle inequality
on the three oracle calls). The approximate polynomial values are

$$
\tilde{P}(x_i) \;=\; \prod_{k=0}^{M-1}\!\Bigl(\Delta_k + \frac{x_i}{2}\Bigr)\;\tilde{f}(x_i),
$$

so the pointwise error is

$$
|\tilde{P}(x_i) - P(x_i)|
\;\le\; 3\epsilon \prod_{k=0}^{M-1}\!\Bigl(\Delta_k + \frac{x_i}{2}\Bigr).
$$

For the Ising Hamiltonians in the paper's reduction, the gaps $\Delta_k$
are non-negative integers at most $\Delta_{\max} = \mathrm{poly}(n)$, and
$x_i \le 2M - 1$. Each factor is at most $\Delta_{\max} + M$, which is
$\mathrm{poly}(n)$. Write $B = \Delta_{\max} + M$. With $M$ factors:

$$
|\tilde{P}(x_i) - P(x_i)|
\;\le\; 3\epsilon\, B^M.
$$

**Step 4: End-to-end error from samples to degeneracies.** We bound the
error in $d_k$ directly from the sample-point errors, bypassing Paturi's
lemma (which the paper uses for the converse direction: establishing
hardness).

The degeneracy extraction formula is
$d_k = N \cdot P(-2\Delta_k) / \prod_{\ell \ne k}(\Delta_\ell - \Delta_k)$.
The polynomial $P$ is reconstructed from the values $P(x_0), \ldots,
P(x_{M-1})$ by Lagrange interpolation:

$$
P(x) \;=\; \sum_{j=0}^{M-1} P(x_j) \prod_{i \ne j}
\frac{x - x_i}{x_j - x_i}.
$$

Define $\tilde{d}_k = N \cdot \tilde{P}(-2\Delta_k) / \prod_{\ell \ne k}
(\Delta_\ell - \Delta_k)$ where $\tilde{P}$ is reconstructed from noisy
values $\tilde{P}(x_j)$. The error is

$$
|d_k - \tilde{d}_k|
\;=\; \frac{N}{|\prod_{\ell \ne k}(\Delta_\ell - \Delta_k)|}
\left|\sum_{j=0}^{M-1}(P(x_j) - \tilde{P}(x_j))
\prod_{i \ne j}\frac{-2\Delta_k - x_i}{x_j - x_i}\right|.
$$

By the triangle inequality and Step 3:

$$
|d_k - \tilde{d}_k|
\;\le\; \frac{3\epsilon\,N}{|\prod_{\ell \ne k}(\Delta_\ell - \Delta_k)|}
\sum_{j=0}^{M-1} \prod_{k'=0}^{M-1}(\Delta_{k'} + x_j/2)
\prod_{i \ne j}\frac{|2\Delta_k + x_i|}{|x_j - x_i|}.
$$

We bound each factor. Write $B = \Delta_{\max} + M$ as before (with
$\Delta_{\max} = \mathrm{poly}(n)$). With nodes $x_j = 2j + 1$:

- Pointwise product: $\prod_{k'=0}^{M-1}(\Delta_{k'} + x_j/2) \le B^M$.
- Numerator of Lagrange basis at $-2\Delta_k$: $|{-2\Delta_k - x_i}| =
  2\Delta_k + 2i + 1 \le 2\Delta_{\max} + 2M - 1 \le 2B + 1$.
- Denominator of Lagrange basis: $|x_j - x_i| = 2|j - i|$, so
  $\prod_{i \ne j}|x_j - x_i| = 2^{M-1} j!(M - 1 - j)!$.

Combining the Lagrange basis bound and summing over $j$:

$$
\sum_{j=0}^{M-1} \frac{(2B+1)^{M-1}}{2^{M-1} j!(M-1-j)!}
\;=\; \frac{(2B+1)^{M-1}}{2^{M-1}} \cdot \frac{2^{M-1}}{(M-1)!}
\;=\; \frac{(2B+1)^{M-1}}{(M-1)!}
$$

where we used the binomial identity $\sum_{j=0}^{M-1} \binom{M-1}{j} =
2^{M-1}$.

For the denominator $\prod_{\ell \ne k}|\Delta_\ell - \Delta_k|$: for the
Ising Hamiltonians in the paper's reduction, the eigenvalues $E_k$ are
distinct integers (paper, Section 3.2, proof of Theorem 3). The gaps
$\Delta_k = E_k - E_0$ are distinct non-negative integers. For any set
of $M$ distinct non-negative integers $a_0 < a_1 < \cdots < a_{M-1}$,
we have $|a_\ell - a_k| \ge |\ell - k|$ (since at least $|\ell - k|$
integers lie strictly between them). Hence $\prod_{\ell \ne k}|a_\ell -
a_k| \ge \prod_{\ell \ne k}|\ell - k| = k!(M-1-k)!$, with equality for
consecutive integers $\{0, 1, \ldots, M-1\}$. This product is minimized
over $k$ at $k = \lfloor(M-1)/2\rfloor$, giving
$(\lfloor(M-1)/2\rfloor!)(\lceil(M-1)/2\rceil!) \ge ((M-1)/2)!^2$ (for
$M$ odd) or $((M/2-1)!)(M/2)!$ (for $M$ even). In either case, by
Stirling: $\min_k k!(M-1-k)! \ge ((M-1)/(2e))^{M-1}$.

The full error bound is:

$$
|d_k - \tilde{d}_k|
\;\le\; \frac{3\epsilon \cdot N \cdot B^M \cdot (2B+1)^{M-1}}
{(M-1)! \cdot ((M-1)/(2e))^{M-1}}.
$$

The amplification factor grows exponentially in $M$. Since
$B = \mathrm{poly}(n)$, the numerator is $B^M \cdot (2B+1)^{M-1}
\le (3B)^{2M}$. For the
denominator: $(M-1)! \ge ((M-1)/e)^{M-1}$ (Stirling) and
$((M-1)/(2e))^{M-1}$ from the product bound, giving a denominator of at
least $((M-1)/e)^{M-1} \cdot ((M-1)/(2e))^{M-1} = ((M-1)^2/(2e^2))^{M-1}
= \Omega(M^{2M-2})$. For the numerator: $(3B)^{2M}$ with
$B = \mathrm{poly}(n)$, so the full ratio is $O((3B)^{2M}/M^{2M-2})
= O(B^{2M} \cdot \mathrm{poly}(M))$. Since $B = \mathrm{poly}(n)$ and
$M = \mathrm{poly}(n)$, this is $2^{O(M \log n)}$. Numerical evaluation
(for normalized Hamiltonians with $B = M + 1$) gives an effective base
$C \approx 20$-$24$ for $M = 4, \ldots, 15$. The precise constant does
not matter; what matters is exponential growth in $M$.

**Step 5: Rounding condition.** Write the amplification factor as $F(M,n)$,
so $|d_k - \tilde{d}_k| \le 3\epsilon \cdot N \cdot F(M,n)$, where
$F(M,n) = 2^{O(M \log n)}$. To extract exact degeneracies by rounding,
we need $3\epsilon \cdot N \cdot F(M,n) < 1/2$, i.e.,

$$
\epsilon \;<\; \frac{1}{6N \cdot F(M,n)} \;=\; 2^{-n - O(M \log n)}.
$$

**Step 6: Evaluation at $\epsilon = 2^{-n/2}$.** Set $\epsilon = 2^{-n/2}$
and $M = \mathrm{poly}(n)$, say $M = n^c$ for constant $c \ge 1$. Then

$$
|d_k - \tilde{d}_k|
\;\le\; 3 \cdot 2^{-n/2} \cdot 2^n \cdot 2^{O(M \log n)}
\;=\; 3 \cdot 2^{n/2 + O(n^c \log n)}.
$$

For any $c \ge 1$, the exponent $n/2 + O(n^c \log n)$ grows
super-polynomially, so the error diverges. Even for $c = 1$
(the most favorable case $M = n$):

$$
|d_k - \tilde{d}_k| \;\ge\; 2^{n/2 + \Omega(n \log n)} \;\gg\; 1.
$$

Rounding fails. The polynomial interpolation technique cannot establish
#P-hardness at precision $2^{-n/2}$. $\square$

**Remark.** The barrier is robust against constant-factor improvements in
the bounds. The error amplification from sample noise to degeneracy error
grows as $2^{O(M \log n)}$. The rounding condition demands
$\epsilon < 2^{-n - O(M \log n)}$, while $2^{-n/2}$ provides only $n/2$
bits of precision. The deficit of $O(M \log n) + n/2$ bits cannot be
overcome by $O(M)$ oracle calls.


## Theorem 2: Quantum Algorithm for $A_1$

**Theorem 2.** *There exists a quantum algorithm that estimates $A_1(H_z)$
to additive precision $\epsilon$ using*

$$
O\!\left(\sqrt{N} + \frac{1}{\epsilon \cdot \Delta_1}\right)
$$

*quantum queries to the diagonal oracle
$O_H\!: |x\rangle|0\rangle \mapsto |x\rangle|E_x\rangle$, where
$\Delta_1 = E_1 - E_0$ is the spectral gap.*

*For $\epsilon = 2^{-n/2}$ and $\Delta_1 = 1/\mathrm{poly}(n)$, the
complexity is $O(2^{n/2} \cdot \mathrm{poly}(n))$.*

**Proof.** The algorithm has two stages.

**Stage 1: Find the ground energy $E_0$.**

$H_z$ is diagonal in the computational basis, so computing $E_x$ for a
given $|x\rangle$ requires one query to $O_H$. Finding the minimum of
$E_x$ over all $x \in \{0,1\}^n$ is an instance of quantum minimum finding
(Durr and Hoyer 1996), which succeeds with high probability in
$O(\sqrt{N})$ queries. This yields $E_0$ exactly (the eigenvalues are
represented with finite precision in the problem description).

**Stage 2: Quantum amplitude estimation of $A_1$.**

Define the function $g\!: \{0,1\}^n \to \mathbb{R}$ by

$$
g(x) \;=\;
\begin{cases}
\displaystyle\frac{1}{E_x - E_0} & \text{if } E_x \ne E_0, \\[6pt]
0 & \text{if } E_x = E_0.
\end{cases}
$$

Then $A_1 = (1/N)\sum_x g(x)$, the mean of $g$ over the uniform
distribution on $\{0,1\}^n$. (The $g(x) = 0$ terms correspond to ground
states, which do not contribute to the $A_1$ sum.)

The values of $g$ on non-ground states lie in $[1/\Delta_{M-1}, 1/\Delta_1]$.
Since $0 \le H_z \le I$ (the normalization assumed for Theorem 2), we have
$\Delta_{M-1} \le 1$, so $1/\Delta_{M-1} \ge 1$ and the range is contained
in $[1, 1/\Delta_1]$. Define the rescaled function

$$
h(x) \;=\; \Delta_1 \cdot g(x) \;\in\; [0, 1].
$$

Then $A_1 = \mu_h / \Delta_1$ where $\mu_h = \mathbb{E}[h(x)]$.

**Quantum oracle for $h$.** We construct a unitary $U_h$ acting on
$|x\rangle|0\rangle$ that produces

$$
U_h\!: |x\rangle|0\rangle \;\mapsto\; |x\rangle\!\bigl(\sqrt{1 - h(x)}\,|0\rangle
+ \sqrt{h(x)}\,|1\rangle\bigr).
$$

Implementation: (i) query $O_H$ to write $E_x$ into an ancilla register,
(ii) compute $E_x - E_0$ (classical arithmetic on the ancilla), (iii) if
$E_x \ne E_0$, compute $\Delta_1/(E_x - E_0) = h(x)$; else set $h = 0$,
(iv) perform a controlled rotation $R_y(2\arcsin(\sqrt{h(x)}))$ on a flag
qubit, (v) uncompute the ancilla. Each application uses $O(1)$ queries to
$O_H$ and $O(\mathrm{poly}(n))$ auxiliary gates for the arithmetic.

**Applying amplitude estimation.** The probability of measuring the flag
qubit in state $|1\rangle$, after preparing the uniform superposition
$|+\rangle^{\otimes n}$ and applying $U_h$, is exactly

$$
p \;=\; \frac{1}{N}\sum_x h(x) \;=\; \mu_h.
$$

Amplitude estimation (Brassard, Hoyer, Mosca, and Tapp 2002) estimates $p$
to additive error $\delta$ using $O(1/\delta)$ applications of $U_h$ and
its inverse, with success probability at least $8/\pi^2 > 0.81$.

We need $|A_1 - \tilde{A}_1| \le \epsilon$, i.e.,
$|\mu_h - \tilde{\mu}_h| \le \epsilon \cdot \Delta_1$. Set
$\delta = \epsilon \cdot \Delta_1$. The number of applications of $U_h$
is $O(1/\delta) = O(1/(\epsilon \cdot \Delta_1))$.

**Total query complexity.** Stage 1 contributes $O(\sqrt{N})$ queries.
Stage 2 contributes $O(1/(\epsilon \cdot \Delta_1))$ queries (each
application of $U_h$ uses $O(1)$ queries). In total:

$$
O\!\left(\sqrt{N} + \frac{1}{\epsilon \cdot \Delta_1}\right).
$$

For $\epsilon = 2^{-n/2}$ and $\Delta_1 = 1/\mathrm{poly}(n)$:

$$
O\!\left(2^{n/2} + 2^{n/2} \cdot \mathrm{poly}(n)\right)
\;=\; O(2^{n/2} \cdot \mathrm{poly}(n)).
$$

$\square$

**Sanity check (Grover, $N = 4$, $M = 2$).** Two energy levels: $E_0 = 0$
with $d_0 = 1$, $E_1 = 1$ with $d_1 = 3$. Then $A_1 = (1/4)(3/1) = 3/4$,
$\Delta_1 = 1$.

- Stage 1: $O(\sqrt{4}) = O(2)$ queries.
- Stage 2: For $\epsilon = 1/2$, need $O(1/(1/2 \cdot 1)) = O(2)$
  applications.
- Total: $O(4)$ queries. The formula gives $\sqrt{4} + 2 = 4$. Consistent
  with $2^{n/2} = 2$.

**Sanity check ($N = 8$, $M = 3$).** Three levels: $E_0 = 0$ ($d_0 = 1$),
$E_1 = 1/4$ ($d_1 = 3$), $E_2 = 1$ ($d_2 = 4$). Then
$A_1 = (1/8)(3/(1/4) + 4/1) = (1/8)(12 + 4) = 2$, $\Delta_1 = 1/4$.

- Stage 1: $O(\sqrt{8}) = O(2\sqrt{2}) \approx 3$ queries.
- Stage 2: For $\epsilon = 2^{-3/2} \approx 0.354$, need
  $O(1/(2^{-3/2} \cdot 1/4)) = O(2^{7/2}) = O(8\sqrt{2}) \approx 11$
  applications.
- Total: formula gives $\sqrt{8} + 2^{7/2} = 2\sqrt{2} + 8\sqrt{2} =
  10\sqrt{2} \approx 14.1$ queries.
- Classical lower bound: $\Omega(1/\epsilon^2) = \Omega(2^3) = \Omega(8)$.

Note: for this small instance the quantum cost ($\approx 14$) exceeds the
classical lower bound ($8$) due to the $1/\Delta_1$ factor from the small
spectral gap $\Delta_1 = 1/4$. The quadratic separation is asymptotic:
it manifests for large $n$ where $2^{n/2} \gg \mathrm{poly}(n)$.


## Theorem 3: Classical Query Lower Bound

**Theorem 3.** *Any classical (randomized) algorithm estimating $A_1(H_z)$
to additive precision $\epsilon$ in the query model (where each query
reveals $E_x$ for a chosen $x$) requires $\Omega(1/\epsilon^2)$ queries
in the worst case.*

*At $\epsilon = 2^{-n/2}$, the lower bound is $\Omega(2^n)$.*

**Proof.**

**Step 1: Adversarial instance.** Consider the family parametrized by a
hidden subset $S \subseteq \{0,1\}^n$ with $|S| = N/2$:

$$
E_x \;=\;
\begin{cases}
0 & \text{if } x \in S, \\
1 & \text{if } x \notin S.
\end{cases}
$$

Then $d_0 = N/2$, $d_1 = N/2$, $\Delta_1 = 1$, and
$A_1 = (1/N)(N/2)/1 = 1/2$.

Now consider a modified instance with $|S'| = N/2 + t$ for integer
$t > 0$, and $E_x = 0$ for $x \in S'$, $E_x = 1$ otherwise. Then
$d_0' = N/2 + t$, $d_1' = N/2 - t$, and $A_1' = (N/2 - t)/N = 1/2 - t/N$.

The difference $|A_1 - A_1'| = t/N$. Setting $t = \lceil \epsilon N \rceil$
makes the two instances differ by approximately $\epsilon$ in $A_1$. An
algorithm estimating $A_1$ to precision $\epsilon/2$ must distinguish
these two cases.

**Step 2: Reduction to hypothesis testing.** The algorithm queries strings
$x_1, x_2, \ldots$ and learns whether each $x_i \in S$ (energy 0) or
$x_i \notin S$ (energy 1). Under the prior where $S$ is a uniformly random
subset of size $N/2$ (or $N/2 + t$), the sampling is without replacement
from a finite population (hypergeometric model). After querying $q$
distinct strings, the number of ground states observed follows a
hypergeometric distribution.

**Step 3: Information-theoretic lower bound.** The per-query KL divergence
between the two hypotheses ($|S| = N/2$ vs $|S| = N/2 + t$) is
$O(t^2/N^2)$. More precisely, for the $j$-th query (conditioned on the
first $j-1$ outcomes), the marginal distribution is Bernoulli with bias
$(N/2 - s_j)/(N - j + 1)$ under hypothesis 0 (where $s_j$ is the number
of ground states seen so far), and similarly for hypothesis 1. For $q \ll N$,
the per-query divergence is $O(t^2/N^2)$, matching the Bernoulli
approximation up to $O(q/N)$ relative corrections. By the chain rule for
KL divergence, the total divergence over $q$ adaptive queries is

$$
D_{\mathrm{KL}}^{(q)} \;\le\; q \cdot O\!\left(\frac{t^2}{N^2}\right).
$$

By Le Cam's two-point method, reliable hypothesis testing requires
$D_{\mathrm{KL}}^{(q)} \ge \Omega(1)$, giving

$$
q \;\ge\; \Omega\!\left(\frac{N^2}{t^2}\right).
$$

The chain rule bound holds for adaptive queries: the total KL divergence
of the joint distribution of $q$ query outcomes factors into a sum of
conditional per-query divergences. For the $j$-th query ($j \le q$),
the conditional per-query divergence is at most $O(t^2/(N-j)^2)$
(hypergeometric with $N-j$ remaining elements). When $q \le N/2$, each
term is at most $O(t^2/N^2) \cdot (1 + O(q/N)) = O(t^2/N^2)$. In
particular, the first $N/2$ queries contribute total KL at most
$(N/2) \cdot O(t^2/N^2) = O(t^2/(2N))$. For $t = O(\sqrt{N})$ (the
case $\epsilon = 2^{-n/2}$), this is $O(1/2)$, insufficient for
reliable testing. Hence $q > N/2 = \Omega(N)$.

With $t = \lceil \epsilon N \rceil$:

$$
q \;\ge\; \Omega\!\left(\frac{N^2}{\epsilon^2 N^2}\right) \;=\; \Omega\!\left(\frac{1}{\epsilon^2}\right).
$$

**Step 4: Concrete bound at $\epsilon = 2^{-n/2}$.** Substituting:

$$
\Omega\!\left(\frac{1}{(2^{-n/2})^2}\right) \;=\; \Omega(2^n).
$$

Since $N = 2^n$ and each query processes one string, this matches the
brute-force cost. No classical algorithm can beat exhaustive sampling
(up to constant factors) for worst-case instances at this precision.

$\square$

**Remark.** The adversarial instance has $\Delta_1 = 1$ (constant gap),
which is the easiest case for the quantum algorithm (Stage 2 costs only
$O(1/\epsilon)$, with no $1/\Delta_1$ penalty). The classical lower bound
already saturates at $\Omega(2^n)$ even here. For instances with
$\Delta_1 = 1/\mathrm{poly}(n)$, the quantum algorithm's cost grows by
$\mathrm{poly}(n)$ while classical sampling remains $\Omega(1/\epsilon^2)$
regardless of $\Delta_1$ (the adversarial construction always uses unit
gap). The quadratic separation persists across all gap regimes.


## Corollary: Quadratic Quantum-Classical Separation

**Corollary.** *In the query model, estimating $A_1(H_z)$ to precision
$\epsilon = 2^{-n/2}$ exhibits a quadratic quantum-classical separation:*

| Model | Query Complexity |
|-------|-----------------|
| Quantum | $O(2^{n/2} \cdot \mathrm{poly}(n))$ |
| Classical | $\Omega(2^n)$ |

*The separation ratio is at least $\Omega(2^{n/2}/\mathrm{poly}(n))$,
matching Grover's quadratic speedup.*

**Proof.** The upper bound is Theorem 2 (with $\Delta_1 = 1$ for the
adversarial instance: $O(\sqrt{N} + 2^{n/2}) = O(2^{n/2})$). The lower
bound is Theorem 3. The ratio is
$\Omega(2^n) / O(2^{n/2} \cdot \mathrm{poly}(n)) =
\Omega(2^{n/2}/\mathrm{poly}(n))$. $\square$

**Discussion.** The precision $2^{-n/2}$ sits at a natural complexity
boundary for three independent reasons:

1. *Algorithmic necessity.* The adiabatic algorithm's optimal schedule
   requires $A_1$ to precision $O(\sqrt{d_0/N})$, which is $O(2^{-n/2})$
   in the worst case $d_0 = O(1)$ (paper Section 2.2).

2. *Proof technique barrier.* The polynomial interpolation technique that
   establishes #P-hardness at $2^{-\mathrm{poly}(n)}$ breaks down at
   $2^{-n/2}$ because error amplification through $O(M)$ stages of
   interpolation and extrapolation demands $2^{-n - O(M \log n)}$ precision,
   far beyond $2^{-n/2}$ (Theorem 1).

3. *Query complexity transition.* At $2^{-n/2}$, quantum amplitude
   estimation achieves $O(2^{n/2})$ queries while classical sampling
   requires $\Omega(2^n)$, giving a Grover-type quadratic separation
   (Theorems 2-3).

This suggests that $2^{-n/2}$ is not an arbitrary precision but a
structurally significant threshold where the problem transitions from one
complexity regime to another.


## Corrected Complexity Landscape

Combining the paper's results with our theorems. The table below involves
two distinct frameworks: computational complexity (NP-hard, #P-hard) for
the problem of estimating $A_1$ given an explicit Hamiltonian description,
and query complexity for the problem of estimating $A_1$ given oracle
access to the diagonal entries $E_x$. These are complementary perspectives,
not directly comparable.

**Computational complexity** (explicit Hamiltonian):

| Precision $\epsilon$ | Hardness | Technique |
|---------------------|----------|-----------|
| $1/\mathrm{poly}(n)$ | NP-hard | Local Hamiltonian (Thm 2 of paper) |
| $2^{-n/2}$ | NP-hard (from above) | Monotonicity of hardness |
| $2^{-\mathrm{poly}(n)}$ | #P-hard | Poly interpolation + Paturi (Thm 3 of paper) |

**Query complexity** (diagonal oracle, precision $\epsilon = 2^{-n/2}$):

| Model | Query Complexity | Source |
|-------|-----------------|--------|
| Quantum | $O(2^{n/2} \cdot \mathrm{poly}(n))$ | Theorem 2 |
| Classical | $\Omega(2^n)$ | Theorem 3 |

NP-hardness at $2^{-n/2}$ follows from NP-hardness at $1/\mathrm{poly}(n)$
by monotonicity: an oracle for precision $2^{-n/2}$ trivially solves the
problem at precision $1/\mathrm{poly}(n)$. The #P-hardness does NOT extend
to $2^{-n/2}$ by Theorem 1.

The quantum query upper bound $O(2^{n/2})$ is not polynomial-time (not in
BQP). It is subexponential relative to the classical $\Omega(2^n)$ lower
bound, with a quadratic gap matching Grover's search.


## Theorem 4: Tight Quantum Query Complexity

**Theorem 4.** *The quantum query complexity of estimating $A_1(H_z)$
to additive precision $\epsilon$ is $\Omega(1/\epsilon)$ for $M = 2$
instances with $\Delta_1 = \Theta(1)$. Combined with Theorem 2, the
quantum query complexity at $\epsilon = 2^{-n/2}$ is $\Theta(2^{n/2})$.*

**Proof.**

The upper bound $O(1/\epsilon)$ for $\Delta_1 = 1$ instances follows from
Theorem 2: $O(\sqrt{N} + 1/(\epsilon \cdot \Delta_1)) = O(\sqrt{N} + 1/\epsilon)
= O(1/\epsilon)$ when $\epsilon \le 1/\sqrt{N}$ (since then
$1/\epsilon \ge \sqrt{N}$).

For the lower bound, we reduce from approximate counting and apply the
Heisenberg limit for quantum phase estimation.

**Step 1: $A_1$ estimation is equivalent to approximate counting for
$M = 2$.**

Consider an approximate counting instance: a function
$f\!: \{0,1\}^n \to \{0,1\}$ given by quantum oracle access
$O_f\!: |x\rangle|b\rangle \mapsto |x\rangle|b \oplus f(x)\rangle$, with
the task of estimating $p = |f^{-1}(1)|/N$ to precision $\epsilon$.

Construct the diagonal Hamiltonian $H_z$ with $E_x = 1 - f(x)$. Then
$E_0 = 0$ with degeneracy $d_0 = |f^{-1}(1)|$, $E_1 = 1$ with
degeneracy $d_1 = N - d_0$, and

$$
A_1 \;=\; \frac{d_1}{N} \;=\; 1 - \frac{d_0}{N} \;=\; 1 - p.
$$

One query to $O_H$ (which returns $E_x$) is equivalent to one query to
$O_f$ (which returns $f(x) = 1 - E_x$). So estimating $A_1$ to precision
$\epsilon$ is equivalent to estimating $p$ to precision $\epsilon$, with
equal query cost in both directions.

**Step 2: Quantum lower bound for approximate counting.**

Amplitude estimation (Brassard, Hoyer, Mosca, Tapp 2002) encodes the
fraction $p = d_0/N$ in the eigenphase of the Grover iterate
$G = (2|\psi\rangle\langle\psi| - I)(I - 2\Pi_S)$, where
$|\psi\rangle = |{+}\rangle^{\otimes n}$ is the uniform superposition
and $\Pi_S$ projects onto the marked set $S = f^{-1}(1)$. The
eigenvalues of $G$ in the relevant two-dimensional subspace are
$e^{\pm 2i\theta}$ where $\sin^2(\theta) = p$.

Estimating $\theta$ to additive precision $\delta$ requires
$\Omega(1/\delta)$ applications of $G$. This is the Heisenberg limit
for quantum phase estimation: given $T$ applications of a unitary $U$
with unknown eigenphase $\phi$, any estimator $\hat{\phi}$ satisfies
$\mathbb{E}[(\hat{\phi} - \phi)^2] \ge 1/(4T^2)$
(Giovannetti, Lloyd, Maccone 2006; the bound follows from the quantum
Cramer-Rao inequality with Fisher information $F_Q \le 4T^2$).

For instances with $p$ near $1/2$ (i.e., $d_0 \approx N/2$), the
eigenphase is $\theta \approx \pi/4$, and $p = \sin^2(\theta)$ has
derivative $dp/d\theta = \sin(2\theta) = 1$. So precision $\epsilon$ in
$p$ requires precision $\delta = \epsilon / |\sin(2\theta)| = \epsilon$
in $\theta$. By the Heisenberg limit:

$$
T \;\ge\; \frac{1}{2\epsilon}.
$$

Each application of $G$ uses $O(1)$ queries to $O_f$. Total query
complexity: $\Omega(1/\epsilon)$.

**Step 3: Combine.** For $M = 2$ diagonal Hamiltonians with $\Delta_1 = 1$
and $d_0 = N/2$:

- Lower bound (Step 2): $\Omega(1/\epsilon)$ quantum queries.
- Upper bound (Theorem 2): $O(\sqrt{N} + 1/\epsilon) = O(1/\epsilon)$
  when $\epsilon \le 1/\sqrt{N}$.

At $\epsilon = 2^{-n/2} = 1/\sqrt{N}$:

$$
\text{Quantum query complexity} \;=\; \Theta(2^{n/2}).
$$

$\square$

**Sanity check (Grover, $N = 4$).** $\epsilon = 2^{-1} = 1/2$. Lower
bound: $\Omega(1/(1/2)) = \Omega(2)$. Upper bound: $O(\sqrt{4} + 2) =
O(4)$. Consistent.

**Remark.** The lower bound $\Omega(1/\epsilon)$ holds for any quantum
algorithm, not only Grover-based approaches. The Heisenberg limit is
fundamental: no quantum strategy (adaptive, entangled, or otherwise)
can circumvent it. Combined with the classical $\Omega(1/\epsilon^2)$
lower bound (Theorem 3), this gives a complete query complexity picture:

| Model | Complexity | Source |
|-------|-----------|--------|
| Quantum | $\Theta(1/\epsilon)$ | Theorems 2 and 4 |
| Classical | $\Theta(1/\epsilon^2)$ | Theorem 3 and brute force |

At $\epsilon = 2^{-n/2}$: quantum $\Theta(2^{n/2})$, classical
$\Theta(2^n)$. Both bounds are tight.


## Theorem 5: Computational Complexity Under ETH

Theorems 2-4 work in the query model (oracle access to the diagonal
entries $E_x$). The paper's open problem concerns the computational
model: given an explicit Hamiltonian description, what is the TIME
complexity of estimating $A_1$ at precision $2^{-n/2}$? We connect this
to the Exponential Time Hypothesis.

**Definition (ETH).** The Exponential Time Hypothesis (Impagliazzo and
Paturi 2001) states that there exists $\delta > 0$ such that 3-SAT on
$n_{\mathrm{var}}$ variables cannot be solved by any deterministic
algorithm in $O(2^{\delta n_{\mathrm{var}}})$ time.

**Theorem 5.** *Under ETH, any classical algorithm that estimates
$A_1(H)$ to precision $2^{-n/2}$ for an explicitly given $n$-qubit
Hamiltonian requires $2^{\Omega(n)}$ time. The quantum algorithm of
Theorem 2 (adapted to the computational setting) runs in
$O(2^{n/2} \cdot \mathrm{poly}(n))$ time when $H$ is given by a
$\mathrm{poly}(n)$-size circuit computing its diagonal entries.*

*Consequently, under ETH, $A_1$ estimation at precision $2^{-n/2}$
exhibits a quadratic quantum speedup in the computational model.*

**Proof.**

**Classical lower bound.** The paper's Theorem 2 (Section 3.1) reduces
3-SAT on $n_{\mathrm{var}}$ variables and $m$ clauses to $A_1$
estimation of a 3-local Hamiltonian on $n = 2(n_{\mathrm{var}} + m)$
qubits. The reduction uses two calls to an $A_1$-estimation oracle at
precision $\epsilon < 1/(72(n - 1))$. For 3-SAT instances with
$m = O(n_{\mathrm{var}})$ (which suffices for ETH-hardness, by the
sparsification lemma of Impagliazzo, Paturi, and Zane 2001):
$n = O(n_{\mathrm{var}})$, hence $n_{\mathrm{var}} = \Omega(n)$.

An $A_1$ oracle at precision $\epsilon = 2^{-n/2}$ is strictly more
powerful than one at precision $1/(72(n-1))$ (since $2^{-n/2} < 1/\mathrm{poly}(n)$
for large $n$). So the oracle at precision $2^{-n/2}$ also solves
3-SAT. Under ETH, 3-SAT on $n_{\mathrm{var}} = \Omega(n)$ variables
requires $2^{\Omega(n_{\mathrm{var}})} = 2^{\Omega(n)}$ time.

**Quantum upper bound.** Given a $\mathrm{poly}(n)$-size circuit $C$
computing the diagonal entries $E_x$ of $H_z$, the quantum algorithm of
Theorem 2 replaces oracle queries with circuit evaluations. Each
"query" becomes: (i) apply $C$ quantumly to compute $E_x$ into an
ancilla ($O(\mathrm{poly}(n))$ gates), (ii) perform arithmetic
($O(\mathrm{poly}(n))$ gates), (iii) uncompute. The total gate count is
$O(2^{n/2} \cdot \mathrm{poly}(n))$ (since there are
$O(2^{n/2})$ oracle calls at $\epsilon = 2^{-n/2}$, $\Delta_1 = \Theta(1)$,
each costing $O(\mathrm{poly}(n))$ gates).

**Separation.** Under ETH:

$$
\underbrace{O(2^{n/2} \cdot \mathrm{poly}(n))}_{\text{quantum}}
\quad\text{vs}\quad
\underbrace{2^{\Omega(n)}}_{\text{classical}}.
$$

The ratio is $2^{\Omega(n)} / 2^{n/2 + O(\log n)} = 2^{\Omega(n)}$, a
quadratic separation in the exponent. $\square$

**Remark 1.** The ETH lower bound applies to the specific Hamiltonians
arising from the 3-SAT reduction. For "typical" diagonal Hamiltonians
with polynomial-time computable entries, the classical brute-force cost
is $O(2^n \cdot \mathrm{poly}(n))$ (enumerate all $2^n$ strings, compute
$A_1$ exactly). Whether the $2^{\Omega(n)}$ lower bound is tight (i.e.,
whether there exist classical algorithms running in $o(2^n)$ time for
general instances) remains open.

**Remark 2.** For diagonal Hamiltonians given as Ising models
$H_z = \sum_i h_i \sigma_z^{(i)} + \sum_{ij} J_{ij}
\sigma_z^{(i)}\sigma_z^{(j)}$, the diagonal entries $E_x$ are
computable in $O(n^2)$ time. Finding the ground state is NP-hard (from
MAX-CUT). The ETH argument applies with $n_{\mathrm{var}} = n$ (one
qubit per variable), giving a clean $2^{\Omega(n)}$ classical lower
bound. The quantum algorithm runs in $O(2^{n/2} \cdot n^2)$ time.


## Theorem 6: Generic Polynomial Extrapolation Barrier

Theorem 1 shows that the paper's specific polynomial interpolation
construction fails at $\epsilon = 2^{-n/2}$. A natural question: could a
cleverer choice of interpolation nodes, auxiliary Hamiltonians, or
polynomial basis rescue the approach? We prove that the answer is no.
The error amplification is inherent in any scheme that extracts integer
information from polynomial extrapolation.

**Definition (Polynomial extrapolation scheme).** A *polynomial
extrapolation scheme* for degeneracy extraction is a procedure that:

(a) Constructs $d$ auxiliary Hamiltonians $H_1, \ldots, H_d$ (each
    depending on a base Hamiltonian $H$) parameterized by real values
    $x_1, \ldots, x_d$ in an interval $I = [a, b]$;

(b) Calls an $A_1$-estimation oracle on each $H_i$ at precision
    $\epsilon$, obtaining noisy values $\tilde{y}_i$ with
    $|y_i - \tilde{y}_i| \le c\epsilon$ for some constant $c$ (where
    $y_i$ depends on $A_1(H_i)$);

(c) Constructs a polynomial $P$ of degree $\le d - 1$ by interpolation
    from the pairs $(x_i, \tilde{y}_i)$;

(d) Evaluates $P$ at a point $x^* \notin [a, b]$ and recovers an
    integer $D \in \{0, \ldots, N\}$ by rounding:
    $D = \lfloor P(x^*) + 1/2 \rfloor$.

**Theorem 6.** *For any polynomial extrapolation scheme with $d$ nodes
in $[a, b]$ and evaluation point $x^*$ at distance $\delta > 0$ from
$[a, b]$:*

$$
\epsilon \;<\; \frac{1}{2c \cdot \Lambda_d(x^*)}
$$

*where $\Lambda_d(x^*)$ is the Lebesgue function at $x^*$:*

$$
\Lambda_d(x^*) \;=\; \sum_{j=1}^{d} \prod_{i \ne j}
\left|\frac{x^* - x_i}{x_j - x_i}\right|.
$$

*For any choice of $d$ real nodes in $[a, b]$ and any $x^*$ at distance
$\ge |b - a|$ from $[a, b]$, the Lebesgue function satisfies
$\Lambda_d(x^*) \ge 2^{d-1}$. Consequently, any polynomial
extrapolation scheme requires $\epsilon < 2^{-(d-1)}/c$. At
$d = \mathrm{poly}(n)$, the required precision is
$\epsilon = 2^{-\Omega(n)}$, and the paper's conclusion follows:
$\epsilon = 2^{-n/2}$ is insufficient.*

**Proof.**

**Step 1: Interpolation error bound.** The interpolated polynomial from
noisy data satisfies

$$
|P(x^*) - \tilde{P}(x^*)| \;\le\;
\sum_{j=1}^{d} |y_j - \tilde{y}_j| \prod_{i \ne j}
\left|\frac{x^* - x_i}{x_j - x_i}\right|
\;\le\; c\epsilon \cdot \Lambda_d(x^*).
$$

For rounding to succeed: $c\epsilon \cdot \Lambda_d(x^*) < 1/2$, giving
the stated bound on $\epsilon$.

**Step 2: Lebesgue function lower bound for extrapolation.** We prove
$\Lambda_d(x^*) \ge 2^{d-1}$ when $x^*$ is at distance $\ge |b-a|$
from $[a, b]$. This holds for ANY choice of $d$ distinct nodes
in $[a, b]$.

Since $\Lambda_d(x^*) = \sum_{j=1}^d |\ell_j(x^*)|$, it suffices to
lower-bound a single term. Let $x_{(1)}$ be the leftmost node. For
$x^* \le a - (b-a) \le x_{(1)} - (b-a)$:

$$
|\ell_{(1)}(x^*)| \;=\; \prod_{i \ne (1)}
\frac{x_i - x^*}{x_i - x_{(1)}}
\;=\; \prod_{i \ne (1)}
\left(1 + \frac{x_{(1)} - x^*}{x_i - x_{(1)}}\right).
$$

Each factor satisfies:

- Numerator shift: $x_{(1)} - x^* \ge b - a$ (since $x_{(1)} \ge a$
  and $x^* \le a - (b-a)$).
- Denominator: $x_i - x_{(1)} \le b - a$ (since both nodes lie in
  $[a, b]$).

Therefore each factor is at least $1 + (b-a)/(b-a) = 2$, and with
$d - 1$ such factors:

$$
|\ell_{(1)}(x^*)| \;\ge\; 2^{d-1}.
$$

Hence $\Lambda_d(x^*) \ge |\ell_{(1)}(x^*)| \ge 2^{d-1}$. This bound
is independent of the node placement: equally spaced, Chebyshev, or
arbitrary.

**Sanity check.** For equally spaced nodes $x_j = a + (j-1)h$ with
$h = (b-a)/(d-1)$ and $x^* = a - (b-a)$, the exact value is
$|\ell_1(x^*)| = \binom{2(d-1)}{d-1} \ge 4^{d-1}/(2\sqrt{d-1})$,
which is much larger than $2^{d-1}$. The bound is not tight but
suffices for the barrier argument.

**Step 3: Application to $A_1$.** In the paper's construction,
$d = M = \mathrm{poly}(n)$ interpolation nodes are used. The evaluation
point $x^* = -2\Delta_k$ lies outside the interpolation interval
$[1, 2M-1]$. The distance from $x^*$ to the interval is at least 1
(since $\Delta_k \ge 0$ and $x^* \le 0$). The interval length is
$2M - 2$. For $\Delta_k = 0$ (the $k = 0$ case): $x^* = 0$, which is
at distance 1 from $[1, 2M-1]$, and the interval length is $2M - 2 > 1$
for $M \ge 2$.

The Lebesgue function bound gives
$\Lambda_d(x^*) \ge 2^{M-1}$. The precision requirement is
$\epsilon < 1/(2c \cdot 2^{M-1})$. Since the degeneracy extraction
involves an additional factor of $N$ (from the rescaling
$d_k = N \cdot P(x^*)/\ldots$), the full requirement is
$\epsilon < 2^{-(n + M - 1)} / (2c)$, matching Theorem 1's bound
(and slightly sharper: the $O(M \log n)$ in Theorem 1 comes from
additional product factors specific to the construction, beyond the
pure Lebesgue amplification).

$\square$

**Remark.** Theorem 6 generalizes Theorem 1 by showing that the
exponential amplification is not an artifact of the paper's specific
choice of odd-integer nodes. ANY polynomial extrapolation scheme that
evaluates outside the interpolation interval faces at least $2^{d-1}$
amplification. No rearrangement of interpolation nodes, no alternative
polynomial basis, and no change of variables can circumvent this.
The barrier is intrinsic to polynomial extrapolation.

This does NOT rule out fundamentally different proof strategies for
#P-hardness at $2^{-n/2}$. An approach that avoids polynomial
interpolation entirely (e.g., direct algebraic reductions, or
information-theoretic arguments) might succeed. The barrier tells us
WHERE new ideas are needed: the challenge is to establish hardness
without extracting exact integer information from approximate real
evaluations.


## Theorem 7: Structure Irrelevance

Can the structure of $A_1$ (a sum of reciprocal gaps weighted by
degeneracies) be exploited to beat the generic mean estimation bounds?
We prove that the answer is no: for every number of energy levels
$M \ge 2$ and every gap structure, there exist instances where the query
complexity of $A_1$ estimation matches the generic bounds of Theorems
3-4.

**Theorem 7.** *For every $M \ge 2$ and every sequence of gaps
$0 < \Delta_1 < \cdots < \Delta_{M-1}$, there exist $n$-qubit diagonal
Hamiltonians with $M$ distinct energy levels and the given gaps for
which:*

- *Quantum query complexity of estimating $A_1$ to precision $\epsilon$
  is $\Omega(1/\epsilon)$.*
- *Classical query complexity is $\Omega(1/\epsilon^2)$.*

*In particular, the sum-of-reciprocals structure of $A_1$ provides no
worst-case advantage over generic mean estimation.*

**Proof.** Fix gaps $\Delta_1 < \cdots < \Delta_{M-1}$ and let
$\alpha_k = 1/\Delta_k$ for $k = 1, \ldots, M-1$. We construct hard
instances by concentrating nearly all degeneracy in the first two
levels, making the higher levels contribute a known constant.

**Step 1: Instance construction.** For a parameter $d_0 \in \{0, \ldots,
N - M + 1\}$, define degeneracies:

- $d_0$ (ground state degeneracy, the unknown)
- $d_1 = N - d_0 - (M - 2)$ (first excited state)
- $d_k = 1$ for $k = 2, \ldots, M - 1$ (one state per higher level)

Then
$$
A_1 \;=\; \frac{1}{N}\left(\frac{N - d_0 - (M-2)}{\Delta_1}
+ \sum_{k=2}^{M-1} \frac{1}{\Delta_k}\right)
\;=\; \frac{N - d_0 - (M-2)}{N \Delta_1} + \frac{C}{N}
$$

where $C = \sum_{k=2}^{M-1} 1/\Delta_k$ is a known constant (since the
gaps are known). Estimating $A_1$ to precision $\epsilon$ is equivalent
to estimating $(N - d_0)/(N\Delta_1)$ to precision $\epsilon$, which is
equivalent to estimating $d_0/N$ to precision $\epsilon \Delta_1$.

**Step 2: Reduction from approximate counting.** Define $f(x) = 1$ if
$E_x = 0$ (i.e., $x$ is a ground state) and $f(x) = 0$ otherwise.
Estimating $d_0/N = |f^{-1}(1)|/N$ to precision $\delta = \epsilon
\Delta_1$ is an approximate counting problem.

The quantum lower bound (Theorem 4): $\Omega(1/\delta) = \Omega(1/
(\epsilon \Delta_1))$ queries. This matches the upper bound from
Theorem 2.

The classical lower bound (Theorem 3 argument): $\Omega(1/\delta^2)
= \Omega(1/(\epsilon^2 \Delta_1^2))$ queries. For the adversarial
instance with $d_0 \approx N/2$, this is $\Omega(1/\epsilon^2)$ (since
$\Delta_1$ is a fixed constant of the instance family).

**Step 3: The higher levels do not help.** The key observation: the
contribution of levels $2, \ldots, M-1$ to $A_1$ is $C/N$, which
is $O(M/N) = O(\mathrm{poly}(n)/2^n) = o(\epsilon)$ for any
$\epsilon \ge 2^{-n/2}$. These levels are informationally invisible at
precision $\epsilon$: no measurement at this precision can detect their
contribution. The entire estimation problem reduces to the first two
levels.

For instances where the higher levels carry significant degeneracy (not
$d_k = 1$), the problem can only become harder: the algorithm must now
resolve the contributions of multiple levels, not just one.

$\square$

**Remark.** Theorem 7 shows that the $M = 2$ instances of Theorems 3-4
are the hardest case, not an artificially simple one. The structure
of $A_1$ as a sum over energy levels provides no asymptotic advantage
because:

1. The unknown quantity (ground state degeneracy) dominates $A_1$ for
   adversarial instances.
2. Higher energy levels can be "hidden" by assigning them negligible
   degeneracy.
3. Known gap values do not help estimate unknown degeneracies.

A positive result would require structural assumptions on the
degeneracies (e.g., $d_k = \Theta(N/M)$ for all $k$, or special
symmetry). Under such promises, the estimation problem may become easier,
but this would be a different problem from worst-case $A_1$ estimation.


## Updated Complexity Landscape

Incorporating Theorems 4-7, the complete picture for $A_1$ estimation at
precision $\epsilon = 2^{-n/2}$ is:

**Query complexity** (tight characterization):

| Model | Lower Bound | Upper Bound | Source |
|-------|-------------|-------------|--------|
| Quantum | $\Omega(2^{n/2})$ | $O(2^{n/2})$ | Thms 4, 2 |
| Classical | $\Omega(2^n)$ | $O(2^n)$ | Thm 3, brute force |

The quantum speedup factor is exactly $\Theta(2^{n/2})$, matching
Grover's quadratic advantage. Both bounds are tight for $\Delta_1 =
\Theta(1)$, and the hardness persists for all $M \ge 2$ (Theorem 7).

**Computational complexity** (under ETH):

| Model | Time | Source |
|-------|------|--------|
| Quantum | $O(2^{n/2} \cdot \mathrm{poly}(n))$ | Thm 2 |
| Classical | $2^{\Omega(n)}$ | Thm 5 (ETH) |

**Proof technique barrier**: Polynomial extrapolation requires precision
$2^{-\Omega(d)}$ for degree-$d$ interpolation (Theorem 6). At
$d = \mathrm{poly}(n)$, the required $\epsilon = 2^{-\Omega(n)}$ is
exponentially below $2^{-n/2}$. No rearrangement of interpolation nodes
can circumvent this.


## Proposition 8: Precision Phase Diagram

Theorems 1-4 resolve the algorithmically relevant point
$\epsilon = 2^{-n/2}$. We now place this point in the full
precision-complexity landscape.

Define the precision-dependent core query complexity by fixing
$M = 2$, $\Delta_1 = 1$, and known ground energy $E_0 = 0$ (the same
approximate-counting family used in Theorem 4). In this core family,
$A_1 = 1 - d_0/N$, so the only task is estimating one mean to
additive error $\epsilon$.

**Proposition 8.** *For $A_1$ estimation, the precision landscape is:*

| Precision regime | Quantum query complexity (core) | Classical query complexity (core) | Computational status |
|------------------|----------------------------------|-----------------------------------|----------------------|
| $\epsilon = \Theta(1)$ | $\Theta(1)$ | $\Theta(1)$ | Trivial additive approximation |
| $\epsilon = 1/\mathrm{poly}(n)$ | $\Theta(1/\epsilon)$ | $\Theta(1/\epsilon^2)$ | NP-hard (paper Theorem 2) |
| $\epsilon = 2^{-cn}$, $0 < c < 1/2$ | $\Theta(2^{cn})$ | $\Theta(2^{2cn})$ | Between NP-hard and #P-hard known points |
| $\epsilon = 2^{-n/2}$ | $\Theta(2^{n/2})$ | $\Theta(2^n)$ | This work (Theorems 2-4) |
| $\epsilon = 2^{-cn}$, $c > 1/2$ | $\Theta(2^{cn})$ | $\Theta(2^{2cn})$ | #P-hard once $cn$ exceeds the paper's interpolation threshold; otherwise unresolved |
| $\epsilon = 2^{-\mathrm{poly}(n)}$ | $\Theta(1/\epsilon)$ | $\Theta(1/\epsilon^2)$ | #P-hard (paper Theorem 3) |

*Hence the query complexity changes continuously with precision
($\Theta(1/\epsilon)$ quantum, $\Theta(1/\epsilon^2)$ classical), while
$\epsilon = 2^{-n/2}$ is the structural boundary where interpolation-based
#P-hardness proofs break (Theorems 1 and 6).*

**Proof.**

For the core family ($M = 2$, $\Delta_1 = 1$, known $E_0$):

1. Quantum upper bound $O(1/\epsilon)$ follows from Theorem 2
   (amplitude-estimation stage).
2. Quantum lower bound $\Omega(1/\epsilon)$ follows from Theorem 4.
3. Classical lower bound $\Omega(1/\epsilon^2)$ follows from Theorem 3.
4. Classical upper bound $O(1/\epsilon^2)$ follows from the sample-mean
   estimator on Bernoulli outcomes (or brute force when $1/\epsilon^2 > N$).

So the core query complexities are exactly
$\Theta(1/\epsilon)$ (quantum) and $\Theta(1/\epsilon^2)$ (classical).
Substituting $\epsilon = 2^{-cn}$ gives
$\Theta(2^{cn})$ and $\Theta(2^{2cn})$, with separation factor $2^{cn}$.
At $c = 1/2$, this yields $\Theta(2^{n/2})$ vs $\Theta(2^n)$.

Computational hardness labels come from the paper:
NP-hard at inverse-polynomial precision (paper Theorem 2) and #P-hard
at exponentially small precision $2^{-\mathrm{poly}(n)}$ (paper Theorem 3).
For $\epsilon = 2^{-cn}$ with $c > 1/2$, we are in an exponential regime.
Paper Theorem 3 applies once the linear exponent $cn$ is at least the
explicit threshold polynomial appearing in that reduction. For linear
exponents below that threshold, the computational classification remains
open.

Finally, Theorems 1 and 6 show that $\epsilon = 2^{-n/2}$ is exactly
where polynomial extrapolation fails to carry #P-hardness downward.
Thus the transition at $2^{-n/2}$ is a transition in available proof
techniques, not a discontinuity in query scaling. $\square$


## Proposition 9: Structured Families and the Limits of Theorem 7

Theorem 7 is a worst-case statement over all diagonal Hamiltonians.
Experiment 08 studies restricted structured families. We now connect the two.

**Proposition 9.** *For the structured families in Experiment 08:*

1. *Theorem 7 does not by itself imply hardness inside those families,
   because its adversarial construction ranges over unrestricted diagonal
   Hamiltonians and does not establish closure under the structural
   constraints (bounded-treewidth local factors, ferromagnetic Ising with
   consistent fields).*
2. *For bounded-treewidth integer local energies (Experiment 08,
   Proposition 8), $A_1$ is exactly computable in
   $2^{O(w)}\mathrm{poly}(n,m)$ time. Therefore precision
   $2^{-n/2}$ is classically tractable whenever $w = O(\log n)$
   (in particular constant $w$).*
3. *For ferromagnetic Ising with consistent fields (Experiment 08,
   Proposition 13), additive-$\eta$ approximation requires
   $\mu \le \eta/(6B)$ and $K \ge 3RB^2/(2\eta)$. At $\eta = 2^{-n/2}$ this
   forces $1/\mu = \Omega(B2^{n/2})$, so with the standard Ising-FPRAS
   dependence $\mathrm{poly}(n,1/\mu,\log(1/\delta_q))$ the induced scheme is
   not polynomial-time at schedule precision.*
4. *The Experiment 08 tractability guarantees extend to schedule-relevant
   precision exactly when either (i) an exact polynomial-time method is
   available (as in bounded treewidth), or (ii) the required precision
   $\eta_{A_1} = \Theta(\sqrt{d_0A_2/N})$ is itself inverse-polynomial
   (equivalently $d_0A_2/N \ge 1/\mathrm{poly}(n)^2$), so that
   $\mathrm{poly}(1/\eta_{A_1})$ remains polynomial.*

**Proof.**

Part 1: Theorem 7 constructs hard instances by freely assigning
degeneracies across levels while preserving only an abstract gap sequence.
That argument does not prove the constructed spectra are realizable inside
the structured subclasses of Experiment 08, so it is not a family-restricted
lower bound.

Part 2: Experiment 08 Proposition 8 computes all degeneracy coefficients
$d_q$ exactly via variable elimination on width-$w$ decompositions in
$2^{O(w)}\mathrm{poly}(n,m)$ time, then evaluates
$A_1 = 2^{-n}\sum_{q > E_0} d_q/(q-E_0)$. Exact computation implies
additive error $0$, hence also precision $2^{-n/2}$.

Part 3: Experiment 08 Proposition 13 imposes the parameter constraints
$\mu \le \eta/(6B)$ and $K \ge 3RB^2/(2\eta)$. At $\eta = 2^{-n/2}$ this
implies $1/\mu = \Omega(B2^{n/2})$ and $K = \Omega(RB^2 2^{n/2})$. The
ferromagnetic-Ising corollary in Experiment 08 assumes per-query
complexity polynomial in $(n,1/\mu,\log(1/\delta_q))$, so these parameter
values make the induced algorithm superpolynomial in $n$ at schedule
precision.

Part 4: Experiment 08 Proposition 14 gives required schedule precision
$\eta_{A_1} = \Theta(\sqrt{d_0A_2/N})$. If $\eta_{A_1} \ge 1/\mathrm{poly}(n)$,
then any method polynomial in $1/\eta$ is polynomial at that target.
If $\eta_{A_1} = 2^{-n/2}$ (worst case $d_0,A_2 = \Theta(1)$), such methods
are no longer polynomial unless an exact structural algorithm is available.
$\square$


## Proposition 10: Promise-Time Characterization and Class Mismatch

Open Question 1 asks for a natural promise-class completeness statement.
The clean statement currently available is time-parameterized.

**Proposition 10.** *Let $\mathrm{A1\mbox{-}EST}_\epsilon$ be the promise
function problem: given a succinctly described diagonal Hamiltonian $H_z$
with $\Delta_1 \ge 1/\mathrm{poly}(n)$, output $\widetilde{A}$ such that
$|\widetilde{A} - A_1(H_z)| \le \epsilon$. Then:*

1. *$\mathrm{A1\mbox{-}EST}_\epsilon \in \mathrm{FBQTIME}(\sqrt{N} +
   1/(\epsilon\Delta_1)\cdot \mathrm{poly}(n))$ (Theorem 2).*
2. *On the $M = 2$ core family with $\Delta_1 = 1$ and known $E_0$,
   quantum query complexity is $\Theta(1/\epsilon)$ (Theorem 4 and
   Theorem 2).*
3. *At $\epsilon = 2^{-n/2}$, this gives
   $\mathrm{FBQTIME}(2^{n/2}\mathrm{poly}(n))$ and quantum lower bound
   $\Omega(2^{n/2})$ in the query model. So the natural characterization is
   parameterized-time, not PromiseBQP-type polynomial-time behavior.*

**Proof.**

Part 1 is exactly Theorem 2. Part 2 is Theorem 4 (lower bound) plus the
matching amplitude-estimation upper bound in the same family. Substituting
$\epsilon = 2^{-n/2}$ gives Part 3.

The class-mismatch statement is in the black-box query sense:
the established scaling is exponential in $n$ at the target precision on
the core family. This supports a time-parameterized characterization, not
a standard fixed class completeness theorem. $\square$

**Remark.** We tested two natural formulations:

1. Decision/promise version:
   decide whether $A_1 \ge \tau + \epsilon$ or $A_1 \le \tau - \epsilon$.
2. Function version:
   output an $\epsilon$-additive approximation.

Both are naturally parameterized by $\epsilon$ and yield
$\mathrm{BQTIME}(1/\epsilon\cdot\mathrm{poly}(n))$ behavior in this
experiment. This explains why standard classes with fixed polynomial
runtime do not cleanly fit the $2^{-n/2}$ regime.

**Formalization note.** A machine-checked discrete skeleton of
Propositions 8-10 is provided in
`src/experiments/13_intermediate_hardness/lean/`, including:

1. Exact core scaling on the grid $\epsilon_k = 2^{-k}$.
2. Threshold specialization at $k = n/2$.
3. One-bit refinement identities ($Q_{k+1}=2Q_k$, separation doubles).
4. Symbolic schedule-barrier inequality on the precision grid (all exponents).
5. Finite-grid certificate of the schedule-barrier proxy up to exponent 1024.
6. Structured bridge runtime specialization.
7. Constant-factor lower/upper matching in the promise-time framing.

An additional stress-verification script
`src/experiments/13_intermediate_hardness/lib/robust_verify.py`
performs randomized checks plus exhaustive small-parameter barrier checks.
