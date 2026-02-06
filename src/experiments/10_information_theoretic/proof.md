# Information-Theoretic Limits: Proof

## Part I: Universal Query Lower Bound

### Setup

We work in the standard quantum query model. The problem Hamiltonian $H_z$ acts on $\mathbb{C}^N$ with $N = 2^n$, is diagonal in the computational basis, and has $M$ distinct eigenlevels with energies $0 \leq E_0 < E_1 < \cdots < E_{M-1} \leq 1$. The ground level has degeneracy $d_0$.

**Problem (Ground State Finding).** Given oracle access to $H_z$, find a computational basis state $|x\rangle$ satisfying $H_z|x\rangle = E_0|x\rangle$.

The oracle is the standard quantum oracle $O_z$ that, given a basis state $|x\rangle$, allows evaluation of $E_x = \langle x|H_z|x\rangle$ in superposition. Concretely, we can implement a phase oracle $O_z|x\rangle = e^{i E_x t}|x\rangle$ for any chosen $t$, or a marking oracle $O_f|x\rangle|b\rangle = |x\rangle|b \oplus f(x)\rangle$ where $f(x) = 1$ iff $E_x = E_0$ (assuming the algorithm has identified $E_0$, or via the minimum-finding reduction below).

**Theorem 1 (Query Lower Bound).** Any quantum algorithm that finds a ground state of $H_z$ with success probability $\geq 2/3$ requires $\Omega(\sqrt{N/d_0})$ oracle queries.

*Proof.* We reduce ground state finding to unstructured search with $d_0$ marked items among $N$ total items. The lower bound holds even when the algorithm knows $E_0$ in advance (giving it strictly more power), so it certainly holds without this knowledge.

Given $E_0$, define $f: \{0,1\}^n \to \{0,1\}$ by $f(x) = 1$ iff $\langle x|H_z|x\rangle = E_0$. The set of marked items $S = \{x : f(x) = 1\}$ has $|S| = d_0$. Finding a ground state of $H_z$ is equivalent to finding an element of $S$.

By Bennett, Bernstein, Brassard, and Vazirani (1997), any quantum algorithm solving the unstructured search problem with $|S| = d_0$ marked items among $N$ requires $\Omega(\sqrt{N/d_0})$ queries. Each query to the marking oracle $f$ requires one call to the phase oracle of $H_z$. Therefore ground state finding requires $\Omega(\sqrt{N/d_0})$ queries.

For the specific adiabatic setting (where $H_0 = -|\psi_0\rangle\langle\psi_0|$ is a rank-one projector), the same bound follows from Farhi, Goldstone, Gutmann, and Nagaj (2008), Theorem 1: for $H_B = E(\mathbb{I} - |s\rangle\langle s|)$ and any $H_P$ diagonal in the computational basis with ground space dimension $k$,
$$T \geq \frac{b}{E}\sqrt{\frac{N}{k}} - \frac{2\sqrt{b}}{E},$$
where $b$ is the success probability. $\square$

**Remark (Tightness).** The bound is tight. The Durr-Hoyer quantum minimum-finding algorithm achieves $O(\sqrt{N})$ queries (Theorem 2 below). When $d_0 = \Theta(1)$, this matches. More precisely, Grover's algorithm with known $d_0$ achieves $O(\sqrt{N/d_0})$ queries exactly (Boyer, Brassard, Hoyer, Tapp 1998), and with unknown $d_0$, $O(\sqrt{N/d_0})$ expected queries via exponential search over the number of iterations.

**Sanity check ($N = 4$, $d_0 = 1$).** The lower bound is $\Omega(\sqrt{4}) = \Omega(2)$. Grover's algorithm: one iterate maps $|\psi_0\rangle = \frac{1}{2}(|0\rangle + |1\rangle + |2\rangle + |3\rangle)$ to the marked state with amplitude $\sin(3 \arcsin(1/2)) = \sin(\pi/2) = 1$, so one query suffices for certainty. This is consistent: $\Omega(2)$ says the number of queries is at least $c \cdot 2$ for some universal constant $c$, and $c \leq 1/2$ for the BBBV bound.


## Part II: Circuit Model Achievability Without Spectral Information

**Theorem 2 (Spectral-Information-Free Ground State Finding).** There exists a quantum algorithm that finds the ground state of any $H_z$ diagonal in the computational basis in $O(\sqrt{N/d_0})$ expected oracle queries, without knowledge of $E_0$, $\Delta$, $A_1$, $d_0$, or any other spectral parameter.

*Proof.* The Durr-Hoyer quantum minimum-finding algorithm (1996) solves this problem.

**Algorithm (Durr-Hoyer).** Input: oracle access to $f: \{0,1\}^n \to \mathbb{R}$ where $f(x) = E_x$.
1. Pick $x_0$ uniformly at random from $\{0,1\}^n$. Set threshold $y = f(x_0)$.
2. Repeat:
   (a) Use Grover's algorithm to search for $x'$ with $f(x') < y$.
   (b) If found, set $y = f(x')$ and $x_0 = x'$.
   (c) If not found after $c\sqrt{N/k_{est}}$ iterations (where $k_{est}$ is the estimated number of items below threshold), output $x_0$.

The algorithm maintains a threshold $y$ and iteratively lowers it. At each stage, the number of items below the current threshold approximately halves. By the analysis of Durr and Hoyer (reproduced in Ambainis 2004, Section 3.3), the expected total query count is
$$\sqrt{N} + \sqrt{N/2} + \sqrt{N/4} + \cdots = \sqrt{N}\left(1 + \frac{1}{\sqrt{2}} + \frac{1}{2} + \cdots\right) = O(\sqrt{N}).$$
The geometric series converges to $1/(1 - 1/\sqrt{2}) = \sqrt{2}/(\sqrt{2}-1) < 3.5$.

When $d_0 > 1$, the Grover subroutine searching for items below each successive threshold benefits from the $d_0$-fold degeneracy of the ground level: once the threshold reaches $E_1$, there are $d_0$ items at energy $E_0$ satisfying the search criterion, costing $O(\sqrt{N/d_0})$ per Grover iteration. Combined with Boyer-Brassard-Hoyer-Tapp (1998) for unknown number of marked items, the expected total query count is $O(\sqrt{N/d_0})$.

At no point does the algorithm compute, estimate, or use $A_1$, $s^*$, $\Delta$, or any spectral parameter. The only information extracted from the oracle is the function value $f(x')$ at each found item, used solely to update the threshold.

$\square$

**Key observation.** The circuit model achieves optimality through amplitude amplification with iterative thresholding. This mechanism does not traverse an adiabatic path, does not encounter an avoided crossing, and does not require knowledge of where any crossing occurs. The quantity $A_1 = \frac{1}{N}\sum_{k \geq 1} d_k/(E_k - E_0)$ parameterizes the adiabatic path $H(s) = -(1-s)|\psi_0\rangle\langle\psi_0| + sH_z$. An algorithm that never takes this path has no use for $A_1$.


## Part III: The Adiabatic Model's Unique Limitation

Combining results from the paper and experiments 04 and 05, we obtain a precise characterization of how much additional information each computational model requires beyond oracle access.

**Theorem 3 (Model Separation).** Consider the problem of finding the ground state of an $n$-qubit Hamiltonian $H_z$ diagonal in the computational basis. Let $T_{\mathrm{opt}} = \Theta(\sqrt{N/d_0})$ denote the optimal query complexity. Then:

(a) **Circuit model:** There exists a circuit-model algorithm achieving $O(T_{\mathrm{opt}})$ queries using 0 bits of spectral information beyond oracle access. (Theorem 2 above.)

(b) **Adiabatic model, fixed schedule:** The ratio of uninformed to informed time satisfies $T_{\mathrm{unf}} / T_{\mathrm{inf}} \geq (s_R - s_L) / \Delta_*$ (Experiment 04, Theorem 2). For unstructured search: $s_R - s_L = \Theta(1)$, $\Delta_* = \Theta(2^{-n/2})$, and $T_{\mathrm{inf}} = \Theta(\sqrt{N/d_0})$ (Paper, Theorem 1). Therefore $T_{\mathrm{unf}} = \Omega(2^{n/2} \cdot \sqrt{N/d_0}) = \Omega(N/\sqrt{d_0})$.

(c) **Adiabatic model, gap-informed:** With $A_1$ known to precision $\delta_s = O(2^{-n/2})$, the optimal local schedule achieves $T_{\mathrm{inf}} = O(T_{\mathrm{opt}})$. (Paper, Theorem 1.)

(d) **Adiabatic model, adaptive:** An adaptive algorithm making $O(n)$ quantum energy measurements during execution achieves $T_{\mathrm{adapt}} = O(T_{\mathrm{opt}})$ without prior knowledge of $A_1$. (Experiment 05.)

*Proof.* Each part is established in the cited work. Part (b) uses the separation ratio from Experiment 04, which itself relies on the informed schedule achievability result from the adiabatic optimization literature (Roland-Cerf 2002, Guo-An 2025). The synthesis is the new content: parts (a)-(d) give a complete picture of what each model requires.

**Information accounting:**
- Circuit model: 0 additional bits. Optimal.
- Adiabatic, fixed: $n/2$ bits of $A_1$ (to precision $2^{-n/2}$). Without these bits, exponential penalty.
- Adiabatic, adaptive: 0 communicated bits, but $O(n)$ quantum measurement outcomes acquired during execution. These $O(n)$ outcomes provide $O(n)$ bits of information about $s^*$.

The information gap between the fixed adiabatic model and the circuit model is $\Theta(n)$ bits. This gap corresponds to the NP-hard quantity $A_1$. But this gap is a property of the model, not the task: the circuit model does not need this information at all.

$\square$

**Remark.** Computing $A_1$ classically to precision $1/\mathrm{poly}(n)$ is NP-hard (Paper, Theorem 2). Computing it exactly is $\#$P-hard (Paper, Theorem 3). The adaptive adiabatic approach circumvents this entirely by acquiring the information quantumly, at the cost of $O(n)$ measurements (which contribute only $O(T_{\mathrm{opt}})$ to the total runtime).


## Part IV: Communication Complexity Formalization

We formalize the model separation using a communication framework.

**Setting.** Alice holds the complete classical description of an $n$-qubit Hamiltonian $H_z$ (all eigenvalues and degeneracies, or equivalently the diagonal entries $E_x$ for each $x \in \{0,1\}^n$). Bob holds a quantum computer and oracle access to $H_z$ (he can query $E_x$ for any $x$ in superposition). Alice can send $C$ classical bits to Bob. Bob's goal: output a ground state $x$ with $E_x = E_0$, using at most $T$ queries.

**Theorem 4 (Communication Complexity of Ground State Finding).**

(a) **Circuit-oracle model:** $C = 0$ suffices for $T = O(\sqrt{N/d_0})$. Bob runs Durr-Hoyer without any communication from Alice.

(b) **Fixed-schedule adiabatic model:** For $T = O(\sqrt{N/d_0})$, it is necessary and sufficient that $C = \Theta(n)$.
- *Lower bound:* Bob must construct a schedule with velocity $v(s) \propto g(s)^2$ near the crossing $s^*$. To do this, he needs $s^*$ to precision $\Delta_* = O(2^{-n/2})$, which requires $\log_2(1/\Delta_*) = n/2$ bits. By experiment 04, without this information the runtime blows up to $\Omega(2^{n/2} \cdot T_{\mathrm{opt}})$.
- *Upper bound:* Alice sends a binary encoding of $A_1$ to $n/2$ bits of precision. Bob computes $s^* = A_1/(A_1 + 1)$ and runs the informed schedule.

(c) **Adaptive adiabatic model:** $C = 0$ suffices for $T = O(\sqrt{N/d_0})$. Bob uses the binary search protocol with $O(n)$ energy measurements during adiabatic evolution. The information is acquired quantumly during execution, not communicated classically.

*Proof.* Part (a) follows from Theorem 2. Part (b): the lower bound follows from experiment 04 (the uninformed penalty is exponential unless $s^*$ is known to precision $\Delta_*$, and specifying $s^*$ to precision $\Delta_* = O(2^{-n/2})$ requires $n/2$ bits); the upper bound follows from the paper (Theorem 1). Part (c) follows from experiment 05.

$\square$

**Interpretation.** The communication complexity of ground state finding is:
$$C_{\mathrm{circuit}} = 0, \quad C_{\mathrm{adiabatic\text{-}fixed}} = \Theta(n), \quad C_{\mathrm{adiabatic\text{-}adaptive}} = 0.$$
The $\Theta(n)$-bit gap between $C_{\mathrm{circuit}}$ and $C_{\mathrm{adiabatic\text{-}fixed}}$ is exactly the information content of $A_1$ at the algorithmically relevant precision. The adaptive model closes this gap by replacing classical communication with quantum measurement.


## Part V: Refutation of Conjecture 4

**Conjecture 4 (No Free Lunch), restated.** For any algorithm achieving $O(\sqrt{N/d_0})$ runtime without explicit spectral information:
- Either it implicitly computes the spectral information (taking additional time), OR
- It works only for structured problem classes (not general $H_z$).

**Theorem 5 (Counterexample).** Conjecture 4 is false. The Durr-Hoyer algorithm is a counterexample.

*Proof.* We verify that neither disjunct holds.

**Disjunct 1 (Implicit computation).** The Durr-Hoyer algorithm at no point computes or approximates $A_1 = \frac{1}{N}\sum_{k \geq 1} d_k/(E_k - E_0)$ or the crossing position $s^* = A_1/(A_1+1)$. Its internal state consists of a threshold value $y$ (the current best function value) and the corresponding basis state $x_0$. The threshold $y$ is the value $E_{x_0}$, a single eigenvalue of $H_z$, not a weighted sum over the full spectrum. At termination, $y = E_0$, and the algorithm has learned one spectral quantity (the ground energy) and one ground state element. It has learned nothing about $A_1$, $\Delta$, $A_2$, or the degeneracy structure beyond $E_0$.

To make this concrete: consider two Hamiltonians $H_z^{(1)}$ and $H_z^{(2)}$ with the same ground energy $E_0$ and same ground space (same $d_0$ elements) but very different excited spectra (different $A_1$). The Durr-Hoyer algorithm's behavior on these two instances is identical once the threshold reaches $E_0$. It cannot distinguish them, and it does not need to. The quantity $A_1$ is invisible to the algorithm.

**Disjunct 2 (Structured problems only).** The Durr-Hoyer algorithm works for ANY function $f: \{0,1\}^n \to \mathbb{R}$ with $d_0$ global minimizers. There is no assumption on structure: the function can be arbitrary, adversarially chosen, with any spectrum. The algorithm's correctness relies only on the existence of a minimum (which every finite function has) and the ability to compare values (which the oracle provides).

Since neither disjunct holds, Conjecture 4 is false. $\square$

**Where the intuition fails.** Conjecture 4 expresses the intuition that "to find a needle in a haystack faster than brute force, you need to know something about where the needle is." This intuition is correct classically (brute force is optimal for classical unstructured search). Quantumly, it is wrong. Grover's algorithm and its descendants find the needle with a quadratic speedup using only the ability to recognize the needle when they see it (the oracle), not any prior knowledge of its location. The algorithmic mechanism (amplitude amplification) is qualitatively different from classical search and does not need the same auxiliary information.


## Part VI: Main Negative Result

**Main Theorem (No Information-Theoretic Limits Beyond Grover).** The query complexity of finding a ground state of an $n$-qubit Hamiltonian $H_z$ diagonal in the computational basis is $\Theta(\sqrt{N/d_0})$. This bound is:
- Achieved by the Durr-Hoyer algorithm using only oracle access (Theorem 2).
- Tight by the BBBV lower bound (Theorem 1).
- Independent of all spectral parameters beyond $d_0$: the quantities $\Delta$, $A_1$, $A_2$, the number of distinct eigenlevels $M$, and the full degeneracy structure $\{d_k\}$ are irrelevant to the query complexity.

*Proof.* Theorem 1 gives $\Omega(\sqrt{N/d_0})$. Theorem 2 gives $O(\sqrt{N/d_0})$. The upper bound uses no spectral information, so the lower bound cannot be improved by conditioning on spectral parameters.

$\square$

**Corollary (A_1 is Model-Specific).** The spectral parameter $A_1 = \frac{1}{N}\sum_{k \geq 1} d_k/(E_k - E_0)$ is:
1. Required for optimal adiabatic evolution with a fixed schedule (Paper, Theorem 1; Experiment 04).
2. NOT required for optimal ground state finding in the circuit model (Theorem 2).
3. NP-hard to compute classically (Paper, Theorem 2).
4. Detectable quantumly via $O(n)$ adaptive measurements within the adiabatic framework (Experiment 05).

The A_1 hardness barrier identified in the paper is a property of the adiabatic computational model (specifically, the need to parameterize a schedule through a one-parameter family $H(s) = -(1-s)|\psi_0\rangle\langle\psi_0| + sH_z$ that has an avoided crossing at $s^*$ determined by $A_1$). It is not a property of the computational task (finding ground states of diagonal Hamiltonians).

**Corollary (Comparison Table).**

| Model | Query Complexity | Additional Information | Communication |
|---|---|---|---|
| Circuit (Grover/Durr-Hoyer) | $O(\sqrt{N/d_0})$ | None | 0 bits |
| Adiabatic, informed | $O(\sqrt{N/d_0})$ | $A_1$ to precision $2^{-n/2}$ | $\Theta(n)$ bits |
| Adiabatic, fixed uninformed | $\Omega(N/\sqrt{d_0})$ | None | 0 bits |
| Adiabatic, adaptive | $O(\sqrt{N/d_0})$ | None (acquired quantumly) | 0 bits |

The circuit model and the adaptive adiabatic model achieve optimal performance with zero classical communication. The fixed adiabatic model pays an exponential penalty without the NP-hard quantity $A_1$. This is a model-specific phenomenon.


## Part VII: $A_1$-Blindness of Circuit Algorithms

The observations in Parts II and V are informal: Durr-Hoyer "does not use" $A_1$. We now make this precise.

**Definition (Spectral Equivalence).** Two problem Hamiltonians $H_z$, $H_z'$ on $\mathbb{C}^N$ are ground-equivalent if they share the same ground energy $E_0$ and the same ground space $S_0 = \{x \in \{0,1\}^n : \langle x|H_z|x\rangle = E_0\}$.

Ground-equivalent Hamiltonians may differ in every other spectral parameter: the number of distinct eigenlevels $M$, the degeneracies $\{d_k\}_{k \geq 1}$, the energy gaps $\{E_k - E_0\}_{k \geq 1}$, and consequently $A_1$, $A_2$, and all derived quantities.

**Proposition 6 (Output Independence).** Let $H_z$, $H_z'$ be ground-equivalent. Then the output distributions of Durr-Hoyer on $H_z$ and $H_z'$ are identical:
$$\Pr[\mathrm{DH}(H_z) = x] = \Pr[\mathrm{DH}(H_z') = x] \quad \text{for all } x \in \{0,1\}^n.$$

*Proof.* The Durr-Hoyer algorithm maintains a threshold $y$ and a candidate $x_0$, and repeatedly uses Grover search to find $x'$ with $E_{x'} < y$. At each Grover subroutine call, the initial state is the uniform superposition $|\psi_0\rangle = N^{-1/2}\sum_x|x\rangle$.

Conditioned on success (outputting a ground state, which occurs with probability $\geq 2/3$), the output $x_0$ satisfies $E_{x_0} = E_0$. At the iteration that produced this $x_0$, the Grover subroutine searched for elements of $\{x : E_x < y\}$ for some threshold $y > E_0$. By the symmetry of Grover's algorithm applied to the uniform initial state, the output is uniformly distributed over the marked set $\{x : E_x < y\}$. Conditioned on $E_{x_0} = E_0$, the output is $\mathrm{Uniform}(S_0)$.

Since $H_z$ and $H_z'$ share the same $S_0$ and $E_0$, the conditional output distributions are identical. $\square$

**Remark (Trajectory differs).** While the output distributions are identical, the execution trajectories differ. The intermediate threshold values $y_0 > y_1 > \cdots > y_T = E_0$ depend on the excited spectrum. For instance, if $H_z$ has two excited levels and $H_z'$ has one, the descent pattern differs. But the terminal state is the same.

**Proposition 7 (Query Complexity Independence).** The expected query complexity of Durr-Hoyer on $H_z$ is $O(\sqrt{N/d_0})$, depending only on $N$ and $d_0 = |S_0|$, not on $A_1$ or any other spectral parameter.

*Proof.* The standard analysis (Durr-Hoyer 1996, reproduced in Ambainis 2004) shows: at each stage, the new threshold is a uniformly random element below the current threshold. This means the expected number of items below each successive threshold decreases geometrically. At stage $i$, the expected number of below-threshold items is at most $N \cdot 2^{-i}$, and the Grover subroutine costs $O(\sqrt{N / (N \cdot 2^{-i})}) = O(2^{i/2})$ queries.

The total cost over all stages is $\sum_{i=0}^{\lceil\log_2(N/d_0)\rceil} O(2^{i/2}) = O(\sqrt{N/d_0})$.

This bound depends on $N$ and $d_0$ only. The geometric halving argument assumes each new threshold eliminates roughly half the below-threshold items. When there are degeneracies (multiple items at the same energy), the threshold may skip entire levels, but this only accelerates the descent. The $O(\sqrt{N/d_0})$ bound holds a fortiori. $\square$

**Proposition 8 ($A_1$ Mutual Information).** Let $X_{\mathrm{DH}}$ denote the output of Durr-Hoyer. Then:
$$I(X_{\mathrm{DH}}; \, A_1 \mid S_0, E_0) = 0.$$

*Proof.* By Proposition 6, the conditional distribution of $X_{\mathrm{DH}}$ given $(S_0, E_0)$ is $\mathrm{Uniform}(S_0)$, regardless of $A_1$. Therefore $X_{\mathrm{DH}} \perp\!\!\!\perp A_1 \mid (S_0, E_0)$, and the conditional mutual information vanishes. $\square$

**Contrast: Adiabatic $A_1$-Dependence.** The informed adiabatic algorithm has the opposite property. Its schedule $s(t)$ is constructed from $s^* = A_1/(A_1+1)$, with velocity $v(s) \propto g(s)^2$ near $s^*$. Two ground-equivalent Hamiltonians with different $A_1$ values produce different crossings $s^*$, different gap profiles $g(s)$, and require different schedules. Concretely:

(a) A schedule tuned to $A_1$ achieves success probability $\geq 1 - \varepsilon$ in time $T_{\mathrm{inf}} = O(\sqrt{N/d_0})$.

(b) The same schedule applied to a ground-equivalent instance with $A_1' \neq A_1$ and $|A_1 - A_1'| \gg \delta_{A_1}$ yields low success probability: the schedule is fast (velocity $v = O(1)$) at the true crossing $s^{*\prime}$, violating the adiabatic condition $v \ll g_{\min}^2$.

(c) A single adiabatic execution therefore reveals $\Theta(1)$ bits about whether $|A_1 - A_1'| \leq \delta_{A_1}$. By binary search over $O(n/2)$ executions, the adaptive protocol of Experiment 05 learns $A_1$ to precision $\delta_{A_1}$.

This is the information-theoretic core of the model separation: the circuit model reveals zero information about $A_1$, while the adiabatic model both requires and leaks information about $A_1$.

**Sanity check ($N = 4$, $d_0 = 1$).** Consider two instances:
- $H_z^{(1)}$: $E_0 = 0$, $E_1 = 1$, $d_0 = 1$, $d_1 = 3$. Then $A_1 = 3/4$.
- $H_z^{(2)}$: $E_0 = 0$, $E_1 = 2$, $d_0 = 1$, $d_1 = 3$. Then $A_1 = 3/8$.

Both have the same ground space ($S_0 = \{x_0\}$ for some fixed $x_0$). Durr-Hoyer outputs $x_0$ on both instances. The output carries zero information about whether $A_1 = 3/4$ or $A_1 = 3/8$. But the adiabatic crossing positions differ: $s^* = 3/7 \approx 0.429$ vs $s^* = 3/11 \approx 0.273$. A schedule tuned to $s^* = 3/7$ would fail on the second instance.


## Part VIII: Unified Information-Runtime Landscape

Experiment 07 establishes the quantitative interpolation between informed and uninformed adiabatic runtimes. We import that result and recast it in the communication framework of Part IV.

**Theorem 6 (Interpolation, Experiment 07).** For the adiabatic algorithm with $A_1$ known to additive precision $\varepsilon$:
$$T(\varepsilon) = \Theta\left(T_{\mathrm{inf}} \cdot \max\left(1, \frac{\varepsilon}{\delta_{A_1}}\right)\right),$$
where $\delta_{A_1} = 2\sqrt{d_0 A_2 / N}$ is the precision threshold for optimality.

For unstructured search with $d_0 = O(1)$, $A_1 = \Theta(1)$, $A_2 = \Theta(1)$: $\delta_{A_1} = \Theta(2^{-n/2})$ and $T(\varepsilon) = T_{\mathrm{inf}} \cdot \Theta(\max(1, \varepsilon \cdot 2^{n/2}))$.

*Proof.* See Experiment 07, Theorems 1-3. $\square$

**Corollary (Bit-Runtime Tradeoff).** Suppose Alice communicates $C$ bits to Bob via uniform fixed-point quantization of $A_1$, encoding it to precision $\varepsilon = R \cdot 2^{-C}$ where $R$ is the a priori range of $A_1$. For unstructured search with $R = \Theta(1)$:
$$T(C) = T_{\mathrm{inf}} \cdot \Theta\left(\max\left(1, 2^{n/2 - C}\right)\right).$$

Each additional bit of $A_1$ information halves the adiabatic runtime, until $C^* = n/2$ bits suffice for optimality.

*Proof.* Substitute $\varepsilon = \Theta(2^{-C})$ into Theorem 6 with $\delta_{A_1} = \Theta(2^{-n/2})$:
$$T(C) = T_{\mathrm{inf}} \cdot \Theta\left(\max\left(1, \frac{2^{-C}}{2^{-n/2}}\right)\right) = T_{\mathrm{inf}} \cdot \Theta\left(\max\left(1, 2^{n/2 - C}\right)\right).$$
$\square$

**Complete Landscape.**

| Model | Communicated Bits | Runtime | Ratio $T/T_{\mathrm{inf}}$ |
|---|---|---|---|
| Circuit (Durr-Hoyer) | 0 | $\Theta(\sqrt{N/d_0})$ | 1 |
| Adiabatic, $C$ bits | $C$ | $T_{\mathrm{inf}} \cdot 2^{n/2 - C}$ | $2^{n/2 - C}$ |
| Adiabatic, $n/4$ bits | $n/4$ | $T_{\mathrm{inf}} \cdot 2^{n/4}$ | $2^{n/4}$ |
| Adiabatic, $n/2$ bits | $n/2$ | $T_{\mathrm{inf}}$ | 1 |
| Adiabatic, uninformed | 0 | $\Omega(N/\sqrt{d_0})$ | $2^{n/2}$ |
| Adiabatic, adaptive | 0 | $\Theta(\sqrt{N/d_0})$ | 1 |

The circuit model achieves the leftmost column (0 bits, optimal runtime) by avoiding the adiabatic path entirely. The adaptive adiabatic model achieves the same by replacing classical communication with $O(n)$ quantum measurements during execution. The fixed adiabatic model traces the diagonal: each missing bit doubles the runtime.

**Theorem 7 (Model-Dependent Information Cost).** The classical communication cost $C^*(T)$ required for the adiabatic model to achieve target runtime $T$ is:
$$C^*_{\mathrm{adiabatic}}(T) = \max\left(0, \; \frac{n}{2} - \log_2\frac{T}{T_{\mathrm{inf}}}\right) \quad \text{bits},$$
while $C^*_{\mathrm{circuit}}(T) = 0$ for all $T \geq T_{\mathrm{inf}}$.

The communication cost is a property of the computational model, not of the computational task.

*Proof.* Inverting the Bit-Runtime Tradeoff: if $T(C) = T_{\mathrm{inf}} \cdot 2^{n/2 - C}$, then $C = n/2 - \log_2(T/T_{\mathrm{inf}})$. Clamping $C \geq 0$ gives the formula. The circuit model achieves $T = T_{\mathrm{inf}}$ at $C = 0$ by Theorem 2. $\square$

**Sanity check ($N = 2^8 = 256$, $d_0 = 1$).** Then $n = 8$, $T_{\mathrm{inf}} = \Theta(16)$, $n/2 = 4$ bits needed.
- $C = 0$: $T = 16 \cdot 2^4 = 256 = N$. Uninformed runtime. $\checkmark$
- $C = 1$: $T = 16 \cdot 2^3 = 128 = N/2$. One bit halves it. $\checkmark$
- $C = 2$: $T = 16 \cdot 2^2 = 64 = N/4$. $\checkmark$
- $C = 4$: $T = 16 \cdot 1 = 16 = \sqrt{N}$. Optimal. $\checkmark$
- Circuit: $T = 16$ at $C = 0$. $\checkmark$


## Part IX: Scope of the $A_1$ Barrier

The $A_1$ barrier is absent in the circuit model (Part VII). It is present in the adiabatic model (Parts III-IV). A natural question: for which computational models does the barrier apply?

The paper remarks (p.983) that $A_1$ hardness "impacts other (non-adiabatic) continuous-time quantum algorithms" sharing the rank-one driver structure. We formalize this as a conjecture.

**Definition (Continuous-Time Rank-One Algorithm).** A continuous-time rank-one algorithm for ground state finding evolves the state $|\psi(t)\rangle$ under:
$$i\frac{d}{dt}|\psi(t)\rangle = H(t)|\psi(t)\rangle, \quad H(t) = f(t)\,|\psi_0\rangle\langle\psi_0| + g(t)\,H_z,$$
where $f, g: [0, T] \to \mathbb{R}$ are control functions and $|\psi_0\rangle = N^{-1/2}\sum_x|x\rangle$. The adiabatic algorithm is the special case $f(t) = -(1 - s(t))$, $g(t) = s(t)$ for a monotone schedule $s$.

**Conjecture 5 (Continuous-Time $A_1$ Barrier).** For any continuous-time rank-one algorithm with control functions $f, g$ chosen without knowledge of $A_1$:
$$T = \Omega(N/\sqrt{d_0}).$$
That is, the uninformed runtime penalty of the fixed adiabatic model extends to the full class of continuous-time algorithms sharing the rank-one driver.

**Evidence for the conjecture.**

(i) *Farhi, Goldstone, Gutmann, Nagaj (2008).* For a rank-one driver $H_B = E'(\mathbb{I} - |s\rangle\langle s|)$ and cost Hamiltonians with spectrum $(0, E, \ldots, E)$, the adiabatic algorithm requires time $T = \Omega(\sqrt{N/k})$ where $k$ is the ground space dimension (their Theorem 1). Their analysis extends to certain alternating-operator protocols beyond the purely adiabatic case, though the precise scope of this extension applies to a specific spectral structure rather than general $H_z$.

(ii) *Heuristic argument.* The evolution under $H(t) = f(t)|\psi_0\rangle\langle\psi_0| + g(t)H_z$, projected onto the two-dimensional subspace spanned by $|\psi_0\rangle$ and the ground state $|\phi_0\rangle$, encounters an avoided crossing structure parameterized by $A_1$. The control functions $f(t), g(t)$ determine how fast the system traverses this crossing. Without knowledge of $A_1$, the controls cannot be tuned to the crossing location. (This projection argument is approximate and does not constitute a proof; the full $N$-dimensional evolution may exploit effects invisible in the two-dimensional projection.)

**Evidence against the conjecture.**

(iii) *Diabatic protocols.* Non-adiabatic strategies (fast passage through the crossing followed by interference) might exploit mechanisms qualitatively different from the adiabatic path. A diabatic transition followed by a suitable rotation could potentially reach the ground state without localizing the crossing.

(iv) *Higher-rank drivers.* Replacing the rank-one driver $|\psi_0\rangle\langle\psi_0|$ with a higher-rank or structured driver could eliminate the crossing bottleneck entirely. This would not refute the conjecture (which specifies rank-one) but would limit its significance.

(v) *Quantum control theory.* The full space of control functions $f(t), g(t)$ is infinite-dimensional. The adiabatic schedule is a one-dimensional subspace. Optimal control over the full space might achieve performance inaccessible to adiabatic strategies.

**Open Question.** Resolve Conjecture 5. A proof would show that the $A_1$ barrier is intrinsic to the rank-one driver structure, not just the adiabatic protocol. A counterexample would exhibit a non-adiabatic continuous-time protocol that achieves $O(\sqrt{N/d_0})$ without knowledge of $A_1$.


## Summary

We resolved all four conjectures:

1. **Conjecture 1 (Oracle Lower Bound): PROVED.** $\Omega(\sqrt{N/d_0})$ queries are necessary. This is the Grover/BBBV bound, and it is the only universal information-theoretic limit.

2. **Conjecture 2 (Information-Complexity Tradeoff): REFINED.** The conjecture as stated is ill-defined (the mutual information quantity $I(\mathrm{algorithm})$ lacks a precise definition for quantum algorithms). The correct statement is model-specific: within the adiabatic model with fixed schedules, $\Theta(n)$ bits of spectral information are necessary for optimal runtime. This is not a universal information-theoretic bound.

3. **Conjecture 3 (Adiabatic Limitation): PROVED.** Adiabatic algorithms with fixed schedules require $n/2$ bits of spectral information (the crossing position to precision $2^{-n/2}$) that circuit-model algorithms do not need. However, the characterization "circuit algorithms get this for free" is misleading: circuit algorithms do not get $A_1$ for free; they do not need $A_1$ at all. Their mechanism bypasses the adiabatic path entirely.

4. **Conjecture 4 (No Free Lunch): REFUTED.** The Durr-Hoyer algorithm is an explicit counterexample. It achieves $O(\sqrt{N/d_0})$ for completely general $H_z$, without computing or using any spectral information. Neither disjunct of the conjecture holds.

**Main insight.** The $A_1$ barrier is not an information-theoretic limit on ground state finding. It is an artifact of the adiabatic path. Algorithms that do not traverse this path (circuit model) or that adaptively probe this path (adaptive adiabatic) are unaffected.

Additionally, the extended results (Parts VII-IX) establish:

5. **$A_1$-Blindness (Part VII).** Durr-Hoyer's output satisfies $I(X_{\mathrm{DH}}; A_1 \mid S_0, E_0) = 0$ exactly. The circuit model reveals zero information about $A_1$, while the adiabatic model both requires and leaks information about $A_1$.

6. **Unified Landscape (Part VIII).** Importing the interpolation theorem from Experiment 07: each bit of $A_1$ knowledge halves the adiabatic runtime, with the tradeoff $T(C) = T_{\mathrm{inf}} \cdot 2^{n/2 - C}$ for $C$ communicated bits. The circuit model bypasses this tradeoff entirely.

7. **Continuous-Time Conjecture (Part IX).** Conjecture 5: the $A_1$ barrier extends to all continuous-time rank-one algorithms, not just the adiabatic protocol. Evidence from Farhi et al. (2008) supports this but a proof remains open.
