# Information-Theoretic Limits: Proof

## Part I: Universal Query Lower Bound

### Setup

We work in the standard quantum query model. The problem Hamiltonian $H_z$ acts on $\mathbb{C}^N$ with $N = 2^n$, is diagonal in the computational basis, and has $M$ distinct eigenlevels with energies $0 \leq E_0 < E_1 < \cdots < E_{M-1} \leq 1$. The ground level has degeneracy $d_0$.

**Problem (Ground State Finding).** Given oracle access to $H_z$, find a computational basis state $|x\rangle$ satisfying $H_z|x\rangle = E_0|x\rangle$.

The oracle is the standard quantum oracle $O_z$ that, given a basis state $|x\rangle$, allows evaluation of $E_x = \langle x|H_z|x\rangle$ in superposition. Concretely, we can implement a phase oracle $O_z|x\rangle = e^{i E_x t}|x\rangle$ for any chosen $t$, or a marking oracle $O_f|x\rangle|b\rangle = |x\rangle|b \oplus f(x)\rangle$ where $f(x) = 1$ iff $E_x = E_0$ (assuming the algorithm has identified $E_0$, or via the minimum-finding reduction below).

**Theorem 1 (Query Lower Bound).** Any quantum algorithm that finds a ground state of $H_z$ with success probability $\geq 2/3$ requires $\Omega(\sqrt{N/d_0})$ oracle queries.

*Proof.* We reduce ground state finding to unstructured search with $d_0$ marked items among $N$ total items.

Define $f: \{0,1\}^n \to \{0,1\}$ by $f(x) = 1$ iff $\langle x|H_z|x\rangle = E_0$. The set of marked items $S = \{x : f(x) = 1\}$ has $|S| = d_0$. Finding a ground state of $H_z$ is equivalent to finding an element of $S$.

By Bennett, Bernstein, Brassard, and Vazirani (1997), any quantum algorithm solving the unstructured search problem with $|S| = d_0$ marked items among $N$ requires $\Omega(\sqrt{N/d_0})$ queries. The reduction from ground state finding to marking requires one oracle call per query (evaluate $E_x$, compare with threshold). Therefore ground state finding requires $\Omega(\sqrt{N/d_0})$ queries.

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

When $d_0 > 1$, the final Grover search has $d_0$ marked items, costing $O(\sqrt{N/d_0})$, and this dominates. Total: $O(\sqrt{N/d_0})$ expected queries.

At no point does the algorithm compute, estimate, or use $A_1$, $s^*$, $\Delta$, or any spectral parameter. The only information extracted from the oracle is the function value $f(x')$ at each found item, used solely to update the threshold.

$\square$

**Key observation.** The circuit model achieves optimality through amplitude amplification with iterative thresholding. This mechanism does not traverse an adiabatic path, does not encounter an avoided crossing, and does not require knowledge of where any crossing occurs. The quantity $A_1 = \frac{1}{N}\sum_{k \geq 1} d_k/(E_k - E_0)$ parameterizes the adiabatic path $H(s) = -(1-s)|\psi_0\rangle\langle\psi_0| + sH_z$. An algorithm that never takes this path has no use for $A_1$.


## Part III: The Adiabatic Model's Unique Limitation

Combining results from the paper and experiments 04 and 05, we obtain a precise characterization of how much additional information each computational model requires beyond oracle access.

**Theorem 3 (Model Separation).** Consider the problem of finding the ground state of an $n$-qubit Hamiltonian $H_z$ diagonal in the computational basis. Let $T_{\mathrm{opt}} = \Theta(\sqrt{N/d_0})$ denote the optimal query complexity. Then:

(a) **Circuit model:** There exists a circuit-model algorithm achieving $O(T_{\mathrm{opt}})$ queries using 0 bits of spectral information beyond oracle access. (Theorem 2 above.)

(b) **Adiabatic model, fixed schedule:** Any fixed adiabatic schedule that achieves error $\leq \epsilon$ for all gap functions in $\mathcal{G}(s_L, s_R, \Delta_*)$ requires
$$T_{\mathrm{unf}} \geq \frac{s_R - s_L}{\sqrt{\epsilon} \cdot \Delta_*}.$$
For unstructured search instances: $s_R - s_L = \Theta(1)$, $\Delta_* = \Theta(2^{-n/2})$, giving $T_{\mathrm{unf}} = \Omega(2^{n/2} \cdot T_{\mathrm{opt}})$. The penalty is exponential in $n$. (Experiment 04, Theorem 2.)

(c) **Adiabatic model, gap-informed:** With $A_1$ known to precision $\delta_s = O(2^{-n/2})$, the optimal local schedule achieves $T_{\mathrm{inf}} = O(T_{\mathrm{opt}})$. (Paper, Theorem 1.)

(d) **Adiabatic model, adaptive:** An adaptive algorithm making $O(n)$ quantum energy measurements during execution achieves $T_{\mathrm{adapt}} = O(T_{\mathrm{opt}})$ without prior knowledge of $A_1$. (Experiment 05.)

*Proof.* Each part is established in the cited work. The synthesis is the new content: parts (a)-(d) give a complete picture of what each model requires.

**Information accounting:**
- Circuit model: 0 additional bits. Optimal.
- Adiabatic, fixed: $\Theta(n)$ bits of $A_1$ (to precision $2^{-n/2}$, requiring $n/2$ bits). Without these bits, exponential penalty.
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
| Adiabatic, fixed uninformed | $\Omega(N/d_0)$ | None | 0 bits |
| Adiabatic, adaptive | $O(\sqrt{N/d_0})$ | None (acquired quantumly) | 0 bits |

The circuit model and the adaptive adiabatic model achieve optimal performance with zero classical communication. The fixed adiabatic model pays an exponential penalty without the NP-hard quantity $A_1$. This is a model-specific phenomenon.


## Summary

We resolved all four conjectures:

1. **Conjecture 1 (Oracle Lower Bound): PROVED.** $\Omega(\sqrt{N/d_0})$ queries are necessary. This is the Grover/BBBV bound, and it is the only universal information-theoretic limit.

2. **Conjecture 2 (Information-Complexity Tradeoff): REFINED.** The conjecture as stated is ill-defined (the mutual information quantity $I(\mathrm{algorithm})$ lacks a precise definition for quantum algorithms). The correct statement is model-specific: within the adiabatic model with fixed schedules, $\Theta(n)$ bits of spectral information are necessary for optimal runtime. This is not a universal information-theoretic bound.

3. **Conjecture 3 (Adiabatic Limitation): PROVED.** Adiabatic algorithms with fixed schedules require $O(n)$ bits of spectral information that circuit-model algorithms do not need. However, the characterization "circuit algorithms get this for free" is misleading: circuit algorithms do not get $A_1$ for free; they do not need $A_1$ at all. Their mechanism bypasses the adiabatic path entirely.

4. **Conjecture 4 (No Free Lunch): REFUTED.** The Durr-Hoyer algorithm is an explicit counterexample. It achieves $O(\sqrt{N/d_0})$ for completely general $H_z$, without computing or using any spectral information. Neither disjunct of the conjecture holds.

**Main insight.** The $A_1$ barrier is not an information-theoretic limit on ground state finding. It is an artifact of the adiabatic path. Algorithms that do not traverse this path (circuit model) or that adaptively probe this path (adaptive adiabatic) are unaffected.
