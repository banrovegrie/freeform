# Introduction

Quantum walks, the quantum analogue of classical random walks, find
widespread applications in several areas of quantum information
processing [@kempe2003quantum]. In particular, they are a universal
model for quantum computation
[@childs2009universal; @childs2013universal] and are central to the
design of several quantum algorithms [@ambainis2003quantum].

The problem of finding a marked node in a graph, known as the spatial
search algorithm, can be formulated as a continuous-time quantum walk
(CTQW). In the original work by Childs and Goldstone
[@childs2004spatial], it was shown that search by CTQW can find a marked
node in $\mathcal{O}(\sqrt{n})$ time [^1] for certain graphs with $n$
nodes such as the complete graph, hybercube and $d$-dimensional lattices
with $d>4$. This implied a quadratic speedup for the spatial search
problem with respect to classical random walks for these graphs. However
for lattices of $d\leq 4$, a full quadratic speedup is lost. Since then
a plethora of results have been published exhibiting a
$\mathcal{O}(\sqrt{n})$ running time of the Childs and Goldstone
algorithm (henceforth referred to as the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm) on certain
specific graphs
[@janmark2014global; @novo2015systematic; @chakraborty2016spatial; @philipp2016continuous; @wong2016quantum; @chakraborty2017optimal; @Boettcher_searchfractals_2017; @wong2018quantum; @glos2018optimal; @rhodes2019quantum].

Although we state the general framework of the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm in detail
in Sec. [2](#sec:prelim){reference-type="ref" reference="sec:prelim"},
here we mention the algorithm briefly as this will aid the understanding
of our contributions. Given a graph $G$ of $n$ nodes, the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm involves
evolving the following search Hamiltonian
$$\label{eqmain-search-ham-def}
H_{\mathrm{search}}=H_{\mathrm{oracle}}+ r H,$$ where $r$ is a tunable
parameter (the hopping rate of the quantum walk on $G$), $H$ is the
Hamiltonian encoding the structure of $G$ (such as the graph's adjacency
matrix or Laplacian) and $H_\mathrm{oracle}$ is the oracular Hamiltonian
that singles out the marked node, which we shall denote as $\ket{w}$
[^2]. Typically, the algorithm commences from the highest eigenvector of
$H$ which has a small overlap with $\ket{w}$ (say $\sqrt{\epsilon}$),
and involves carefully choosing the value of $r$, such that evolving
$H_{\mathrm{search}}$ for the minimum possible time, results in a state
that has a large overlap with $\ket{w}$. It can be
shown [@farhi1998analog] that the algorithm is optimal if it can find
the marked node with constant probability in $\Theta(\sqrt{\epsilon})$
time (in many cases $\epsilon=1/n$ as we discuss in
Sec. [2](#sec:prelim){reference-type="ref" reference="sec:prelim"}).

Most prior results on the optimality of the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm, for
particular graphs, have required an analysis specific to the underlying
instance. For example in Ref. [@janmark2014global], the authors
demonstrated, using degenerate perturbation theory that the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm can find a
marked node on a strongly regular graph in
$\ensuremath{\mathcal{O}}(\sqrt{n})$ time, a graph that lacks global
symmetry. Using similar techniques it was shown that a marked node can
be found in optimal time on a graph with low algebraic connectivity
[@meyer2015connectivity]. A long standing open problem has been to
obtain the general conditions for the optimality of the algorithm and in
particular to quantify the necessary and sufficient conditions a given
graph must satisfy for the algorithm to be optimal.

A first attempt towards deriving sufficient conditions for the
optimality of the algorithm was made in Ref. [@chakraborty2016spatial]
by connecting the graph spectral properties to the algorithmic running
time. Namely, the authors demonstrated that the algorithm is optimal if
the Hamiltonian encoding the graph structure, i.e. $H$ has a constant
spectral gap (without loss of generality, we assume $H$ to have
eigenvalues in the interval $[0,1]$, see
Sec. [2](#sec:prelim){reference-type="ref" reference="sec:prelim"} for
details). However in the scenario where the spectral gap is no longer a
constant, i.e, it decreases with the size of the graph, the results of
the aforementioned work are not applicable.

In our work, we significantly extend this result and provide the
*necessary and sufficient* conditions for the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm to be
optimal, for any $H$ obeying certain general assumptions
(Sec. [3](#sec:performance_non_degenerate){reference-type="ref"
reference="sec:performance_non_degenerate"}). The regime of validity of
our results is defined by a *spectral condition* which is obeyed, for
example, when the spectral gap of $H$ (say $\Delta$) is sufficiently
larger than the overlap of the initial state with the marked node,
i.e. $\Delta\gg \sqrt{\epsilon}$. To the best of our knowledge, this
condition is general enough to encompass most prior works predicting
optimality of the $\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$
algorithm for specific graphs. Examples include the complete graph,
hypercube [@childs2004spatial], strongly regular graphs
[@janmark2014global], complete bipartite graphs [@novo2015systematic],
lattices of dimension greater than four [@childs2004spatial],
Erdös-Renyi random graphs [@chakraborty2016spatial] or balanced trees
[@philipp2016continuous] (for specific positions of the marked node).

To prove our optimality conditions, we first obtain general results
regarding the best possible performance of the algorithm for any given
graph obeying the previously mentioned validity regime. Precisely, we
obtain general expressions, depending on the spectrum of $H$, for the
optimal value of $r$, the maximum possible amplitude that can be
obtained at the marked node and the time at which this amplitude is
reached (Theorem
[2](#lem_main:search-highest-estate){reference-type="ref"
reference="lem_main:search-highest-estate"}). The optimality conditions
follow by imposing the maximum amplitude to be constant after a time
$\sqrt{\epsilon}$.

These predictions are, however, not valid for graphs with a sufficiently
low spectral gap. Such low spectral gaps appear, for example, on graphs
composed by highly connected clusters that are sparsely connected among
each other, which find applications in spectral clustering
[@von2007tutorial]. A simple example is the so-called *joined
complete-graph* of $n$ nodes: two complete graphs of $n/2$ nodes each,
joined by a single edge between them (See
Fig. [2](#subfig:joined-complete){reference-type="ref"
reference="subfig:joined-complete"}). If $H$ is defined by the
normalized adjacency matrix of this graph, the spectral gap of $H$ is
small enough to violate the spectral condition. However in
Ref. [@meyer2015connectivity], using an analysis tailored to this
particular instance, the authors showed that the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm can find a
marked node on this graph in $\Theta(\sqrt{n})$ time.

Such instances are characterized by the following features in the
spectrum of $H$: (i) A few of the highest eigenvalues are closely spaced
(nearly degenerate), implying an extremely small spectral gap and (ii) A
large gap between the closely spaced eigenvalues and the rest of the
spectrum. We capture these properties precisely via new spectral
conditions and provide, in
Sec. [4](#sec:search-degenerate-spectra){reference-type="ref"
reference="sec:search-degenerate-spectra"}, a general theorem regarding
the performance of quantum search on such graphs
(Theorem [8](#thm:performance_qd){reference-type="ref"
reference="thm:performance_qd"}). This leads to a sufficient condition
that is able to predict optimal quantum search on the joined complete
graph and other graphs with similar spectral properties.

In Sec. [5](#sec:quantum-walk-chessboard){reference-type="ref"
reference="sec:quantum-walk-chessboard"}, we provide an explicit example
which compares and contrasts the applicability of Theorem
[2](#lem_main:search-highest-estate){reference-type="ref"
reference="lem_main:search-highest-estate"} and Theorem
[8](#thm:performance_qd){reference-type="ref"
reference="thm:performance_qd"}, respectively. Therein, we consider the
quantum walk of a rook on a rectangular chessboard. This corresponds to
the Cartesian product between two complete graphs, known as the *Rook's
graph* (See Fig. [7](#figmain:chessboard){reference-type="ref"
reference="figmain:chessboard"}) [@moon1963line; @hoffman1964line]. By
altering the length and breadth of the chessboard (equivalently, by
changing the size of the complete graphs) the spectral properties of the
graph (namely, the spectral gap) can be changed. We identify different
regimes of optimal and suboptimal quantum search, elucidating how the
interplay between different choices of $r$ affect the algorithmic
performance. Finally, we summarize and discuss upon the results of the
article in Sec. [6](#sec:discussion){reference-type="ref"
reference="sec:discussion"}.

# Preliminaries {#sec:prelim}

First, we describe the framework of the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm. Consider
any graph $G$ with a set of $n$ vertices labelled $\{1,2,...n\}$ and a
Hamiltonian $H$, which is an Hermitian matrix of dimension $n$ that
encodes the connectivity of the underlying graph. In other words, we
demand that $H$ is *local*, i.e. its $(i,j)^{\mathrm{th}}$-entry is
non-zero if and only if node $i$ (or $i^{\mathrm{th}}$ edge) is adjacent
to node $j$ (or $j^{\mathrm{th}}$ edge) in $G$ (for example, $H$ could
be proportional to the graph's adjacency matrix). Then, evolution under
the Hamiltonian $H$ implements the continuous-time quantum walk on the
graph that it encodes. Without loss of generality, it is assumed that
$H$ has eigenvalues in the interval $[0,1]$ [^3].

As mentioned earlier the search Hamiltonian corresponding to the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm is given by
$$H_{\mathrm{search}}=H_{\mathrm{oracle}}+ r H.$$ We require that
$H_{\mathrm{oracle}}$ is local so that it perturbs the node $\ket{w}$ in
a way that affects only vertices (or edges) in its vicinity. We will
focus on the original formulation of the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm where
$H_{\mathrm{oracle}}=\ket{w}\bra{w}$ adds a local energy at node
$\ket{w}$, leaving the remaining vertices unaffected. In fact,
simulating this oracular Hamiltonian for a time $t$, corresponds to
$\ensuremath{\mathcal{O}}(t)$-queries to the oracle of the Grover's
search algorithm [@roland2003quantum]. The steps of this algorithm are
explained in
Algorithm [\[algo-cg-general\]](#algo-cg-general){reference-type="ref"
reference="algo-cg-general"}.

::: algorithm
Choose some $r> 0$ such that $H_{\mathrm{search}}=\ket{w}\bra{w}+rH$.

-   Prepare the $1$-eigenstate of $H$.\

-   Evolve the state of $1)$ under $H_{\mathrm{search}}$ for some time
    $T$.
:::

We note that our formulation of the $\ensuremath{\mathcal{C G}}$
algorithm is slightly more general than that of [@childs2004spatial],
where the authors consider the Hamiltonian
$H_{\mathrm{search}}= - r L - \ket{w}\bra{w}$, such that $L$ is the
Laplacian of the graph [@bollobas2013modern], and choose the inital
state $\ket{s}=n^{-1/2}\sum_i \ket{i}$ which is the 0-eigenstate of $L$.
Our formulation becomes equivalent to that of [@childs2004spatial] if we
set $H=I-\mathcal{L}$, where $\mathcal{L}$ is the normalized Laplacian
and by suitably rescaling $r$.

The essential parameter in
Algorithm [\[algo-cg-general\]](#algo-cg-general){reference-type="ref"
reference="algo-cg-general"} is the value of $r$, which has to be chosen
judiciously so that the state $\ket{\Psi(T)}$ prepared after step 2) has
a large overlap with the marked node
$$\alpha(T)=|\braket{w}{\Psi(T)}|,$$ for the minimum possible $T$. The
marked node can then be obtained from this final state via a measurement
on the state-space basis, or via amplitude amplification followed by
measurement.

## Running time of $\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm

To fully quantify the cost of running the $\ensuremath{\mathcal{C G}}$
algorithm, it is important to take into account not only the cost of
evolving the search Hamiltonian for a given time, but also the cost to
set-up the initial state and measure the final state. Furthermore, in
some prior works
 [@childs2004spatial; @childs2004spatial-dirac; @childs2014spatial-crystal]
amplitude amplification has been used in conjunction with Hamiltonian
evolution in order to find a marked node on lattices. To quantify the
cost of such a procedure we need to introduce the cost of implementing
the Grover oracle (the cost of evolving $H_{\text{oracle}}$ for constant
time), which we denote as $\mathcal{C}_w$.

We use the following notation for the different costs.  \

Setup cost $\mathcal{S}$

:   the cost of preparing the initial state of the algorithm
    ($1$-eigenstate of $H$). [^4] \

Time-evolution cost $\mathcal{T}$

:   The cost of implementing the time-evolution operator
    $e^{iTH_{\mathrm{search}}}$. A discrete simulation of this operator
    would require $O(T)$ queries to the Grover oracle [^5]. \

Measurement cost $\mathcal{M}$

:   The cost of performing a measurement in the state-space basis.

 \
Depending on the strategy used to obtain the marked node from the state
$\ket{\Psi(T)}$, the overall cost can be quantified as follows (constant
factors are omitted for simplicity):\
 \
**i) Amplitude Amplification**: Applying $1/\alpha(T)$ - rounds of the
quantum amplitude amplification procedure [@brassard2002quantum] results
in obtaining the marked node with constant probability. The overall
running time of the $\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$
algorithm along with amplitude amplification is
$$\label{eqmain:search-time-with-amp-amp}
T_{\mathrm{search}}=\dfrac{1}{\alpha(T)}\left(\mathcal{S}+\mathcal{T}+\mathcal{C}_w\right)+\mathcal{M}.$$
However, amplitude amplification is a discrete-time procedure, which
implies that the overall algorithm is no longer continuous-time.

Furthermore, as evident from
Eq. [\[eqmain:search-time-with-amp-amp\]](#eqmain:search-time-with-amp-amp){reference-type="eqref"
reference="eqmain:search-time-with-amp-amp"}, the setup cost plays a
crucial role in the overall running time of the algorithm. In fact in
prior works on the $\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$
algorithm, the *Setup cost* $\mathcal{S}$ and the cost of making a
measurement $\mathcal{M}$ have not been considered in order to compute
the overall running time.

It is important to guarantee that it is advantageous to run the quantum
walk, as opposed to using only amplitude amplification on the initial
state and bypassing the walk altogether. If the initial state of
Algorithm [\[algo-cg-general\]](#algo-cg-general){reference-type="ref"
reference="algo-cg-general"} has an overlap of $\sqrt{\epsilon}$ with
$\ket{w}$, the cost of the latter strategy is
$$\label{eqmain:adv-amp-amp}
T_{AA}=\frac{1}{\sqrt{\epsilon}}\left (\mathcal{S} + \mathcal{C}_w\right)+\mathcal{M},$$
where $\mathcal{C}_w$ is the cost of implementing the Grover oracle
(evolving $H_{\mathrm{oracle}}$ for constant time). Clearly for the CTQW
to be advantageous we need $T_{AA}$ to be larger than
$T_{\mathrm{search}}$ from
Eq. [\[eqmain:search-time-with-amp-amp\]](#eqmain:search-time-with-amp-amp){reference-type="eqref"
reference="eqmain:search-time-with-amp-amp"}.

In the case of the $\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$
algorithm, if the setup cost is reasonably large, such as for the
applications considered in [@ambainis2005coins; @ambainis2007quantum],
the aforementioned inequality is indeed satisfied and bypassing the
quantum walk will invariably be disadvantageous. Hence, the choice of
$r$ and $T$ should be such that the overhead due to amplitude
amplification is as low as possible, or in other words $\alpha(T)$ is as
large as possible.\
 \
**ii) Repetition**: By repeating the time-evolution followed by a
measurement in the state-space basis $1/\alpha(T)^2$-times would result
in obtaining the marked node with a high probability. The overall
running time of the procedure in this case is
$$\label{eqmain:search-time-with-repetition}
T_{\mathrm{search}}=\dfrac{1}{\alpha(T)^2}\left(\mathcal{S}+\mathcal{T}+\mathcal{M}\right).$$
Clearly, repeating the algorithm results in the overall running time
being quadratically slower (with respect to $1/\alpha(T)$) as compared
to that of amplitude amplification. However, if one assumes access only
to the time-evolution of $H_{\mathrm{search}}$, then repeating this
procedure is the only way to amplify the success probability.\
 \

## Optimality of the algorithm {#sec:def_optimality}

It is natural to ask, in this context, what is the minimum time needed
to find the marked node for any Hamiltonian $H$. From the seminal work
by Farhi and Gutmann [@farhi1998analog], it is easy to obtain the
following lower bound on the evolution time $T$ required to find
$\ket{w}$ $$\label{eqmain:lower-bound-search}
T=\Omega\left(\dfrac{1}{\sqrt{\epsilon}}\right).$$ For vertex-transitive
graphs, which informally means that there is no particular structure
that allows to distinguish a node from any other node, we have that
$\epsilon=1/n$, recovering the familiar Grover lower bound
$T=\Omega(\sqrt{n})$ [^6].

As such, throughout the article we shall say that the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm is
*optimal* for a given graph $G$ if Algorithm
[\[algo-cg-general\]](#algo-cg-general){reference-type="ref"
reference="algo-cg-general"} results in a state that has a constant
overlap with $\ket{w}$ after evolving for a time that matches the
aforementioned lower bound,
i.e. $T=\Theta\left(1/\sqrt{\epsilon}\right)$. In such a case, the
overall search time would scale as
$$T_{\mathrm{search}}=\mathcal{S}+\Theta\left(\dfrac{\mathcal{C}_w}{\sqrt{\epsilon}}\right)+\mathcal{M},$$
assuming the cost of implementing the walk evolution for time
$T=\Theta\left(1/\sqrt{\epsilon}\right)$ is dominated by the cost
$\mathcal{C}_w$ of implementing the oracle, i.e.,
$$\mathcal{T}=\Theta\left(\dfrac{\mathcal{C}_w}{\sqrt{\epsilon}}\right).$$
In this scenario, running the walk is advantageous as compared to simply
doing amplitude amplification on the initial state
(Eq. [\[eqmain:adv-amp-amp\]](#eqmain:adv-amp-amp){reference-type="eqref"
reference="eqmain:adv-amp-amp"}) when the set-up cost is considerably
larger than the cost of implementing the oracle.

It is worth noting that in order to quantify a speedup, one can also
compare the running time of quantum spatial search with the time
required by classical random walks to solve the same problem. In fact,
the time required by a classical random walk to find a marked node on
any graph, known as the *hitting time*, is bounded as follows:
$$\label{eqmain:hitting-time-bounds}
\dfrac{1}{\epsilon}\leq \mathrm{HT}(w) \leq \dfrac{1}{\Delta\epsilon},$$
where $\Delta$ is the spectral gap of the operator defining the random
walk (such as the normalized adjacency matrix or the graph Laplacian).

In fact, it has been established that discrete-time quantum walk search
algorithms
[@magniez2011search; @krovi2016quantum; @ambainis2019quadratic] as well
as the recent continuous-time quantum walk search algorithm we proposed
[@chakraborty2018finding], can find a marked node on any graph in square
root of the hitting time, resulting in a generic quadratic advantage.
However, such algorithms require a larger Hilbert space and can be seen
as quantum walks on the edges of the underlying graph. As such, in this
article we shall also compare the running time of the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm with the
*hitting time* of classical random walks, towards identifying the
regimes for which a quadratic speed-up can be obtained as well as the
limitations of this framework for quantum search.

# Performance of the $\mathbb{\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}}$ algorithm {#sec:performance_non_degenerate}

In this section we derive the main results characterizing the
performance of the $\ensuremath{\mathcal{C G}}$ algorithm. Let $H$ have
eigenvalues
$0\leq \lambda_1\leq \lambda_2\leq\cdots\lambda_{n-1}<\lambda_n=1$ with
the corresponding eigenvectors, $\ket{v_1},\cdots,\ket{v_n}$ such that
$$H\ket{v_i}=\lambda_i\ket{v_i}.$$ Also let the gap between the two
highest eigenvalues of $H$ (spectral gap) be given by
$$\Delta=1-\lambda_{n-1}.$$ It will be convenient to express the marked
node in the basis of the eigenstates of $H$ as
$$\label{eqmain:sol-in-eigenbasis}
\ket{w}=\sum_{i=1}^{n}a_i\ket{v_i}$$ and define the following set of
parameters $$\label{eqmain:Sk}
S_k=\sum_{i=1}^{n-1}\dfrac{|a_i|^2}{(1-\lambda_i)^k},$$ for integer
$k\geq 1$. These parameters depend only on the spectral properties of
the graph and the position of the marked node and turn out to be crucial
to understanding the algorithmic performance, as it is clear, for
example, in the studies of quantum search on
lattices [@childs2004spatial] and fractals
[@Boettcher_searchfractals_2017]. We note also that for
vertex-transitive graphs these parameters depend only on the eigenvalues
of $H$, as all the probabilities $|a_i|^2=1/n$.

Furthermore, we impose the following *spectral condition* that defines
the regime of validity of our analysis $$\label{eq:spectral_con}
\sqrt{\epsilon} < c \min\left\{\frac{S_1 S_2}{S_3},\Delta\sqrt{S_2}\right\},$$
where $c$ is a small positive constant. The reason why we need to impose
this condition will become clear in
Sec. [3.1](#sec:criticalpoint){reference-type="ref"
reference="sec:criticalpoint"}. In a nutshell, this condition ensures
that we can bound the error in our perturbative analysis and
furthermore, that the additive error we obtain in the final amplitude at
the marked node is small enough for our predictions to be meaningful.

In
subsection [3.3](#subsec:applicability-of-lemma-1){reference-type="ref"
reference="subsec:applicability-of-lemma-1"} we discuss the generality
of this condition and prove that it is fulfilled for any graph where
$\sqrt{\epsilon} \leq c \Delta$. However, it is more general than that
since it also includes the critical case of the 4d-lattice, where both
$\sqrt{\epsilon}$ and $\Delta$ scale as $\Theta(1/\sqrt{n})$.

Our main results regarding the performance of the algorithm are the
following. In subsection [3.1](#sec:criticalpoint){reference-type="ref"
reference="sec:criticalpoint"}, we demonstrate that the optimal choice
for $r$ is $r=S_1$, provided the spectral condition from
Eq. [\[eq:spectral_con\]](#eq:spectral_con){reference-type="eqref"
reference="eq:spectral_con"} is respected. In this case we show that the
maximum amplitude at the solution is reached at time
$$\label{eqmain:evolution-time-cg-algorithm}
T=\Theta\left(\dfrac{1}{\sqrt{\epsilon}}\dfrac{\sqrt{S_2}}{S_1}\right)$$
and is given by $$\label{eq:maxamp}
\nu \approx \dfrac{S_1}{\sqrt{S_2}}.$$ Furthermore, we show that
essentially the same behavior is maintained if we choose $r$ within a
window of $|r-S_1|= O(\sqrt{\epsilon S_2})$. If $r$ is chosen outside
this interval, we show in
Sec. [3.2](#sec:failure_critpoint){reference-type="ref"
reference="sec:failure_critpoint"} that the maximum amplitude reached is
$o(S_1/\sqrt{S_2})$, independently of the evolution time we choose. This
implies that $\Theta(S_1/\sqrt{S_2})$ is the maximum amplitude
achievable for any time and any choice of $r$.

Consequently, we can draw the following *necessary and sufficient
condition* for optimal quantum search (in the sense discussed in
Sec. [2.2](#sec:def_optimality){reference-type="ref"
reference="sec:def_optimality"}), within the regime of validity of our
analysis.

::: {#thm:optimalityCG .theorem}
**Theorem 1** (Optimality of quantum search). *Let $H$ be such that the
spectral condition from
Eq. [\[eq:spectral_con\]](#eq:spectral_con){reference-type="eqref"
reference="eq:spectral_con"} is fulfilled. Then the
$\ensuremath{\mathcal{C G}}$ algorithm is optimal iff
$S_1/\sqrt{S_2}=\Theta(1)$.*
:::

The proof of this result follows directly from the statements above. If
$S_1/\sqrt{S_2}=\Theta(1)$, choosing $r$ sufficiently close to $S_1$
ensures that we obtain a constant amplitude at the marked node after
$T= \Theta\left(1/\sqrt{\epsilon}\right)$ (see Eqs.
[\[eqmain:evolution-time-cg-algorithm\]](#eqmain:evolution-time-cg-algorithm){reference-type="eqref"
reference="eqmain:evolution-time-cg-algorithm"} and
[\[eq:maxamp\]](#eq:maxamp){reference-type="eqref"
reference="eq:maxamp"}), matching the lower bound in
Eq. [\[eqmain:lower-bound-search\]](#eqmain:lower-bound-search){reference-type="eqref"
reference="eqmain:lower-bound-search"}. On the other hand, since
$\Theta(S_1/\sqrt{S_2})$ is the maximum amplitude achievable, if we have
that $S_1/\sqrt{S_2}=o(1)$ the algorithm is never optimal.

With this necessary and sufficient condition, many hitherto published
results showing that this algorithm is optimal for specific graphs can
be recovered , without the need to do a graph specific analysis
[@childs2004spatial; @janmark2014global; @novo2015systematic; @wong2016quantum; @wong2016quantum2; @philipp2016continuous; @wong2016laplacian; @wong2016engineering; @chakraborty2016spatial; @chakraborty2017optimal; @glos2018vertices; @glos2018optimal; @wong2018quantum].
For example, it is possible to see, from the fact that
$S_1/\sqrt{S_2}\geq \sqrt{\Delta}$ (see Lemma
[5](#lem:nu-bound-1){reference-type="ref" reference="lem:nu-bound-1"}),
that search is optimal for any Hamiltonian $H$ with a constant spectral
gap, and thus recover the main result from
Ref. [@chakraborty2016spatial]. This encompasses graphs such as
Erdös-Renyi random graphs, complete bipartite graphs or strongly regular
graphs. Additionally, our results also predict optimality for graphs
such as hypercubes, lattices of dimension greater than four even though
they do not exhibit a constant spectral gap.

One can wonder whether a simpler and more intuitive sufficient condition
for optimality can be derived from
Theorem [1](#thm:optimalityCG){reference-type="ref"
reference="thm:optimalityCG"}. To our knowledge, all previously known
examples of graphs whose spectral gap is large enough compared to
$\sqrt{\epsilon}$ can be searched by quantum walk in optimal time (e.g.
lattices of dimension $d\geq5$), so one could think that
$\sqrt{\epsilon}\ll \Delta$ is a sufficient condition for optimal
quantum search. We show explicitly that this is not the case -- there
exist graphs for which the spectral condition is satisfied and the
spectral gap is such that $\sqrt{\epsilon}\ll \Delta$ but nevertheless
the value of $S_1/\sqrt{S_2}$ decreases with the size of the graph which
implies suboptimality. This is the case, for example, for the normalized
adjacency matrix of the Rook's graph in some regime (see
Sec. [5](#sec:quantum-walk-chessboard){reference-type="ref"
reference="sec:quantum-walk-chessboard"}). In fact, this example shows
that this quantum walk algorithm can also be slower than the square root
of the hitting time of the corresponding classical walk.

## Performance of quantum search at the critical point ($r\approx S_1$) {#sec:criticalpoint}

Here we present one of our main results, which characterizes the
performance of quantum search when the parameter $r$ is close to its
optimal value.  \

::: {#lem_main:search-highest-estate .theorem}
**Theorem 2**. *Let $H$ be such that the spectral condition of
Eq. [\[eq:spectral_con\]](#eq:spectral_con){reference-type="eqref"
reference="eq:spectral_con"} is obeyed, with $S_k$ defined as in
Eq. [\[eqmain:Sk\]](#eqmain:Sk){reference-type="eqref"
reference="eqmain:Sk"}. By choosing $r=S_1$ and
$$T=\Theta\left(\dfrac{1}{\sqrt{\epsilon}}\dfrac{\sqrt{S_2}}{S_1}\right),$$
Algorithm [\[algo-cg-general\]](#algo-cg-general){reference-type="ref"
reference="algo-cg-general"} prepares a state $\ket{f}$ such that
$\nu=|\braket{w}{f}|=\Theta\left(S_1/\sqrt{S_2}\right)$.*
:::

 \
As defined previously, the Hamiltonian $H$ has eigenvalues $\lambda_i$
and corresponding eigenvectors $\ket{v_i}$. We denote each eigenvalue of
$rH$ as $\lambda'_{i}:=r\lambda_{i}$. First, we express the solution
state $\ket{w}$ in terms of the eigenstates of $H$. We have
$$\label{eqmain:solution_expanded}
\left|w\right\rangle =\sum_{i=1}^{n}a_{i}\left|v_{i}\right\rangle,$$
such that $|a_n|=\sqrt{\epsilon}$. Now we find the condition for which a
quantum state $\ket{\psi}$ defined as
$$\left|\psi\right\rangle =\sum_{i=1}^{n} b_{i}\left|v_{i}\right\rangle,$$
is an eigenstate of $H_{\mathrm{search}}=rH+H_{\mathrm{oracle}}$. That
is, $$\begin{aligned}
H_{\mathrm{search}}\left|\psi\right\rangle  & =E\ket{\psi}\\
\implies\sum_{i}\lambda_{i}'b_{i}\left|v_{i}\right\rangle +\underbrace{\left\langle w|\psi\right\rangle }_{=:\gamma}\left|w\right\rangle &= E\ket{\psi}\\
\implies\sum_{i}\left(\lambda_{i}'b_{i}+\gamma a_{i}\right)\left|v_{i}\right\rangle &=\sum_{i}E b_{i}\left|v_{i}\right\rangle.
\end{aligned}$$ This implies that $$\label{eq:coeff-estates-Hsearch}
b_{i}=\frac{\gamma a_{i}}{E-\lambda'_{i}}.$$ Note that
$$\gamma=\left\langle w|\psi\right\rangle =\sum_{i}a^*_{i}b_{i}$$ where
we substitute for $b_{i}$ to get $$\label{eq:condition_new_eigenvalue}
1=\sum_{i}\dfrac{|a_{i}|^{2}}{E-\lambda_{i}'}.$$ This equation gives us
the condition for $E$ to be an eigenvalue of $H_{\text{search}}$. It can
be seen that the RHS of
[\[eq:condition_new_eigenvalue\]](#eq:condition_new_eigenvalue){reference-type="eqref"
reference="eq:condition_new_eigenvalue"} is a monotonically decreasing
function of $E$ within each interval $]\lambda'_{i-1},\lambda'_{i}[$ and
$\lambda'_{i}$ are poles of this function. This guarantees that each of
these intervals, as well as as the interval $]\lambda'_n, +\infty[$,
contains exactly one eigenvalue.

We are interested in finding the two largest eigenvalues of
$H_{\text{search}}$. We choose $r=S_1$ and will look for solutions of
Eq. [\[eq:condition_new_eigenvalue\]](#eq:condition_new_eigenvalue){reference-type="eqref"
reference="eq:condition_new_eigenvalue"} of the form
$E=\lambda'_n+\delta$, within the interval $|\delta| < c' S_1 \Delta$
for some small constant $c'$. Indeed, we will demonstrate that there are
two solutions within this interval.

To show this, we rewrite
Eq. [\[eq:condition_new_eigenvalue\]](#eq:condition_new_eigenvalue){reference-type="eqref"
reference="eq:condition_new_eigenvalue"} in terms of $\delta$ and choose
$r=S_1$ to obtain $$\label{eq:condition-new-evalue-2}
\frac{\epsilon}{\delta}+\sum_{i<n}\frac{|a_i|^2}{S_1\Delta_i+\delta}=1,$$
where $\Delta_i=\lambda_n-\lambda_i$. Finding solutions of this equation
is equivalent to finding the zeros of a function $F(\delta)$ which can
be written as $$\begin{aligned}
F(\delta)&=\dfrac{\epsilon}{\delta}+\sum_{i<n}\dfrac{|a_i|^2}{S_1\Delta_i+\delta}-1\\
         &=\dfrac{\epsilon}{\delta}+\sum_{i<n}\dfrac{|a_i|^2}{S_1\Delta_i}\left(1+\sum_{k=1}^{\infty}\dfrac{(-\delta)^k}{S^k_1\Delta^k_i}\right)-1\\
         &= \dfrac{\epsilon}{\delta}-\dfrac{S_2\delta}{S_1^2}+\sum_{i<n}\dfrac{|a_i|^2\delta^2}{S_1^3\Delta_i^3}\sum_{k=0}^{\infty}
         \dfrac{(-\delta)^k}{\Delta^k_i S_1^k} \\
          &=\dfrac{\epsilon}{\delta}\left\{1-\dfrac{S_2\delta^2}{S_1^2\epsilon}+f(\delta)\right\}\label{eq:Fdelta},
\end{aligned}$$ The term $f(\delta)$ can be seen as an error term that
can be bounded as $$\begin{aligned}
\label{eq:error-bound-taylor}
|f(\delta)|\leq\dfrac{S_3|\delta|^3}{S^3_1\epsilon}\dfrac{1}{1-\frac{|\delta|}{S_1\Delta}}\leq \dfrac{S_3|\delta|^3}{S^3_1\epsilon}\dfrac{1}{1-c'}.
\end{aligned}$$ If this error term was neglected, the function
$F(\delta)$ would have zeros at $\pm \delta_0$, where
$$\label{eq:def_delta0}
\delta_0=\sqrt{\epsilon} \dfrac{S_{1}}{\sqrt{S_2}}.$$ We will see that
the presence of the term $f(\delta)$ introduces a relative error in
these solutions i.e., there are two solutions $\delta_{\pm}$ in the
intervals $$\begin{aligned}
%\label{eq:solution-eigenvalue-equation}
\delta_+&\in\left[(1-\eta)\delta_0,(1+\eta)\delta_0\right] \label{eq:interval_deltaplus}\\
\delta_-&\in\left[-(1+\eta)\delta_0,-(1-\eta)\delta_0\right]\label{eq:interval_deltaminus},
\end{aligned}$$ where the relative error is given by
$$\label{eq:eta-ratio}
\eta=\dfrac{S_3\sqrt{\epsilon}}{S^{3/2}_2}.$$ To demonstrate this let us
focus on the interval given by
Eq. [\[eq:interval_deltaplus\]](#eq:interval_deltaplus){reference-type="eqref"
reference="eq:interval_deltaplus"} and show that $F(\delta)$ has a zero
in this interval (an analogous derivation can be done for the other
interval in
Eq. [\[eq:interval_deltaminus\]](#eq:interval_deltaminus){reference-type="eqref"
reference="eq:interval_deltaminus"}). If we take
$\delta_+=\delta_0(1+\eta')$, where $|\eta'|\leq \eta$ we can bound
$|f(\delta_+)|$ as $$\begin{aligned}
\label{eq:error-bound2}
|f(\delta_+)|\leq\dfrac{S_3\delta_0^3(1+\eta)^3}{S^3_1\epsilon(1-c')}\leq \dfrac{\eta(1+\eta)^3}{(1-c')},
\end{aligned}$$ where we used the definitions from
Eqs. [\[eq:def_delta0\]](#eq:def_delta0){reference-type="eqref"
reference="eq:def_delta0"} and
[\[eq:eta-ratio\]](#eq:eta-ratio){reference-type="eqref"
reference="eq:eta-ratio"}. Note that the spectral condition imposed in
Eq. [\[eq:spectral_con\]](#eq:spectral_con){reference-type="eqref"
reference="eq:spectral_con"} guarantees that $\eta$ is small. Using this
condition we can show that $$\label{eq:bound_eta}
    \eta\leq c \frac{S_1}{\sqrt{S_2}}\leq c,$$ where we also used the
fact that $\frac{S_1}{\sqrt{S_2}}\leq 1$ which is demonstrated later in
Lemma [5](#lem:nu-bound-1){reference-type="ref"
reference="lem:nu-bound-1"}.

On the other hand, from
[\[eq:Fdelta\]](#eq:Fdelta){reference-type="eqref"
reference="eq:Fdelta"} we have that $$\begin{aligned}
\label{eq:Fdeltaplus}
 F(\delta_+)=\dfrac{\epsilon}{\delta_+}\left\{2\eta'+\eta'^2+f(\delta_+)\right\}.   
\end{aligned}$$ Given the bound
[\[eq:error-bound2\]](#eq:error-bound2){reference-type="eqref"
reference="eq:error-bound2"}, we see that the RHS of
[\[eq:Fdeltaplus\]](#eq:Fdeltaplus){reference-type="eqref"
reference="eq:Fdeltaplus"} is positive if $\eta'=\eta$ and negative if
$\eta'=-\eta$, provided $c$ and $c'$ are sufficiently small. This shows
that indeed $\delta_+$ is in the interval from
Eq. [\[eq:interval_deltaplus\]](#eq:interval_deltaplus){reference-type="eqref"
reference="eq:interval_deltaplus"}. The same reasoning can be used to
show that $\delta_-$ belongs to the interval in
Eq. [\[eq:interval_deltaminus\]](#eq:interval_deltaminus){reference-type="eqref"
reference="eq:interval_deltaminus"}.

We can now verify the validity of the assumption
$\delta_+\leq c' S_1 \Delta$, for some small constant $c'$, which was
necessary to obtain the bound in
Eq. [\[eq:error-bound-taylor\]](#eq:error-bound-taylor){reference-type="eqref"
reference="eq:error-bound-taylor"}. We have that $$\begin{aligned}
    \delta_+&\leq \delta_0 (1+|\eta|)\\
    &\leq \frac{S_1}{\sqrt{S_2}}\sqrt{\epsilon}(1+c)\\
    &\leq c (1+c) S_1 \Delta,
\end{aligned}$$ where in the second step we used
Eqs. [\[eq:bound_eta\]](#eq:bound_eta){reference-type="eqref"
reference="eq:bound_eta"} and
[\[eq:def_delta0\]](#eq:def_delta0){reference-type="eqref"
reference="eq:def_delta0"} and in the last step we used the spectral
condition [\[eq:spectral_con\]](#eq:spectral_con){reference-type="eqref"
reference="eq:spectral_con"}. Hence, for sufficiently small $c$ the
condition $\delta_+\leq c' S_1 \Delta$ is verified.

Now that we have obtained two approximate solutions to
Eq. [\[eq:condition_new_eigenvalue\]](#eq:condition_new_eigenvalue){reference-type="eqref"
reference="eq:condition_new_eigenvalue"}
$E_{\pm}=\lambda'_n+\delta_{\pm}$, we proceed to compute the overlap of
the corresponding eigenstates $\ket{\psi_{\pm}}$ with the marked node.
From the normalization condition of the eigenstates of
$H_{\mathrm{search}}$, we have $\sum |b_{i}|^{2}=1$. So from
Eq. [\[eq:coeff-estates-Hsearch\]](#eq:coeff-estates-Hsearch){reference-type="eqref"
reference="eq:coeff-estates-Hsearch"}, we can obtain the following
equation for $\gamma_{\pm}=\braket{w}{\psi_{\pm}}$ $$\begin{aligned}
&\sum_{i}\frac{|\gamma_\pm a_{i}|^2}{\left(E_\pm-\lambda'_{i}\right)^{2}}=1\\
\implies &|\gamma_\pm|^2=\left[\frac{\epsilon}{\delta_\pm^{2}}+\sum_{i<n}\frac{|a_{i}|^{2}}{\left(E_\pm-\lambda'_{i}\right)^{2}}\right]^{-1}\\
\implies |\gamma_\pm|^2 &=\left[\frac{\epsilon}{\delta_\pm^{2}}+\sum_{i<n}\frac{|a_{i}|^{2}}{S_1^2\Delta_i^2\left(1+\frac{\delta_\pm}{S_1\Delta_i}\right)^{2}}\right]^{-1}.
\end{aligned}$$

Replacing the values of $\delta^\pm$ and neglecting terms scaling as
$\Theta\left(\eta^2\right)$ we obtain $$\begin{aligned}
&|\gamma_\pm|^2=\dfrac{S_1^2}{2S_2}\left(1+\Theta\left(\eta\right)\right)\\
\implies & |\gamma_\pm|=\dfrac{S_1}{\sqrt{2S_2}}\left(1+\Theta\left(\eta\right)\right)      
\end{aligned}$$ Without loss of generality we can choose the eigenbasis
of $H_{search}$ such that the overlaps $\gamma_{\pm}$ are positive.
Furthermore, we can calculate the values of
$b^\pm_{n}=\braket{\psi_{\pm}}{v_n}$ from
Eq. [\[eq:coeff-estates-Hsearch\]](#eq:coeff-estates-Hsearch){reference-type="eqref"
reference="eq:coeff-estates-Hsearch"}, which yields
$$b^\pm_{n}=\gamma_\pm\frac{a_{n}}{\delta_\pm}.$$ Substituting the
values of $\delta_\pm$ and $\gamma_\pm$, we obtain that,
$$\begin{aligned}
b^\pm_n&=\pm \dfrac{1}{\sqrt{2}}\left(1+\Theta(\eta)\right).
\end{aligned}$$ So the starting state can be written as
$$\left|v_{n}\right\rangle = \dfrac{\ket{\psi_+}-\ket{\psi_-}}{\sqrt{2}}+\ket{\Phi},$$
where $\ket{\Phi}$ is an unnormalized quantum state such that
$\left\lVert \ket{\Phi} \right\rVert\leq \Theta\left(\eta\right)$.

So evolving $\ket{v_n}$ under $H_{\mathrm{search}}$ for a time $t$
results in $$\begin{aligned}
&e^{-iH_{\mathrm{search}}t}\left|v_{n}\right\rangle\\
&=\frac{1}{\sqrt{2}}e^{-i\lambda'_{n}t}\left(e^{-i\delta_+ t}\left|v_{+}\right\rangle -e^{-i\delta_- t}\left|v_{-}\right\rangle \right)+\Theta\left(\eta\right).
\end{aligned}$$ Thus after a time
$T=\frac{\pi}{2\delta_0}=\Theta(\frac{1}{\sqrt{\epsilon}}\frac{\sqrt{S_2}}{S_1})$,
up to a global phase, we end up in the state
$$\ket{f}=\dfrac{\ket{v_+}+\ket{v_-}}{\sqrt{2}}+\ket{\Phi'},$$ such that
$\left\lVert \ket{\Phi'} \right\rVert\leq \Theta\left(\eta\right)$. The
overlap of $\ket{f}$ with the solution state is given by
$$\begin{aligned}
\nu&=|\braket{w}{f}|\\
       &=\dfrac{S_1}{\sqrt{S_2}}\left(1+\Theta\left(\eta\frac{\sqrt{S_2}}{S_1}\right)\right)=\Theta\left(\dfrac{S_1}{\sqrt{S_2}}\right),
\end{aligned}$$ where we have used the spectral condition
[\[eq:spectral_con\]](#eq:spectral_con){reference-type="eqref"
reference="eq:spectral_con"} which ensures that
$$\eta\dfrac{\sqrt{S_2}}{S_1}=\dfrac{\sqrt{\epsilon}S_3}{S_1 S_2}\leq c.$$
$\Box$\
 \
Subsequently, we show that essentially the same behavior is maintained
if we choose any $r$ within a small enough interval around $S_1$.  \

::: {#lem_main:robustness_r .theorem}
**Theorem 3**. *Let $H$ be such that the spectral condition of
Eq. [\[eq:spectral_con\]](#eq:spectral_con){reference-type="eqref"
reference="eq:spectral_con"} is obeyed and $r$ be chosen such that
$$\label{eq:ropt_deviation}
|r-S_1|\leq |\beta| \sqrt{\epsilon S_2},$$ for some small constant
$\beta$ such that $|\beta|\ll 1$. After a time
$$T=\Theta\left(\dfrac{1}{\sqrt{\epsilon}}\dfrac{\sqrt{S_2}}{S_1}\right),$$
Algorithm [\[algo-cg-general\]](#algo-cg-general){reference-type="ref"
reference="algo-cg-general"} prepares a state $\ket{f}$ such that
$\nu=|\braket{w}{f}|=\Theta\left(S_1/\sqrt{S_2}\right)$.*
:::

 \
The proof of this result follows from the fact that, for any $r$ within
this interval, we still have that the value of
$|\delta_{\pm}|=\Theta(\delta_0)$. More precisely, by rewriting
Eq. [\[eq:Fdelta\]](#eq:Fdelta){reference-type="eqref"
reference="eq:Fdelta"} for arbitrary $r$ we have
$$F(\delta)= \frac{\epsilon}{\delta}\left\{1+\frac{\delta }{\epsilon }\left(\frac{S_1}{r}-1\right)- \frac{S_2\delta^2}{r^2\epsilon}\right\}$$
which will have two zeros in the intervals $$\begin{aligned}
\delta_+&\in\left[(1-\eta)\delta^{(+)}_0,(1+\eta)\delta_0^{(+)}\right] \label{eq:interval_deltaplus}\\
\delta_-&\in\left[-(1+\eta)\delta^{(-)}_0,-(1-\eta)\delta^{(-)}_0\right]\label{eq:interval_deltaminus},
\end{aligned}$$ where
$$\delta_0^{(\pm)}=\left|\frac{S_1\sqrt{\epsilon}}{\sqrt{S_2}}\left(\frac{\beta}{2}\pm \sqrt{1+\frac{\beta^2}{4}}\right)\right|+\mathcal{O}(\epsilon)$$
which is of the same order of the value $\delta_0$ from
Eq. [\[eq:def_delta0\]](#eq:def_delta0){reference-type="eqref"
reference="eq:def_delta0"}. Hence, with analogous arguments to those
used in the proof of
Theorem [2](#lem_main:search-highest-estate){reference-type="ref"
reference="lem_main:search-highest-estate"} we conclude that a deviation
to the optimal value of $r$ as in
Eq. [\[eq:ropt_deviation\]](#eq:ropt_deviation){reference-type="eqref"
reference="eq:ropt_deviation"}, only changes the maximum amplitude and
the evolution time needed to reach this amplitude by constant factors.
$\Box$\
 \

## Failure of the algorithm away from $\mathbf{r\approx S_1}$ {#sec:failure_critpoint}

Previously, we have established that Algorithm
[\[algo-cg-general\]](#algo-cg-general){reference-type="ref"
reference="algo-cg-general"} prepares a state with an overlap of
$\Theta(S_1/\sqrt{S_2})$ with the marked vertex for any choice of $r$
within the interval $$\label{eq:robust-range-of-r}
r^* \in \left[S_1-\Theta\left(\sqrt{S_2\epsilon}\right), S_1+\Theta\left(\sqrt{S_2\epsilon}\right) \right],$$
after a time
$$T=\Theta\left(\dfrac{1}{\sqrt{\epsilon}}\dfrac{\sqrt{S_2}}{S_1}\right).$$

In this section we prove that for any choice of $r$ outside the window
mentioned in
Eq. [\[eq:robust-range-of-r\]](#eq:robust-range-of-r){reference-type="eqref"
reference="eq:robust-range-of-r"}, the amplitude of the algorithm is
less than $S_1/\sqrt{S_2}$, irrespective of $T$.  \

::: {#lem:sub-optimality-for-any-r .theorem}
**Theorem 4**. *For any $r\geq 0$, such that $r \notin r^*$,
$$|\braket{w}{e^{-iH_{\mathrm{search}}T}|v_n}|\leq o\left(\dfrac{S_1}{\sqrt{S_2}}\right),$$
$\forall T\geq 0$.*
:::

 \
In order to derive this, we require all the eigenvalues and eigenvectors
of $H_{\mathrm{search}}$. As such we consider that $H_{\mathrm{search}}$
has eigenvalues $E_n > E_{n-1}>\cdots \geq E_1$, such that
$H_{\mathrm{search}}\ket{\psi_i}=E_i\ket{\psi_i}$. As before, we
consider that the eigenvectors and corresponding eigenvalues of $H$ are
$\lambda_i$ and $\ket{v_i}$, respectively.

Then for $1\leq \alpha \leq n$ let
$$\ket{\psi_\alpha}=\sum_{i=1}^n b^{(\alpha)}_i\ket{v_i},$$ and define
$$\label{eq:gamma-alpha}
\gamma_\alpha =\braket{w}{\psi_\alpha}.$$

So, by using the fact that
$H_{\mathrm{search}}\ket{\psi_i}=E_i\ket{\psi_i}$, we obtain
$$\label{eq:b-i-alpha}
b^{(\alpha)}_i=\dfrac{\gamma_\alpha a_i}{E_\alpha - r \lambda_i},~~1\leq\alpha\leq n.$$
For all $1\leq \alpha \leq n$, we use the definition of $\gamma_\alpha$
in Eq. [\[eq:gamma-alpha\]](#eq:gamma-alpha){reference-type="eqref"
reference="eq:gamma-alpha"} and the expression for $b^{(\alpha)}_i$ in
Eq. [\[eq:b-i-alpha\]](#eq:b-i-alpha){reference-type="eqref"
reference="eq:b-i-alpha"} to obtain $$\begin{aligned}
\label{eq:eigenvalue-condition-alpha}
F(E_{\alpha}):=\sum_{i=1}^n \dfrac{|a_i|^2}{E_\alpha-r\lambda_i}=1.
\end{aligned}$$

From the normalization condition, $\sum_i |b^{(\alpha)}_i|^2=1$, for
every $\alpha$, we also obtain that $$\label{eq:gamma-alpha2}
\dfrac{1}{|\gamma_\alpha|^2}=\sum_{i=1}^n \dfrac{|a_i|^2}{(E_\alpha-r\lambda_i)^2}.$$

Now, $$\begin{aligned}
\braket{w}{e^{-iH_{\mathrm{search}}t}|v_n}&=\sum_{\alpha}e^{-iE_\alpha t}\braket{w}{\psi_\alpha}\braket{\psi_\alpha}{v_n}\\
                                          &=\sqrt{\epsilon}\sum_{\alpha}e^{-iE_\alpha t}\gamma_\alpha b^{(\alpha) *}_n\\                                        
\label{eq:final-amplitude-any-t}                                          
                                          &=\sqrt{\epsilon}\sum_{\alpha} \dfrac{|\gamma_\alpha|^2 e^{-iE_\alpha t}}{E_\alpha -r},
\end{aligned}$$ where in the last line we have replaced the value of
$b^{(\alpha)}_n$ from
Eq. [\[eq:b-i-alpha\]](#eq:b-i-alpha){reference-type="eqref"
reference="eq:b-i-alpha"}.

Note that from the condition that the amplitude at $t=0$ is
$\sqrt{\epsilon}$ we obtain $$\label{eq:initial-amplitude}
\sum_{\alpha=1}^n \dfrac{|\gamma_\alpha|^2}{E_{\alpha}-r}=1.$$

Now we shall consider the following two cases, each of which we treat
differently: (i) When $r>r^*$ and (ii) $r<r^*$.\
 \
**(i) $\mathbf{r>r^*}$**: We first use
Eq. [\[eq:final-amplitude-any-t\]](#eq:final-amplitude-any-t){reference-type="eqref"
reference="eq:final-amplitude-any-t"} and
Eq. [\[eq:initial-amplitude\]](#eq:initial-amplitude){reference-type="eqref"
reference="eq:initial-amplitude"} to obtain that
$$\label{eq:upper-bound-amplitude}
|\braket{w}{e^{-iH_{\mathrm{search}}t}|v_n}|\leq \dfrac{2\sqrt{\epsilon}|\gamma_n|^2}{E_n-r}-\sqrt{\epsilon}.$$

Let $E_n=r+\delta_+$ and $\Delta_j=1-\lambda_j$. From
Eq. [\[eq:gamma-alpha2\]](#eq:gamma-alpha2){reference-type="eqref"
reference="eq:gamma-alpha2"} we have $$\begin{aligned}
 \dfrac{1}{|\gamma_n|^2}&\geq \dfrac{\epsilon}{\delta^2_+}
\label{eq:upper-bound-gamma-n}\\
\implies |\gamma_n|^2&\leq \dfrac{\delta^2_+}{\epsilon}.
\end{aligned}$$

Substituting this into
Eq. [\[eq:upper-bound-amplitude\]](#eq:upper-bound-amplitude){reference-type="eqref"
reference="eq:upper-bound-amplitude"}, we get
$$\label{eq:upper-bound-amplitude-2}
|\braket{w}{e^{-iH_{\mathrm{search}}t}|v_n}|\leq \dfrac{2\delta_+}{\sqrt{\epsilon}}$$

Next using the fact that $F(E_n)=1$
(Eq. [\[eq:eigenvalue-condition-alpha\]](#eq:eigenvalue-condition-alpha){reference-type="eqref"
reference="eq:eigenvalue-condition-alpha"}), we obtain an upper bound on
$\delta_+$ as follows $$\begin{aligned}
&\dfrac{\epsilon}{\delta_+}+\sum_{j=1}^{n-1}\dfrac{|a_j|^2}{E_n-r+r\Delta_j}=1\\
&\implies \dfrac{\epsilon}{\delta_+}+\dfrac{S_1}{r}>1\\
\label{eq:upper-bound-delta-+}
&\implies \delta_+ < \dfrac{\epsilon r}{r-S_1}.
\end{aligned}$$ Next we substitute the upper bound on $\delta_+$ into
Eq. [\[eq:upper-bound-amplitude-2\]](#eq:upper-bound-amplitude-2){reference-type="eqref"
reference="eq:upper-bound-amplitude-2"} to obtain
$$|\braket{w}{e^{-iH_{\mathrm{search}}t}|v_n}|\leq \dfrac{2\sqrt{\epsilon}r}{S_1-r}.$$
For any $r=S_1+\omega\left(S_2\sqrt{\epsilon}\right)$, we indeed obtain
that
$$|\braket{w}{e^{-iH_{\mathrm{search}}t}|v_n}|\leq o\left(\dfrac{S_1}{\sqrt{S_2}}\right).$$\
 \
(ii) **$\mathbf{r<r^*}$: **In this region, the proof is similar in
spirit to the case where $r>r^*$. Here we can bound the amplitude by
bounding the value of $\delta_-$ where $E_{n-1}=r-\delta_-$.

In fact as before, using
Eq. [\[eq:final-amplitude-any-t\]](#eq:final-amplitude-any-t){reference-type="eqref"
reference="eq:final-amplitude-any-t"} and
Eq. [\[eq:initial-amplitude\]](#eq:initial-amplitude){reference-type="eqref"
reference="eq:initial-amplitude"} to obtain that
$$\label{eq:upper-bound-amplitude-left}
|\braket{w}{e^{-iH_{\mathrm{search}}t}|v_n}|\leq \dfrac{2\sqrt{\epsilon}|\gamma_{n-1}|^2}{\delta_-}+\sqrt{\epsilon}.$$
From Eq. [\[eq:gamma-alpha\]](#eq:gamma-alpha){reference-type="eqref"
reference="eq:gamma-alpha"}, it is easy to obtain that $$\begin{aligned}
\label{eq:upper-bound-gamma-n-left}
|\gamma_{n-1}|^2\leq \dfrac{\delta^2_-}{\epsilon}.
\end{aligned}$$

This gives us $$\label{eq:upper-bound-amplitude-2-left}
|\braket{w}{e^{-iH_{\mathrm{search}}t}|v_n}|\leq \dfrac{2\delta_-}{\sqrt{\epsilon}}+\sqrt{\epsilon}$$

Here we use the fact that $F(E_{n-1})=1$ to obtain an upper bound on
$\delta_-$. We have, $$\begin{aligned}
&-\dfrac{\epsilon}{\delta_-}+\sum_{j=1}^{n-1}\dfrac{|a_j|^2}{-\delta_-+r\Delta_j}=1\\
&\implies -\dfrac{\epsilon}{\delta_-}+\dfrac{S_1}{r}<1~~~~~~[\because~\delta_-< r\Delta]\\
\label{eq:upper-bound-delta--}
&\implies \delta_- < \dfrac{\epsilon r}{S_1-r}.
\end{aligned}$$ We now substitute the upper bound on $\delta_-$ into
Eq. [\[eq:upper-bound-amplitude-2-left\]](#eq:upper-bound-amplitude-2-left){reference-type="eqref"
reference="eq:upper-bound-amplitude-2-left"} to obtain
$$|\braket{w}{e^{-iH_{\mathrm{search}}t}|v_n}|\leq \dfrac{2\sqrt{\epsilon}r}{r-S_1}+\sqrt{\epsilon}.$$
Thus any $r=S_1-\omega\left(S_2\sqrt{\epsilon}\right)$, we indeed obtain
that
$$|\braket{w}{e^{-iH_{\mathrm{search}}t}|v_n}|\leq o\left(\dfrac{S_1}{\sqrt{S_2}}\right),$$
where in the last line we use the fact that we are in a regime where
$\sqrt{\epsilon}=o\left(S_1/\sqrt{S_2}\right)$.\
 \
This concludes the proof. $\Box$\

## Validity of the spectral condition and implications to algorithmic performance {#subsec:applicability-of-lemma-1}

We have seen that the maximum amplitude at the marked node is determined
by the ratio $S_1/\sqrt{S_2}$ and hence it is important to obtain upper
and lower bounds on this quantity, given any $H$. We do so via the
following lemma:\
 \

::: {#lem:nu-bound-1 .lemma}
**Lemma 5**. *If $S_1,~S_2$ and $\epsilon$ are defined as in
Lemma [2](#lem_main:search-highest-estate){reference-type="ref"
reference="lem_main:search-highest-estate"}, then
$$\sqrt{\Delta(1-\epsilon)}\leq \frac{S_1}{\sqrt{S_2}} \leq 1.$$*
:::

 \
 \
The lower bound is obtained in a straightforward manner. Observe that
$$\begin{aligned}
\dfrac{S_1}{\sqrt{S_2}}&=\frac{\sum_{i<n}\frac{|a_{i}|^{2}}{1-\lambda_{i}}}{\sqrt{\sum_{i<n}\frac{|a_{i}|^{2}}{\left(1-\lambda{}_{i}\right)^{2}}}}\\
   &\geq \sqrt{\Delta\sum_{i<n}\frac{|a_{i}|^{2}}{1-\lambda_{i}}}\geq\sqrt{\Delta(1-\epsilon)}=\Theta\left(\sqrt{\Delta}\right),
\end{aligned}$$ It is possible to show that this bound is in fact tight.
For example, we can construct a normalized Hamiltonian for which
$|a_i|^2=1/n$ [^7] and the spectrum is such that:  \

-   there is one eigenvector with eigenvalue $1$. \

-   there are $\Theta(n\sqrt{\Delta})$ eigenvectors with eigenvalue
    $1-\Delta$. \

-   there are $\Theta(n(1-\sqrt{\Delta}))$ eigenvectors with eigenvalue
    $0$.

 \
It can be seen in this case the quantity
$S_1/{\sqrt{S_2}}=\Theta(\sqrt{\Delta})$.

To prove the upper bound, we show that $S_1^2/S_2 \leq 1$, for which it
suffices to prove that
$$S_2-S_1^2=\sum_{i<n}\dfrac{|a_{i}|^{2}}{(1-\lambda_{i})^2}-\left(\sum_{i<n}\dfrac{|a_{i}|^{2}}{1-\lambda_{i}}\right)^2> 0.$$
The left hand side of this inequality can be written as
$$\begin{aligned}
\label{eq:sum}
&|a_n|^2\sum_{i<n}\dfrac{|a_{i}|^{2}}{(1-\lambda_{i})^2}+\sum_{i,k < n}\left(\frac{|a_{i}|^{2}|a_k|^2}{(1-\lambda_{i})^2}-\frac{|a_{i}|^{2}|a_k|^2}{(1-\lambda_{i})(1-\lambda_k)}\right).
\end{aligned}$$ Clearly, the first term is always non-negative so we now
show that the second term is also non-negative. The second term can be
written as $$\begin{aligned}
&\sum_{i,k < n}\left(\frac{|a_{i}|^{2}|a_k|^2}{(1-\lambda_{i})^2}-\frac{|a_{i}|^{2}|a_k|^2}{(1-\lambda_{i})(1-\lambda_k)}\right)=\\
&\dfrac{1}{2}\sum_{i,k < n}\left(\frac{|a_{i}|^{2}|a_k|^2}{(1-\lambda_{i})^2}-\frac{|a_{i}|^{2}|a_k|^2}{(1-\lambda_{i})(1-\lambda_k)}\right)+\\
&\dfrac{1}{2}\sum_{k,i < n}\left(\frac{|a_{i}|^{2}|a_k|^2}{(1-\lambda_{k})^2}-\frac{|a_{i}|^{2}|a_k|^2}{(1-\lambda_{i})(1-\lambda_k)}\right)=\\
&\sum_{i,k < n}\dfrac{|a_i|^2|a_k|^2}{2}\left(\dfrac{1}{(1-\lambda_i)^2}+\dfrac{1}{(1-\lambda_k)^2}-\dfrac{2}{(1-\lambda_i)(1-\lambda_k)}\right)\\
&=\dfrac{1}{2}\left[\sum_{i,k < n}|a_i|^2|a_k|^2 \dfrac{(\lambda_k-\lambda_i)^2}{(1-\lambda_i)^2(1-\lambda_k)^2}\right]\geq 0.
\end{aligned}$$ This implies that $S_1^2/S_2\leq 1$ and hence
$S_1/\sqrt{S_2}\leq 1$. This is saturated (up to $O(1/n)$ terms), for
example, if $H$ is the normalized adjacency matrix of the complete
graph. $\Box$\
\
 \
Furthermore, we need to understand the validity of the spectral
condition imposed in
Eq. [\[eq:spectral_con\]](#eq:spectral_con){reference-type="eqref"
reference="eq:spectral_con"}. For this, it will be useful to write a
weaker condition in terms of the spectral gap $\Delta$. From the
definition of the quantities $S_k$ (see
Eq. [\[eqmain:Sk\]](#eqmain:Sk){reference-type="eqref"
reference="eqmain:Sk"}) it is possible to see that $S_2\geq \Delta S_3$
and $S_1, S_2\geq 1$. Furthermore, from
Lemma [5](#lem:nu-bound-1){reference-type="ref"
reference="lem:nu-bound-1"} we have that $S_1\leq \sqrt{S_2}$. Hence, we
can bound the RHS of the spectral condition as
$$\label{eq:spectral_con_bound}
 c \min\left\{\frac{S_1 S_2}{S_3},\Delta\sqrt{S_2}\right\}\geq c \Delta S_1  \geq c\Delta.$$
This implies that our analysis is valid for any graph with
$\sqrt{\epsilon}\leq c \Delta$ i.e., with a sufficiently large spectral
gap compared to the overlap of the initial state with the marked node.
For example, for $d$-dimensional lattices the spectral gap is
$\Delta\sim n^{-2/d}$ and $\epsilon=1/n$ and so it is easy to see from
the bound in
Eq. [\[eq:spectral_con\]](#eq:spectral_con){reference-type="eqref"
reference="eq:spectral_con"} and
[\[eq:spectral_con_bound\]](#eq:spectral_con_bound){reference-type="eqref"
reference="eq:spectral_con_bound"} that the spectral condition is
satisfied for lattices of dimension larger than $5$. In this scenario,
we have that both $S_1$ and $S_2$ are constants [@childs2004spatial] and
so we recover the result that marked node can be found in
$\Theta(\sqrt{n})$ time in such a case as demonstrated by Childs and
Goldstone. A similar behaviour appears in certain fractal lattices. The
scaling of the gap depends on the spectral dimension $d_s$ as
$\Delta\sim n^{-2/d_s}$ and the coefficients $S_1$ and $S_2$ are
constant for spectral dimension larger than 4
[@Boettcher_evaluation_2017]. Hence, it can be shown that quantum search
is optimal in this regime [@Boettcher_searchfractals_2017].

We nottice, in addition, that for regular lattices the performance of
quantum search for the critical case $d=4$ is also recovered. For
$4d$-lattices, we have that $\Delta=\Theta(1/\sqrt{n})$,
$S_1=\Theta(1)$, $S_2=\Theta(\log n)$ and $S_3=\Theta(\sqrt{n})$
[@childs2004spatial]. As such the spectral condition is satisfied. Thus,
the amplitude of the final state with the solution node is
$S_1/\sqrt{S_2}=\Theta(1/\sqrt{\log n})$ after a time
$T=\Theta(\sqrt{n\log n})$. It can be seen, however, than for dimensions
$2$ and $3$ where the algorithm has been shown to be suboptimal
[@childs2004spatial], the spectral condition is violated and our
analysis fails.

On the other hand, there exist graphs for which the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm can be
demonstrated to run in $\Theta(\sqrt{n})$ time, even though the spectral
condition is violated. In the next section, we show how a different
analysis helps capture the algorithmic performance on such instances.

# Quantum search on graphs with quasi-degenerate highest eigenvalues {#sec:search-degenerate-spectra}

In this section, we begin by considering examples of graphs for which
the $\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm runs
optimally even though their normalized adjacency matrix violates the
*spectral condition* in
Eq. [\[eq:spectral_con\]](#eq:spectral_con){reference-type="eqref"
reference="eq:spectral_con"}.

An example of this is the following vertex-transitive graph, which we
shall refer to as a *bridged-complete graph*: two complete graphs of
$n/2$ nodes such that every node in one complete graph is connected to
the corresponding node in the other (See
Fig. [1](#subfig:bridged-complete){reference-type="ref"
reference="subfig:bridged-complete"}). This is a particular case of the
Rook's graph which we discuss in
Sec. [5](#sec:quantum-walk-chessboard){reference-type="ref"
reference="sec:quantum-walk-chessboard"}. The normalized adjacency
matrix of this graph (i) has an extremely small spectral gap
($\Delta=\Theta\left(n^{-1+o(1)}\right)$) and (ii) there exists a
constant gap between the first two eigenvalues and the rest of the
spectrum. The spectral condition is violated, since
$$\min\left\{\frac{S_1 S_2}{S_3},\Delta\sqrt{S_2}\right\}=\Theta\left(\epsilon\right)\ll \sqrt{\epsilon},$$
implying that Theorem
[2](#lem_main:search-highest-estate){reference-type="ref"
reference="lem_main:search-highest-estate"} is not applicable for
analyzing the algorithmic performance for this graph.

<figure id="figmain:bridged-joined-cg">
<figure id="subfig:bridged-complete">
<p><img src="bridged-complete.jpg" style="width:60.0%"
alt="image" /><br />
</p>
<figcaption> </figcaption>
</figure>
<p><br />
</p>
<figure id="subfig:joined-complete">
<img src="joined-complete.jpg" style="width:60.0%" />
<figcaption> </figcaption>
</figure>
<figcaption><span>(a) The <em>bridged-complete</em></span> graph is a
special case of a Rook’s graph with <span
class="math inline"><em>n</em><sub>1</sub> = 2</span> and <span
class="math inline"><em>n</em><sub>2</sub> = <em>n</em>/2</span>. This
corresponds to two complete graphs of <span
class="math inline"><em>n</em>/2</span> edges such that each node in one
complete graph is connected to the corresponding node in the other. (b)
<em>Joined-complete graph</em>: two complete graphs of <span
class="math inline"><em>n</em>/2</span> nodes each are connected by a
single edge.</figcaption>
</figure>

However, intuitively the quantum walk search algorithm should run
optimally for the bridged-complete graph. The quantum walk starts with
an equal superposition of all nodes and, if we neglect the effect of the
bridges connecting the two complete graphs, it is expected to be able to
find a node marked in any of the two complete graphs of $n/2$ nodes with
probability $1/2$ in $\sim \sqrt{n}/2$ time. Moreover, since there is a
bridge connecting each node in one complete graph to another node in the
other, the walker can transition between any of the two complete graphs.
So one expects that a marked node would be obtained in
$\Theta(\sqrt{n})$ time. A very similar example, with analogous spectral
properties is the *joined-complete graph* (two complete-graphs joined by
a single bridge, Fig [2](#subfig:joined-complete){reference-type="ref"
reference="subfig:joined-complete"}). This example was used in
Ref. [@meyer2015connectivity] to show that large spectral gaps are
indeed not necessary for optimal quantum search.

Thus, for both these graphs, we find that the spectrum of their
normalized adjacency matrix satisfies the following two properties:
(i) A few of the highest eigenvalues are closely spaced (nearly
degenerate) and (ii) there exists a large gap between these highest
eigenvalues and the rest of the spectrum (see
Fig. [4](#fig:qd_eigenvalues){reference-type="ref"
reference="fig:qd_eigenvalues"}). We call the space spanned by the
eigenvectors corresponding to the closely-spaced eigenvalues as
*quasi-degenerate*. Generally such graphs find applications in spectral
clustering as they can be partitioned into clusters [@von2007tutorial].

We show here that a modification of the analysis done in
Sec. [3](#sec:performance_non_degenerate){reference-type="ref"
reference="sec:performance_non_degenerate"}, which explicitly takes into
account this quasi-degeneracy of the highest eigenvalues, allows us to
construct spectral conditions which are sufficient to predict whether
the $\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm is
optimal for Hamiltonians that satisfy the aforementioned properties. In
particular, these conditions will allow us to predict optimality of
quantum search for graphs such as the joined complete, or the bridged
complete graph.

Formally, consider a Hamiltonian $H$ such that its eigenvalues are
$$0\leq\lambda_1\leq\cdots\leq \lambda_n=1,$$ such that
$$H\ket{v_i}=\lambda_i\ket{v_i}.$$ Let us denote by
$\ensuremath{\mathcal{D}}$ the space spanned by the $D$ eigenstates
corresponding to the highest eigenvalues of $H$,
i.e. $$\label{eq:quasi-degenerate-space}
\ensuremath{\mathcal{D}}=\mathrm{Span}\{\ket{v_n},\cdots,\ket{v_{n-D+1}}\},$$
such that $|\ensuremath{\mathcal{D}}|=D$. Consequently, we refer to the
space spanned by the remaining eigenstates by
$\bar{\ensuremath{\mathcal{D}}}$. Furthermore, we denote the gaps
between the eigenvalues $\lambda_n=1$ and $\lambda_{n-D+1}$ as
$$\label{eqmain:gap-degenerate-space}
\Delta_\ensuremath{\mathcal{D}}= 1-\lambda_{n-D+1},$$ and the gap
between the $\lambda_n=1$ and $\lambda_{n-D}$ as
$$\label{eqmain:gap-bet-nonD-D}
\Delta=1-\lambda_{n-D},$$ as depicted in
Fig. [4](#fig:qd_eigenvalues){reference-type="ref"
reference="fig:qd_eigenvalues"}. Our analysis aims at predicting the
algorithmic performance in cases where
$\Delta_\ensuremath{\mathcal{D}}\ll \sqrt{\epsilon}$ and $\Delta$ is
sufficiently large, for example, when $\Delta\gg \epsilon$. Hence, we
say that the $D$ largest eigenvalues are nearly degenerate or
*quasi-degenerate*. The precise spectral properties that the Hamiltonian
$H$ must fulfil are stated precisely in terms of a new spectral
condition later on. Also, note that $D=1$ corresponds to the
non-degenerate case considered in
Theorem [2](#lem_main:search-highest-estate){reference-type="ref"
reference="lem_main:search-highest-estate"} with $\Delta$ being the
spectral gap of $H$.

We demonstrate the algorithmic performance for such instances in the
following subsections in two steps. We first assume that
$\ensuremath{\mathcal{D}}$ is completely degenerate, i.e. all
eigenstates in $\ensuremath{\mathcal{D}}$ have eigenvalue one
($\Delta_\ensuremath{\mathcal{D}}=0$) and find the evolution time and
final amplitude of the algorithm based on this assumption
(Subsec. [4.1](#subsec:search-degenerate){reference-type="ref"
reference="subsec:search-degenerate"}) [^8]. Next, we demonstrate that,
given certain conditions on $\Delta_\ensuremath{\mathcal{D}}$, the
algorithmic dynamics for the aforementioned case is the same as when
$\ensuremath{\mathcal{D}}$ is completely degenerate, up to some small
error.

## Performance of the $\mathbf{\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}}$ algorithm when $\mathbf{\ensuremath{\mathcal{D}}}$ is degenerate {#subsec:search-degenerate}

In order to analyse graphs with a $D$-degenerate highest eigenvalue
($\Delta_\ensuremath{\mathcal{D}}=0$), it will be useful to define the
following quantities $$\label{eqmain:Sk-D}
S_{k,\bar{\ensuremath{\mathcal{D}}}}=\sum_{i=1}^{n-D}\dfrac{|a_i|^2}{(1-\lambda_i)^k},$$
where $k\geq 1$. These parameters are similar to $S_k$ defined in
Eq. [\[eqmain:Sk\]](#eqmain:Sk){reference-type="eqref"
reference="eqmain:Sk"}, except that the sum excludes all the $D$
degenerate eigenvalues (note that the quantities $S_k$ are not defined
if there is degeneracy of the largest eigenvalue).

Furthermore, we define $\sqrt{\epsilon_\ensuremath{\mathcal{D}}}$ as the
overlap of the solution with the $\ensuremath{\mathcal{D}}$ subspace. If
the solution state $\ket{w}$ is expressed in the eigenbasis of $H$ as in
Eq. [\[eqmain:sol-in-eigenbasis\]](#eqmain:sol-in-eigenbasis){reference-type="eqref"
reference="eqmain:sol-in-eigenbasis"}, this is given by
$$\label{eqmain:overlap:w-D}
\epsilon_\ensuremath{\mathcal{D}}=\sum_{i\in \ensuremath{\mathcal{D}}} |a_i|^2.$$
In addition, we define $\sqrt{\epsilon}=|\braket{w}{v_n}|=|a_n|$ as
before, except that in this case $\ket{v_n}$ can be any state in the
degenerate subspace $\ensuremath{\mathcal{D}}$. We introduce the
following spectral condition, analogous to the one in
Eq. [\[eq:spectral_con\]](#eq:spectral_con){reference-type="eqref"
reference="eq:spectral_con"}, in terms of the
$S_{k,\bar{\ensuremath{\mathcal{D}}}}$ parameters
$$\label{eq:spec-cond-deg}
\sqrt{\epsilon_{\ensuremath{\mathcal{D}}}}\leq c\min\left\{\dfrac{S_{1,\bar{\ensuremath{\mathcal{D}}}}S_{2,\bar{\ensuremath{\mathcal{D}}}}}{S_{3,\bar{\ensuremath{\mathcal{D}}}}},\Delta\sqrt{S_{2,\bar{\ensuremath{\mathcal{D}}}}}\right\}.$$
Our result regarding the performance of the quantum search algorithm is
the following.  \

::: {#thm:performance-search-deg .theorem}
**Theorem 6**. *Let $H$ be such that its largest $D$ highest eigenvalues
are degenerate and the spectral condition of
Eq. [\[eq:spec-cond-deg\]](#eq:spec-cond-deg){reference-type="eqref"
reference="eq:spec-cond-deg"} is obeyed, with
$S_{k,\bar{\ensuremath{\mathcal{D}}}}$ defined as in
Eq. [\[eqmain:Sk-D\]](#eqmain:Sk-D){reference-type="eqref"
reference="eqmain:Sk-D"}. By choosing
$r=S_{1,\bar{\ensuremath{\mathcal{D}}}}$ and
$$T=\Theta\left(\dfrac{1}{\sqrt{\epsilon_{\ensuremath{\mathcal{D}}}}}\dfrac{\sqrt{S_{2,\bar{\ensuremath{\mathcal{D}}}}}}{S_{1,\bar{\ensuremath{\mathcal{D}}}}}\right),$$
Algorithm [\[algo-cg-general\]](#algo-cg-general){reference-type="ref"
reference="algo-cg-general"}, starting from any one of the
$1$-eigenstates of $H$, denoted by $\ket{v_n}$, prepares a state
$\ket{f}$ such that $$\label{eq:nu_deg}
\nu=|\braket{w}{f}|=\Theta\left(\sqrt{\frac{\epsilon}{\epsilon_{\ensuremath{\mathcal{D}}}}}\frac{S_{1,\bar{\ensuremath{\mathcal{D}}}}}{\sqrt{S_{2,\bar{\ensuremath{\mathcal{D}}}}}}\right).$$*
:::

![The analysis of
Sec. [4](#sec:search-degenerate-spectra){reference-type="ref"
reference="sec:search-degenerate-spectra"} is tailored to the study of
quantum search on graphs whose spectrum exhibits the features displayed
in this figure. A small number $D$ of quasi-degenerate eigenvalues lie
close to the maximum value $1$, within an energy gap
$\Delta_{\ensuremath{\mathcal{D}}}$. The next largest eigenvalue has an
energy $1-\Delta$, where $\Delta\gg \Delta_{\ensuremath{\mathcal{D}}}$.
Such spectral features appear, for example, in the graphs of
Fig [3](#figmain:bridged-joined-cg){reference-type="ref"
reference="figmain:bridged-joined-cg"} or, more generally, in graphs
composed by highly connected clusters that are sparsely connected to
each other.](eigenvalues_quasidegenerate.jpg){#fig:qd_eigenvalues}

 \
Let the solution state $\ket{w}$ be expressed in the eigenbasis of $H$
as in
Eq. [\[eqmain:sol-in-eigenbasis\]](#eqmain:sol-in-eigenbasis){reference-type="eqref"
reference="eqmain:sol-in-eigenbasis"}. It will be convenient to consider
a rotated basis for the degenerate subspace $\ensuremath{\mathcal{D}}$
such that a single eigenstate, defined as
$$\label{eqmain:state-relabeled-basis}
\ket{v_\ensuremath{\mathcal{D}}^{(1)}}=\dfrac{1}{\sqrt{\epsilon_\ensuremath{\mathcal{D}}}}\sum_{j\in\ensuremath{\mathcal{D}}} a_j\ket{v_j},$$
contains the whole overlap of this subspace with $\ket{w}$, i.e.
$|\braket{w}{v_\ensuremath{\mathcal{D}}^{(1)}}|=\sqrt{\epsilon_{\ensuremath{\mathcal{D}}}}$.
We complete the basis with the states
$\ket{v_\ensuremath{\mathcal{D}}^{(j)}}$, $2\leq j\leq D$, such that
$\braket{v_\ensuremath{\mathcal{D}}^{(l)}}{v_\ensuremath{\mathcal{D}}^{(m)}}=\delta_{l,m}$
for any $l,m\in \{1,...,D\}$.

We note that this choice guarantees that
$\braket{w}{v_\ensuremath{\mathcal{D}}^{(j)}}=0$, for $2\leq j\leq D$.
This implies that these are eigenstates of $H_{\text{search}}$ with
eigenvalue $1$, since $$\label{eq:trivial_eigenstates}
    H_{\text{search}}\ket{v_\ensuremath{\mathcal{D}}^{(j)}}= H \ket{v_\ensuremath{\mathcal{D}}^{(j)}}=\ket{v_\ensuremath{\mathcal{D}}^{(j)}},$$
for $2\leq j \leq D$. This gives us a set of $D-1$ eigenstates which do
not play a role in the computation of the final amplitude. To see this,
let us first express the initial state $\ket{v_n}$ [^9] as
$$\label{eq:start-state-relabelled}
\ket{v_n}=\sum_{j=1}^{D}\alpha_j\ket{v_{\ensuremath{\mathcal{D}}}^{(j)}},$$
where $\sum_{j=1}^D |\alpha_j|^2=1$ and
$\alpha_1=\sqrt{\epsilon/\epsilon_{\ensuremath{\mathcal{D}}}}$. We can
now write $$\label{eq:amplitude_deg}
    \bra{w}e^{i H_{\text{search}}T} \ket{v_n} = \sqrt{\epsilon/\epsilon_{\ensuremath{\mathcal{D}}}} \bra{w}e^{i H_{\text{search}}T} \ket{v_\ensuremath{\mathcal{D}}^{(1)}},$$
using
Eq. [\[eq:trivial_eigenstates\]](#eq:trivial_eigenstates){reference-type="eqref"
reference="eq:trivial_eigenstates"} and the fact that
$\braket{w}{v_\ensuremath{\mathcal{D}}^{(j)}}=0$, for $2\leq j\leq D$.

Hence, to analyse the amplitude
$\bra{w}e^{i H_{\text{search}}T} \ket{v_\ensuremath{\mathcal{D}}^{(1)}}$
it is enough to consider the dynamics in the subspace
$$V=\text{span}\left\{\ket{v_\ensuremath{\mathcal{D}}^{(1)}}, \ket{v_i}, i\in\{1,...,n-D\}\right\}.$$
We do this by applying the same techniques of
Sec. [3](#sec:performance_non_degenerate){reference-type="ref"
reference="sec:performance_non_degenerate"} for the projected search
Hamiltonian
$$H'_{\text{search}}=P_V H_{\text{search}} P_V =\ket{w}\bra{w} + P_V H P_V,$$
where $P_V$ is the projector in the $V$ subspace. Note that the
Hamiltonian $H'=P_V H P_V$ has a single eigenvalue 1 (the state
$\ket{v_\ensuremath{\mathcal{D}}^{(1)}}$) and a spectral gap $\Delta$.
The only difference with respect to the analysis in
Sec. [3](#sec:performance_non_degenerate){reference-type="ref"
reference="sec:performance_non_degenerate"} is that its dimension is
$n-D+1$. Hence, we can apply
Theorem [2](#lem_main:search-highest-estate){reference-type="ref"
reference="lem_main:search-highest-estate"} by replacing the parameters
$S_k$ by $S_{k,\bar{\ensuremath{\mathcal{D}}}}$ defined in
Eq. [\[eqmain:Sk-D\]](#eqmain:Sk-D){reference-type="eqref"
reference="eqmain:Sk-D"} as well as replacing the spectral condition of
Eq. [\[eq:spectral_con\]](#eq:spectral_con){reference-type="eqref"
reference="eq:spectral_con"} by the one in
Eq. [\[eq:spec-cond-deg\]](#eq:spec-cond-deg){reference-type="eqref"
reference="eq:spec-cond-deg"}. This implies that, by choosing
$r=S_{1,\bar{\ensuremath{\mathcal{D}}}}$ and evolving
$H'_{\mathrm{search}}$ for time $$\label{eq:tsearch_deg}
T=\Theta\left(\dfrac{\sqrt{S_{2,\bar{\ensuremath{\mathcal{D}}}}}}{S_{1,\bar{\ensuremath{\mathcal{D}}}}}\dfrac{1}{\sqrt{\epsilon_{\ensuremath{\mathcal{D}}}}}\right),$$
with initial state $\ket{v_\ensuremath{\mathcal{D}}^{(1)}}$, results in
a state that has an overlap with the solution
$$\label{eqmain:amplitude-degenerate}
|\bra{w}e^{i H_{\text{search}}T} \ket{v_\ensuremath{\mathcal{D}}^{(1)}}|= \Theta\left(\frac{S_{1,\bar{\ensuremath{\mathcal{D}}}}}{\sqrt{S_{2,\bar{\ensuremath{\mathcal{D}}}}}}\right).$$
Finally, replacing this amplitude in
Eq. [\[eq:amplitude_deg\]](#eq:amplitude_deg){reference-type="eqref"
reference="eq:amplitude_deg"} we obtain that after this time the
amplitude $| \bra{w}e^{i H_{\text{search}}T} \ket{v_n}|$ is given by
Eq. [\[eq:nu_deg\]](#eq:nu_deg){reference-type="eqref"
reference="eq:nu_deg"}. $\Box$\
 \
One can easily see that for $D=1$,
$|\epsilon|=|\epsilon_{\ensuremath{\mathcal{D}}}|$,
$S_{1,\bar{\ensuremath{\mathcal{D}}}}=S_1$ and
$S_{2,\bar{\ensuremath{\mathcal{D}}}}=S_2$ we recover the statement of
Theorem [2](#lem_main:search-highest-estate){reference-type="ref"
reference="lem_main:search-highest-estate"}. However, for $D>1$ there
is, in general, no way to have
$|\epsilon|=|\epsilon_{\ensuremath{\mathcal{D}}}|$ as this would assume
we are able to prepare the state
$\ket{v_\ensuremath{\mathcal{D}}^{(1)}}$ from
Eq. [\[eqmain:state-relabeled-basis\]](#eqmain:state-relabeled-basis){reference-type="eqref"
reference="eqmain:state-relabeled-basis"}, which depends on $w$ via the
overlaps $a_i$. Given this, a possible strategy would be to choose
$\ket{v_n}$ as a random state in the degenerate subspace
$\ensuremath{\mathcal{D}}$, in which case the expected value of
$\epsilon/\epsilon_{\ensuremath{\mathcal{D}}}$ would be $1/D$.

Similarly to Theorem [3](#lem_main:robustness_r){reference-type="ref"
reference="lem_main:robustness_r"}, it can be shown that the same
algorithmic performance is maintained by choosing $r$ such that
$|r-S_{1,\bar{\ensuremath{\mathcal{D}}}}|\ll \epsilon_{\ensuremath{\mathcal{D}}}S_{2,\bar{\ensuremath{\mathcal{D}}}}$.
An analogous derivation to that of
Theorem [4](#lem:sub-optimality-for-any-r){reference-type="ref"
reference="lem:sub-optimality-for-any-r"} shows that any choice of $r$
such that $$\label{eq:robust-range-of-r-deg}
r \not\in \left[S_{1,\bar{\ensuremath{\mathcal{D}}}}-\Theta\left(\sqrt{S_{2,\bar{\ensuremath{\mathcal{D}}}}\epsilon_\ensuremath{\mathcal{D}}}\right), S_{1,\bar{\ensuremath{\mathcal{D}}}}+\Theta\left(\sqrt{S_{2,\bar{\ensuremath{\mathcal{D}}}}\epsilon_\ensuremath{\mathcal{D}}}\right) \right],$$
leads to a maximum amplitude of
$$o\left(\sqrt{\frac{\epsilon}{\epsilon_{\ensuremath{\mathcal{D}}}}}\frac{S_{1,\bar{\ensuremath{\mathcal{D}}}}}{\sqrt{S_{2,\bar{\ensuremath{\mathcal{D}}}}}}\right).$$

This implies the following necessary and sufficient conditions for
optimality for Hamiltonians with degenerate highest eigenvalues.
Provided that the spectral condition in
Eq. [\[eq:spec-cond-deg\]](#eq:spec-cond-deg){reference-type="eqref"
reference="eq:spec-cond-deg"} holds, we obtain that the algorithm is
optimal, in the sense discussed in
Sec. [2.2](#sec:def_optimality){reference-type="ref"
reference="sec:def_optimality"}, *if and only if*
$$\label{eq:cond_optimality_deg}
\frac{S_{1,\bar{\ensuremath{\mathcal{D}}}}}{\sqrt{S_{2,\bar{\ensuremath{\mathcal{D}}}}}}=\Theta(1),$$
and $D=\Theta(1)$, which ensures that an amplitude of
$\sqrt{\epsilon/\epsilon_{\ensuremath{\mathcal{D}}}}=\Theta(1)$ after a
time $T=\Theta(1/\sqrt{\epsilon})$. More generally, if $D$ is not
constant and provided
Eq. [\[eq:cond_optimality_deg\]](#eq:cond_optimality_deg){reference-type="eqref"
reference="eq:cond_optimality_deg"} holds, we obtain an amplitude
$$\nu\sim \sqrt{\frac{\epsilon}{\epsilon_\ensuremath{\mathcal{D}}}},$$
after a time
$$T=\Theta\left(\dfrac{1}{\sqrt{\epsilon_\ensuremath{\mathcal{D}}}}\right).$$
Hence, from
Eq. [\[eqmain:search-time-with-amp-amp\]](#eqmain:search-time-with-amp-amp){reference-type="eqref"
reference="eqmain:search-time-with-amp-amp"}, using
$\sqrt{\epsilon_{\ensuremath{\mathcal{D}}}/\epsilon}$ rounds of quantum
amplitude amplification would also result in finding the marked vertex
in time $$\label{eq:cost_deg_nuequal1}
T_{\mathrm{search}}=\sqrt{\dfrac{\epsilon_\ensuremath{\mathcal{D}}}{\epsilon}}\mathcal{S} + \dfrac{\ensuremath{\mathcal{C}}_w}{\sqrt{\epsilon}}+\mathcal{M},$$
which is similar to the optimal performance except that there is a
multiplicative overhead in the set-up cost of
$\sqrt{\epsilon_\ensuremath{\mathcal{D}}/\epsilon}$.

## Performance of the $\mathbf{\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}}$ algorithm when $\mathbf{\ensuremath{\mathcal{D}}}$ is quasi-degenerate {#subsec:search-quasi-degenerate}

In this subsection, we explicitly calculate an upper bound on the error
of the predicted performance of the $\ensuremath{\mathcal{C G}}$
algorithm when $\Delta_\ensuremath{\mathcal{D}}$, defined in
Eq. [\[eqmain:gap-degenerate-space\]](#eqmain:gap-degenerate-space){reference-type="eqref"
reference="eqmain:gap-degenerate-space"}, is larger than $0$. In this
case, we write $H$ in its spectral form as
$$\label{eq:spectral-form-quasi-deg-Ham}
H=\sum_{j\in\ensuremath{\mathcal{D}}} \ket{v_j}\bra{v_j}+\sum_{j\notin\ensuremath{\mathcal{D}}} \lambda_j\ket{v_j}\bra{v_j}+\sum_{j\in\ensuremath{\mathcal{D}}} (\lambda_j-1)\ket{v_j}\bra{v_j}.$$

This in turn implies that the search Hamiltonian $H_{\mathrm{search}}$
can be split as $$\begin{aligned}
\label{eq:spectral-form-quasi-deg-Ham-search}
H_{\mathrm{search}}&=H^{\mathrm{deg}}_{\mathrm{search}}+H_{\mathrm{err}},
\end{aligned}$$ where $H^{\mathrm{deg}}_{\mathrm{search}}$ corresponds
to the search Hamiltonian assuming that eigenspace
$\ensuremath{\mathcal{D}}$ of $H$ is exactly degenerate with all
eigenvalues in $\ensuremath{\mathcal{D}}$ equal to $1$,
i.e. $$\label{eq:spectral-form-deg-Ham-search}
H^{\mathrm{deg}}_{\mathrm{search}}=\ket{w}\bra{w}+r \left(\sum_{j\in\ensuremath{\mathcal{D}}} \ket{v_j}\bra{v_j}+\sum_{j\notin\ensuremath{\mathcal{D}}} \lambda_j\ket{v_j}\bra{v_j}\right)$$
and $$\label{eq:Herr}
H_{\mathrm{err}}=r \sum_{j\in\ensuremath{\mathcal{D}}} (\lambda_j-1)\ket{v_j}\bra{v_j}.$$
We can quantify the error caused by neglecting $H_{err}$ in the time
evolution of $H_{\mathrm{search}}$ for time $T$ via the Trotter formulas
[@childs2019trotter]. This leads to the following Lemma.  \

::: {#lem:trotter-error .lemma}
**Lemma 7**. *Let
$H_{\mathrm{search}}=H^{\mathrm{deg}}_{\mathrm{search}}+H_{\mathrm{err}}$,
with $H^{\mathrm{deg}}_{\mathrm{search}}$ and $H_{\mathrm{err}}$ defined
in
Eqs. [\[eq:spectral-form-deg-Ham-search\]](#eq:spectral-form-deg-Ham-search){reference-type="eqref"
reference="eq:spectral-form-deg-Ham-search"} and
[\[eq:Herr\]](#eq:Herr){reference-type="eqref" reference="eq:Herr"},
respectively. For any time $T\geq 1/\sqrt{\epsilon_D}$, we have that
$$\bra{w}e^{i H_{\mathrm{search}}T} \ket{v_n}= \bra{w}e^{iH^{\mathrm{deg}}_{\mathrm{search}}T} \ket{v_n}+\eta_{qd},$$
where
$$\eta_{qd}=O\left(r \Delta_\ensuremath{\mathcal{D}}\sqrt{\epsilon_{\ensuremath{\mathcal{D}}}}T^2\right).$$*
:::

 \
Using first order Trotter formula [@childs2019trotter] we have
$$\begin{aligned}
e^{-iTH_{\mathrm{search}}}&=e^{-iT\left(H^{\mathrm{deg}}_{\mathrm{search}}+H_{\mathrm{err}}\right)}\\
\label{eqmain:trotter-error1}                          
                          &=e^{-iTH^{\mathrm{deg}}_{\mathrm{search}}}e^{-iTH_{\mathrm{err}}}+O\left(\left\lVert [\ket{w}\bra{w},H_{\mathrm{err}}] \right\rVert T^2\right)\\
                          &=e^{-iTH^{\mathrm{deg}}_{\mathrm{search}}}e^{-iTH_{\mathrm{err}}}+O\left(r\Delta_\ensuremath{\mathcal{D}}\sqrt{\epsilon_{\ensuremath{\mathcal{D}}}}T^2\right),
\end{aligned}$$ where we used the bound
$$\left\lVert [\ket{w}\bra{w},H_{\mathrm{err}}] \right\rVert=O(r\Delta_\ensuremath{\mathcal{D}}\sqrt{\epsilon_{\ensuremath{\mathcal{D}}}}),$$
which can be demonstrated by using the fact that $H_{\mathrm{err}}$ has
support only on the $\ensuremath{\mathcal{D}}$ subspace.

Moreover, we have that $$\begin{aligned}
e^{-iTH^{\mathrm{deg}}_{\mathrm{search}}}e^{-iTH_{\mathrm{err}}}&=e^{-iTH^{\mathrm{deg}}_{\mathrm{search}}}\left(I-iTH_{\mathrm{err}}+\cdots\right)\\
\label{eqmain:truncating-exponential}                                                                
                                                                &=e^{-iTH^{\mathrm{deg}}_{\mathrm{search}}}+O\left(T\left\lVert H_{\mathrm{err}} \right\rVert\right)\\
                                                                &=e^{-iTH^{\mathrm{deg}}_{\mathrm{search}}}+O\left(r\Delta_\ensuremath{\mathcal{D}}T\right).
\end{aligned}$$ The error in the approximation can be bounded by
combining
Eq. [\[eqmain:trotter-error1\]](#eqmain:trotter-error1){reference-type="eqref"
reference="eqmain:trotter-error1"} and
Eq. [\[eqmain:truncating-exponential\]](#eqmain:truncating-exponential){reference-type="eqref"
reference="eqmain:truncating-exponential"} as $$\begin{aligned}
\label{eq:error-trotter}
e^{-iTH_{\mathrm{search}}}=
&e^{-iTH^{\mathrm{deg}}_{\mathrm{search}}}
+\eta_{qd},
\end{aligned}$$ with $$\begin{aligned}
   \eta_{qd}&= O\left(r\Delta_\ensuremath{\mathcal{D}}\max\left\{\sqrt{\epsilon_{\ensuremath{\mathcal{D}}}}T^2,T\right\}\right)
   \\&=O\left(r \Delta_\ensuremath{\mathcal{D}}\sqrt{\epsilon_{\ensuremath{\mathcal{D}}}}T^2\right),
\end{aligned}$$ where in the last step we assumed
$T\geq 1/\sqrt{\epsilon_D}$. $\Box$\
 \
Using this Lemma, we can now adapt
Theorem [6](#thm:performance-search-deg){reference-type="ref"
reference="thm:performance-search-deg"} to Hamiltonians with
quasi-degenerate highest eigenvalues. To do so, we need to impose a
condition on the spectrum of $H$, that guarantees that the error
$\eta_{qd}$ in Lemma [7](#lem:trotter-error){reference-type="ref"
reference="lem:trotter-error"} is small enough for the predictions of
Theorem [6](#thm:performance-search-deg){reference-type="ref"
reference="thm:performance-search-deg"} to be meaningful. It can be seen
that this is possible if $$\begin{aligned}
 \sqrt{\epsilon}\geq \dfrac{1}{c_1}\dfrac{S^{3/2}_{2,\bar{\ensuremath{\mathcal{D}}}}\Delta_\ensuremath{\mathcal{D}}}{S^2_{1,\bar{\ensuremath{\mathcal{D}}}}}.\label{eq:lowerbound_epsilonD}
\end{aligned}$$ For a sufficiently small positive constant $c_1$. A
simpler, but less tight form for this condition in terms of the gaps
$\Delta_\ensuremath{\mathcal{D}}$ and $\Delta$ can be obtained by using
the lower bound in
Lemma [\[lem:nu-bound-1\]](#lem:nu-bound-1){reference-type="eqref"
reference="lem:nu-bound-1"} (which is valid also for
$S_{1,\bar{\ensuremath{\mathcal{D}}}}/\sqrt{S_{2,\bar{\ensuremath{\mathcal{D}}}}}$).
It can be shown that if
$$\sqrt{\epsilon} \geq \frac{\Delta_\ensuremath{\mathcal{D}}}{ c_1 \Delta^2}$$
then
Eq. [\[eq:lowerbound_epsilonD\]](#eq:lowerbound_epsilonD){reference-type="eqref"
reference="eq:lowerbound_epsilonD"} is satisfied. For graphs such as the
joined or bridged complete graph, we can take $D=2$ in which case
$\Delta_{\ensuremath{\mathcal{D}}}=\Theta(1/n)$ and $\Delta=\Theta(1)$,
whereas $\sqrt{\epsilon}=\Theta(n^{-1/2})$, ensuring this condition is
satisfied.

Our general result for search on graphs for which $H$ has
quasi-degenerate highest eigenvalues is the following.  \

::: {#thm:performance_qd .theorem}
**Theorem 8**. *For a given Hamiltonian $H$, assume there is a positive
integer $D$ such that the conditions in
Eqs. [\[eq:lowerbound_epsilonD\]](#eq:lowerbound_epsilonD){reference-type="eqref"
reference="eq:lowerbound_epsilonD"} and
[\[eq:spec-cond-deg\]](#eq:spec-cond-deg){reference-type="eqref"
reference="eq:spec-cond-deg"} are true. Then, by choosing
$r=S_{1,\bar{\ensuremath{\mathcal{D}}}}$ and
$$T=\Theta\left(\dfrac{1}{\sqrt{\epsilon_{\ensuremath{\mathcal{D}}}}}\dfrac{\sqrt{S_{2,\bar{\ensuremath{\mathcal{D}}}}}}{S_{1,\bar{\ensuremath{\mathcal{D}}}}}\right),$$
Algorithm [\[algo-cg-general\]](#algo-cg-general){reference-type="ref"
reference="algo-cg-general"} prepares a state $\ket{f}$ such that
$$\label{eq:nu_deg}
\nu=|\braket{w}{f}|=\Theta\left(\sqrt{\frac{\epsilon}{\epsilon_{\ensuremath{\mathcal{D}}}}}\frac{S_{1,\bar{\ensuremath{\mathcal{D}}}}}{\sqrt{S_{2,\bar{\ensuremath{\mathcal{D}}}}}}\right).$$*
:::

 \
The proof follows by combining the result of
Lemma [7](#lem:trotter-error){reference-type="ref"
reference="lem:trotter-error"} with that of
Theorem [6](#thm:performance-search-deg){reference-type="ref"
reference="thm:performance-search-deg"}. After a time
$$T=\Theta\left(\dfrac{\sqrt{S_{2,\bar{\ensuremath{\mathcal{D}}}}}}{S_{1,\bar{\ensuremath{\mathcal{D}}}}}\dfrac{1}{\sqrt{\epsilon_{\ensuremath{\mathcal{D}}}}}\right),$$
we have the following bound for the error term $$\begin{aligned}
\eta_{qd}&=O\left(\dfrac{\Delta_\ensuremath{\mathcal{D}}S_{2,\bar{\ensuremath{\mathcal{D}}}}}{\sqrt{\epsilon_{\ensuremath{\mathcal{D}}}}S_{1,\bar{\ensuremath{\mathcal{D}}}}}\right)\\
& =c_1 O\left(\sqrt{\frac{\epsilon}{\epsilon_{\ensuremath{\mathcal{D}}}}}\frac{S_{1,\bar{\ensuremath{\mathcal{D}}}}}{\sqrt{S_{2,\bar{\ensuremath{\mathcal{D}}}}}}\right),
\label{eq:additive-error-trotter}
\end{aligned}$$ where in the second step we use the condition from
Eq. [\[eq:lowerbound_epsilonD\]](#eq:lowerbound_epsilonD){reference-type="eqref"
reference="eq:lowerbound_epsilonD"}. Hence, for a sufficient small value
of constant $c_1$, the amplitude obtained at the solution after evolving
for this time $T$ from
Eq. [\[eq:tsearch_deg\]](#eq:tsearch_deg){reference-type="eqref"
reference="eq:tsearch_deg"} is given by $$\begin{aligned}
    \bra{w}e^{i H_{\text{search}}T} \ket{v_n}& = \bra{w}e^{i H_{\text{search}}^{\mathrm{deg}}T}  \ket{v_n} + \eta_{qd}\\&
    =\Theta\left(\sqrt{\frac{\epsilon}{\epsilon_{\ensuremath{\mathcal{D}}}}}\frac{S_{1,\bar{\ensuremath{\mathcal{D}}}}}{\sqrt{S_{2,\bar{\ensuremath{\mathcal{D}}}}}}\right),
\end{aligned}$$ where we used
Eq. [\[eq:additive-error-trotter\]](#eq:additive-error-trotter){reference-type="eqref"
reference="eq:additive-error-trotter"} and
Theorem [6](#thm:performance-search-deg){reference-type="ref"
reference="thm:performance-search-deg"}. $\Box$\

This result leads to the following *sufficient* condition for optimal
quantum search: provided there is an integer $D=\Theta(1)$ such that
Eqs. [\[eq:lowerbound_epsilonD\]](#eq:lowerbound_epsilonD){reference-type="eqref"
reference="eq:lowerbound_epsilonD"} and
[\[eq:spec-cond-deg\]](#eq:spec-cond-deg){reference-type="eqref"
reference="eq:spec-cond-deg"} are satisfied and
$S_{1,\bar{\ensuremath{\mathcal{D}}}}/{\sqrt{S_{2,\bar{\ensuremath{\mathcal{D}}}}}}=\Theta(1)$,
quantum search is optimal. This is the case, for example, for graphs in
which there a constant $D$ such that
$\Delta_{\ensuremath{\mathcal{D}}}=o(\sqrt{\epsilon})$ and a large gap
$\Delta=\Theta(1)$, such as the bridged or joined-complete graph.

Note that, even though in the fully degenerate case in
Sec. [4.1](#subsec:search-degenerate){reference-type="ref"
reference="subsec:search-degenerate"} our analysis provided necessary
and sufficient conditions for optimal quantum search, here we can only
provide a sufficient condition because our analysis gives no guarantee
that the choice $r=S_{1,\bar{\ensuremath{\mathcal{D}}}}$ gives the best
algorithmic performance when there is quasi-degeneracy. This is because,
the error term that we obtain by approximating the quasi-degenerate case
with the fully degenerate case in
Lemma [7](#lem:trotter-error){reference-type="ref"
reference="lem:trotter-error"}, becomes too large for sufficiently large
values of $r$ and $T$.

# Finding a marked node on the Rook's graph {#sec:quantum-walk-chessboard}

In this section, we discuss the performance of the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm on the
Rook's graph. The edges of this graph correspond to the possible
movements of a rook on a rectangular chessboard with $n=n_1 n_2$ nodes,
where $n_1$ is the number of rows and $n_2$ the number of columns. We
assume, without loss of generality, that $n_2\geq n_1$ and take
$n_1=n^{\sigma}$ and $n_2=n^{1-\sigma}$ where $0<\sigma<1/2$.

The motivation for studying quantum search on this graph is that,
depending on the choice of $\sigma$, the performance of the algorithm
varies drastically. The analysis of
Sec. [3](#sec:performance_non_degenerate){reference-type="ref"
reference="sec:performance_non_degenerate"} can be applied in certain
regimes, showing that for $1/3\leq \sigma \leq 1/2$ the algorithm is
optimal, whereas for $1/4 \leq \sigma < 1/3$ the algorithm is suboptimal
and also slower than the square root of the classical hitting time,
which for this graph is $\Theta(n)$. Interestingly, this suboptimality
result holds even when the spectral gap $\Delta_{RG}\gg \sqrt{\epsilon}$
showing that the latter condition is not sufficient for optimal quantum
search.

For sufficiently low values of $\sigma$, the analysis of
Sec. [3](#sec:performance_non_degenerate){reference-type="ref"
reference="sec:performance_non_degenerate"} breaks down and the
quasi-degenerate treatment from
Sec. [4](#sec:search-degenerate-spectra){reference-type="ref"
reference="sec:search-degenerate-spectra"} can be used to provide lower
bounds on the amplitude that can be obtained at the marked node after a
certain time. This allows us, for example, to demonstrate that if
$n_1=\Theta(1)$ the algorithm is optimal. Our predictions regarding the
algorithmic performance are summarized in
Table [\[tab:compare\]](#tab:compare){reference-type="ref"
reference="tab:compare"} for different regimes of $\sigma$.

## The Rook's graph and its spectrum

We begin by introducing the Rook's graph and the associated Hamiltonian
$H$ that drives the quantum walk.

Consider the movement of a rook on a rectangular chessboard of $n_1$
rows and $n_2$ columns. The position of the rook on the chessboard is
defined by the tuple $(i_{\leftrightarrow},j_{\updownarrow})$, where
$i_{\leftrightarrow}\in [n_2]$ and $j_{\updownarrow}\in [n_1]$. From any
given position, the rook can move horizontally (left or right) to any of
the available $n_2$ positions or it can move vertically (forward and
backward) to any of the available $n_1$ positions. Furthermore, suppose
the rook accesses one of these available positions uniformly at random.

<figure id="figmain:chessboard">
<figure id="subfig:chessboard">
<img src="rook_chessboard.jpg" />
<figcaption> </figcaption>
</figure>
<figure id="subfig:cartesian-complete-graphs">
<img src="cartesian_product.jpg" />
<figcaption> </figcaption>
</figure>
<figcaption> The possible moves of a rook on a rectangular chessboard of
<span class="math inline"><em>n</em><sub>1</sub></span> rows and <span
class="math inline"><em>n</em><sub>2</sub></span> columns (a)
corresponds to a graph which is the Cartesian product of two complete
graphs (Rook’s graph) of <span
class="math inline"><em>n</em><sub>1</sub></span> and <span
class="math inline"><em>n</em><sub>2</sub></span> nodes respectively as
depicted in (b).</figcaption>
</figure>

If every cell of the chessboard is represented by the node of a graph
then, the vertical movement of the rook is a walk on a complete graph of
$n_1$ nodes and the horizontal movement corresponds to a walk on the
complete graph of $n_2$ nodes. So, overall there are $n_2-1$ number of
cliques (complete subgraphs) of $n_1$ nodes such that each node of an
$n_1$-sized clique is connected to the corresponding node in $n_2-1$
other cliques. The resulting graph has $n=n_1n_2$ vertices and each node
has degree $d=n_1+n_2-2$. This regular graph, known as the *Rook's
graph* [@moon1963line; @hoffman1964line], corresponds to the Cartesian
product of two complete graphs of $n_1$ nodes and $n_2$ nodes
respectively and is also vertex-transitive. This has been depicted in
Fig. [7](#figmain:chessboard){reference-type="ref"
reference="figmain:chessboard"}.

The Cartesian product of two graphs $G_1$ and $G_2$ is denoted as
$G_1\square G_2$. If the adjacency matrix of $G_1$ is $A_{G_1}$ and the
adjacency matrix of $G_2$ is $A_{G_2}$, then
$$A_{G_1\square G_2}= A_{G_1}\otimes I_{n_2}+ I_{n_1}\otimes A_{G_2},$$
where $\otimes$ denotes the Kronecker product and $I_j$ denotes the
identity matrix of dimension $j$. Thus, the adjacency matrix of the
Rook's graph is given by $$\begin{aligned}
\label{eq:adj-matrix-graph}
A_G&= A^{n_1}_{CG}\otimes I_{n_2}+ I_{n_1}\otimes A^{n_2}_{CG},
\end{aligned}$$ where $A^{n_1}_{CG}$ and $A^{n_2}_{CG}$ are the
adjacency matrices of the complete graph with $n_1$ vertices and $n_2$
vertices respectively. As an aside, note that the graph corresponding to
the case where $n_1=2$ and $n_2=n/2$ is the *bridged-complete graph* see
Fig. [1](#subfig:bridged-complete){reference-type="ref"
reference="subfig:bridged-complete"} and the case where $n_2=n$ and
$n_1=1$ is the complete graph.

We divide $A_G$ by the degree of each node $(n_1+n_2-2)$ and rescale its
eigenvalues so they lie between $0$ and $1$. So the Hamiltonian we
consider for the spatial search problem is the rescaled and shifted
version of $A_G$ which we denote by $H$. Without loss of generality, we
take $n_2\geq n_1$ (the case $n_1\geq n_2$ can be recovered simply by
exchanging the labels $1$ and $2$ i.e. what we refer to as horizontal
and vertical directions). Furthermore, we assume that $n_1=n^{\sigma}$
and $n_2=n^{1-\sigma}$ where $0<\sigma<1/2$.

It can be demonstrated that the Hamiltonian has 4 distinct eigenvalues
(except in the case $n_1=n_2$, when there are there only three) which
are shown in Table
[\[tab:evalues-chessboard\]](#tab:evalues-chessboard){reference-type="ref"
reference="tab:evalues-chessboard"} along with its degeneracies. Its
spectral gap is given by $$\label{eqmain:spectral-gap-chessboard}
\Delta_{RG}=1-\lambda_B=\Theta\left(\dfrac{n_1}{n_2}\right)=\Theta\left(\dfrac{1}{n^{1-2\sigma}}\right).$$
Hence, by changing the value of $\sigma$, both the gap as well as the
degeneracy of the different eigenvalues changes.

In what follows we shall analyse the problem of finding a marked node on
this graph for different regimes of $\sigma$. In particular, we will
highlight regimes of $\sigma$ where treating the first few eigenstates
of $H$ as quasi-degenerate shall help in deducing the algorithmic
running time.

::: center
::: tabular
\@lll@ Eigenvalue & Degeneracy\
$\lambda_A=1$   &   $1$\
$\lambda_B=\frac{n_2-\frac{1}{n_2}}{n_1+n_2-\frac{1}{n_1}-\frac{1}{n_2}}=1-\Theta(n^{2\sigma-1})$  
&   $n_1-1$\
$\lambda_C=\frac{n_1-\frac{1}{n_1}}{n_1+n_2-\frac{1}{n_1}-\frac{1}{n_2}}=\Theta(n^{2\sigma-1})$  
&   $n_2-1$\
$\lambda_D=0$  &   $(n_1-1)(n_2-1)$\
:::
:::

## Algorithmic performance when $\mathbf{r=S_1}$ {#subsec:r-S1-chessboard}

We will first analyse the performance of quantum search via the approach
developed in
Sec. [3](#sec:performance_non_degenerate){reference-type="ref"
reference="sec:performance_non_degenerate"}. In order to determine the
regime of validity of this approach we need to estimate the quantities
$\epsilon, S_1$, $S_2$ and $S_3$. First observe that the resultant graph
is symmetric and vertex-transitive, i.e. $|a_i|=1/\sqrt{n},~\forall i$,
where $a_i$ is as defined in
Eq. [\[eqmain:sol-in-eigenbasis\]](#eqmain:sol-in-eigenbasis){reference-type="eqref"
reference="eqmain:sol-in-eigenbasis"}. Consequently, we have
$\epsilon=1/n$.

Furthermore, using the definition of the parameters $S_k$ from
Eq. [\[eqmain:Sk\]](#eqmain:Sk){reference-type="eqref"
reference="eqmain:Sk"}, it can be shown that these parameters scale with
$n$ as $$\begin{aligned}
    S_k&= \Theta\left(\frac{n^{\sigma-1}}{(n^{2\sigma-1})^k}+1\right).
\end{aligned}$$ In particular, this implies that $$\begin{aligned}
S_1=\Theta(1)
\end{aligned}$$ and $$S _2 = \begin{cases}
        \Theta\left(n^{1-3\sigma}\right),~&\text{for } 0< \sigma\leq 1/3\\
        \Theta\left(1\right),~&\text{for } 1/3\leq \sigma \leq 1/2.
        \end{cases}$$ We can now verify the regime of validity of
*spectral condition* in
Eq.[\[eq:spectral_con\]](#eq:spectral_con){reference-type="eqref"
reference="eq:spectral_con"}, which is required for Theorem
[2](#lem_main:search-highest-estate){reference-type="ref"
reference="lem_main:search-highest-estate"} to be applied. It is easy to
verify that this holds only when $1/4\leq \sigma \leq 1/2$. Consequently
the amplitude of the final state of the algorithm with the marked vertex
is $$\begin{aligned}
\nu=\Theta\left(\frac{S_1}{\sqrt{S_2}}\right)&=\begin{cases}
       \Theta\left(n^{-(1-3\sigma)/2}\right),~&\text{for } 1/4\leq \sigma\leq 1/3\\
       \Theta\left(1\right),~&\text{for } 1/3\leq \sigma \leq 1/2,
        \end{cases}
\end{aligned}$$ after a time $$\begin{aligned}
T=\Theta\left(\dfrac{1}{\sqrt{\epsilon}}\dfrac{\sqrt{S_2}}{S_1}\right)&=\begin{cases}
       \Theta\left(n^{1-3\sigma/2}\right),~&\text{for } 1/4\leq \sigma\leq 1/3\\
       \Theta\left(\sqrt{n}\right),~&\text{for } 1/3\leq \sigma \leq 1/2.
       \end{cases}
\end{aligned}$$ The performance of the algorithm is thus quite distinct
in the following two regimes.\
 \
***i) $\mathbf{1/3\leq \sigma\leq 1/2}$:* ** In this regime the
algorithm is optimal, since $\nu=\Theta(1)$ after a time
$\Theta(\sqrt{n})$. This provides another example of optimal search for
graphs which do not have constant spectral gap. In fact, from
Eq. [\[eqmain:spectral-gap-chessboard\]](#eqmain:spectral-gap-chessboard){reference-type="eqref"
reference="eqmain:spectral-gap-chessboard"} we see that in this regime
the scaling of the spectral gap changes from $n^{-1/3}$ for $\sigma=1/3$
to constant for $\sigma=1/2$ .\
 \
***ii) $\mathbf{1/4\leq \sigma< 1/3}$:* ** In this regime, the algorithm
is suboptimal, as the final overlap with the marked node
$\nu=\Theta\left(n^{-(1-3\sigma)/2}\right)$ after
$T= \Theta\left(n^{1-3\sigma/2}\right)$. In the worst case, for
$\sigma=1/4$, even if we assume that amplitude amplification can be
used, one would need to evolve the walk for a total time of
$\Theta(n^{3/4})$ to find the marked node.  \
Interestingly, the Rook's graph within this region of $\sigma$ provides
an example of suboptimality even though in this regime we have that
$\Delta_{RG}\gg \sqrt{\epsilon}=n^{-1/2}$ (excluding in the case
$\sigma=1/4$). This proves that the latter condition is not sufficient
for optimal quantum search. In addition, given that the hitting time for
the Rook's graph is $\Theta(n)$ for any $\sigma$, this shows that there
exists a range of values of $\sigma$ for which the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm is slower
than the square root of the classical hitting time.

## Algorithmic performance when $\mathbf{r=S_{1,\bar{\mathcal{\mathbf{D}}}}}$

In order to go beyond the limitations imposed by the spectral condition
of Eq. [\[eq:spectral_con\]](#eq:spectral_con){reference-type="eqref"
reference="eq:spectral_con"}, which is only valid in the regime
$1/4\leq \sigma\leq 1/2$, we use the analysis of
Sec. [4](#sec:search-degenerate-spectra){reference-type="ref"
reference="sec:search-degenerate-spectra"}. It is expected that this
analysis is valid for low values of $\sigma$, since the gap
$1-\lambda_B$ becomes very small
(Eq. [\[eqmain:spectral-gap-chessboard\]](#eqmain:spectral-gap-chessboard){reference-type="eqref"
reference="eqmain:spectral-gap-chessboard"}) whereas the gap
$1-\lambda_C=\Theta(1)$ is much larger (see
Table [\[tab:evalues-chessboard\]](#tab:evalues-chessboard){reference-type="ref"
reference="tab:evalues-chessboard"}).

Hence, we will treat the eigenstate with eigenvalue $\lambda_A=1$ and
the $n_1-1$ eigenstates with eigenvalue $\lambda_B$ as
*quasi-degenerate*. To be consistent with the notation in
Sec. [4](#sec:search-degenerate-spectra){reference-type="ref"
reference="sec:search-degenerate-spectra"}, we denote this space as
$\ensuremath{\mathcal{D}}$ such that
$D=|\ensuremath{\mathcal{D}}|=n_1=n^\sigma$. In addition, the gaps
$\Delta_\ensuremath{\mathcal{D}}$ and $\Delta$ defined in
Sec. [4](#sec:search-degenerate-spectra){reference-type="ref"
reference="sec:search-degenerate-spectra"} are in this case
$$\begin{aligned}
  \Delta_\ensuremath{\mathcal{D}}&\equiv \Delta_{RG}=1-\lambda_B=\Theta(n^{2\sigma-1}),\\
  \Delta&=1-\lambda_C=\Theta(1).
\end{aligned}$$ The projection of the marked node $\ket{w}$ in the
quasi-degenerate subspace $\ensuremath{\mathcal{D}}$ is
$$\label{eqmain:epsilon-D-chessboard}
\epsilon_\ensuremath{\mathcal{D}}=\frac{D}{n}=\frac{n_1}{n},$$ where we
have used the fact that the underlying graph is vertex-transitive
implying that $|a_i|^2=1/n,~\forall i$. The parameters
$S_{k,\bar{\ensuremath{\mathcal{D}}}}$, defined in
Eq. [\[eqmain:Sk-D\]](#eqmain:Sk-D){reference-type="eqref"
reference="eqmain:Sk-D"}, are given by $$\begin{aligned}
S_{k,\bar{\ensuremath{\mathcal{D}}}}&=\frac{1}{n} \left[\dfrac{n_2-1}{(1-\lambda_C)^k}+\dfrac{(n_1-1)(n_2-1)}{(1-\lambda_D)^k}\right]\\
         &=1+\Theta(1/n_1)=\Theta(1),
\end{aligned}$$ $\forall k\geq 1$.

For Theorem [8](#thm:performance_qd){reference-type="ref"
reference="thm:performance_qd"} to hold, we require that both conditions
Eqs. [\[eq:lowerbound_epsilonD\]](#eq:lowerbound_epsilonD){reference-type="eqref"
reference="eq:lowerbound_epsilonD"} and
[\[eq:spec-cond-deg\]](#eq:spec-cond-deg){reference-type="eqref"
reference="eq:spec-cond-deg"} are satisfied. Since $\Delta$ and the
parameters $S_{k,\bar{\ensuremath{\mathcal{D}}}}$ are constants, the
condition in
Eq. [\[eq:spec-cond-deg\]](#eq:spec-cond-deg){reference-type="eqref"
reference="eq:spec-cond-deg"} is valid for any $0\leq \sigma < 1/2$. On
the other hand, it can be shown that
[\[eq:lowerbound_epsilonD\]](#eq:lowerbound_epsilonD){reference-type="eqref"
reference="eq:lowerbound_epsilonD"} is valid as long as
$\sigma\leq 1/4$. Hence, Theorem
[8](#thm:performance_qd){reference-type="ref"
reference="thm:performance_qd"} allows us to predict the performance of
the algorithm for the choice of $r=S_{1,\bar{\ensuremath{\mathcal{D}}}}$
and in the regime $0\leq \sigma\leq 1/4$.

::: table*
::: center
   Range of $n_1=n^\sigma$                  $r=S_1$                                                               $r=S_{1,\bar{\ensuremath{\mathcal{D}}}}$     
  -------------------------- -------------------------------------- ----------------------------------------- ------------------------------------------------ ------------------------------------------------
             2-5                              $T$                                     $\nu$                                         $T$                                             $\nu$
     1-5 $n_1=\Theta(1)$                       --                                      --                              $\Theta\left(\sqrt{n}\right)$                             $\Theta(1)$
        $0<\sigma<1/4$                         --                                      --                      $\Theta\left(\sqrt{\frac{n}{n^\sigma}}\right)$   $\Theta\left(\frac{1}{\sqrt{n^\sigma}}\right)$
    $1/4\leq \sigma <1/3$     $\Theta\left(n^{1-3\sigma/2}\right)$   $\Theta\left(n^{-(1-3\sigma)/2}\right)$                         --                                               --
   $1/3\leq \sigma\leq 1/2$      $\Theta\left(\sqrt{n}\right)$                     $\Theta(1)$                                       --                                               --
:::
:::

We obtain that, after a time $$\label{eq:time-chessboard}
T=\Theta\left(\dfrac{\sqrt{S_{2,\bar{\ensuremath{\mathcal{D}}}}}}{S_{1,\bar{\ensuremath{\mathcal{D}}}}}\dfrac{1}{\sqrt{\epsilon_{\ensuremath{\mathcal{D}}}}}\right)=\Theta\left(\sqrt{\dfrac{n}{n_1}}\right)=\Theta\left(\sqrt{n^{1-\sigma}}\right),$$
Algorithm [\[algo-cg-general\]](#algo-cg-general){reference-type="ref"
reference="algo-cg-general"} prepares a state that has an overlap of
$$\label{eq:amp-chessboard}
\nu =\Theta\left(\sqrt{\dfrac{\epsilon}{\epsilon_\ensuremath{\mathcal{D}}}}\frac{S_{1,\bar{\ensuremath{\mathcal{D}}}}}{\sqrt{S_{2,\bar{\ensuremath{\mathcal{D}}}}}}\right)=\Theta\left(\frac{1}{\sqrt{n_1}}\right)=\Theta\left(\frac{1}{\sqrt{n^\sigma}}\right)$$
with the marked node. We discuss the following two cases:\
 \
***i) constant $\mathbf{n_1}$ $(\mathbf{\sigma=0})$:* ** In this regime,
the algorithm is optimal, as the marked node is found with a constant
probability after $T=\Theta\left(\sqrt{n}\right)$. Note that, as
mentioned before, the *bridged-complete graph* corresponds to the choice
of $n_1=2$ and $n_2=n/2$. As such, this demonstrates the optimality of
the algorithm for this instance.\
 \
***ii) $\mathbf{n_1=n^\sigma}$, with $\mathbf{0<\sigma<1/4}$:* ** In
this range, the amplitude at the marked node is $\Theta(1/\sqrt{n_1})$
after $\Theta(\sqrt{n/n_1})$ time. If the quantum amplitude
amplification procedure is available, then using $\sqrt{n_1}$ rounds of
amplitude amplification, the marked node can be obtained for
$T=\Theta(\sqrt{n})$, however, with an overhead due to the need of
reflecting on the initial state that has a certain set-up cost (in this
case the total cost is given by
Eq. [\[eq:cost_deg_nuequal1\]](#eq:cost_deg_nuequal1){reference-type="eqref"
reference="eq:cost_deg_nuequal1"}).

On the other hand, if we assume access to simply the time evolution
according to $H_{\mathrm{search}}$, we have to repeat the entire
procedure $\sim n_1$ times to find the marked node, leading to an
overall evolution time of $T=\Theta(\sqrt{n.n_1})$. However, as we
previously pointed out, the predicition from
Theorem [8](#thm:performance_qd){reference-type="ref"
reference="thm:performance_qd"} does not guarantee that this is the best
possible performance. We leave open the question of whether a better
running time can be obtained for a different choice of $r$. Indeed, one
would expect that the best choice of $r$ should converge to the value
$S_1$ at $c=1/4$ and recover the prediction of
Sec. [5.2](#subsec:r-S1-chessboard){reference-type="ref"
reference="subsec:r-S1-chessboard"}.\
 \

# Discussion {#sec:discussion}

In this article, we provide the necessary and sufficient conditions for
the $\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm to be
optimal, assuming very general conditions on the spectrum of the
Hamiltonian encoding the structure of the underlying graph. An immediate
consequence is that our necessary and sufficient conditions hold for all
graphs whose normalized adjacency matrices exhibit a large enough
spectral gap ($\Delta\gg \sqrt{\epsilon}$). Additionally, we also
provide strategies to analyze the algorithmic performance for graphs
with a few quasi-degenerate highest eigenvalues, followed by a large
gap. Such spectral features appear, for example, in graphs composed by a
few clusters with sparse connections among them. Our work implies that,
to the best of our knowledge, all prior results demonstrating the
optimality of the algorithm for specific graphs, requiring
instance-specific analysis, can now be recovered from our general
results. We also provided an explicit example, namely, the application
of the $\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm to
the Rook's graph which highlights the predictive power of our results
and the limitations of this search algorithm, which is suboptimal for
certain regimes of the "aspect ratio" of the chessboard.

Our results provide a recipe to compute analytically the performance of
the $\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm on any
graph fulfilling the spectral conditions required for our main theorems
to be valid (Theorem
[2](#lem_main:search-highest-estate){reference-type="ref"
reference="lem_main:search-highest-estate"} and
[8](#thm:performance_qd){reference-type="ref"
reference="thm:performance_qd"}). They can hence be used to analyse
quantum search on graphs that have not been previously studied or on
graphs that were analysed only numerically such as the Chimera
graph [@glos2019impact] -- a graph that encodes the underlying
architecture of the hardware of quantum annealers.

We remark that our results are not directly applicable, but could in
principle be extended, to some modified versions of the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm. For
example, it would be interesting to extend our analysis to encompass
strategies with different choices of the parameter $r$ for different
evolution times. Such strategies have been known to improve the
algorithmic performance for some graphs [@meyer2015connectivity]. We
also note that our results are only valid for the oracle Hamiltonian
introduced in [@childs2004spatial], which singles out the marked node by
adding a local energy term to the Hamiltonian. Different oracles, which
remove edges connected to the marked node, have been considered in works
that show optimal quantum search on certain lattices such as graphene
[@foulger2014quantum] or crystal lattices [@childs2014spatial-crystal].
General conditions for optimal quantum search with such oracles are
still unknown (some progress has been made in
[@chakraborty2018finding]).

Our work further highlights the difficulty in comparing the performance
of the $\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm to
its classical counterpart (search by a classical random walk), where the
performance is measured by the classical hitting time. In fact, it is
not clear how the expressions that we have obtained for predicting the
performance of this quantum search algorithm relate to this classical
quantity. We can nevertheless guarantee that whenever the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm is optimal,
there exists at least a quadratic speed-up with respect to the classical
hitting time, since the latter is lower bounded by $1/\epsilon$ (see
Eq. [\[eqmain:hitting-time-bounds\]](#eqmain:hitting-time-bounds){reference-type="eqref"
reference="eqmain:hitting-time-bounds"}). However, we also proved that
the $\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm fails
to achieve quadratic speedups with respect to classical search in some
cases, as evidenced by the algorithmic running time on the Rook's graph
in the suboptimal regime (See
Eq. [\[eq:time-chessboard\]](#eq:time-chessboard){reference-type="eqref"
reference="eq:time-chessboard"} and
Eq. [\[eq:amp-chessboard\]](#eq:amp-chessboard){reference-type="eqref"
reference="eq:amp-chessboard"}).

Different quantum walk based algorithms are known to achieve this
general quadratic speed-up in the discrete-time framework
[@szegedy2004quantum; @krovi2016quantum; @ambainis2019quadratic] and in
continuous-time, as recently demonstrated in
Ref. [@chakraborty2018finding]. In the latter work, we propose a new
continuous-time time quantum walk algorithm based on the time-evolution
of a Hamiltonian encoding an interpolating Markov chain. Compared to the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm, it has the
additional advantages that it can be applied to any ergodic, reversible
Markov chain and has a guaranteed performance even when there are
multiple marked nodes.

We also propose a modified version of the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm that is
applicable to search problems on Markov chains [@chakraborty2018finding]
which can be seen as a quantum walk on the edges and thus requires an
extension of the walk's Hilbert space. This modified algorithm improves
upon the performance of the original
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm for several
instances such as lattices of dimension less than five. In particular,
this modified algorithm can find a marked node on the Rook's graph in
$\Theta(\sqrt{n})$ time for any dimensions of the chessboard, without
requiring amplitude amplification. However, the modified
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm does not
provide a generic speedup over the
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm and
counterexamples have also been demonstrated in
Ref. [@chakraborty2018finding]. Moreover, a simple comparison of the
performance of this modified
$\ensuremath{\mathcal{C}}\ensuremath{\mathcal{G}}$ algorithm to the
classical hitting time remains elusive.

An interesting direction of future research would be to explore the
possibility of using continuous-time quantum walks to solve optimization
problems, namely, to find ground states of classical Ising Hamiltonians
which encode the solution to some NP-Hard problems [@lucas2014ising].
Recently, the applicability of CTQW to tackle this problem has been
numerically investigated [@callison2019finding]. In this approach, each
node represents a spin configuration, and the idea is to perform a
continuous-time quantum walk on a graph where the local energies of each
node, instead of being set by an oracle, corresponds to the energy of
this respective configuration according to the Ising Hamiltonian. The
aim is thus to use the quantum walk to find the node of minimum energy
faster than classical methods. In Ref [@callison2019finding], the
authors observe that this approach leads a faster than quadratic
speedup, with respect to unstructured search, in the time required to
find the ground state of random Ising Hamiltonians, for quantum walks on
certain graphs. We remark that when the underlying graph of this quantum
walk is the complete graph, our results can be used to make some
analytical predictions, since the Hamiltonian of the walk has the form
$H+r P$, where $P$ is a one-dimensional projector (in this case, $H$ is
the classical Ising Hamiltonian and the adjacency matrix of the complete
graph is a one-dimensional projector). It would be interesting if
extensions of our results could help derive analytical expressions for
the performance of this approach on different graphs. This could lead to
a better understanding of the potential of CTQW-based algorithms to
solve optimization problems.\
 \

::: acknowledgments
S.C. and J.R. are supported by the Belgian Fonds de la Recherche
Scientifique - FNRS under grants no F.4515.16 (QUICTIME) and
R.50.05.18.F (QuantAlgo). S.C. and L.N. acknowledge support from
F.R.S.-FNRS. L.N. also acknowledges funding from the Wiener-Anspach
Foundation.
:::

[^1]: Throughout the article, we use a plethora of complexity theoretic
    notations which we briefly define now. $f(n)=\mathcal{O}(g(n))$, if
    there exists a positive constant $c$ such that $|f(n)|\leq c. g(n)$.
    If $f(n)=\mathcal{O}(g(n))$, then $g(n)=\Omega(f(n))$. Also
    $f(n)=o(g(n))$ if for all positive constants $k$, $|f(n)|<k.g(n)$.
    Consequently, if $f(n)=o(g(n))$, then $g(n)=\omega(f(n))$.

[^2]: It is worth mentioning, that throughout the article we consider
    the scenario where only a single node is marked and analogous
    results for multiple marked nodes is an open problem in this
    framework.

[^3]: This can be ensured by replacing $H$ with $(H/||H||+I)/2$, where
    $I$ is the identity matrix.

[^4]: The cost of reflecting on this state can be quantified as
    $2\mathcal{S}$. However, we shall omit constant factors for
    simplicity.

[^5]: The results of [@berry2017exponential] on simulating continuous
    query models can be used to quantify the cost of implementing
    time-evolution of $H_{search}$ in terms of discrete queries to the
    Grover oracle as well as the cost of simulating $H$ and the error of
    the simulation.

[^6]: For non vertex-transitive graphs, the structure can be such that
    certain particular nodes can be found faster than $\sqrt{n}$ time.
    For example, the central node on a star graph can be found in
    constant time. However, if any of the graph's nodes can be marked,
    the minimum time needed to find any node in a graph is lower bounded
    by $\sqrt{n}$ [@farhi1998analog].

[^7]: This is possible independently of the position of the marked node
    $\ket{w}$, for example, if the Hamiltonian is diagonalized by the
    Fourier transform.

[^8]: From the Perron-Frobenius theorem,
    $\Delta_\ensuremath{\mathcal{D}}$ can never zero for the adjacency
    matrix (or Laplacian) of a connected graph.

[^9]: Since we are assuming $D$ eigenstates with eigenvalue $1$,
    $\ket{v_n}$ can be any state in the subspace
    $\ensuremath{\mathcal{D}}$.
