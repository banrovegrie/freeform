# Message for Shantanav

**Subject:** Sanity check on a minimax result for gap-uninformed schedules

Hi Shantanav,

I have been exploring a theorem connecting your NP-hardness result with Guo-An's optimality results. After some self-critique, I think I have the framing right, but want your assessment.

## The Result

This is a pure minimax statement with no complexity theory in the theorem itself.

**Theorem (Minimax Lower Bound).** Let $\mathcal{C}$ be a class of $n$-qubit Hamiltonians where the spectral gap minimum $s^* = A_1/(A_1+1)$ can lie anywhere in $[s_L, s_R]$. For any fixed schedule $u$,

$$\max_{H \in \mathcal{C}} \frac{T(u, H)}{T_{\mathrm{opt}}(H)} \geq \frac{s_R - s_L}{\delta_s}$$

where $T(u, H)$ is the runtime for schedule $u$ on instance $H$, and $T_{\mathrm{opt}}(H) = O(1/\Delta_*)$ is the optimal gap-informed runtime.

**Corollary.** For Ising Hamiltonians with $A_1 \in [\Omega(1), O(\mathrm{poly}(n))]$, we have $s_R - s_L = \Theta(1)$ and $\delta_s = \Theta(\Delta_*) = \Theta(2^{-n/2})$, giving

$$\frac{T_{\mathrm{uninformed}}}{T_{\mathrm{informed}}} = \Omega(2^{n/2})$$

## The Argument

1. The adversary sees the fixed schedule $u$, then picks $H \in \mathcal{C}$ to place $s^*$ where $u$ is fastest.

2. If $u$ has velocity $v(s) > \Delta_*^2$ anywhere in $[s_L, s_R]$, the adversary exploits it.

3. Therefore $u$ must satisfy $v(s) \leq O(\Delta_*^2)$ throughout $[s_L, s_R]$.

4. Time to traverse $[s_L, s_R]$: $T_{\mathrm{unf}} \geq (s_R - s_L)/\Delta_*^2$.

5. Ratio: $T_{\mathrm{unf}}/T_{\mathrm{inf}} = [(s_R - s_L)/\Delta_*^2] / [1/\Delta_*] = (s_R - s_L)/\Delta_*$.

## Connection to NP-Hardness

This is an **observation about model relevance**, not part of the theorem.

The NP-hardness of computing $A_1$ implies that polynomial-time preprocessing cannot determine $s^*$. Therefore, algorithms with fixed schedules and poly-time preprocessing are forced into the gap-uninformed model and subject to the minimax bound.

**Important:** I am NOT claiming "NP-hardness implies $2^{n/2}$ slowdown." The logical chain is:
- NP-hardness $\Rightarrow$ cannot compute $s^*$ $\Rightarrow$ forced into gap-uninformed model
- Gap-uninformed model has minimax lower bound (game-theoretic, not complexity-theoretic)
- Therefore this class of algorithms pays the $\Omega(2^{n/2})$ penalty

## Contrast with Adaptive Methods

Han-Park-Choi 2025 achieves $O(1/\Delta_*)$ without prior spectral knowledge via adaptive probing during evolution. The minimax bound only applies to **fixed** schedules determined before evolution begins.

## My Questions

1. Is the pure minimax result already known or folklore?

2. Is the connection to NP-hardness correctly stated? I am NOT claiming the bound follows from NP-hardness, only that NP-hardness justifies the model.

3. Is the instance class well-defined? Does $A_1$ actually range over $[\Omega(1), O(\mathrm{poly}(n))]$ for Ising Hamiltonians as stated in the paper?

4. Is this worth developing, or is it too simple an observation to include in the thesis?

Thanks,
Alapan
