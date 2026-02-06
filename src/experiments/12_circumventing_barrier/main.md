# Circumventing the Barrier: Modified Hamiltonians and the A_1 Dependence

## Problem Statement

The paper proves that the optimal adiabatic schedule requires knowledge of $s^* = A_1 / (A_1 + 1)$, and that computing $A_1$ is NP-hard. The Discussion section explicitly poses the question: can we modify the adiabatic Hamiltonian (adding ancilla qubits, intermediate Hamiltonians) so that $s^*$ no longer depends on the problem spectrum?

**Central Question**: Can tensor product ancilla extensions or multi-segment adiabatic paths eliminate the dependence of $s^*$ on $A_1(H_z)$?

**Answer**: No, within the rank-one framework with instance-independent design.


## Why Novel

The paper identifies this as the central open problem (Discussion, p.983):
> "expanding the dimension of the Hamiltonian (by adding qubits) and introducing intermediate Hamiltonians at various points in the adiabatic path. These strategies can potentially shift the position of the avoided crossing to a point independent of the spectrum of the problem Hamiltonian."

This experiment directly attacks the question. The result is negative: neither ancillas nor multi-segment paths can eliminate the $A_1$ dependence within the rank-one framework. The proof is constructive and identifies the precise mechanism (universality of the uniform superposition).

The same $A_1$ barrier applies to the non-adiabatic oscillation algorithm (forthcoming [Eduardo]), since it uses the same Hamiltonian family.


## Results

**Status**: COMPLETE

### Theorem 1 (Product State Invariance)
For any product initial state $|\Psi\rangle = |\psi_0\rangle \otimes |\phi\rangle$ and uncoupled final Hamiltonian $H_z \otimes I_{2^m}$, the eigenvalue branches participating in the avoided crossing are identical to the bare system. The crossing position is exactly $s^* = A_1/(A_1+1)$, unchanged by the ancilla.

This is STRONGER than the original Conjecture 1, which predicted a correction. There is no correction: the ancilla does literally nothing to the crossing.

### Theorem 2 (Universality of Uniform Superposition)
Among all states $|\psi\rangle \in \mathbb{C}^N$, the uniform superposition $|\psi_0\rangle = (1/\sqrt{N})\sum_z |z\rangle$ is the unique state (up to phases on individual basis states) for which the weights $w_k = \sum_{z \in \Omega_k} |\langle z|\psi\rangle|^2$ depend only on $\{E_k, d_k\}$ and not on the specific assignment of energies to basis states. This extends to entangled initial states on $\mathbb{C}^N \otimes \mathbb{C}^{2^m}$: the reduced weights $q(z) = \sum_a |\langle z,a|\Psi\rangle|^2$ must satisfy $q(z) = 1/N$ for all $z$.

This is the key structural result. Any instance-independent algorithm must use the uniform superposition, fixing the crossing at $A_1/(A_1+1)$.

### Theorem 3 (Coupled Ancilla Extension)
No fixed instance-independent system-ancilla coupling $V$ makes $A_1^{\text{eff}}$ constant across all problem instances. The effective crossing position $s^*_{\text{ext}}$ remains a non-constant function of the spectrum. Proved via large-$\Delta$ asymptotics: $A_1^{\text{eff}}(\Delta) = C_{\text{ground}}(V) + \Theta(1/\Delta)$ where the excited-cluster contribution varies with $\Delta$. Numerically verified across coupling strengths $\lambda \in \{0.01, 0.05, 0.1, 0.5, 1.0\}$.

### Theorem 4 (Multi-Segment Rigidity)
For a multi-segment adiabatic path, the crossing in the final segment depends on $B_1 = \sum_k w_k(\psi_{\text{mid}})/(E_k - E_0)$. By Theorem 2, instance-independence forces $|\psi_{\text{mid}}\rangle = |\psi_0\rangle$, giving $B_1 = A_1$.

### Theorem 5 (No-Go)
For any adiabatic algorithm using rank-one initial Hamiltonian, encoding the same unstructured optimization problem, with instance-independent design: the crossing position cannot be made spectrum-independent. In the uncoupled case, $\partial s^*/\partial A_1 = 1/(A_1+1)^2 > 0$ quantitatively. In the coupled case, $A_1^{\text{eff}}$ is non-constant across instances (Theorem 3).

### Corollary (Non-Adiabatic Oscillation)
The $A_1$ barrier applies to the non-adiabatic oscillation algorithm (forthcoming [Eduardo]) since it uses the same Hamiltonian $H(s) = -(1-s)|\psi_0\rangle\langle\psi_0| + sH_z$.


## Conjecture Status

### Conjecture 1 (Single Ancilla Failure): DISPROVED
Original claim: $A_1^{\text{combined}} = (1/2)A_1(H_z) + \text{correction}$. Actual result: $A_1^{\text{combined}} = A_1(H_z)$ exactly (no factor of 1/2, no correction). The ancilla subspace decouples completely, and the crossing branches are identical to the bare system.

### Conjecture 2 (General Ancilla Suppression): DISPROVED
Original claim: correction is $O(d_0/N)$. Actual result: for uncoupled product ancilla, the correction is exactly ZERO (Theorem 1). The claim about $d_0/N$ suppression is irrelevant.

### Conjecture 3 (Multi-Segment Rigidity): PROVED (Theorem 4)
The crossing in the final segment depends on $A_1$ through the overlaps. Instance-independence forces $B_1 = A_1$.

### Conjecture 4 (Informal No-Go): PROVED (Theorem 5)
Stronger than originally stated. The mechanism is the universality of the uniform superposition (Theorem 2), not $d_0/N$ suppression.

### Conjecture 5 (Escape Requires Spectral Knowledge): PROVED (Theorem 2 converse)
Non-uniform states can change the effective $A_1$, but computing the right state requires knowing which basis states have which energies.


## Approach

### What Worked
1. Subspace decomposition of the extended Hamiltonian (Theorem 1)
2. Permutation argument for universality (Theorem 2)
3. Secular equation analysis throughout
4. Numerical verification for all theorems via exact diagonalization

### What Changed from Original Plan
1. The original perturbative analysis for Theorem 3 was wrong: naive $O(\|V\|/\Delta)$ bounds fail because coupling can split ground levels, creating $1/\|V\|$ divergences in $A_1^{\text{eff}}$. Replaced with a qualitative argument showing instance-independent $V$ cannot collapse $s^*$.
2. Conjecture 1 was completely wrong: predicted a correction where there is none.


## Open Questions

1. Can higher-rank initial Hamiltonians ($H_0 = -P$ with $\text{rank}(P) > 1$) circumvent the barrier?
2. Can time-dependent couplings $V(s)$ eliminate the $A_1$ dependence? (Theorem 3 only covers fixed $V$.)
3. Can non-rank-one intermediate Hamiltonians circumvent Theorem 4? (The secular equation analysis requires rank one.)
4. Is there a polynomial-time quantum algorithm that estimates $A_1$ to sufficient precision?
5. Can non-adiabatic protocols (beyond oscillation) bypass the barrier entirely?
6. For structured problems, does the barrier persist or does exploitable structure change the picture?


## Connection to Other Experiments

- Subsumes 08 (structured tractability): if ancillas could eliminate $A_1$ dependence, tractability becomes irrelevant
- Complements 13 (intermediate hardness): circumvention fails, so the complexity question becomes more urgent
- Informs 05 (adaptive schedules): adaptive measurement may be the only escape from the barrier
- Applies to non-adiabatic oscillation: same Hamiltonian, same $A_1$ barrier


## References

1. Paper Discussion, p.983 - Explicit open problem statement
2. Paper Section 3 - Hardness of $A_1$
3. Paper Section 2.1 - Spectral analysis and crossing position
4. Roland-Cerf 2002 - Local adiabatic schedule (motivates the $s^*$ dependence)


## Status

**Phase**: Complete

**Open problem note**: Directly addresses the paper's central open problem (Discussion, p.983). The answer is negative within the rank-one framework. Also applies as a corollary to the non-adiabatic oscillation setting (same $A_1$ barrier).
