# Structured Tractability: When is A_1 Polynomial-Time Computable?

## Problem Statement

The hardness results apply to general Hamiltonians. Are there structured cases where A_1 is efficiently computable?


## Why Novel

The paper proves hardness for general H but doesn't characterize tractable cases. Finding such cases would identify problems where AQO is provably optimal.


## Key Finding

A_1 is polynomial-time computable for Hamiltonians with low-dimensional spectral structure:

**Example**: Complete graph Ising model H = J sum_{i<j} sigma_z^i sigma_z^j
- Spectrum parameterized by magnetization m (1-dimensional)
- Degeneracies are binomial coefficients C(n,m)
- A_1 = sum of O(n) efficiently computable terms


## Tractable Cases Identified

1. Complete graph Ising (magnetization structure)
2. Permutation-invariant Hamiltonians (total spin)
3. Product Hamiltonians H = H_1 ⊗ H_2
4. Mean-field models


## Conjectures

1. A_1 tractability is characterized by "spectral dimension" - how many parameters describe the spectrum
2. dim(H) = O(log n) implies A_1 in P
3. General H has dim(H) = Theta(2^n), recovering NP-hardness


## Status

**Exploratory**. Analysis in `notes/`. Numerical verification in `lib/`. No formal theorem yet.


## Relation to Other Experiments

- Predecessor to 08_structured_tractability_v2 (more refined analysis)
- Complements 01_precision_gap (structure vs precision)


## References

- Original paper (hardness proofs)
- Schur-Weyl theory (permutation-invariant systems)
- Notes in `notes/structured_tractability.md`
