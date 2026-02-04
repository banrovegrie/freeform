# Precision Gap: Complexity at Intermediate Precision

## Problem Statement

The paper establishes:
- NP-hard: approximating A_1 to precision 1/poly(n)
- #P-hard: approximating A_1 to precision 2^{-poly(n)}

AQO requires precision ~2^{-n/2}, which falls in between. What is the complexity at this intermediate precision?

```
Precision:  1/poly(n)  <------ 2^{-n/2} ------>  2^{-poly(n)}
Complexity:   NP-hard           ???                #P-hard
```


## Why Novel

The paper explicitly acknowledges this gap (line 962): "Unfortunately, these proof techniques based on polynomial interpolation do not allow us to conclude anything about the hardness of the approximation of A_1(H) up to the additive error tolerated by the adiabatic algorithm."


## Conjectures

1. The complexity at precision 2^{-n^alpha} interpolates smoothly with alpha
2. There exists a threshold alpha_c where complexity jumps (phase transition)
3. For unique solution problems (d_0 = 1), the required precision 2^{-n/2} might be easier


## Approach

- Attempt to extend NP-hardness proof to finer precision
- Look for problems with exponentially small promise gaps
- Investigate counting hierarchy connections


## Status

**Exploratory**. Initial analysis in `notes/precision_gap_analysis.md`. No proofs yet.


## Relation to Other Experiments

- Complements 07_partial_information (complexity vs runtime perspective)
- Informs 08_structured_tractability (precision requirements may differ by structure)


## References

- Original paper Section 3 (hardness proofs)
- Counting hierarchy literature
- Promise problem complexity
