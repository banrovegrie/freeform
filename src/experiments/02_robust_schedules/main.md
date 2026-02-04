# Robust Schedules: Instance-Independent Performance

## Problem Statement

Can schedules achieve good performance without knowing A_1 or the specific problem instance?


## Why Novel

The paper focuses on optimal (A_1-informed) vs worst-case (uninformed). The middle ground of "robust" schedules that work well on average without calibration is unexplored theoretically.


## Key Finding (Empirical)

Instance-independent schedules that slow down over [0.4, 0.8] achieve 50-90% of the total scheduling benefit without any calibration:

| n | Uniform | Wide [0.4,0.8] | A_1-Informed | Instance-Independent Benefit |
|---|---------|----------------|--------------|------------------------------|
| 8 | 0.652 | 0.805 | 0.827 | ~90% |
| 10 | 0.600 | 0.693 | 0.828 | ~50% |
| 12 | 0.545 | 0.657 | 0.762 | ~50% |


## Conjectures

1. Instance-independent schedules can achieve constant-factor approximation to optimal
2. The benefit of A_1 knowledge grows with system size
3. Simple "slow around the middle" captures most of the value


## Status

**Exploratory**. Numerical results in `lib/` and `notes/`. No rigorous bounds yet.


## Relation to Other Experiments

- Motivates 07_partial_information (how much precision is "enough"?)
- Empirical complement to 04_separation_theorem (worst-case vs average-case)


## References

- Original paper (local vs uniform schedules)
- Numerical results in `notes/FINAL_CONTRIBUTION.md`
