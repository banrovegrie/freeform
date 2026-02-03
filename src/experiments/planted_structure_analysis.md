# A_1 Tractability for Problems with Planted Structure

## Motivation

The paper's hardness results apply to GENERAL Hamiltonians. Many practical problems have additional structure, particularly those with "planted" solutions.

**Key observation**: If the cost function depends only on distance from the optimal solution, A_1 becomes tractable.


## Spherically Symmetric Cost Functions

**Definition**: A Hamiltonian H has *spherically symmetric* structure around state |x*> if:

E_x = f(d_H(x, x*))

where d_H is Hamming distance and f is an increasing function.

**Theorem**: For spherically symmetric Hamiltonians, A_1 is computable in O(n^2) time.

**Proof**:

The degeneracy at distance d is C(n,d) (choosing which d bits to flip).

A_1 = (1/N) sum_{d=1}^{n} C(n,d) / (f(d) - f(0))

This is a sum of n terms, each computable in O(n) time.

QED.


## Example: Linear Cost Function

For f(d) = c * d (linear cost):

A_1 = (1/N) * (1/c) * sum_{d=1}^{n} C(n,d) / d

Let S_n = sum_{d=1}^{n} C(n,d) / d.

**Computing S_n**:

Using the identity sum_{d=0}^{n} C(n,d) * x^d = (1+x)^n:

Integrating: sum_{d=0}^{n} C(n,d) * x^{d+1} / (d+1) = integral of (1+x)^n

This gives: sum_{d=1}^{n+1} C(n,d-1) / d * x^d = ((1+x)^{n+1} - 1) / (n+1)

Setting x = 1: sum_{d=1}^{n+1} C(n,d-1) / d = (2^{n+1} - 1) / (n+1)

Rearranging: sum_{d=1}^{n} C(n,d) / d = n * sum_{d=1}^{n} C(n-1,d-1) / (n*d)
                                        = ... (more algebra needed)

**Numerical evaluation**: For n = 10, S_10 ≈ 234.4, so A_1 ≈ 0.23/c.


## Relevance to Hard Problems

**Planted SAT**: A planted SAT instance has a known satisfying assignment x*. The clause structure is designed so that x* satisfies all clauses, and random assignments violate many.

For planted random k-SAT:
- E_x ≈ (number of violated clauses)
- Violated clauses ~ (number of "wrong" variables) for well-designed instances
- This gives approximately linear cost structure

**Planted MAX-CUT**: A planted partition is hidden in a random graph. The cut value depends approximately on how close the partition is to the planted one.

**Planted Clique**: A clique is planted in a random graph. The cost can be designed to depend on overlap with the planted clique.


## Key Insight

**For problems with planted structure, the cost function often exhibits approximate spherical symmetry around the planted solution.**

If we know (or can estimate) the symmetry parameters, A_1 becomes tractable even though:
- The ground state degeneracy d_0 = O(1) (hard problem)
- The precision requirement is 2^{-n/2} (falls in complexity gap)


## What We Need to Estimate

To use this approach, we need:
1. The function f(d) (cost vs. distance profile)
2. The "center" x* of the cost function

**Issue**: Knowing x* means we've solved the problem!

**Resolution**: We don't need to know x* exactly. We need the AVERAGE cost profile:

E[f(d)] over random planted instances

This is a property of the DISTRIBUTION, not the specific instance.


## A Concrete Result

**Proposition**: Let H be drawn from a planted random problem ensemble where:
1. The ground state |x*> is planted uniformly at random
2. E_x = f(d_H(x, x*)) + noise, where noise has small variance

Then A_1 concentrates around:

A_1 ≈ (1/2^n) * sum_{d=1}^{n} C(n,d) / f(d)

and this value is computable in O(n) time given knowledge of f.


## Implications

1. **No instance-specific calibration needed**: The optimal A_1 depends only on the problem DISTRIBUTION, not the specific instance.

2. **Practical recommendation**: For planted problems, estimate f(d) from the problem structure, compute the universal A_1, and use it for all instances.

3. **Robustness**: Instance-to-instance variation in A_1 is small, so using the ensemble average introduces only mild error.


## What Would Make This Significant

To verify this is a genuine contribution:

1. [ ] Check if planted problems have been studied in AQO context
2. [ ] Verify the concentration claim for specific planted ensembles
3. [ ] Quantify the error from using ensemble A_1 instead of instance A_1
4. [ ] Compare against the paper's hardness results (which apply to worst-case)


## Honest Assessment

**Is this novel?** Possibly - connects planted problem structure to AQO calibration.

**Is this correct?** The basic observation is correct. Details need verification.

**Is this significant?** Moderate - shows that average-case complexity might differ from worst-case.

**Limitation**: We're essentially showing that EASY problems have tractable A_1. The planted structure makes FINDING the solution tractable, so we're back to "tractable A_1 implies tractable problem."

**But**: The distinction is between knowing x* (full solution) vs. knowing the cost profile f(d) (distributional property). The latter is much weaker.
