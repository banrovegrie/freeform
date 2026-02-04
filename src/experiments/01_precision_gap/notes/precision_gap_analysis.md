# Precision Gap Analysis: A Genuine Open Question

After careful analysis of the paper's proofs, I've identified a genuine gap.


## What the Paper Proves

**NP-hardness (Theorem 3.1)**:
- Estimating A_1 to precision epsilon < 1/(72(n-1)) is NP-hard
- Proof: 2 oracle calls solve 3-SAT

**#P-hardness (Section 3.2)**:
- Estimating A_1 to precision 2^{-poly(n)} is #P-hard
- Proof: Polynomial interpolation extracts degeneracies


## What AQO Actually Needs

The required precision for optimal AQO is:
```
delta_A1 = O(delta_s / (A_1+1)) = O(sqrt(d_0 * A_2 / N) / (A_1+1)^2)
```

For typical cases:
- d_0 = O(1) (few solutions): delta_A1 = O(2^{-n/2})
- d_0 = O(2^{n/2}): delta_A1 = O(1)


## The Gap

The complexity at precision 2^{-n/2} is UNKNOWN.

```
Precision:  1/poly(n)  <------ 2^{-n/2} ------>  2^{-poly(n)}
Complexity:   NP-hard           ???                #P-hard
```

This is NOT addressed in the paper.


## Why This Matters

For unique solution problems (d_0 = 1), AQO needs precision 2^{-n/2}, which falls in the gap.

If this precision is:
- Still NP-hard: AQO is fundamentally limited even for unique solutions
- Easier than NP: There might be hope for efficient calibration in special cases
- Something in between: New complexity insight


## Analyzing the NP-hardness Proof

The proof reduces 3-SAT to A_1 estimation via:
1. Create Hamiltonian H where E_0 = 0 iff SAT, E_0 >= 1/(6m) otherwise
2. Create H' = H ⊗ (I+σz)/2
3. Compute A_1(H) - 2*A_1(H')
4. This is 0 when E_0=0, and Ω(1/poly(n)) otherwise

The gap between cases is:
```
gap = μ_1/(1-μ_1) - (d_0/2^n) * 1/(μ_1*μ_2)
    ≈ 1/(6m) for 3-SAT reduction
    = Ω(1/poly(n))
```

**Key limitation**: The gap comes from μ_1 = 1/(6m), which is inherent to the 3-SAT structure. Each unsatisfied clause contributes 1/(6m) energy.


## Can We Strengthen the Proof?

To get NP-hardness at precision 2^{-n/2}, we'd need:
- A reduction where the gap is 2^{-n/2}
- But still solving an NP-complete problem

**Challenge**: NP-complete problems have "coarse" structure. The gap between YES and NO instances is typically Ω(1/poly(n)) because the difference corresponds to satisfying one constraint.

**Possible approach**: Problems with finer structure?
- Unique Games Conjecture related problems?
- Promise problems with exponentially small gaps?


## Analyzing the #P-hardness Proof

The proof uses polynomial interpolation:
- Create H'(x) = H ⊗ I - I ⊗ (x/2)σ_+
- f(x) = sum_k d_k / (Δ_k + x/2) is rational
- Evaluate at M points to extract {d_k}

**Key**: Polynomial interpolation requires precision exponential in M because:
- Vandermonde matrix condition number is exponential
- Need to distinguish nearby roots

**Could we weaken this?**
- If we only want d_0 (not all d_k), maybe less precision suffices?
- But extracting just d_0 from f(x) still seems hard...


## A Concrete Question

**Question**: What is the complexity of:

Problem A_1(n, α): Given description of n-qubit diagonal Hamiltonian H, output A_1(H) to precision 2^{-n^α}.

- For α = 0: Precision O(1), trivial
- For α close to 0: Precision 1/poly(n), NP-hard
- For α = 1/2: Precision 2^{-sqrt(n)}, ???
- For α close to 1: Precision 2^{-n+o(n)}, probably #P-hard


## Potential Research Direction

**Goal**: Characterize the complexity of A_1(n, α) as a function of α.

**Approach 1**: Try to extend NP-hardness to α > 0
- Find a problem with exponentially small promise gap
- Show reduction still works

**Approach 2**: Show a separation
- Prove that for some α, A_1(n, α) is NOT NP-hard
- Would require a polynomial-time algorithm or oracle separation

**Approach 3**: Introduce intermediate complexity classes
- Promise versions of counting problems?
- Connections to average-case complexity?


## Relation to d_0

The required precision depends on d_0:
```
delta_A1 ∝ sqrt(d_0 / N)
```

So the complexity might depend on the number of solutions:
- Many solutions (d_0 large): Lower precision needed, might be easier
- Few solutions (d_0 small): Higher precision needed, might be harder

This is a genuine complexity-theoretic question that could lead to new results.


## Honest Assessment

**Is this novel?** Yes - the paper explicitly leaves this gap open.

**Is this tractable?** Unclear - it requires serious complexity theory.

**Would it be a significant contribution?** Yes - characterizing intermediate precision complexity would be a real result.

**Can I solve it?** Probably not without significant complexity theory expertise.


## Next Steps

1. Literature search: Has anyone studied promise problems with exponentially small gaps?

2. Consult references: Check papers on local Hamiltonian problem complexity

3. Simplest case: What about precision 1/2^{sqrt(n)}? Can NP-hardness be extended to this?

4. Talk to advisor: This is a well-posed theoretical question worth discussing
