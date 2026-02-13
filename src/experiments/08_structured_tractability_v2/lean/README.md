# Experiment 08 Lean Verification

This Lean project machine-checks algebraic components of the main proofs in
`../proof.md`.

## Scope

- `StructuredTractability08/Prop13.lean`
  - generic tail suppression lemma from minimum excited energy ($\Delta_{\min}$)
  - three-term error decomposition (`|a-d|` split)
  - midpoint-oracle term bound used in Proposition 13
  - midpoint quadrature-aggregation algebra (`K` interval errors to `L B^2/(2K)`)
  - parameter-choice budget lemma implying total additive error `<= eta`
- `StructuredTractability08/Prop14.lean`
  - crossing-shift identity
  - local absolute-sensitivity bound
  - explicit target-bound lemma with the min-condition
  - scale-substitution identity used with the paper's $\delta_s$ formula
- `StructuredTractability08/Prop15.lean`
  - exact $A_1$-matching identity between the two obstruction families
  - parameter inequality $1/B < c_B < B$ for $B>1$
  - quantitative gap core bound for $B \ge 3$:
    $\frac{e^{-1}}{16}-\frac{7}{16}\exp(-7B^2/(B^2+6))>1/100$
  - explicit transcendental constant control used in that bound

## Build

```bash
cd src/experiments/08_structured_tractability_v2/lean
lake update
lake build
```
