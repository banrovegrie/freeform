# Lean Formalization for Experiment 13

This folder provides a self-contained Lean 4 formalization of the discrete
algebraic core behind Propositions 8-10 in `proof.md`.

## Files

- `IntermediateHardness/Basic.lean`
  - Precision grid `epsilon_k = 2^{-k}`
  - Core scaling models `Q(epsilon)=1/epsilon`, `C(epsilon)=1/epsilon^2`
  - Closed forms at `epsilon_k` and at the threshold `k = n/2`
- `IntermediateHardness/PhaseDiagram.lean`
  - Discrete phase point representation and closed forms
  - One-bit refinement laws: `Q` doubles and separation doubles
- `IntermediateHardness/BarrierGrid.lean`
  - Schedule-barrier proxy on the precision grid
  - Symbolic inequality proof `scheduleErrorProxy_gt_half` for all exponents
  - Finite machine-checked certificate up to exponent 1024
- `IntermediateHardness/StructuredBridge.lean`
  - Exact-estimator logic and inverse-precision runtime specialization
- `IntermediateHardness/PromiseTime.lean`
  - Lower/upper proxy forms and threshold parameterized bound
- `IntermediateHardness.lean`
  - Aggregator file with `#check` summary

## Toolchain

Pinned in `lean-toolchain`:

- `leanprover/lean4:v4.28.0-rc1`

## Verify

From this directory:

```bash
lake build
lake env lean IntermediateHardness.lean
```

This formalization deliberately avoids Mathlib and depends only on Lean core,
so it is lightweight and reproducible.
