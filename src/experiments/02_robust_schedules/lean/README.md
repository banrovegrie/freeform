# Hedging Theorem Lean Formalization

Lean 4 formalization of the Hedging Theorem for adiabatic quantum optimization.

## Main Result

When the crossing position is known to lie in $[u_L, u_R]$, a hedging schedule
achieves error ratio $(u_R - u_L)$ compared to uniform schedule.

For $[u_L, u_R] = [0.4, 0.8]$, this means 60% error reduction.

## Files

- `HedgingTheorem/Basic.lean`: Core definitions and numerical verification (Float)
- `HedgingTheorem/Proofs.lean`: Machine-checked proofs (Real)
- `HedgingTheorem.lean`: Root module

## Building

Build from the `experiments/` directory:

```bash
cd src/experiments
lake build HedgingTheorem
```

## Verification Status

### Fully Machine-Checked (No Sorry)

1. **Schedule Constraint** (`schedule_constraint`):
   For $w \in (0,1)$ and $v_{slow} > w$, defining $v_{fast} = (1-w) v_{slow} / (v_{slow} - w)$
   gives $w / v_{slow} + (1-w) / v_{fast} = 1$.

   Axioms: propext, Classical.choice, Quot.sound (standard Lean axioms)

2. **Sqrt Term Bound** (`sqrt_term_bound`):
   For any $\varepsilon > 0$, there exists $R_0$ such that for $R > R_0$,
   $\sqrt{(1-w) w / R} < \varepsilon$.

3. **Optimal Velocity Convergence** (`v_slow_opt_approaches_w`):
   The optimal slow velocity $v_{slow}^{opt} = w + \sqrt{(1-w) w / R}$ approaches $w$
   as $R \to \infty$.

4. **Supporting Lemmas**:
   - `v_slow_opt_gt_w`: optimal velocity exceeds $w$
   - `sqrt_term_nonneg`: sqrt term is nonnegative
   - `corollary_w_04_velocity`: For $w = 0.4$, $v_{slow}^{opt} \to 0.4$
   - `improvement_factor`: algebraic fact about improvement

### Statement Verified, Proof Uses Sorry

5. **Main Theorem** (`error_ratio_approaches_w`):
   Error ratio $E_{hedge} / E_{unif}$ approaches $w$ as $R \to \infty$.

   The statement is machine-checked. The proof requires connecting the
   algebraic structure of the error ratio formula to the established bounds.
   This involves showing:
   $$\text{ratio} - w = \frac{2w(1-w) + s(1-2w)}{s(R+1)}$$
   where $s = \sqrt{(1-w)w/R}$, and bounding this expression.

   The mathematical proof is complete in `proof.md` and numerically validated
   in `Basic.lean`. The formal Lean proof of this algebraic connection is pending.

## Mathematical Content

The Hedging Theorem establishes that for adiabatic quantum optimization
with uncertainty about the gap minimum location:

1. **Constraint Identity**: The hedging schedule satisfies normalization
   $w / v_{slow} + (1-w) / v_{fast} = 1$ when $v_{fast} = (1-w) v_{slow} / (v_{slow} - w)$.

2. **Optimal Velocity**: The error-minimizing slow velocity is
   $v_{slow} = w + \sqrt{(1-w) w / R}$ where $R = I_{slow} / I_{fast}$.

3. **Asymptotic Ratio**: As $R \to \infty$, the error ratio approaches $w$,
   meaning the improvement factor approaches $(1-w)$.

4. **Practical Result**: For $w = 0.4$ (uncertainty interval $[0.4, 0.8]$),
   the hedging schedule achieves 60% error reduction compared to uniform.

## Axiom Summary

All completed proofs depend only on standard Lean/Mathlib axioms:
- `propext` (propositional extensionality)
- `Classical.choice` (axiom of choice)
- `Quot.sound` (quotient soundness)

No custom axioms are declared. One theorem uses `sorry` (see above).
