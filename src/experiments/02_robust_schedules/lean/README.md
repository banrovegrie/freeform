# Hedging Theorem Lean Formalization

Lean 4 formalization of the Hedging Theorem for adiabatic quantum optimization.

## Main Result

When the crossing position is known to lie in `[u_L, u_R]`, a hedging schedule
achieves error ratio `(u_R - u_L)` compared to uniform schedule.

For `[u_L, u_R] = [0.4, 0.8]`, this means 60% error reduction.

## Files

- `HedgingTheorem/Basic.lean`: Core definitions and numerical verification (Float)
- `HedgingTheorem/Proofs.lean`: Machine-checked proofs (Real)
- `HedgingTheorem.lean`: Root module
- `Main.lean`: Executable for numerical verification

## Building

```bash
lake build
```

## Key Theorems and Verification Status

### Fully Machine-Checked

1. **Schedule Constraint** (`schedule_constraint`):
   For w in (0,1) and v_slow > w, defining v_fast = (1-w)*v_slow/(v_slow-w)
   gives w/v_slow + (1-w)/v_fast = 1.

   ```lean
   theorem schedule_constraint (w v_slow : Real)
       (hw_pos : 0 < w) (hw_lt : w < 1) (hv : w < v_slow) :
       w / v_slow + (1 - w) / (v_fast w v_slow) = 1
   ```
   Axioms: propext, Classical.choice, Quot.sound

2. **Sqrt Term Bound** (`sqrt_term_bound`):
   For any epsilon > 0, there exists R0 such that for R > R0,
   sqrt((1-w)*w/R) < epsilon.

   ```lean
   theorem sqrt_term_bound (w epsilon : Real)
       (hw_pos : 0 < w) (hw_lt : w < 1) (heps : 0 < epsilon) :
       exists R0 : Real, R0 > 0 /\ forall R : Real, R > R0 ->
         sqrt_term w R < epsilon
   ```
   Axioms: propext, Classical.choice, Quot.sound

3. **Optimal Velocity Convergence** (`v_slow_opt_approaches_w`):
   The optimal slow velocity v_slow_opt = w + sqrt((1-w)*w/R) approaches w
   as R -> infinity.

   ```lean
   theorem v_slow_opt_approaches_w (w epsilon : Real)
       (hw_pos : 0 < w) (hw_lt : w < 1) (heps : 0 < epsilon) :
       exists R0 : Real, R0 > 0 /\ forall R : Real, R > R0 ->
         |v_slow_opt w R - w| < epsilon
   ```
   Axioms: propext, Classical.choice, Quot.sound

4. **Supporting Lemmas**:
   - `v_slow_opt_gt_w`: optimal velocity exceeds w
   - `sqrt_term_nonneg`: sqrt term is nonnegative
   - `optimal_velocity_decomposition`: v_slow_opt = w + sqrt_term

### Statement Verified, Proof Incomplete

5. **Main Theorem** (`error_ratio_approaches_w`):
   Error ratio E_hedge/E_unif approaches w as R -> infinity.

   The statement is machine-checked but the proof uses `sorry`.
   The incomplete step involves analyzing the v_fast contribution
   to the error formula in the limit.

   ```lean
   theorem error_ratio_approaches_w (w epsilon : Real)
       (hw_pos : 0 < w) (hw_lt : w < 1) (heps : 0 < epsilon) :
       exists R0 : Real, R0 > 0 /\ forall R : Real, R > R0 ->
         |optimal_error_ratio w R - w| < epsilon
   ```

### Numerical Verification

The `Basic.lean` file provides Float-based computations that numerically verify:
- Constraint satisfaction for various R values
- Asymptotic behavior of error ratio
- Optimal velocity convergence

Run with:
```bash
lake env lean --run Main.lean
```

## Mathematical Content

The Hedging Theorem establishes that for adiabatic quantum optimization
with uncertainty about the gap minimum location:

1. **Constraint Identity**: The hedging schedule satisfies the normalization
   w/v_slow + (1-w)/v_fast = 1 when v_fast = (1-w)*v_slow/(v_slow-w).

2. **Optimal Velocity**: The error-minimizing slow velocity is
   v_slow = w + sqrt((1-w)*w/R) where R = I_slow/I_fast.

3. **Asymptotic Ratio**: As R -> infinity, the error ratio approaches w,
   meaning the improvement factor approaches (1-w).

4. **Practical Result**: For w = 0.4 (uncertainty interval [0.4, 0.8]),
   the hedging schedule achieves 60% error reduction compared to uniform.

See `proof.md` in the parent directory for the full mathematical treatment.

## Axiom Summary

All machine-checked proofs depend only on standard Lean/Mathlib axioms:
- `propext` (propositional extensionality)
- `Classical.choice` (axiom of choice)
- `Quot.sound` (quotient soundness)

No custom axioms are declared. One theorem (`error_ratio_approaches_w`) uses `sorry`.
