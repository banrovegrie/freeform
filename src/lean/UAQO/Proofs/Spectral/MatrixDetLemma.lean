/-
  Matrix Determinant Lemma for rank-1 updates.

  This file provides bridge lemmas connecting our custom definitions (outerProd, innerProd)
  to Mathlib's equivalents (replicateCol/replicateRow, dotProduct with star).

  Key Mathlib theorems used:
  - det_add_replicateCol_mul_replicateRow (from SchurComplement)
  - det_one_add_replicateCol_mul_replicateRow (from SchurComplement)

  Bridge lemmas in this file:
  - outerProd_eq_replicateCol_mul_replicateRow: connects our outerProd to Mathlib
  - dotProduct_star_eq_innerProd: connects our innerProd to Mathlib's dotProduct
  - replicateRow_mul_mul_replicateCol_eq_dotProduct_mulVec: helper for determinant proofs

  Main theorems:
  - det_one_add_outerProd: det(I + |u><v|) = 1 + <v|u>
  - matrix_det_lemma: det(A + |u><v|) = det(A) * (1 + <v|A^-1|u>)
-/
import UAQO.Foundations.Operators
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement

namespace UAQO.Proofs.Spectral

open UAQO Matrix Finset

/-- Connection between conj and star for complex numbers. -/
theorem conj_eq_star_complex (z : ℂ) : conj z = star z := rfl

/-- Our outerProd equals Mathlib's replicateCol * replicateRow with conjugation. -/
theorem outerProd_eq_replicateCol_mul_replicateRow {N : Nat} (u v : Ket N) :
    outerProd u v = replicateCol Unit u * replicateRow Unit (star v) := by
  ext i j
  simp only [outerProd, Matrix.of_apply, Matrix.mul_apply, replicateCol_apply,
             replicateRow_apply, Finset.univ_unique, Finset.sum_singleton,
             Pi.star_apply, conj_eq_star_complex]

/-- Connection between dotProduct with star and innerProd. -/
theorem dotProduct_star_eq_innerProd {N : Nat} (v u : Ket N) :
    (star v) ⬝ᵥ u = innerProd v u := by
  simp only [dotProduct, innerProd, Pi.star_apply, conj_eq_star_complex]

/-- The determinant of I + outer product equals 1 + inner product.

    det(I + |u⟩⟨v|) = 1 + ⟨v|u⟩ -/
theorem det_one_add_outerProd {N : Nat} [NeZero N] (u v : Ket N) :
    (1 + outerProd u v).det = 1 + innerProd v u := by
  rw [outerProd_eq_replicateCol_mul_replicateRow, det_one_add_replicateCol_mul_replicateRow,
      dotProduct_star_eq_innerProd]

/-- Helper: replicateRow * M * replicateCol equals dotProduct with mulVec. -/
theorem replicateRow_mul_mul_replicateCol_eq_dotProduct_mulVec {N : Nat}
    (r : Fin N → ℂ) (M : Matrix (Fin N) (Fin N) ℂ) (c : Fin N → ℂ) :
    (replicateRow Unit r * M * replicateCol Unit c) default default = r ⬝ᵥ (M *ᵥ c) := by
  simp only [Matrix.mul_apply, replicateRow_apply, replicateCol_apply, mulVec, dotProduct]
  -- Goal: ∑ x, (∑ x_1, r x_1 * M x_1 x) * c x = ∑ x, r x * ∑ x_1, M x x_1 * c x_1
  -- This requires index swapping and associativity
  conv_lhs =>
    arg 2
    ext x
    rw [sum_mul]
  rw [sum_comm]
  congr 1
  ext i
  rw [mul_sum]
  congr 1
  ext j
  ring

/-- Matrix Determinant Lemma: det(A + |u⟩⟨v|) = det(A) * (1 + ⟨v|A⁻¹|u⟩)

    For invertible A. -/
theorem matrix_det_lemma {N : Nat} [NeZero N] (A : Matrix (Fin N) (Fin N) ℂ)
    (u v : Ket N) (hA : IsUnit A.det) :
    (A + outerProd u v).det = A.det * (1 + innerProd v (A⁻¹ ⬝ u)) := by
  rw [outerProd_eq_replicateCol_mul_replicateRow]
  rw [det_add_replicateCol_mul_replicateRow hA]
  congr 1
  -- The LHS is det of a 1×1 matrix
  rw [det_unique]
  simp only [Matrix.one_apply_eq, Matrix.add_apply]
  congr 1
  rw [replicateRow_mul_mul_replicateCol_eq_dotProduct_mulVec]
  rw [dotProduct_star_eq_innerProd]
  -- innerProd v (A⁻¹ *ᵥ u) = innerProd v (A⁻¹ ⬝ u)
  unfold applyOp
  rfl

end UAQO.Proofs.Spectral
