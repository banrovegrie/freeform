/-
  Basic definitions and notation used throughout the formalization.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Field.Basic

namespace UAQO

/-! ## Notation -/

/-- The dimension N = 2^n for an n-qubit system -/
def dim (n : Nat) : Nat := 2^n

/-- Big-O notation (informal, for documentation) -/
def BigO (f : Nat -> Real) (g : Nat -> Real) : Prop :=
  exists (c : Real) (n0 : Nat), c > 0 /\ forall n, n >= n0 -> f n <= c * g n

/-- Big-Omega notation -/
def BigOmega (f : Nat -> Real) (g : Nat -> Real) : Prop := BigO g f

/-- Theta notation -/
def Theta (f : Nat -> Real) (g : Nat -> Real) : Prop := BigO f g /\ BigOmega f g

/-- Polynomial in n -/
def Poly (n : Nat) : Type := { p : Nat -> Nat // exists d : Nat, forall m, p m <= m^d + d }

notation "O(" f ")" => BigO f
notation "Omega(" f ")" => BigOmega f

/-! ## Basic complex number utilities -/

/-- The imaginary unit -/
noncomputable def i : Complex := Complex.I

/-- Complex conjugate -/
noncomputable def conj (z : Complex) : Complex := starRingEnd Complex z

/-- Absolute value squared -/
noncomputable def absSquared (z : Complex) : Real := Complex.normSq z

theorem absSquared_nonneg (z : Complex) : absSquared z >= 0 := Complex.normSq_nonneg z

theorem absSquared_eq_mul_conj (z : Complex) : absSquared z = (z * conj z).re := by
  simp [absSquared, conj, Complex.normSq]

/-! ## Basic lemmas for finite sums -/

lemma sum_nonneg_of_nonneg {n : Nat} (f : Fin n -> Real) (hf : forall i, f i >= 0) :
    Finset.sum Finset.univ f >= 0 := by
  apply Finset.sum_nonneg
  intro i _
  exact hf i

end UAQO
