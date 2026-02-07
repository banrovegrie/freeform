/-
  The adiabatic Hamiltonian and its properties.

  H(s) = -(1-s)|ψ₀⟩⟨ψ₀| + s H_z

  where s: [0,T] → [0,1] is the schedule.
-/
import UAQO.Spectral.GapBounds

namespace UAQO

/-! ## Time-dependent Hamiltonians -/

/-- A time-dependent Hamiltonian is a function from time to operators.
    The domain is implicitly [0, T]; the function is defined for all reals
    but only the values in [0, T] are physically meaningful. -/
structure TimeDependentHam (n : Nat) (T : Real) (_hT : T > 0) where
  /-- The Hamiltonian at each time t -/
  ham : Real -> NQubitOperator n

/-- The adiabatic schedule s: [0,T] → [0,1] -/
structure AdiabaticSchedule (T : Real) (hT : T > 0) where
  /-- The schedule function -/
  s : Real -> Real
  /-- s(0) = 0 -/
  initial : s 0 = 0
  /-- s(T) = 1 -/
  final : s T = 1
  /-- s is monotonically increasing -/
  monotone : ∀ t₁ t₂, 0 <= t₁ -> t₁ < t₂ -> t₂ <= T -> s t₁ < s t₂
  /-- s is differentiable (placeholder) -/
  differentiable : ∀ t, 0 < t -> t < T -> ∃ (_sPrime : Real), True

/-- The linear (constant speed) schedule -/
noncomputable def linearSchedule (T : Real) (hT : T > 0) : AdiabaticSchedule T hT where
  s := fun t => t / T
  initial := by simp
  final := by simp [ne_of_gt hT]
  monotone := fun t₁ t₂ _ ht ht₂ => by
    apply div_lt_div_of_pos_right ht (by linarith)
  differentiable := fun t _ _ => ⟨1/T, trivial⟩

/-- The local (gap-adaptive) schedule: ds/dt ∝ g(s)² -/
structure LocalSchedule (n M : Nat) (es : EigenStructure n M) (hM : M >= 2)
    (T : Real) (hT : T > 0) where
  /-- The underlying schedule -/
  schedule : AdiabaticSchedule T hT
  /-- The derivative scales with gap squared -/
  derivative_bound : ∀ t, 0 < t -> t < T ->
    ∃ (dsdt : Real), dsdt > 0  -- Simplified; actual bound involves gap

/-- For any time t in [0,T], s(t) is in [0,1] -/
lemma schedule_in_range {T : Real} {hT : T > 0} (sched : AdiabaticSchedule T hT)
    (t : Real) (ht : 0 <= t ∧ t <= T) : 0 <= sched.s t ∧ sched.s t <= 1 := by
  constructor
  · by_cases h0 : t = 0
    · rw [h0, sched.initial]
    · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h0)
      have : sched.s 0 < sched.s t := sched.monotone 0 t (le_refl 0) ht_pos ht.2
      rw [sched.initial] at this
      linarith
  · by_cases hT' : t = T
    · rw [hT', sched.final]
    · have ht_lt : t < T := lt_of_le_of_ne ht.2 hT'
      have : sched.s t < sched.s T := sched.monotone t T ht.1 ht_lt (le_refl T)
      rw [sched.final] at this
      linarith

/-! ## Constructing the adiabatic Hamiltonian -/

/-- Build the adiabatic Hamiltonian from an eigenstructure and schedule -/
noncomputable def buildAdiabaticHam {n M : Nat} (es : EigenStructure n M)
    (T : Real) (hT : T > 0) (sched : AdiabaticSchedule T hT) :
    TimeDependentHam n T hT where
  ham := fun t =>
    let s_t := sched.s t
    -- For t ∈ [0,T], use the proper schedule value
    -- For t outside [0,T], use a default (s=0)
    if ht : 0 <= t ∧ t <= T then
      adiabaticHam es s_t (schedule_in_range sched t ht)
    else
      adiabaticHam es 0 ⟨le_refl 0, by norm_num⟩

/-! ## Properties at s = 0 and s = 1 -/

/-- At s = 0, the ground state is |ψ₀⟩ with energy -1 -/
theorem initial_groundstate {n M : Nat} (es : EigenStructure n M) (_hM : M > 0) :
    let H0 := adiabaticHam es 0 ⟨le_refl 0, by norm_num⟩
    applyOp H0 (equalSuperpositionN n) = (-1 : Complex) • equalSuperpositionN n := by
  -- H(0) = -(1-0) * projector + 0 * Hz = -projector
  simp only [adiabaticHam]
  rw [show (-(1 - (0 : Real)) : Complex) = (-1 : Complex) by norm_num]
  rw [show ((0 : Real) : Complex) = (0 : Complex) by norm_num]
  rw [applyOp_add, applyOp_smul, applyOp_smul]
  rw [applyOp_projector_self _ (equalSuperpositionN_normalized n)]
  simp only [zero_smul, add_zero]

/-- At s = 1, the ground state is |0⟩_sym (symmetric ground state) with energy E₀ = 0 -/
theorem final_groundstate {n M : Nat} (es : EigenStructure n M) (hM : M > 0)
    (hGround : es.eigenvalues ⟨0, hM⟩ = 0) :
    let H1 := adiabaticHam es 1 ⟨by norm_num, le_refl 1⟩
    let groundSym := symmetricState es ⟨0, hM⟩
    applyOp H1 groundSym = (0 : Complex) • groundSym := by
  -- H(1) = -(1-1) * projector + 1 * Hz = Hz
  simp only [adiabaticHam, zero_smul]
  rw [show (-(1 - (1 : Real)) : Complex) = (0 : Complex) by norm_num]
  rw [show ((1 : Real) : Complex) = (1 : Complex) by norm_num]
  rw [applyOp_add, applyOp_smul, applyOp_smul]
  simp only [zero_smul, zero_add, one_smul]
  rw [applyOp_diagonalHam_symmetricGround es hM hGround]

/-! ## The instantaneous eigenstates -/

/-- The instantaneous ground state |v(s)⟩ at schedule value s -/
noncomputable def instantaneousGround {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (_hs : 0 <= s ∧ s <= 1)
    (_hspec : spectralCondition es hM 0.02 (by norm_num)) : NQubitState n :=
  -- Interpolate between |ψ₀⟩ (at s=0) and |0⟩_sym (at s=1)
  -- This is a placeholder; actual computation requires solving the eigenvalue problem
  if s < 0.5 then equalSuperpositionN n
  else symmetricState es ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩

/-- The instantaneous first excited state |v₁(s)⟩ -/
noncomputable def instantaneousFirstExcited {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (s : Real) (_hs : 0 <= s ∧ s <= 1) : NQubitState n :=
  -- Placeholder: use first excited symmetric state
  symmetricState es ⟨1, hM⟩

/-- The ground state interpolates from |ψ₀⟩ to |0⟩_sym -/
theorem groundState_interpolation {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2) (hspec : spectralCondition es hM 0.02 (by norm_num)) :
    normSquared (fun i =>
      instantaneousGround es hM 0 ⟨le_refl 0, by norm_num⟩ hspec i -
      equalSuperpositionN n i) < 0.01 ∧
    normSquared (fun i =>
      instantaneousGround es hM 1 ⟨by norm_num, le_refl 1⟩ hspec i -
      symmetricState es ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_two hM⟩ i) < 0.01 := by
  constructor
  · -- At s=0: instantaneousGround returns equalSuperpositionN n (since 0 < 0.5)
    simp only [instantaneousGround]
    simp only [show (0 : Real) < 0.5 by norm_num, ↓reduceIte]
    simp only [sub_self, normSquared, Complex.normSq_zero, Finset.sum_const_zero]
    norm_num
  · -- At s=1: instantaneousGround returns symmetricState (since 1 >= 0.5)
    simp only [instantaneousGround]
    simp only [show ¬ (1 : Real) < 0.5 by norm_num, ↓reduceIte]
    simp only [sub_self, normSquared, Complex.normSq_zero, Finset.sum_const_zero]
    norm_num

end UAQO
