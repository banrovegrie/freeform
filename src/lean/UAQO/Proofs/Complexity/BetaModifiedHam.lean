/-
  Proofs for beta-modified Hamiltonian axioms in Hardness.lean.

  Status:
  - betaModifiedHam_deg_sum: FULLY PROVED (references main file)
  - betaModifiedHam_deg_count: FULLY PROVED (references main file)
  - betaModifiedHam_eigenval_ordered: FULLY PROVED (references main file, requires gap constraint)
  - betaModifiedHam_eigenval_ordered_strict: FULLY PROVED (references main file)
  - betaModifiedHam_eigenval_bounds: FULLY PROVED (references main file)

  Note: All theorems are now proved in Hardness.lean. This file provides
  alternative entry points that delegate to the main implementations.
-/
import UAQO.Complexity.Hardness
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

namespace UAQO.Complexity.Proofs

open UAQO UAQO.Complexity

/-- For k in Fin (2*M), k.val / 2 < M always holds. -/
lemma div2_lt_of_fin_2M {M : Nat} (k : Fin (2 * M)) : k.val / 2 < M := by
  have hk := k.isLt
  exact Nat.div_lt_of_lt_mul hk

/-- Helper: if i/2 = j/2 and i < j (as Nat), then i is even and j = i + 1. -/
lemma same_div2_implies_consec {i j : Nat} (h_div : i / 2 = j / 2) (h_lt : i < j) :
    i % 2 = 0 ∧ j = i + 1 := by
  have hi_mod := Nat.div_add_mod i 2
  have hj_mod := Nat.div_add_mod j 2
  have hi_rem : i % 2 < 2 := Nat.mod_lt i (by norm_num)
  have hj_rem : j % 2 < 2 := Nat.mod_lt j (by norm_num)
  constructor
  · by_contra h
    have : i % 2 = 1 := by omega
    omega
  · omega

/-- The even indices in Fin (2*M) are in bijection with Fin M via k ↦ 2k. -/
def evenBij (M : Nat) (_hM : M > 0) : Fin M → Fin (2 * M) :=
  fun i => ⟨2 * i.val, by omega⟩

/-- The odd indices in Fin (2*M) are in bijection with Fin M via k ↦ 2k+1. -/
def oddBij (M : Nat) (_hM : M > 0) : Fin M → Fin (2 * M) :=
  fun i => ⟨2 * i.val + 1, by omega⟩

/-- The degeneracy sum in the beta-modified Hamiltonian equals the new Hilbert space dimension.

    Each k in Fin (2*M) has origIdx = k.val / 2 < M, so the "else 1" branch is never taken.
    Sum = Σ_{k=0}^{2M-1} d_{k/2} = Σ_{i=0}^{M-1} (d_i + d_i) = 2 * Σ d_i = 2 * N = qubitDim (n+1). -/
theorem betaModifiedHam_deg_sum_proof {n M : Nat} (es : EigenStructure n M) (hM : M > 0) :
    Finset.sum Finset.univ (fun k : Fin (2 * M) =>
      let origIdx := k.val / 2
      if hOrig : origIdx < M then es.degeneracies ⟨origIdx, hOrig⟩ else 1) = qubitDim (n + 1) := by
  -- Step 1: Simplify away the dite (the else branch is never taken)
  have hSimp : ∀ k : Fin (2 * M), (let origIdx := k.val / 2
       if hOrig : origIdx < M then es.degeneracies ⟨origIdx, hOrig⟩ else 1) =
       es.degeneracies ⟨k.val / 2, div2_lt_of_fin_2M k⟩ := by
    intro k
    simp only [div2_lt_of_fin_2M k, dite_true]
  conv_lhs => arg 2; ext k; rw [hSimp k]

  -- Step 2: Show sum = 2 * (sum of original degeneracies)
  rw [qubitDim_succ]

  -- Step 3: Reindex the sum
  -- Sum over Fin (2*M) where f(k) = d_{k/2}
  -- = Sum over even k of d_{k/2} + Sum over odd k of d_{k/2}
  -- = Sum over Fin M of d_i + Sum over Fin M of d_i
  -- = 2 * Sum over Fin M of d_i

  -- Use Fintype.sum_equiv to reindex
  have h2M_pos : 0 < 2 * M := Nat.mul_pos (by norm_num) hM

  -- Show that the sum equals 2 * (sum of degeneracies)
  -- Each degeneracy d_i appears twice: once for k = 2i (even), once for k = 2i+1 (odd)
  have hSum : Finset.sum Finset.univ (fun k : Fin (2 * M) =>
        es.degeneracies ⟨k.val / 2, div2_lt_of_fin_2M k⟩) =
      2 * Finset.sum Finset.univ es.degeneracies := by
    -- Split Fin (2*M) into evens and odds
    have hSplit : (Finset.univ : Finset (Fin (2 * M))) =
        Finset.filter (fun k => k.val % 2 = 0) Finset.univ ∪
        Finset.filter (fun k => k.val % 2 = 1) Finset.univ := by
      ext k
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and]
      have := Nat.mod_two_eq_zero_or_one k.val
      tauto
    have hDisj : Disjoint
        (Finset.filter (fun k : Fin (2 * M) => k.val % 2 = 0) Finset.univ)
        (Finset.filter (fun k : Fin (2 * M) => k.val % 2 = 1) Finset.univ) := by
      rw [Finset.disjoint_filter]
      intro k _ hk0
      omega
    rw [hSplit, Finset.sum_union hDisj, Finset.mul_sum]
    -- Sum over evens: each even k = 2i maps to i with d_{k/2} = d_i
    -- Sum over odds: each odd k = 2i+1 maps to i with d_{k/2} = d_i
    -- Both sums equal Σ d_i, so total = 2 * Σ d_i
    have hEvenSum : Finset.sum (Finset.filter (fun k : Fin (2 * M) => k.val % 2 = 0) Finset.univ)
        (fun k => es.degeneracies ⟨k.val / 2, div2_lt_of_fin_2M k⟩) =
        Finset.sum Finset.univ es.degeneracies := by
      symm
      apply Finset.sum_nbij (fun i : Fin M => (⟨2 * i.val, by omega⟩ : Fin (2 * M)))
      · intro i _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Nat.mul_mod_right 2 i.val
      · intro i j _ _ h
        simp only [Fin.mk.injEq] at h
        ext; omega
      · intro k hk
        -- hk : k ∈ (filter (fun k => k.val % 2 = 0) univ)
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hk
        refine ⟨⟨k.val / 2, div2_lt_of_fin_2M k⟩, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
        ext
        simp only []
        have hkrec : k.val = 2 * (k.val / 2) + k.val % 2 := (Nat.div_add_mod k.val 2).symm
        omega
      · intro i _
        congr 1
        ext
        simp only []
        exact (Nat.mul_div_cancel_left i.val (by norm_num : 0 < 2)).symm
    have hOddSum : Finset.sum (Finset.filter (fun k : Fin (2 * M) => k.val % 2 = 1) Finset.univ)
        (fun k => es.degeneracies ⟨k.val / 2, div2_lt_of_fin_2M k⟩) =
        Finset.sum Finset.univ es.degeneracies := by
      symm
      apply Finset.sum_nbij (fun i : Fin M => (⟨2 * i.val + 1, by omega⟩ : Fin (2 * M)))
      · intro i _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      · intro i j _ _ h
        simp only [Fin.mk.injEq] at h
        ext; omega
      · intro k hk
        -- hk : k ∈ (filter (fun k => k.val % 2 = 1) univ)
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hk
        refine ⟨⟨k.val / 2, div2_lt_of_fin_2M k⟩, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
        ext
        simp only []
        have hkrec : k.val = 2 * (k.val / 2) + k.val % 2 := (Nat.div_add_mod k.val 2).symm
        omega
      · intro i _
        congr 1
        ext
        simp only []
        have h1 : (2 * i.val + 1) / 2 = i.val := by
          omega
        exact h1.symm
    rw [hEvenSum, hOddSum, ← two_mul, Finset.mul_sum]
  rw [hSum, es.deg_sum]

/-- Helper: z/2 < qubitDim n for any z in Fin(qubitDim(n+1)) -/
lemma div2_lt_qubitDim {n : Nat} (z : Fin (qubitDim (n + 1))) : z.val / 2 < qubitDim n := by
  have hz := z.isLt
  simp only [qubitDim_succ] at hz
  omega

/-- The degeneracy count matches the assignment function. -/
theorem betaModifiedHam_deg_count_proof {n M : Nat} (es : EigenStructure n M) (hM : M > 0) :
    ∀ k : Fin (2 * M),
      (let origIdx := k.val / 2
       if hOrig : origIdx < M then es.degeneracies ⟨origIdx, hOrig⟩ else 1) =
      (Finset.filter (fun z : Fin (qubitDim (n + 1)) =>
        betaModifiedHam_assignment es hM z = k) Finset.univ).card := by
  intro k
  have horigK : k.val / 2 < M := div2_lt_of_fin_2M k
  simp only [horigK, dite_true]

  -- Key insight: betaModifiedHam_assignment(z) = k iff
  --   es.assignment(z/2) = k/2  AND  z % 2 = k % 2
  -- So the filter has same cardinality as {np : es.assignment(np) = k/2}
  -- which equals es.degeneracies(k/2) by es.deg_count

  let orig : Fin M := ⟨k.val / 2, horigK⟩
  let spin := k.val % 2

  -- Rewrite using es.deg_count
  rw [es.deg_count orig]

  -- Show the two filters have equal cardinality via bijection
  apply Finset.card_bij (fun np _ => (⟨2 * np.val + spin, by
      have h := np.isLt
      simp only [qubitDim_succ]
      have hspin : spin < 2 := Nat.mod_lt k.val (by norm_num)
      omega⟩ : Fin (qubitDim (n + 1))))

  -- 1. The function maps into the target filter
  · intro np hnp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnp ⊢
    -- hnp : es.assignment np = orig
    -- Goal: betaModifiedHam_assignment ⟨2*np + spin, _⟩ = k
    unfold betaModifiedHam_assignment
    have hnp_lt : np.val < qubitDim n := np.isLt
    have hspin_lt : spin < 2 := Nat.mod_lt k.val (by norm_num)
    have h_div : (2 * np.val + spin) / 2 = np.val := by omega
    have h_div_lt : (2 * np.val + spin) / 2 < qubitDim n := by omega
    simp only [h_div_lt, dite_true]
    -- Goal: ⟨2 * (es.assignment ⟨(2*np+spin)/2, _⟩).val + (2*np+spin) % 2, _⟩ = k
    have h_mod : (2 * np.val + spin) % 2 = spin := by omega
    -- Show the assignment arguments are equal using h_div
    have h_arg_eq : (⟨(2 * np.val + spin) / 2, h_div_lt⟩ : Fin (qubitDim n)) = np := by
      ext; exact h_div
    -- Compute the final goal step by step
    have h_result : 2 * (es.assignment np).val + spin = k.val := by
      have h1 : (es.assignment np).val = orig.val := by rw [hnp]
      have h2 : orig.val = k.val / 2 := rfl
      have h3 : spin = k.val % 2 := rfl
      rw [h1, h2, h3]
      exact Nat.div_add_mod k.val 2
    ext
    simp only [h_arg_eq, h_mod]
    exact h_result

  -- 2. The function is injective
  · intro np1 np2 _ _ h
    simp only [Fin.mk.injEq] at h
    ext
    omega

  -- 3. The function is surjective onto the target filter
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    -- hz : betaModifiedHam_assignment z = k
    unfold betaModifiedHam_assignment at hz
    have hz_lt := z.isLt
    simp only [qubitDim_succ] at hz_lt
    have h_div_lt : z.val / 2 < qubitDim n := by omega
    simp only [h_div_lt, dite_true] at hz
    -- hz : ⟨2 * (es.assignment ⟨z/2, _⟩).val + z%2, _⟩ = k
    have hz_val : 2 * (es.assignment ⟨z.val / 2, h_div_lt⟩).val + z.val % 2 = k.val := by
      exact congrArg Fin.val hz
    -- Extract that es.assignment(z/2) = orig and z%2 = spin
    have h_ass : (es.assignment ⟨z.val / 2, h_div_lt⟩).val = k.val / 2 := by omega
    have h_spin : z.val % 2 = spin := by omega
    -- The preimage is ⟨z/2, _⟩
    refine ⟨⟨z.val / 2, h_div_lt⟩, ?_, ?_⟩
    · -- Show ⟨z/2, _⟩ is in source filter (es.assignment(z/2) = orig)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      -- Need to show es.assignment ⟨z/2, _⟩ = orig
      exact Fin.ext h_ass
    · -- Show ⟨2*(z/2) + spin, _⟩ = z as Fin elements
      apply Fin.ext
      simp only []
      have hzrec : z.val = 2 * (z.val / 2) + z.val % 2 := (Nat.div_add_mod z.val 2).symm
      omega

/-- Eigenvalue ordering in beta-modified Hamiltonian (weak inequality).

    NOTE: The original version without gap constraint was unprovable.
    The correct theorem requires `allGapsAtLeast es (beta / 2)`.
    The full proof is in Hardness.lean as `betaModifiedHam_eigenval_ordered`. -/
theorem betaModifiedHam_eigenval_ordered_proof {n M : Nat} (es : EigenStructure n M)
    (hM : M >= 2)
    (beta : Real) (hbeta : 0 < beta ∧ beta < 1)
    (hgap : allGapsAtLeast es (beta / 2)) :
    ∀ i j : Fin (2 * M), i < j ->
      (let origI := i.val / 2
       let isUpperI := i.val % 2 = 1
       if hI : origI < M then es.eigenvalues ⟨origI, hI⟩ + if isUpperI then beta/2 else 0 else 1) <=
      (let origJ := j.val / 2
       let isUpperJ := j.val % 2 = 1
       if hJ : origJ < M then es.eigenvalues ⟨origJ, hJ⟩ + if isUpperJ then beta/2 else 0 else 1) :=
  betaModifiedHam_eigenval_ordered es hM beta hbeta hgap

/-- Strict eigenvalue ordering with gap constraint.

    With the stronger hypothesis `allGapsGreaterThan es (beta/2)`, we can now prove
    the ordering for different original levels. -/
theorem betaModifiedHam_eigenval_ordered_strict_proof {n M : Nat} (es : EigenStructure n M)
    (_hM : M >= 2)
    (beta : Real) (hbeta : 0 < beta ∧ beta < 1)
    (hgap : allGapsGreaterThan es (beta / 2)) :
    ∀ i j : Fin (2 * M), i < j ->
      (let origI := i.val / 2
       let isUpperI := i.val % 2 = 1
       if hI : origI < M then es.eigenvalues ⟨origI, hI⟩ + if isUpperI then beta/2 else 0 else 1) <
      (let origJ := j.val / 2
       let isUpperJ := j.val % 2 = 1
       if hJ : origJ < M then es.eigenvalues ⟨origJ, hJ⟩ + if isUpperJ then beta/2 else 0 else 1) := by
  intro i j hij
  have horigI : i.val / 2 < M := div2_lt_of_fin_2M i
  have horigJ : j.val / 2 < M := div2_lt_of_fin_2M j
  simp only [horigI, horigJ, dite_true]
  by_cases hEqOrig : i.val / 2 = j.val / 2
  · -- Same original level: i even, j odd, so E_i < E_i + beta/2
    obtain ⟨hi_even, _⟩ := same_div2_implies_consec hEqOrig hij
    have hj_odd : j.val % 2 = 1 := by omega
    have hi_not_odd : ¬(i.val % 2 = 1) := by omega
    have hSameOrig : es.eigenvalues ⟨i.val / 2, horigI⟩ = es.eigenvalues ⟨j.val / 2, horigJ⟩ := by
      congr 1; exact Fin.ext hEqOrig
    simp only [hi_not_odd, hj_odd, ite_false, ite_true, add_zero]
    rw [hSameOrig]
    linarith [hbeta.1]
  · -- Different original levels: use allGapsGreaterThan to show E_origI + beta/2 < E_origJ
    have hOrigLt : i.val / 2 < j.val / 2 := by
      have h1 : i.val / 2 ≤ j.val / 2 := Nat.div_le_div_right (le_of_lt hij)
      omega
    -- With allGapsGreaterThan (strict), we have consecutive gap > beta/2
    -- Therefore E_origJ - E_origI >= consecutive gap > beta/2
    have hGapBound : es.eigenvalues ⟨j.val / 2, horigJ⟩ - es.eigenvalues ⟨i.val / 2, horigI⟩ > beta / 2 := by
      -- For consecutive levels, this is exactly the strict gap constraint
      -- For non-consecutive, it's even larger due to strictly increasing eigenvalues
      have hk : i.val / 2 + 1 < M := by omega
      have hConsecGap := hgap (i.val / 2) hk
      simp only [consecutiveGap] at hConsecGap
      have hEleTrans : es.eigenvalues ⟨i.val / 2 + 1, hk⟩ <= es.eigenvalues ⟨j.val / 2, horigJ⟩ := by
        by_cases hEq : i.val / 2 + 1 = j.val / 2
        · simp only [hEq]; exact le_refl _
        · have hLt : i.val / 2 + 1 < j.val / 2 := by omega
          exact le_of_lt (es.eigenval_ordered ⟨i.val / 2 + 1, hk⟩ ⟨j.val / 2, horigJ⟩ hLt)
      linarith
    -- Now show E_origI + (shift) < E_origJ where shift <= beta/2
    split_ifs with hiUpper hjUpper
    · -- Both upper: E_origI + beta/2 < E_origJ + beta/2
      linarith
    · -- i upper, j lower: E_origI + beta/2 < E_origJ (follows from strict gap bound)
      simp only [add_zero]
      linarith
    · -- i lower, j upper: E_origI < E_origJ + beta/2
      simp only [add_zero]
      have hElt := es.eigenval_ordered ⟨i.val / 2, horigI⟩ ⟨j.val / 2, horigJ⟩ hOrigLt
      linarith [hbeta.1]
    · -- Both lower: E_origI < E_origJ
      simp only [add_zero]
      exact es.eigenval_ordered ⟨i.val / 2, horigI⟩ ⟨j.val / 2, horigJ⟩ hOrigLt

/-- Eigenvalue bounds in beta-modified Hamiltonian.

    Note: This requires the hypothesis that all eigenvalues are <= 1 - beta/2,
    which ensures the upper level eigenvalues E_k + beta/2 don't exceed 1. -/
theorem betaModifiedHam_eigenval_bounds_proof {n M : Nat} (es : EigenStructure n M)
    (beta : Real) (hbeta : 0 < beta ∧ beta < 1) (_hM : M > 0)
    (hEigBound : ∀ k : Fin M, es.eigenvalues k <= 1 - beta / 2) :
    ∀ k : Fin (2 * M),
      let origIdx := k.val / 2
      let isUpperLevel := k.val % 2 = 1
      0 <= (if hOrig : origIdx < M then
              es.eigenvalues ⟨origIdx, hOrig⟩ + if isUpperLevel then beta / 2 else 0
            else 1) ∧
      (if hOrig : origIdx < M then
         es.eigenvalues ⟨origIdx, hOrig⟩ + if isUpperLevel then beta / 2 else 0
       else 1) <= 1 := by
  intro k
  have horigK : k.val / 2 < M := div2_lt_of_fin_2M k
  simp only [horigK, dite_true]
  constructor
  · -- Lower bound: E_origK + (0 or beta/2) >= 0
    have hE_nonneg := (es.eigenval_bounds ⟨k.val / 2, horigK⟩).1
    split_ifs <;> linarith [hbeta.1]
  · -- Upper bound: E_origK + (0 or beta/2) <= 1
    have hE_bound := hEigBound ⟨k.val / 2, horigK⟩
    split_ifs with h
    · -- Upper level: E_origK + beta/2 <= 1 since E_origK <= 1 - beta/2
      linarith
    · -- Lower level: E_origK + 0 <= 1 - beta/2 <= 1
      linarith [hbeta.1]

end UAQO.Complexity.Proofs
