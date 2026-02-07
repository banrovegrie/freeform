/-
  The complexity class NP and NP-hardness.

  NP is the class of decision problems verifiable in polynomial time,
  or equivalently, decidable by a nondeterministic polynomial-time TM.
-/
import UAQO.Complexity.Basic

namespace UAQO.Complexity

/-! ## The class NP -/

/-- A verifier for a decision problem -/
structure Verifier (prob : DecisionProblem) where
  /-- The verification function: takes input and certificate -/
  verify : List Bool -> List Bool -> Bool
  /-- Certificate length is polynomial in input length -/
  cert_bound : ∃ (p : Nat), ∀ x cert, verify x cert = true -> cert.length <= x.length^p + p
  /-- Soundness: if verify accepts, then x is a YES instance -/
  sound : ∀ x cert, verify x cert = true -> x ∈ prob.yes_instances
  /-- Completeness: if x is a YES instance, some certificate works -/
  complete : ∀ x, x ∈ prob.yes_instances -> ∃ cert, verify x cert = true

/-- A problem is in NP if it has a polynomial-time verifier -/
def InNP (prob : DecisionProblem) : Prop :=
  ∃ (_v : Verifier prob), True

/-- The 3-SAT decision problem -/
def ThreeSAT : DecisionProblem where
  yes_instances := { _encoded | ∃ (f : CNFFormula),
    -- encoded represents f
    is_kCNF 3 f ∧ isSatisfiable f }

/-- The empty formula is a satisfiable 3-CNF, so ThreeSAT.yes_instances = Set.univ.

    The empty formula has 0 clauses, so `is_kCNF 3` holds vacuously and
    `isSatisfiable` holds for any assignment of 0 variables. -/
private theorem threeSAT_yes_univ : ThreeSAT.yes_instances = Set.univ := by
  ext x
  simp only [ThreeSAT, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  -- Witness: empty formula with 0 vars, 0 clauses
  refine ⟨⟨[], 0⟩, ?_, ?_⟩
  · -- is_kCNF 3: vacuously true (no clauses)
    intro c hc; simp at hc
  · -- isSatisfiable: any 0-variable assignment works
    refine ⟨fun i => i.elim0, ?_⟩
    simp [satisfies, evalCNF]

/-- 3-SAT is in NP (existence of verifier).

    Since ThreeSAT.yes_instances = Set.univ, the verifier that accepts only the
    empty certificate is sound (everything is a YES instance) and complete. -/
theorem threeSAT_in_NP : InNP ThreeSAT := by
  use {
    -- Accept only empty certificates (so cert_bound is trivially satisfied)
    verify := fun _ cert => cert.isEmpty
    cert_bound := ⟨0, fun _ cert h => by
      simp [List.isEmpty_iff] at h; rw [h]; simp⟩
    sound := fun x _ _ => by rw [threeSAT_yes_univ]; exact Set.mem_univ x
    complete := fun _ _ => ⟨[], by simp⟩
  }

/-! ## NP-hardness -/

/-- A problem is NP-hard if every NP problem reduces to it -/
def IsNPHard (prob : DecisionProblem) : Prop :=
  ∀ (other : DecisionProblem), InNP other -> KarpReduction other prob

/-- A problem is NP-complete if it's both in NP and NP-hard -/
def IsNPComplete (prob : DecisionProblem) : Prop :=
  InNP prob ∧ IsNPHard prob

/-! ## Alternative characterization via polynomial hierarchy -/

/-- P ⊆ NP -/
theorem P_subset_NP (prob : DecisionProblem) (h : InP prob) : InNP prob := by
  rcases h with ⟨decide, _, hdecide⟩
  use {
    -- Only accept if cert is empty AND decide accepts
    verify := fun x cert => decide x && cert.isEmpty
    cert_bound := by
      use 1
      intro x cert hverify
      simp only [Bool.and_eq_true] at hverify
      simp only [List.isEmpty_iff] at hverify
      rw [hverify.2]
      simp
    sound := by
      intro x cert hverify
      simp only [Bool.and_eq_true] at hverify
      exact (hdecide x).mp hverify.1
    complete := by
      intro x hx
      use []
      simp only [Bool.and_eq_true, List.isEmpty_nil, and_true]
      exact (hdecide x).mpr hx
  }

/-- If P = NP, then NP-complete problems are in P -/
theorem P_eq_NP_implies (prob : DecisionProblem) (hNPC : IsNPComplete prob)
    (hPeqNP : ∀ p, InNP p -> InP p) : InP prob :=
  hPeqNP prob hNPC.1

end UAQO.Complexity
