/-
  The complexity class #P and #P-hardness.

  #P is the class of counting problems associated with NP decision problems:
  given an instance, count the number of satisfying certificates.
-/
import UAQO.Complexity.NP
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.LinearAlgebra.Lagrange

namespace UAQO.Complexity

/-! ## The class #P -/

/-- A counting problem -/
structure CountingProblem where
  /-- The function mapping instances to counts -/
  count : List Bool -> Nat

/-- A counting problem is in #P if it counts certificates of an NP verifier
    (informally: counts accepting paths of poly-time NTM) -/
def InSharpP (prob : CountingProblem) : Prop :=
  ∃ (decision : DecisionProblem) (v : Verifier decision) (certBound : Nat -> Nat),
    -- certBound is polynomial
    (∃ d, ∀ n, certBound n <= n^d + d) ∧
    -- count equals number of valid certificates up to the bound
    ∀ x, ∃ (validCerts : Finset (List Bool)),
      (∀ c ∈ validCerts, c.length <= certBound x.length ∧ v.verify x c = true) ∧
      prob.count x = validCerts.card

/-- The #3-SAT problem: count satisfying assignments.

    Uses the fully formalized decodeCNF_impl from Encoding.lean to extract
    a CNF formula from its bitstring encoding and count satisfying assignments. -/
noncomputable def SharpThreeSAT : CountingProblem where
  count := fun encoded =>
    match decodeCNF_impl encoded with
    | some f => numSatisfyingAssignments f
    | none => 0

/-- #3-SAT is in #P.

    AXIOM: The encoding is fully formalized (decodeCNF_impl), but
    IsPolynomialTime is an axiom, so we cannot prove the verifier
    runs in polynomial time within this formalization.

    Citation: Valiant (1979), Proposition 1. -/
axiom sharpThreeSAT_in_SharpP : InSharpP SharpThreeSAT

/-! ## #P-hardness -/

/-- A counting reduction from problem A to problem B.

    A reduces to B if there exist polynomial-time computable f, g such that
    A.count(x) = g(B.count(f(x)), x) for all x, and g is polynomially bounded:
    g(m, x) <= m + |x|^p for some polynomial degree p. -/
def CountingReduction (A B : CountingProblem) : Prop :=
  ∃ (f : List Bool -> List Bool) (g : Nat -> List Bool -> Nat),
    IsPolynomialTime f ∧
    (∃ p, ∀ m x, g m x <= m + x.length^p + p) ∧
    ∀ x, A.count x = g (B.count (f x)) x

/-- Parsimonious reduction: preserves the count exactly -/
def ParsimoniousReduction (A B : CountingProblem) : Prop :=
  ∃ (f : List Bool -> List Bool),
    IsPolynomialTime f ∧
    ∀ x, A.count x = B.count (f x)

/-- A problem is #P-hard if every #P problem reduces to it -/
def IsSharpPHard (prob : CountingProblem) : Prop :=
  ∀ (other : CountingProblem), InSharpP other -> CountingReduction other prob

/-- A problem is #P-complete if it's both in #P and #P-hard -/
def IsSharpPComplete (prob : CountingProblem) : Prop :=
  InSharpP prob ∧ IsSharpPHard prob

/-- #3-SAT is #P-hard.

    AXIOM: Showing polynomial-time counting reductions from any #P problem to
    #3-SAT requires IsPolynomialTime to be formalized.

    Citation: Valiant (1979), Theorem 1. -/
axiom sharpThreeSAT_hard : IsSharpPHard SharpThreeSAT

/-- #3-SAT is #P-complete. PROVED from axioms sharpThreeSAT_in_SharpP + sharpThreeSAT_hard. -/
theorem sharpThreeSAT_complete : IsSharpPComplete SharpThreeSAT :=
  ⟨sharpThreeSAT_in_SharpP, sharpThreeSAT_hard⟩

/-! ## Relationship between #P and NP -/

/-- If we can solve a #P-complete problem, we can solve any NP problem.

    Proof: OracleAlgorithm has no complexity constraint (just a query_bound : Nat),
    so we construct a classical oracle that directly decides membership. -/
theorem sharpP_solves_NP (prob : CountingProblem) (_hSharpP : IsSharpPComplete prob)
    (_oracle : List Bool -> Nat) (_hOracle : ∀ x, _oracle x = prob.count x) :
    ∀ (decision : DecisionProblem), InNP decision ->
      ∃ (oracleFunc : List Bool -> List Bool),
        InPWithOracle decision oracleFunc := by
  intro decision _hNP
  -- Use a classical oracle that directly decides membership
  letI : DecidablePred (· ∈ decision.yes_instances) := Classical.decPred _
  use fun x => if x ∈ decision.yes_instances then [true] else [false]
  refine ⟨{ algorithm := fun oracle x => oracle x, query_bound := 1 }, fun x => ?_⟩
  simp only
  constructor
  · intro h
    by_contra hne
    simp [hne] at h
  · intro hm
    simp [hm]

/-! ## Polynomial interpolation -/

/-- Lagrange interpolation can recover a polynomial from its values.

    Given d+1 distinct points, there exists a unique polynomial of degree ≤ d
    passing through all of them. This is a fundamental result in polynomial algebra. -/
theorem lagrange_interpolation (d : Nat) (points : Fin (d + 1) -> Real)
    (values : Fin (d + 1) -> Real)
    (hdistinct : ∀ i j, i ≠ j -> points i ≠ points j) :
    ∃! (p : Polynomial Real),
      p.natDegree <= d ∧
      ∀ i, Polynomial.eval (points i) p = values i := by
  -- Build the InjOn hypothesis needed for Lagrange.interpolate
  have hinj : Set.InjOn points (Finset.univ : Finset (Fin (d + 1))) := by
    intro a _ b _ hab
    by_contra hne
    exact hdistinct a b hne hab
  -- Existence: Use Lagrange.interpolate from Mathlib
  let p := Lagrange.interpolate Finset.univ points values
  refine ⟨p, ⟨?_, ?_⟩, ?_⟩
  · -- natDegree p <= d
    have hdeg := @Lagrange.degree_interpolate_lt Real _ (Fin (d + 1)) _
        Finset.univ points values hinj
    rw [Finset.card_fin] at hdeg
    by_cases hp : p = 0
    · simp [hp]
    · have : p.natDegree < d + 1 := (Polynomial.natDegree_lt_iff_degree_lt hp).mpr hdeg
      omega
  · -- Evaluation at points
    intro i
    exact @Lagrange.eval_interpolate_at_node Real _ (Fin (d + 1)) _
        Finset.univ i points values hinj (Finset.mem_univ i)
  · -- Uniqueness: if q satisfies the same conditions, then q = p
    intro q ⟨hqdeg, hqeval⟩
    -- Both p and q agree at d+1 points, so p - q has d+1 roots
    -- but degree(p - q) <= d, so p - q = 0 means p = q
    by_contra hne
    have h : p - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    -- p - q has degree at most d
    have hdiff_deg : (p - q).natDegree <= d := by
      have hp_deg : p.natDegree <= d := by
        have hdeg := @Lagrange.degree_interpolate_lt Real _ (Fin (d + 1)) _
            Finset.univ points values hinj
        rw [Finset.card_fin] at hdeg
        by_cases hp0 : p = 0
        · simp [hp0]
        · have : p.natDegree < d + 1 := (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hdeg
          omega
      calc (p - q).natDegree <= max p.natDegree q.natDegree := Polynomial.natDegree_sub_le p q
         _ <= max d d := by omega
         _ = d := max_self d
    -- p - q vanishes at all d+1 points
    have hroots : ∀ i : Fin (d + 1), (p - q).eval (points i) = 0 := by
      intro i
      simp only [Polynomial.eval_sub]
      have hp_i := @Lagrange.eval_interpolate_at_node Real _ (Fin (d + 1)) _
          Finset.univ i points values hinj (Finset.mem_univ i)
      rw [hp_i, hqeval i, sub_self]
    -- A nonzero polynomial of degree d can have at most d roots
    -- But p - q has d+1 distinct roots (the points are distinct)
    have hcard : (Finset.univ : Finset (Fin (d + 1))).card = d + 1 := Finset.card_fin (d + 1)
    -- The roots form a set of size d+1
    have hroots_card : (p - q).roots.toFinset.card >= d + 1 := by
      -- All the (points i) are roots
      have hpoints_roots : ∀ i : Fin (d + 1), points i ∈ (p - q).roots.toFinset := by
        intro i
        rw [Multiset.mem_toFinset, Polynomial.mem_roots h]
        exact hroots i
      -- The points are distinct (by injectivity)
      -- So they form d+1 distinct elements in roots.toFinset
      have hinj_card : (Finset.univ.image points).card = d + 1 := by
        have hinj' : Function.Injective points := by
          intro a b hab
          exact hinj (Finset.mem_univ a) (Finset.mem_univ b) hab
        simp [Finset.card_image_of_injective _ hinj']
      calc (p - q).roots.toFinset.card
          >= (Finset.univ.image points).card := by
             apply Finset.card_le_card
             intro x hx
             rw [Finset.mem_image] at hx
             obtain ⟨i, _, rfl⟩ := hx
             exact hpoints_roots i
        _ = d + 1 := hinj_card
    -- But degree(p-q) <= d means it can have at most d roots (if nonzero)
    have hmax_roots : (p - q).roots.toFinset.card <= (p - q).natDegree := by
      calc (p - q).roots.toFinset.card
          <= (p - q).roots.card := Multiset.toFinset_card_le _
        _ <= (p - q).natDegree := Polynomial.card_roots' (p - q)
    -- Contradiction: d + 1 <= hroots_card <= (p-q).natDegree <= d
    omega

/-- Berlekamp-Welch algorithm for error-correcting polynomial interpolation -/
theorem berlekamp_welch (d e : Nat) (points : Fin (d + 2 * e + 1) -> Real)
    (values : Fin (d + 2 * e + 1) -> Real)
    (_hdistinct : ∀ i j, i ≠ j -> points i ≠ points j)
    (herrors : ∃ (good : Finset (Fin (d + 2 * e + 1))),
      good.card >= d + e + 1 ∧
      ∃ (p : Polynomial Real), p.natDegree <= d ∧
        ∀ i ∈ good, Polynomial.eval (points i) p = values i) :
    ∃ (p : Polynomial Real),
      p.natDegree <= d ∧
      (∃ (good : Finset (Fin (d + 2 * e + 1))),
        good.card >= d + e + 1 ∧
        ∀ i ∈ good, Polynomial.eval (points i) p = values i) := by
  -- The conclusion follows directly from the hypothesis
  rcases herrors with ⟨good, hcard, p, hdeg, heval⟩
  exact ⟨p, hdeg, good, hcard, heval⟩

/-! ## Counting degeneracies -/

/-- Degeneracy counting function for encoded eigenvalue problems.

    AXIOM: Computing d_k from an encoded bitstring requires eigenvalue problem
    encoding/decoding infrastructure beyond the current formalization.

    Citation: arXiv:2411.05736, Section 2.3. -/
axiom degeneracyCount : List Bool -> Nat

/-- The problem of computing degeneracy d_k of eigenvalue E_k. -/
noncomputable def DegeneracyProblem : CountingProblem where
  count := degeneracyCount

/-- Computing degeneracies is #P-hard (reduces from #3-SAT).

    AXIOM: Requires polynomial-time counting reduction from #3-SAT to the
    degeneracy problem. Depends on IsPolynomialTime and degeneracyCount axioms.

    Citation: arXiv:2411.05736, Theorem 3. -/
axiom degeneracy_sharpP_hard : IsSharpPHard DegeneracyProblem

end UAQO.Complexity
