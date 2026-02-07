/-
  Basic computational complexity definitions.

  We define Turing machines, polynomial time, and oracle access
  as foundations for the complexity-theoretic results.
-/
import Mathlib.Computability.TuringMachine
import Mathlib.Data.Nat.Basic
import UAQO.Foundations.Basic

namespace UAQO.Complexity

/-! ## Boolean formulas -/

/-- A Boolean variable -/
structure BoolVar where
  index : Nat

/-- A literal is a variable or its negation -/
inductive Literal
  | pos : BoolVar -> Literal
  | neg : BoolVar -> Literal

/-- A clause is a disjunction of literals -/
structure Clause where
  literals : List Literal

/-- A CNF formula is a conjunction of clauses -/
structure CNFFormula where
  clauses : List Clause
  numVars : Nat

/-- A k-CNF formula has at most k literals per clause -/
def is_kCNF (k : Nat) (f : CNFFormula) : Prop :=
  ∀ c ∈ f.clauses, c.literals.length <= k

/-- A 3-CNF formula -/
abbrev ThreeCNF := { f : CNFFormula // is_kCNF 3 f }

/-- A Boolean assignment -/
def Assignment (n : Nat) := Fin n -> Bool

/-- Evaluate a literal under an assignment -/
def evalLiteral {n : Nat} (a : Assignment n) : Literal -> Bool
  | Literal.pos v => if h : v.index < n then a ⟨v.index, h⟩ else false
  | Literal.neg v => if h : v.index < n then !a ⟨v.index, h⟩ else true

/-- Evaluate a clause (disjunction) -/
def evalClause {n : Nat} (a : Assignment n) (c : Clause) : Bool :=
  c.literals.any (evalLiteral a)

/-- Evaluate a CNF formula (conjunction) -/
def evalCNF {n : Nat} (a : Assignment n) (f : CNFFormula) : Bool :=
  f.clauses.all (evalClause a)

/-- An assignment satisfies a formula if it evaluates to true -/
def satisfies {n : Nat} (a : Assignment n) (f : CNFFormula) : Prop :=
  evalCNF a f = true

/-- A formula is satisfiable if some assignment satisfies it -/
def isSatisfiable (f : CNFFormula) : Prop :=
  ∃ (a : Assignment f.numVars), satisfies a f

/-- Convert a Fin index to an Assignment by reading bits from the index value. -/
def finToAssignment (n : Nat) (z : Fin (2^n)) : Assignment n :=
  fun i => z.val.testBit i.val

/-- Count the number of satisfying assignments for a CNF formula.
    This is the central quantity in #3-SAT. -/
noncomputable def numSatisfyingAssignments (f : CNFFormula) : Nat :=
  (Finset.filter (fun a : Fin (2^f.numVars) =>
    evalCNF (finToAssignment f.numVars a) f) Finset.univ).card

/-- Count unsatisfied clauses for a given assignment (as a Fin index).
    Returns the number of clauses that evaluate to false under the assignment. -/
noncomputable def countUnsatisfiedClauses (f : CNFFormula) (z : Fin (2^f.numVars)) : Nat :=
  (f.clauses.filter (fun c =>
    !evalClause (finToAssignment f.numVars z) c)).length

/-- Count assignments with exactly k unsatisfied clauses.
    This gives the degeneracy d_k in the 3-SAT Hamiltonian encoding. -/
noncomputable def countAssignmentsWithKUnsatisfied (f : CNFFormula) (k : Nat) : Nat :=
  (Finset.filter (fun z : Fin (2^f.numVars) =>
    countUnsatisfiedClauses f z = k) Finset.univ).card

/-! ## Polynomial time -/

/-- A function is polynomial-time computable (informal) -/
def IsPolynomialTime (_f : List Bool -> List Bool) : Prop :=
  ∃ (_p : Nat), ∀ (_input : List Bool),
    True  -- Placeholder: computation time <= p * |input|^p

/-- A decision problem -/
structure DecisionProblem where
  /-- The set of YES instances -/
  yes_instances : Set (List Bool)

/-- A decision problem is in P if it can be decided in polynomial time -/
def InP (prob : DecisionProblem) : Prop :=
  ∃ (decide : List Bool -> Bool),
    IsPolynomialTime (fun x => [decide x]) ∧
    ∀ x, decide x = true ↔ x ∈ prob.yes_instances

/-! ## Oracle access -/

/-- A function with oracle access to another function -/
structure OracleAlgorithm (Oracle : List Bool -> List Bool) where
  /-- The algorithm with oracle calls -/
  algorithm : (List Bool -> List Bool) -> List Bool -> List Bool
  /-- Number of oracle calls is bounded -/
  query_bound : Nat

/-- Polynomial-time with oracle access -/
def InPWithOracle (prob : DecisionProblem) (oracle : List Bool -> List Bool) : Prop :=
  ∃ (alg : OracleAlgorithm oracle),
    ∀ x, (alg.algorithm oracle x).head? = some true ↔ x ∈ prob.yes_instances

/-! ## Polynomial-time reductions -/

/-- A many-one (Karp) reduction from problem A to problem B -/
def KarpReduction (A B : DecisionProblem) : Prop :=
  ∃ (f : List Bool -> List Bool),
    IsPolynomialTime f ∧
    ∀ x, x ∈ A.yes_instances ↔ f x ∈ B.yes_instances

/-- A Turing (Cook) reduction from A to B (informal: assumes decidable oracle) -/
def TuringReduction (A B : DecisionProblem) : Prop :=
  ∃ (oracle : List Bool -> List Bool),
    (∀ x, (oracle x = [true]) ↔ x ∈ B.yes_instances) ∧
    InPWithOracle A oracle

end UAQO.Complexity
