/-
  Encoding and decoding of CNF formulas as bitstrings.

  This provides the infrastructure needed to make ThreeSAT and SharpThreeSAT
  proper decision/counting problems with well-defined yes_instances.

  Encoding scheme (unary-delimited):
  - A natural number n is encoded as n ones followed by a zero
  - A literal is encoded as (variable index in unary, sign bit)
  - A clause is encoded as (number of literals in unary, sequence of literals)
  - A CNF formula is encoded as (numVars in unary, number of clauses in unary, sequence of clauses)
-/
import UAQO.Complexity.Basic

namespace UAQO.Complexity

/-! ## Natural number encoding (unary) -/

/-- Encode a natural number in unary: n ones followed by a zero. -/
def encodeNat : Nat -> List Bool
  | 0 => [false]
  | n + 1 => true :: encodeNat n

/-- Decode a unary-encoded natural number from the front of a bitstring.
    Returns the decoded number and the remaining bits, or none on failure. -/
def decodeNatAux : List Bool -> Option (Nat × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest =>
    match decodeNatAux rest with
    | some (n, rest') => some (n + 1, rest')
    | none => none

/-- encodeNat produces a valid encoding that decodeNatAux can recover. -/
theorem decodeNatAux_encodeNat (n : Nat) (suffix : List Bool) :
    decodeNatAux (encodeNat n ++ suffix) = some (n, suffix) := by
  induction n with
  | zero => simp [encodeNat, decodeNatAux]
  | succ k ih => simp [encodeNat, decodeNatAux, ih]

/-! ## Literal encoding -/

/-- Encode a literal as (variable index in unary, sign bit).
    Positive literal: encodeNat(index) ++ [true]
    Negative literal: encodeNat(index) ++ [false] -/
def encodeLiteral : Literal -> List Bool
  | Literal.pos v => encodeNat v.index ++ [true]
  | Literal.neg v => encodeNat v.index ++ [false]

/-- Decode a literal from the front of a bitstring. -/
def decodeLiteralAux (bits : List Bool) : Option (Literal × List Bool) :=
  match decodeNatAux bits with
  | some (idx, rest) =>
    match rest with
    | true :: rest' => some (Literal.pos ⟨idx⟩, rest')
    | false :: rest' => some (Literal.neg ⟨idx⟩, rest')
    | [] => none
  | none => none

/-- Round-trip correctness for literals. -/
theorem decodeLiteralAux_encodeLiteral (lit : Literal) (suffix : List Bool) :
    decodeLiteralAux (encodeLiteral lit ++ suffix) = some (lit, suffix) := by
  cases lit with
  | pos v =>
    simp only [encodeLiteral, decodeLiteralAux, List.append_assoc, List.cons_append,
      List.nil_append, decodeNatAux_encodeNat]
  | neg v =>
    simp only [encodeLiteral, decodeLiteralAux, List.append_assoc, List.cons_append,
      List.nil_append, decodeNatAux_encodeNat]

/-! ## Clause encoding -/

/-- Encode a list of literals. -/
def encodeLiterals : List Literal -> List Bool
  | [] => []
  | l :: ls => encodeLiteral l ++ encodeLiterals ls

/-- Decode a list of n literals from the front of a bitstring. -/
def decodeLiteralsAux : Nat -> List Bool -> Option (List Literal × List Bool)
  | 0, bits => some ([], bits)
  | n + 1, bits =>
    match decodeLiteralAux bits with
    | some (lit, rest) =>
      match decodeLiteralsAux n rest with
      | some (lits, rest') => some (lit :: lits, rest')
      | none => none
    | none => none

/-- Round-trip correctness for literal lists. -/
theorem decodeLiteralsAux_encodeLiterals (lits : List Literal) (suffix : List Bool) :
    decodeLiteralsAux lits.length (encodeLiterals lits ++ suffix) = some (lits, suffix) := by
  induction lits with
  | nil => simp [decodeLiteralsAux, encodeLiterals]
  | cons l ls ih =>
    simp only [List.length_cons, encodeLiterals, List.append_assoc]
    simp only [decodeLiteralsAux, decodeLiteralAux_encodeLiteral, ih]

/-- Encode a clause as (number of literals in unary, sequence of literals). -/
def encodeClause (c : Clause) : List Bool :=
  encodeNat c.literals.length ++ encodeLiterals c.literals

/-- Decode a clause from the front of a bitstring. -/
def decodeClauseAux (bits : List Bool) : Option (Clause × List Bool) :=
  match decodeNatAux bits with
  | some (n, rest) =>
    match decodeLiteralsAux n rest with
    | some (lits, rest') => some (⟨lits⟩, rest')
    | none => none
  | none => none

/-- Round-trip correctness for clauses. -/
theorem decodeClauseAux_encodeClause (c : Clause) (suffix : List Bool) :
    decodeClauseAux (encodeClause c ++ suffix) = some (c, suffix) := by
  simp only [encodeClause, List.append_assoc]
  simp only [decodeClauseAux, decodeNatAux_encodeNat, decodeLiteralsAux_encodeLiterals]

/-! ## Clause list encoding -/

/-- Encode a list of clauses. -/
def encodeClauses : List Clause -> List Bool
  | [] => []
  | c :: cs => encodeClause c ++ encodeClauses cs

/-- Decode a list of n clauses from the front of a bitstring. -/
def decodeClausesAux : Nat -> List Bool -> Option (List Clause × List Bool)
  | 0, bits => some ([], bits)
  | n + 1, bits =>
    match decodeClauseAux bits with
    | some (c, rest) =>
      match decodeClausesAux n rest with
      | some (cs, rest') => some (c :: cs, rest')
      | none => none
    | none => none

/-- Round-trip correctness for clause lists. -/
theorem decodeClausesAux_encodeClauses (cs : List Clause) (suffix : List Bool) :
    decodeClausesAux cs.length (encodeClauses cs ++ suffix) = some (cs, suffix) := by
  induction cs with
  | nil => simp [decodeClausesAux, encodeClauses]
  | cons c cs' ih =>
    simp only [List.length_cons, encodeClauses, List.append_assoc]
    simp only [decodeClausesAux, decodeClauseAux_encodeClause, ih]

/-! ## CNF formula encoding -/

/-- Encode a CNF formula as a bitstring.
    Format: (numVars in unary, number of clauses in unary, sequence of clauses). -/
def encodeCNF (f : CNFFormula) : List Bool :=
  encodeNat f.numVars ++ encodeNat f.clauses.length ++ encodeClauses f.clauses

/-- Decode a bitstring to a CNF formula.
    Returns some f if the bitstring is a valid encoding, none otherwise. -/
def decodeCNF_impl (bits : List Bool) : Option CNFFormula :=
  match decodeNatAux bits with
  | some (numVars, rest1) =>
    match decodeNatAux rest1 with
    | some (numClauses, rest2) =>
      match decodeClausesAux numClauses rest2 with
      | some (clauses, []) => some ⟨clauses, numVars⟩
      | _ => none  -- trailing bits or decode failure
    | none => none
  | none => none

/-- Round-trip correctness: decoding an encoded formula recovers the original. -/
theorem decode_encode (f : CNFFormula) : decodeCNF_impl (encodeCNF f) = some f := by
  simp only [encodeCNF, List.append_assoc]
  simp only [decodeCNF_impl, decodeNatAux_encodeNat]
  have h := decodeClausesAux_encodeClauses f.clauses []
  simp only [List.append_nil] at h
  simp only [h]

/-- The encoding is injective: distinct formulas produce distinct bitstrings. -/
theorem encodeCNF_injective : Function.Injective encodeCNF := by
  intro f g h
  have hf := decode_encode f
  have hg := decode_encode g
  rw [h] at hf
  rw [hf] at hg
  exact Option.some_injective _ hg

end UAQO.Complexity
