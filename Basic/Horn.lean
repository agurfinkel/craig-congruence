-- SPDX-License-Identifier: MIT

import Basic.Color
import Basic.Semantics

/-!
Equality atoms, equality Horn clauses, and conjunctions of Horn clauses. The
module defines their semantics, entailment and inconsistency predicates, and
sharedness conditions used by interpolation.
-/

namespace EUF

/-- An equality atom, separated from `Literal` so it can be used as a positive
atom in an equality Horn clause. -/
structure Equality (signature : Signature) where
  left : Term signature
  right : Term signature

namespace Equality

def literal (equality : Equality signature) : Literal signature :=
  .eq equality.left equality.right

def Satisfied (interpretation : Interpretation signature)
    (equality : Equality signature) : Prop :=
  interpretation.eval equality.left = interpretation.eval equality.right

def IsShared (sig : ColoredSignature k) (boundary : Fin (k - 1))
  (equality : Equality sig) : Prop :=
  equality.literal.HasColor sig (.shared boundary)

@[simp]
theorem satisfied_iff_satisfies_literal
    (interpretation : Interpretation signature)
    (equality : Equality signature) :
    equality.Satisfied interpretation ↔
      SatisfiesLiteral interpretation equality.literal :=
  Iff.rfl

end Equality

/-- A Horn clause over equality atoms. `none` denotes a clause with no positive
conclusion, so `premises ⇒ false`. -/
structure EqualityHornClause (signature : Signature) where
  premises : List (Equality signature)
  conclusion : Option (Equality signature)

namespace EqualityHornClause

def Satisfied (interpretation : Interpretation signature)
    (clause : EqualityHornClause signature) : Prop :=
  (∀ equality ∈ clause.premises, equality.Satisfied interpretation) →
    match clause.conclusion with
    | some equality => equality.Satisfied interpretation
    | none => False

def IsShared (sig : ColoredSignature k) (boundary : Fin (k - 1))
  (clause : EqualityHornClause sig) : Prop :=
  (∀ equality ∈ clause.premises, equality.IsShared sig boundary) ∧
    ∀ equality ∈ clause.conclusion, equality.IsShared sig boundary

end EqualityHornClause

/-- The interpolant fragment produced by EUF interpolation: a conjunction of
Horn clauses over equality atoms. -/
abbrev EqualityHornFormula (signature : Signature) :=
  List (EqualityHornClause signature)

def SatisfiesEqualityHornFormula (interpretation : Interpretation signature)
    (formula : EqualityHornFormula signature) : Prop :=
  ∀ clause ∈ formula, clause.Satisfied interpretation

@[simp]
theorem satisfies_equality_literals
    (interpretation : Interpretation signature)
    (equalities : List (Equality signature)) :
    Satisfies interpretation
      (Cube.ofList (equalities.map Equality.literal)) ↔
      ∀ equality ∈ equalities, equality.Satisfied interpretation := by
  simp only [Satisfies, Cube.mem_ofList_iff, List.mem_map]
  constructor
  · intro satisfies equality member
    exact (equality.satisfied_iff_satisfies_literal interpretation).mpr
      (satisfies equality.literal ⟨equality, member, rfl⟩)
  · rintro satisfies literal ⟨equality, member, rfl⟩
    exact (equality.satisfied_iff_satisfies_literal interpretation).mp
      (satisfies equality member)

def EntailsEqualityHornFormula (antecedent : Cube signature)
    (consequent : EqualityHornFormula signature) : Prop :=
  ∀ interpretation : Interpretation signature,
    Satisfies interpretation antecedent →
      SatisfiesEqualityHornFormula interpretation consequent

def UnsatisfiableWithEqualityHornFormula
    (horn : EqualityHornFormula signature) (cube : Cube signature) : Prop :=
  ¬∃ interpretation : Interpretation signature,
    SatisfiesEqualityHornFormula interpretation horn ∧
      Satisfies interpretation cube

namespace EqualityHornFormula

def IsShared (sig : ColoredSignature k) (boundary : Fin (k - 1))
  (formula : EqualityHornFormula sig) : Prop :=
  ∀ clause ∈ formula, clause.IsShared sig boundary

/-- The always-false Horn formula, represented by `true ⇒ false`. -/
def falsum : EqualityHornFormula signature :=
  [{ premises := [], conclusion := none }]

@[simp]
theorem not_satisfies_falsum
    (interpretation : Interpretation signature) :
    ¬SatisfiesEqualityHornFormula interpretation
      (falsum : EqualityHornFormula signature) := by
  simp [falsum, SatisfiesEqualityHornFormula,
    EqualityHornClause.Satisfied]

@[simp]
theorem isShared_falsum (sig : ColoredSignature k)
    (boundary : Fin (k - 1)) :
    IsShared sig boundary
      (falsum : EqualityHornFormula sig) := by
  simp [falsum, IsShared, EqualityHornClause.IsShared]

@[simp]
theorem satisfies_nil (interpretation : Interpretation signature) :
    SatisfiesEqualityHornFormula interpretation [] := by
  intro clause member
  exact nomatch member

@[simp]
theorem satisfies_singleton (interpretation : Interpretation signature)
    (clause : EqualityHornClause signature) :
    SatisfiesEqualityHornFormula interpretation [clause] ↔
      clause.Satisfied interpretation := by
  constructor
  · intro satisfies
    exact satisfies clause (by simp)
  · intro satisfies other member
    have equal : other = clause := by
      simpa only [List.mem_singleton] using member
    subst other
    exact satisfies

@[simp]
theorem isShared_nil (sig : ColoredSignature k)
    (boundary : Fin (k - 1)) :
    IsShared sig boundary [] := by
  intro clause member
  exact nomatch member

@[simp]
theorem isShared_singleton (sig : ColoredSignature k)
    (boundary : Fin (k - 1))
    (clause : EqualityHornClause sig) :
    IsShared sig boundary [clause] ↔
      clause.IsShared sig boundary := by
  constructor
  · intro shared
    exact shared clause (by simp)
  · intro shared other member
    have equal : other = clause := by
      simpa only [List.mem_singleton] using member
    subst other
    exact shared

@[simp]
theorem isShared_append (sig : ColoredSignature k)
    (boundary : Fin (k - 1))
    (left right : EqualityHornFormula sig) :
    IsShared sig boundary (left ++ right) ↔
      IsShared sig boundary left ∧ IsShared sig boundary right := by
  simp only [IsShared, List.mem_append]
  constructor
  · intro shared
    constructor
    · intro clause member
      exact shared clause (Or.inl member)
    · intro clause member
      exact shared clause (Or.inr member)
  · rintro ⟨sharedLeft, sharedRight⟩ clause (member | member)
    · exact sharedLeft clause member
    · exact sharedRight clause member

@[simp]
theorem satisfies_append (interpretation : Interpretation signature)
    (left right : EqualityHornFormula signature) :
    SatisfiesEqualityHornFormula interpretation (left ++ right) ↔
      SatisfiesEqualityHornFormula interpretation left ∧
        SatisfiesEqualityHornFormula interpretation right := by
  simp only [SatisfiesEqualityHornFormula, List.mem_append]
  constructor
  · intro satisfies
    constructor
    · intro clause member
      exact satisfies clause (Or.inl member)
    · intro clause member
      exact satisfies clause (Or.inr member)
  · rintro ⟨satisfiesLeft, satisfiesRight⟩ clause (member | member)
    · exact satisfiesLeft clause member
    · exact satisfiesRight clause member

end EqualityHornFormula

end EUF
