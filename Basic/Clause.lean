-- SPDX-License-Identifier: MIT

import Basic.Semantics
import Basic.Color

/-!
Disjunctive clauses and conjunctive CNFs over EUF literals, together with their
satisfaction semantics and basic operations. This includes falsity, append,
distributed CNF disjunction, and their semantic characterization lemmas.
-/

namespace EUF

/-- A clause is a disjunction of EUF literals. This is intentionally distinct
from `Formula`, whose list structure denotes conjunction. -/
abbrev Clause (signature : Signature) := List (Literal signature)

/-- A clausal formula is a conjunction of disjunctive clauses. -/
abbrev CNF (signature : Signature) := List (Clause signature)

namespace Literal

@[simp]
theorem satisfies_negate_iff_not (interpretation : Interpretation signature)
    (literal : Literal signature) :
    SatisfiesLiteral interpretation literal.negate ↔
      ¬SatisfiesLiteral interpretation literal := by
  cases literal <;> simp [Literal.negate, SatisfiesLiteral]

end Literal

namespace Clause

/-- The empty clause. -/
def empty : Clause signature := []

@[simp]
theorem empty_eq : (empty : Clause signature) = [] := rfl

/-- The unit clause containing only `literal`. -/
def unit (literal : Literal signature) : Clause signature := [literal]

@[simp]
theorem unit_eq (literal : Literal signature) : unit literal = [literal] := rfl

/-- Return the unique literal when a clause is syntactically unit. -/
def isUnit : Clause signature → Option (Literal signature)
  | [literal] => some literal
  | _ => none

@[simp]
theorem isUnit_iff (clause : Clause signature) (literal : Literal signature) :
    isUnit clause = some literal ↔ clause = [literal] := by
  cases clause with
  | nil => simp [isUnit]
  | cons head tail =>
      cases tail with
      | nil => simp [isUnit]
      | cons next rest => simp [isUnit]

/-- Negate every literal in a clause, producing the conjunctive formula that
falsifies it. -/
def negate (clause : Clause signature) : Formula signature :=
  clause.map Literal.negate

@[simp]
theorem negate_eq (clause : Clause signature) :
    clause.negate = clause.map Literal.negate := rfl

/-- An interpretation satisfies a clause when it satisfies one of its
literals. -/
def Satisfied (interpretation : Interpretation signature)
    (clause : Clause signature) : Prop :=
  ∃ literal ∈ clause, SatisfiesLiteral interpretation literal

/-- Semantic EUF validity of a clause. -/
def Valid (clause : Clause signature) : Prop :=
  ∀ interpretation : Interpretation signature,
    clause.Satisfied interpretation

@[simp]
theorem not_satisfied_nil (interpretation : Interpretation signature) :
    ¬Satisfied interpretation ([] : Clause signature) := by
  simp [Satisfied]

@[simp]
theorem satisfied_cons_iff (interpretation : Interpretation signature)
    (literal : Literal signature) (clause : Clause signature) :
    Satisfied interpretation (literal :: clause) ↔
      SatisfiesLiteral interpretation literal ∨
        Satisfied interpretation clause := by
  simp [Satisfied]

@[simp]
theorem satisfied_append_iff (interpretation : Interpretation signature)
    (left right : Clause signature) :
    Satisfied interpretation (left ++ right) ↔
      Satisfied interpretation left ∨ Satisfied interpretation right := by
  constructor
  · rintro ⟨literal, member, satisfies⟩
    rcases List.mem_append.mp member with member | member
    · exact Or.inl ⟨literal, member, satisfies⟩
    · exact Or.inr ⟨literal, member, satisfies⟩
  · rintro (⟨literal, member, satisfies⟩ | ⟨literal, member, satisfies⟩)
    · exact ⟨literal, List.mem_append.mpr (Or.inl member), satisfies⟩
    · exact ⟨literal, List.mem_append.mpr (Or.inr member), satisfies⟩

/-- A clause cannot be satisfied together with the conjunction negating all
of its literals. -/
theorem contradicts_falsifying_formula
    {signature : Signature} {clause : Clause signature}
    {interpretation : Interpretation signature}
    (satisfiesClause : clause.Satisfied interpretation)
    (satisfiesFalsification :
      Satisfies interpretation clause.negate) : False := by
  obtain ⟨literal, member, satisfiesLiteral⟩ := satisfiesClause
  have satisfiesNegation := satisfiesFalsification literal.negate
    (List.mem_map.mpr ⟨literal, member, rfl⟩)
  exact (Literal.satisfies_negate_iff_not interpretation literal).mp
    satisfiesNegation satisfiesLiteral

end Clause

namespace CNF

def Satisfied (interpretation : Interpretation signature)
    (cnf : CNF signature) : Prop :=
  ∀ clause ∈ cnf, clause.Satisfied interpretation

def Satisfiable (cnf : CNF signature) : Prop :=
  ∃ interpretation : Interpretation signature, cnf.Satisfied interpretation

def Unsatisfiable (cnf : CNF signature) : Prop :=
  ¬cnf.Satisfiable

/-- The false CNF, consisting of the empty clause. -/
def falsum : CNF signature := [[]]

@[simp]
theorem not_satisfied_falsum (interpretation : Interpretation signature) :
    ¬Satisfied interpretation (falsum : CNF signature) := by
  intro satisfies
  exact Clause.not_satisfied_nil interpretation
    (satisfies [] (by simp [falsum]))

@[simp]
theorem satisfied_nil (interpretation : Interpretation signature) :
    Satisfied interpretation ([] : CNF signature) := by
  intro clause member
  exact nomatch member

@[simp]
theorem satisfied_append_iff (interpretation : Interpretation signature)
    (left right : CNF signature) :
    Satisfied interpretation (left ++ right) ↔
      Satisfied interpretation left ∧ Satisfied interpretation right := by
  constructor
  · intro satisfies
    exact ⟨fun clause member => satisfies clause (List.mem_append.mpr (Or.inl member)),
      fun clause member => satisfies clause (List.mem_append.mpr (Or.inr member))⟩
  · rintro ⟨satisfiesLeft, satisfiesRight⟩ clause member
    rcases List.mem_append.mp member with member | member
    · exact satisfiesLeft clause member
    · exact satisfiesRight clause member

/-- CNF representation of disjunction, obtained by distributing every clause
of the left CNF over every clause of the right CNF. -/
def disjoin (left right : CNF signature) : CNF signature :=
  left.flatMap fun leftClause =>
    right.map fun rightClause => leftClause ++ rightClause

@[simp]
theorem satisfied_disjoin_iff (interpretation : Interpretation signature)
    (left right : CNF signature) :
    Satisfied interpretation (disjoin left right) ↔
      Satisfied interpretation left ∨ Satisfied interpretation right := by
  classical
  constructor
  · intro satisfiesDisjunction
    by_cases satisfiesLeft : Satisfied interpretation left
    · exact Or.inl satisfiesLeft
    · right
      have counterexample :
          ∃ clause, clause ∈ left ∧ ¬clause.Satisfied interpretation := by
        exact Classical.byContradiction fun noCounterexample =>
          satisfiesLeft fun clause member =>
            Classical.byContradiction fun notSatisfied =>
              noCounterexample ⟨clause, member, notSatisfied⟩
      obtain ⟨leftClause, leftMember, leftUnsatisfied⟩ := counterexample
      intro rightClause rightMember
      have combined := satisfiesDisjunction (leftClause ++ rightClause) (by
        simp only [disjoin, List.mem_flatMap, List.mem_map]
        exact ⟨leftClause, leftMember,
          ⟨rightClause, rightMember, rfl⟩⟩)
      rcases (Clause.satisfied_append_iff interpretation _ _).mp combined with
        satisfiesLeftClause | satisfiesRightClause
      · exact False.elim (leftUnsatisfied satisfiesLeftClause)
      · exact satisfiesRightClause
  · rintro (satisfiesLeft | satisfiesRight) clause member
    · simp only [disjoin, List.mem_flatMap, List.mem_map] at member
      obtain ⟨leftClause, leftMember, rightClause, rightMember, rfl⟩ := member
      exact (Clause.satisfied_append_iff interpretation _ _).mpr
        (Or.inl (satisfiesLeft leftClause leftMember))
    · simp only [disjoin, List.mem_flatMap, List.mem_map] at member
      obtain ⟨leftClause, leftMember, rightClause, rightMember, rfl⟩ := member
      exact (Clause.satisfied_append_iff interpretation _ _).mpr
        (Or.inr (satisfiesRight rightClause rightMember))

end CNF

end EUF
