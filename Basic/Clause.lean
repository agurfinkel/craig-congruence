-- SPDX-License-Identifier: MIT

import Basic.Semantics
import Basic.Color
import ClausalProofs.Syntax

/-!
Disjunctive clauses and conjunctive CNFs over EUF literals, together with their
satisfaction semantics and basic operations. This includes falsity, append,
distributed CNF disjunction, and their semantic characterization lemmas.
-/

namespace EUF

/-- A clause is a disjunction of EUF literals. This is intentionally distinct
from `Cube`, whose list structure denotes conjunction. -/
abbrev Clause (signature : Signature) := Clausal.Clause (Literal signature)

/-- A clausal formula is a conjunction of disjunctive clauses. -/
abbrev CNF (signature : Signature) := Clausal.CNF (Literal signature)

namespace Literal

@[simp]
theorem satisfies_negate_iff_not (interpretation : Interpretation signature)
    (literal : Literal signature) :
    SatisfiesLiteral interpretation literal.negate ↔
      ¬SatisfiesLiteral interpretation literal := by
  cases literal <;> simp [Literal.negate, SatisfiesLiteral]

end Literal

namespace Clause

def IsShared (sig : ColoredSignature k) (boundary : Fin (k - 1))
  (clause : Clause sig) : Prop :=
  LiteralList.IsShared sig boundary (Clausal.Clause.literals clause)

def IsColor (sig : ColoredSignature k) (partition : Fin k)
  (clause : Clause sig) : Prop :=
  LiteralList.IsColor sig partition (Clausal.Clause.literals clause)

private def uniqueWith [DecidableEq α] : List α → List α
  | [] => []
  | head :: tail =>
      let rest := uniqueWith tail
      if head ∈ rest then rest else head :: rest

private theorem mem_uniqueWith [DecidableEq α] (list : List α) :
    ∀ item : α, item ∈ uniqueWith list ↔ item ∈ list := by
  induction list with
  | nil => simp [uniqueWith]
  | cons head tail ih =>
      intro item
      simp only [uniqueWith]
      split
      · have headTail : head ∈ tail := (ih head).mp (by assumption)
        rw [ih item]
        constructor
        · exact fun member => by simp [member]
        · intro member
          cases member with
          | head => exact headTail
          | tail _ member => exact member
      · rw [List.mem_cons, List.mem_cons, ih item]

private theorem nodup_uniqueWith [DecidableEq α] (list : List α) :
    (uniqueWith list).Nodup := by
  induction list with
  | nil => simp [uniqueWith]
  | cons head tail ih =>
      simp only [uniqueWith]
      split <;> simp_all

/-- Remove repeated literals from a clause. EUF signatures do not require
decidable equality, so this normalization uses a classical equality decision
internally. -/
noncomputable def unique (clause : Clause signature) : Clause signature := by
  letI := Classical.typeDecidableEq (Literal signature)
  exact Clausal.Clause.ofList (uniqueWith (Clausal.Clause.literals clause))

@[simp]
theorem mem_unique (literal : Literal signature) (clause : Clause signature) :
    literal ∈ Clause.unique clause ↔ literal ∈ clause := by
  classical
  exact mem_uniqueWith (Clausal.Clause.literals clause) literal

theorem unique_nodup (clause : Clause signature) :
    Clausal.Clause.Nodup (Clause.unique clause) := by
  classical
  exact nodup_uniqueWith (Clausal.Clause.literals clause)

@[simp] theorem unique_nil :
    unique (Clausal.Clause.empty : Clause signature) = Clausal.Clause.empty := by
  classical
  simp [unique, uniqueWith, Clausal.Clause.empty]

@[simp] theorem unique_singleton (literal : Literal signature) :
    unique (Clausal.Clause.unit literal) = Clausal.Clause.unit literal := by
  classical
  simp [unique, uniqueWith, Clausal.Clause.unit]

@[simp] theorem unique_duplicate_unit (literal : Literal signature) :
    unique (Clausal.Clause.ofList [literal, literal]) =
      Clausal.Clause.unit literal := by
  classical
  simp [unique, uniqueWith, Clausal.Clause.unit]

@[simp] theorem unique_ofList_nil :
    unique (Clausal.Clause.ofList [] : Clause signature) =
      Clausal.Clause.ofList [] := by
  simpa [Clausal.Clause.empty] using (unique_nil (signature := signature))

@[simp] theorem unique_ofList_singleton (literal : Literal signature) :
    unique (Clausal.Clause.ofList [literal]) =
      Clausal.Clause.ofList [literal] := by
  simpa [Clausal.Clause.unit] using
    (unique_singleton (signature := signature) literal)

/-- The empty clause. -/
abbrev empty : Clause signature := Clausal.Clause.empty

@[simp]
theorem empty_eq :
    (empty : Clause signature) = Clausal.Clause.ofList [] := rfl

/-- The unit clause containing only `literal`. -/
abbrev unit (literal : Literal signature) : Clause signature :=
  Clausal.Clause.unit literal

@[simp]
theorem unit_eq (literal : Literal signature) :
    unit literal = Clausal.Clause.ofList [literal] := rfl

/-- Return the unique literal when a clause is syntactically unit. -/
def isUnit (clause : Clause signature) : Option (Literal signature) :=
  match Clausal.Clause.literals clause with
  | [literal] => some literal
  | _ => none

@[simp]
theorem isUnit_iff (clause : Clause signature) (literal : Literal signature) :
    isUnit clause = some literal ↔ clause = Clausal.Clause.unit literal := by
  rw [← Clausal.Clause.ofList_literals clause]
  cases Clausal.Clause.literals clause with
  | nil => simp [isUnit, Clausal.Clause.unit]
  | cons head tail =>
      cases tail with
      | nil => simp [isUnit, Clausal.Clause.unit]
      | cons next rest => simp [isUnit, Clausal.Clause.unit]

/-- Negate every literal in a clause, producing the conjunctive cube that
falsifies it. -/
def falsifyingCube (clause : Clause signature) : Cube signature :=
  Cube.mapLiterals (Cube.ofList (Clausal.Clause.literals clause)) Literal.negate

/-- Compatibility name for `falsifyingCube`. -/
abbrev negate (clause : Clause signature) : Cube signature :=
  falsifyingCube clause

@[simp]
theorem negate_eq (clause : Clause signature) :
    clause.negate.literals =
      (Clausal.Clause.literals clause).map Literal.negate := rfl

@[simp]
theorem negate_empty :
    negate (Clausal.Clause.empty : Clause signature) = Cube.empty := rfl

/-- An interpretation satisfies a clause when it satisfies one of its
literals. -/
def Satisfied (interpretation : Interpretation signature)
    (clause : Clause signature) : Prop :=
  ∃ literal ∈ Clausal.Clause.literals clause,
    SatisfiesLiteral interpretation literal

/-- Semantic EUF validity of a clause. -/
def Valid (clause : Clause signature) : Prop :=
  ∀ interpretation : Interpretation signature,
    Clause.Satisfied interpretation clause

@[simp]
theorem not_satisfied_nil (interpretation : Interpretation signature) :
    ¬Satisfied interpretation (Clausal.Clause.empty : Clause signature) := by
  simp [Satisfied]

@[simp]
theorem satisfied_cons_iff (interpretation : Interpretation signature)
    (literal : Literal signature) (clause : Clause signature) :
    Satisfied interpretation (Clausal.Clause.cons literal clause) ↔
      SatisfiesLiteral interpretation literal ∨
        Satisfied interpretation clause := by
  simp [Satisfied]

@[simp]
theorem satisfied_append_iff (interpretation : Interpretation signature)
    (left right : Clause signature) :
    Satisfied interpretation (Clausal.Clause.append left right) ↔
      Satisfied interpretation left ∨ Satisfied interpretation right := by
  constructor
  · rintro ⟨literal, member, satisfies⟩
    rcases Clausal.Clause.mem_append_iff literal left right |>.mp member with member | member
    · exact Or.inl ⟨literal, member, satisfies⟩
    · exact Or.inr ⟨literal, member, satisfies⟩
  · rintro (⟨literal, member, satisfies⟩ | ⟨literal, member, satisfies⟩)
    · exact ⟨literal,
        Clausal.Clause.mem_append_iff literal left right |>.mpr (Or.inl member),
        satisfies⟩
    · exact ⟨literal,
        Clausal.Clause.mem_append_iff literal left right |>.mpr (Or.inr member),
        satisfies⟩

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
  ∀ clause ∈ cnf, Clause.Satisfied interpretation clause

def Satisfiable (cnf : CNF signature) : Prop :=
  ∃ interpretation : Interpretation signature, cnf.Satisfied interpretation

def Unsatisfiable (cnf : CNF signature) : Prop :=
  ¬cnf.Satisfiable

/-- The false CNF, consisting of the empty clause. -/
def falsum : CNF signature := [Clausal.Clause.empty]

@[simp]
theorem not_satisfied_falsum (interpretation : Interpretation signature) :
    ¬Satisfied interpretation (falsum : CNF signature) := by
  intro satisfies
  exact Clause.not_satisfied_nil interpretation
    (satisfies Clausal.Clause.empty (by simp [falsum]))

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
of the left CNF over every clause of the right CNF. Repeated literals are
removed from every combined clause. -/
noncomputable def disjoin (left right : CNF signature) : CNF signature :=
  left.flatMap fun leftClause =>
    right.map fun rightClause =>
      Clause.unique (Clausal.Clause.append leftClause rightClause)

theorem disjoin_clauses_nodup
    (clause : Clause signature) (member : clause ∈ disjoin left right) :
    Clausal.Clause.Nodup clause := by
  classical
  simp only [disjoin, List.mem_flatMap, List.mem_map] at member
  obtain ⟨leftClause, _, rightClause, _, rfl⟩ := member
  exact Clause.unique_nodup (Clausal.Clause.append leftClause rightClause)

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
          ∃ clause, clause ∈ left ∧ ¬Clause.Satisfied interpretation clause := by
        exact Classical.byContradiction fun noCounterexample =>
          satisfiesLeft fun clause member =>
            Classical.byContradiction fun notSatisfied =>
              noCounterexample ⟨clause, member, notSatisfied⟩
      obtain ⟨leftClause, leftMember, leftUnsatisfied⟩ := counterexample
      intro rightClause rightMember
      have combined := satisfiesDisjunction
          (Clause.unique (Clausal.Clause.append leftClause rightClause)) (by
        simp only [disjoin, List.mem_flatMap, List.mem_map]
        exact ⟨leftClause, leftMember,
          ⟨rightClause, rightMember, rfl⟩⟩)
      have combined' :
          Clause.Satisfied interpretation
            (Clausal.Clause.append leftClause rightClause) := by
        obtain ⟨literal, member, satisfiesLiteral⟩ := combined
        exact ⟨literal, (Clause.mem_unique literal _).mp member,
          satisfiesLiteral⟩
      rcases (Clause.satisfied_append_iff interpretation _ _).mp combined' with
        satisfiesLeftClause | satisfiesRightClause
      · exact False.elim (leftUnsatisfied satisfiesLeftClause)
      · exact satisfiesRightClause
  · rintro (satisfiesLeft | satisfiesRight) clause member
    · simp only [disjoin, List.mem_flatMap, List.mem_map] at member
      obtain ⟨leftClause, leftMember, rightClause, rightMember, rfl⟩ := member
      obtain ⟨literal, literalMember, satisfiesLiteral⟩ :=
        satisfiesLeft leftClause leftMember
      exact ⟨literal, Clause.mem_unique literal _ |>.mpr
        (List.mem_append.mpr (Or.inl literalMember)), satisfiesLiteral⟩
    · simp only [disjoin, List.mem_flatMap, List.mem_map] at member
      obtain ⟨leftClause, leftMember, rightClause, rightMember, rfl⟩ := member
      obtain ⟨literal, literalMember, satisfiesLiteral⟩ :=
        satisfiesRight rightClause rightMember
      exact ⟨literal, Clause.mem_unique literal _ |>.mpr
        (List.mem_append.mpr (Or.inr literalMember)), satisfiesLiteral⟩

end CNF

end EUF
