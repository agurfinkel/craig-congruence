-- SPDX-License-Identifier: MIT

/-!
Generic clausal syntax shared by the EUF clause layer and the proof-relevant
resolution calculus.
-/

namespace Clausal

/-- A clause is an ordered collection representing a disjunction of literals.
Resolution steps below enforce that their produced clauses contain no
duplicates. -/
structure Clause (Literal : Type) where
  private raw : List Literal

namespace Clause

/-- Construct a clause from its literal list. -/
def ofList (literals : List Literal) : Clause Literal := ⟨literals⟩

/-- The literals disjoined by a clause, in order. -/
def literals (clause : Clause Literal) : List Literal := clause.raw

/-- List literals coerce into clauses only when the expected type is already a
clause. There is deliberately no coercion in the reverse direction. -/
instance : Coe (List Literal) (Clause Literal) := ⟨ofList⟩

instance : Membership Literal (Clause Literal) where
  mem clause literal := literal ∈ literals clause

@[simp] theorem literals_ofList (items : List Literal) :
    literals (ofList items) = items := rfl

@[simp] theorem ofList_literals (clause : Clause Literal) :
    ofList (literals clause) = clause := by cases clause <;> rfl

@[simp]
theorem ofList_inj (left right : List Literal) :
    ofList left = ofList right ↔ left = right := by
  constructor
  · exact fun equal => congrArg literals equal
  · exact fun equal => congrArg ofList equal

@[ext]
theorem ext {left right : Clause Literal}
    (equal : literals left = literals right) : left = right := by
  cases left
  cases right
  cases equal
  rfl

@[simp] theorem mem_literals_iff (literal : Literal) (clause : Clause Literal) :
    literal ∈ literals clause ↔ literal ∈ clause := Iff.rfl

@[simp] theorem mem_ofList_iff (literal : Literal) (literals : List Literal) :
    literal ∈ ofList literals ↔ literal ∈ literals := Iff.rfl

/-- The empty disjunction. -/
def empty : Clause Literal := ofList []

@[simp] theorem literals_empty : literals (empty : Clause Literal) = [] := rfl

/-- A unit clause. -/
def unit (literal : Literal) : Clause Literal := ofList [literal]

@[simp] theorem literals_unit (literal : Literal) :
    literals (unit literal) = [literal] := rfl

/-- Add a literal to the front of a clause. -/
def cons (literal : Literal) (clause : Clause Literal) : Clause Literal :=
  ofList (literal :: literals clause)

@[simp] theorem literals_cons (literal : Literal) (clause : Clause Literal) :
    literals (cons literal clause) = literal :: literals clause := rfl

/-- Disjoin two clauses. -/
def append (left right : Clause Literal) : Clause Literal :=
  ofList (literals left ++ literals right)

@[simp] theorem literals_append (left right : Clause Literal) :
    literals (append left right) = literals left ++ literals right := rfl

@[simp]
theorem append_ofList (left right : List Literal) :
    append (ofList left) (ofList right) = ofList (left ++ right) := rfl

@[simp]
theorem mem_append_iff (literal : Literal) (left right : Clause Literal) :
    literal ∈ append left right ↔ literal ∈ left ∨ literal ∈ right := by
  exact List.mem_append

/-- Map literal occurrences while preserving their disjunction order. -/
def mapLiterals (clause : Clause Literal₁) (map : Literal₁ → Literal₂) :
    Clause Literal₂ :=
  ofList ((literals clause).map map)

@[simp] theorem literals_mapLiterals (clause : Clause Literal₁)
    (map : Literal₁ → Literal₂) :
    literals (mapLiterals clause map) = (literals clause).map map := rfl

@[simp]
theorem mem_mapLiterals_iff (literal : Literal₂) (clause : Clause Literal₁)
    (map : Literal₁ → Literal₂) :
    literal ∈ mapLiterals clause map ↔
      ∃ source ∈ clause, map source = literal := by
  exact List.mem_map

/-- A clause contains no repeated literal occurrences. -/
def Nodup (clause : Clause Literal) : Prop := (literals clause).Nodup

@[simp]
theorem nodup_ofList (items : List Literal) :
    Nodup (ofList items) ↔ items.Nodup := Iff.rfl

/-- Two clauses contain the same literal occurrences up to permutation. -/
def Perm (left right : Clause Literal) : Prop :=
  List.Perm (literals left) (literals right)

@[simp]
theorem perm_ofList (left right : List Literal) :
    Perm (ofList left) (ofList right) ↔ List.Perm left right := Iff.rfl

end Clause

/-- A CNF is a list representing a conjunction of clauses. -/
abbrev CNF (Literal : Type) := List (Clause Literal)

end Clausal
