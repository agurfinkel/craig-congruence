-- SPDX-License-Identifier: MIT

/-!
Ground EUF syntax: arity-indexed signatures, terms, equality and disequality
literals, and conjunctive formulas. Convenience constructors cover constants
and unary applications, along with literal and formula helpers.
-/

namespace EUF

/-- A signature assigns a type of function symbols to every arity. -/
structure Signature where
  Function : Nat → Type

/-- Ground EUF terms. Constants are applications of arity-zero symbols. -/
inductive Term (σ : Signature) where
  | app {arity : Nat} (function : σ.Function arity)
      (arguments : Fin arity → Term σ)

namespace Term

/-- Construct a term from a constant (an arity-zero function symbol). -/
def constant (symbol : σ.Function 0) : Term σ :=
  .app symbol Fin.elim0

/-- Apply a unary function symbol without explicitly constructing a `Fin 1`
indexed argument vector. -/
def unary (function : σ.Function 1) (argument : Term σ) : Term σ :=
  .app function (fun _ => argument)

end Term

/-- The atomic formulas needed by a conjunction of EUF constraints. -/
inductive Literal (σ : Signature) where
  | eq (left right : Term σ)
  | ne (left right : Term σ)

namespace Literal

/-- Complement an equality literal. This is used to turn the disjunctive
contents of a clause into the conjunctive formula falsifying that clause. -/
def negate : Literal σ → Literal σ
  | .eq left right => .ne left right
  | .ne left right => .eq left right

@[simp]
theorem negate_negate (literal : Literal σ) :
    literal.negate.negate = literal := by
  cases literal <;> rfl

end Literal

/-- An EUF cube is a conjunction of equality and disequality literals. -/
structure Cube (σ : Signature) where
  private raw : List (Literal σ)

namespace Cube

/-- Construct a cube from its literal list. -/
def ofList (literals : List (Literal σ)) : Cube σ := ⟨literals⟩

/-- The literals conjoined by a cube, in order. -/
def literals (cube : Cube σ) : List (Literal σ) := cube.raw

/-- Construct a cube implicitly when a list of literals has an expected cube
type. There is intentionally no coercion in the other direction. -/
instance : Coe (List (Literal σ)) (Cube σ) where
  coe := ofList

instance : Membership (Literal σ) (Cube σ) where
  mem cube literal := literal ∈ cube.literals

@[simp]
theorem literals_ofList (literals : List (Literal σ)) :
    (ofList literals).literals = literals := rfl

@[simp]
theorem ofList_literals (cube : Cube σ) :
    ofList cube.literals = cube := rfl

@[ext]
theorem ext {left right : Cube σ} (equal : left.literals = right.literals) :
    left = right := by
  cases left
  cases right
  cases equal
  rfl

@[simp]
theorem mem_literals_iff (literal : Literal σ) (cube : Cube σ) :
    literal ∈ cube.literals ↔ literal ∈ cube := Iff.rfl

@[simp]
theorem mem_ofList_iff (literal : Literal σ) (literals : List (Literal σ)) :
    literal ∈ ofList literals ↔ literal ∈ literals := Iff.rfl

/-- The empty conjunction of literals. -/
def empty : Cube σ := ofList []

@[simp]
theorem literals_empty : (empty : Cube σ).literals = [] := rfl

@[simp]
theorem not_mem_empty (literal : Literal σ) : literal ∉ (empty : Cube σ) := by
  change literal ∉ ([] : List (Literal σ))
  simp

/-- The conjunction containing one literal. -/
def singleton (literal : Literal σ) : Cube σ := ofList [literal]

@[simp]
theorem literals_singleton (literal : Literal σ) :
    (singleton literal).literals = [literal] := rfl

@[simp]
theorem mem_singleton_iff (member : Literal σ) (literal : Literal σ) :
    member ∈ singleton literal ↔ member = literal := by
  change member ∈ [literal] ↔ member = literal
  simp

/-- Add a literal to the front of a cube. -/
def cons (literal : Literal σ) (cube : Cube σ) : Cube σ :=
  ofList (literal :: cube.literals)

@[simp]
theorem literals_cons (literal : Literal σ) (cube : Cube σ) :
    (cons literal cube).literals = literal :: cube.literals := rfl

/-- Conjoin two cubes. -/
def append (left right : Cube σ) : Cube σ :=
  ofList (left.literals ++ right.literals)

@[simp]
theorem literals_append (left right : Cube σ) :
    (append left right).literals = left.literals ++ right.literals := rfl

@[simp]
theorem mem_append_iff (literal : Literal σ) (left right : Cube σ) :
    literal ∈ append left right ↔ literal ∈ left ∨ literal ∈ right := by
  simp [append]

/-- Map literal occurrences while preserving their conjunction order. -/
def mapLiterals (cube : Cube σ) (map : Literal σ → Literal τ) : Cube τ :=
  ofList (cube.literals.map map)

@[simp]
theorem literals_mapLiterals (cube : Cube σ) (map : Literal σ → Literal τ) :
    (mapLiterals cube map).literals = cube.literals.map map := rfl

@[simp]
theorem mem_mapLiterals_iff (literal : Literal τ) (cube : Cube σ)
    (map : Literal σ → Literal τ) :
    literal ∈ mapLiterals cube map ↔
      ∃ source ∈ cube, map source = literal := by
  simp [mapLiterals]

/-- Extract the equality literals from a cube, preserving their order. -/
def equalities (cube : Cube σ) : List (Literal σ) :=
  cube.literals.filter (· matches .eq _ _)

/-- Extract the disequality literals from a cube, preserving their order. -/
def disequalities (cube : Cube σ) : List (Literal σ) :=
  cube.literals.filter (· matches .ne _ _)

@[simp]
theorem eq_mem_equalities_iff {cube : Cube σ} :
    Literal.eq left right ∈ Cube.equalities cube ↔
      Literal.eq left right ∈ cube := by
  simp [equalities]

@[simp]
theorem ne_mem_disequalities_iff {cube : Cube σ} :
    Literal.ne left right ∈ Cube.disequalities cube ↔
      Literal.ne left right ∈ cube := by
  simp [disequalities]

end Cube

end EUF
