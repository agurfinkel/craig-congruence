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

/-- An EUF formula is a conjunction of equality and disequality literals. -/
abbrev Formula (σ : Signature) := List (Literal σ)

namespace Formula

/-- Extract the equality literals from a formula, preserving their order. -/
def equalities (formula : Formula σ) : List (Literal σ) :=
  formula.filter (· matches .eq _ _)

/-- Extract the disequality literals from a formula, preserving their order. -/
def disequalities (formula : Formula σ) : List (Literal σ) :=
  formula.filter (· matches .ne _ _)

@[simp]
theorem eq_mem_equalities_iff {formula : Formula σ} :
    Literal.eq left right ∈ formula.equalities ↔
      Literal.eq left right ∈ formula := by
  simp [equalities]

@[simp]
theorem ne_mem_disequalities_iff {formula : Formula σ} :
    Literal.ne left right ∈ formula.disequalities ↔
      Literal.ne left right ∈ formula := by
  simp [disequalities]

end Formula

end EUF
