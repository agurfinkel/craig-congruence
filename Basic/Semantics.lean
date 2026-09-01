-- SPDX-License-Identifier: MIT

import Basic.Syntax

/-!
Standard semantics for ground EUF: interpretations, recursive term evaluation,
literal and conjunctive-formula satisfaction, semantic entailment, and
satisfiability helpers.
-/

namespace EUF

/-- An interpretation supplies a nonempty domain and meanings for the function
symbols. -/
structure Interpretation (σ : Signature) where
  Domain : Type
  nonempty : Nonempty Domain
  function {arity : Nat} :
    σ.Function arity → (Fin arity → Domain) → Domain

namespace Interpretation

def eval (interpretation : Interpretation σ) : Term σ → interpretation.Domain
  | .app function arguments =>
      interpretation.function function (fun i => eval interpretation (arguments i))

@[simp]
theorem eval_constant (interpretation : Interpretation σ)
    (symbol : σ.Function 0) :
    interpretation.eval (.constant symbol) =
      interpretation.function symbol Fin.elim0 := by
  apply congrArg (interpretation.function symbol)
  funext i
  exact Fin.elim0 i

@[simp]
theorem eval_unary (interpretation : Interpretation σ)
    (function : σ.Function 1) (argument : Term σ) :
    interpretation.eval (.unary function argument) =
      interpretation.function function (fun _ => interpretation.eval argument) :=
  rfl

end Interpretation

def SatisfiesLiteral (interpretation : Interpretation σ) : Literal σ → Prop
  | .eq left right => interpretation.eval left = interpretation.eval right
  | .ne left right => interpretation.eval left ≠ interpretation.eval right

def Satisfies (interpretation : Interpretation σ) (cube : Cube σ) : Prop :=
  ∀ literal ∈ cube, SatisfiesLiteral interpretation literal

/-- Semantic entailment between conjunctive EUF cubes. -/
def Entails (antecedent consequent : Cube σ) : Prop :=
  ∀ interpretation : Interpretation σ,
    Satisfies interpretation antecedent →
      Satisfies interpretation consequent

@[simp]
theorem satisfies_append (interpretation : Interpretation σ)
    (left right : Cube σ) :
    Satisfies interpretation (Cube.append left right) ↔
      Satisfies interpretation left ∧ Satisfies interpretation right := by
  simp only [Satisfies, Cube.mem_append_iff]
  constructor
  · intro satisfies
    constructor
    · intro literal member
      exact satisfies literal (Or.inl member)
    · intro literal member
      exact satisfies literal (Or.inr member)
  · rintro ⟨satisfiesLeft, satisfiesRight⟩ literal (member | member)
    · exact satisfiesLeft literal member
    · exact satisfiesRight literal member

def Satisfiable (cube : Cube σ) : Prop :=
  ∃ interpretation : Interpretation σ, Satisfies interpretation cube

def Unsatisfiable (cube : Cube σ) : Prop :=
  ¬Satisfiable cube

/-- Entailment of an unsatisfiable continuation makes the original
conjunction unsatisfiable. This is the semantic core of the redundancy of the
usual interpolation consistency condition. -/
theorem unsatisfiable_append_of_entails_of_unsatisfiable
    (entails : Entails left middle)
    (unsatisfiable : Unsatisfiable (Cube.append middle right)) :
    Unsatisfiable (Cube.append left right) := by
  rintro ⟨interpretation, satisfies⟩
  have satisfiesLeft : Satisfies interpretation left :=
    (satisfies_append interpretation left right).mp satisfies |>.1
  have satisfiesRight : Satisfies interpretation right :=
    (satisfies_append interpretation left right).mp satisfies |>.2
  apply unsatisfiable
  refine ⟨interpretation, ?_⟩
  exact (satisfies_append interpretation middle right).mpr
    ⟨entails interpretation satisfiesLeft, satisfiesRight⟩

end EUF
