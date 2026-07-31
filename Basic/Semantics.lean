import Basic.Syntax

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

def Satisfies (interpretation : Interpretation σ) (formula : Formula σ) : Prop :=
  ∀ literal ∈ formula, SatisfiesLiteral interpretation literal

/-- Semantic entailment between conjunctive EUF formulas. -/
def Entails (antecedent consequent : Formula σ) : Prop :=
  ∀ interpretation : Interpretation σ,
    Satisfies interpretation antecedent →
      Satisfies interpretation consequent

@[simp]
theorem satisfies_append (interpretation : Interpretation σ)
    (left right : Formula σ) :
    Satisfies interpretation (left ++ right) ↔
      Satisfies interpretation left ∧ Satisfies interpretation right := by
  simp only [Satisfies, List.mem_append]
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

def Satisfiable (formula : Formula σ) : Prop :=
  ∃ interpretation : Interpretation σ, Satisfies interpretation formula

def Unsatisfiable (formula : Formula σ) : Prop :=
  ¬Satisfiable formula

/-- Entailment of an unsatisfiable continuation makes the original
conjunction unsatisfiable. This is the semantic core of the redundancy of the
usual interpolation consistency condition. -/
theorem unsatisfiable_append_of_entails_of_unsatisfiable
    (entails : Entails left middle)
    (unsatisfiable : Unsatisfiable (middle ++ right)) :
    Unsatisfiable (left ++ right) := by
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
