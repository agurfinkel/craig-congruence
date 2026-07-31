import EufItpLean.Syntax

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

def Satisfiable (formula : Formula σ) : Prop :=
  ∃ interpretation : Interpretation σ, Satisfies interpretation formula

def Unsatisfiable (formula : Formula σ) : Prop :=
  ¬Satisfiable formula

end EUF
