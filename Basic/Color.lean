import Basic.Syntax

namespace EUF

/-- A symbol is either local to one of `k` formulas or shared by two
consecutive formulas. A shared index `i : Fin (k - 1)` denotes the boundary
between formulas `i` and `i + 1`. -/
inductive Color (k : Nat) where
  | local (formula : Fin k)
  | shared (boundary : Fin (k - 1))
  deriving DecidableEq

namespace Color

/-- The formulas in which a symbol of this color may occur. -/
def Allows : Color k → Fin k → Prop
  | .local owner, formula => formula = owner
  | .shared boundary, formula =>
      formula.val = boundary.val ∨ formula.val = boundary.val + 1

/-- In the two-formula setting, the local color of the first formula. -/
def A : Color 2 := .local 0

/-- In the two-formula setting, the local color of the second formula. -/
def B : Color 2 := .local 1

/-- In the two-formula setting, the color shared by A and B. -/
def sharedAB : Color 2 := .shared 0

end Color

/-- A signature together with a color for every function symbol. -/
structure ColoredSignature (k : Nat) extends Signature where
  color {arity : Nat} : Function arity → Color k

namespace Term

/-- A term is available in a formula when every symbol occurring in it is
allowed in that formula. -/
def AvailableIn (colored : ColoredSignature k) (formula : Fin k) :
    Term colored.toSignature → Prop
  | .app function arguments =>
      (colored.color function).Allows formula ∧
        ∀ i, AvailableIn colored formula (arguments i)

/-- A term has a color when exactly the formulas admitted by that color can
contain all symbols in the term. This realizes the "most restrictive symbol"
rule by intersecting the availability of all occurring symbols. -/
def HasColor (colored : ColoredSignature k)
    (term : Term colored.toSignature) (color : Color k) : Prop :=
  ∀ formula, AvailableIn colored formula term ↔ color.Allows formula

/-- A term is colorable when its symbols have a nonempty availability that is
represented by a local or adjacent-shared color. -/
def Colorable (colored : ColoredSignature k)
    (term : Term colored.toSignature) : Prop :=
  ∃ color, HasColor colored term color

end Term

namespace Literal

/-- A literal is available in a formula when both of its terms are. -/
def AvailableIn (colored : ColoredSignature k) (formula : Fin k) :
    Literal colored.toSignature → Prop
  | .eq left right | .ne left right =>
      left.AvailableIn colored formula ∧ right.AvailableIn colored formula

/-- The color of a literal is the most restrictive color among all symbols in
its two terms. -/
def HasColor (colored : ColoredSignature k)
    (literal : Literal colored.toSignature) (color : Color k) : Prop :=
  ∀ formula, AvailableIn colored formula literal ↔ color.Allows formula

/-- A literal is colorable when it has a local or adjacent-shared color. -/
def Colorable (colored : ColoredSignature k)
    (literal : Literal colored.toSignature) : Prop :=
  ∃ color, HasColor colored literal color

@[simp]
theorem availableIn_negate_iff (colored : ColoredSignature k)
    (formula : Fin k) (literal : Literal colored.toSignature) :
    literal.negate.AvailableIn colored formula ↔
      literal.AvailableIn colored formula := by
  cases literal <;> rfl

@[simp]
theorem hasColor_negate_iff (colored : ColoredSignature k)
    (literal : Literal colored.toSignature) (color : Color k) :
    literal.negate.HasColor colored color ↔
      literal.HasColor colored color := by
  simp only [HasColor, availableIn_negate_iff]

@[simp]
theorem colorable_negate_iff (colored : ColoredSignature k)
    (literal : Literal colored.toSignature) :
    literal.negate.Colorable colored ↔ literal.Colorable colored := by
  simp only [Colorable, hasColor_negate_iff]

end Literal

namespace Formula

/-- A formula is shared across a boundary when all of its literals have that
shared color. In particular, the empty formula is shared. -/
def IsShared (colored : ColoredSignature k) (boundary : Fin (k - 1))
    (formula : Formula colored.toSignature) : Prop :=
  ∀ literal ∈ formula, literal.HasColor colored (.shared boundary)

/-- A formula has color `i` when every literal is colorable and may occur in
formula `i`. Its literals may freely mix local-`i` and compatible shared
colors. -/
def IsColor (colored : ColoredSignature k) (i : Fin k)
    (formula : Formula colored.toSignature) : Prop :=
  ∀ literal ∈ formula,
    literal.Colorable colored ∧ literal.AvailableIn colored i

end Formula

end EUF
