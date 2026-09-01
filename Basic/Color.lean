-- SPDX-License-Identifier: MIT

import Basic.Syntax

/-!
Colors for local and adjacent-shared function symbols. The module lifts symbol
colors to availability, exact color, and colorability predicates on terms,
literals, and conjunctive formulas.
-/

namespace EUF

/-- A symbol is either local to one of `k` formulas or shared by two
consecutive formulas. A shared index `i : Fin (k - 1)` denotes the boundary
between formulas `i` and `i + 1`. -/
inductive Color (k : Nat) where
  | local (partition : Fin k)
  | shared (boundary : Fin (k - 1))
  deriving DecidableEq

namespace Color

/-- The formulas in which a symbol of this color may occur. -/
def Allows : Color k → Fin k → Prop
  | .local owner, partition => partition = owner
  | .shared boundary, partition =>
      partition.val = boundary.val ∨ partition.val = boundary.val + 1

/-- In the two-formula setting, the local color of the first formula. -/
def A : Color 2 := .local 0

/-- In the two-formula setting, the local color of the second formula. -/
def B : Color 2 := .local 1

/-- In the two-formula setting, the color shared by A and B. -/
def sharedAB : Color 2 := .shared 0

end Color

/-- A signature together with a color for every function symbol. -/
structure ColoredSignature (k : Nat) extends Signature where
  colorOf {arity : Nat} : Function arity → Color k

/-- Forget the colors attached to a signature's function symbols. -/
instance : CoeOut (ColoredSignature k) Signature where
  coe := ColoredSignature.toSignature

namespace Term

/-- A term is available in a formula when every symbol occurring in it is
allowed in that formula. -/
def AvailableIn (sig : ColoredSignature k) (partition : Fin k) :
  Term sig → Prop
  | .app function arguments =>
      (sig.colorOf function).Allows partition ∧
        ∀ i, AvailableIn sig partition (arguments i)

/-- A term has a color when exactly the formulas admitted by that color can
contain all symbols in the term. This realizes the "most restrictive symbol"
rule by intersecting the availability of all occurring symbols. -/
def HasColor (sig : ColoredSignature k)
  (term : Term sig) (color : Color k) : Prop :=
  ∀ partition, AvailableIn sig partition term ↔ color.Allows partition

/-- A term is colorable when its symbols have a nonempty availability that is
represented by a local or adjacent-shared color. -/
def Colorable (sig : ColoredSignature k)
  (term : Term sig) : Prop :=
  ∃ color, HasColor sig term color

end Term

namespace Literal

/-- A literal is available in a partition when both of its terms are. -/
def AvailableIn (coloredSig : ColoredSignature k) (partition : Fin k) :
  Literal coloredSig → Prop
  | .eq left right | .ne left right =>
      left.AvailableIn coloredSig partition ∧ right.AvailableIn coloredSig partition

/-- The color of a literal is the most restrictive color among all symbols in
its two terms. -/
def HasColor (sig : ColoredSignature k)
  (literal : Literal sig) (color : Color k) : Prop :=
  ∀ partition, AvailableIn sig partition literal ↔ color.Allows partition

/-- A literal is colorable when it has a local or adjacent-shared color. -/
def Colorable (sig : ColoredSignature k)
  (literal : Literal sig) : Prop :=
  ∃ color, HasColor sig literal color

@[simp]
theorem availableIn_negate_iff (sig : ColoredSignature k)
  (partition : Fin k) (literal : Literal sig) :
  literal.negate.AvailableIn sig partition ↔
    literal.AvailableIn sig partition := by
  cases literal <;> rfl

@[simp]
theorem hasColor_negate_iff (sig : ColoredSignature k)
  (literal : Literal sig) (color : Color k) :
  literal.negate.HasColor sig color ↔
    literal.HasColor sig color := by
  simp only [HasColor, availableIn_negate_iff]

@[simp]
theorem colorable_negate_iff (sig : ColoredSignature k)
  (literal : Literal sig) :
  literal.negate.Colorable sig ↔ literal.Colorable sig := by
  simp only [Colorable, hasColor_negate_iff]

end Literal

namespace LiteralList

/-- A list of literals is shared across a boundary when all of its literals
have that shared color. In particular, the empty list is shared. -/
def IsShared (sig : ColoredSignature k) (boundary : Fin (k - 1))
  (literals : List (Literal sig)) : Prop :=
  ∀ literal ∈ literals, literal.HasColor sig (.shared boundary)

/-- A list of literals has color `i` when every literal is colorable and may
occur in formula `i`. Its literals may freely mix local-`i` and compatible shared
colors. -/
def IsColor (sig : ColoredSignature k) (partition : Fin k)
  (literals : List (Literal sig)) : Prop :=
  ∀ literal ∈ literals,
    literal.Colorable sig ∧ literal.AvailableIn sig partition

end LiteralList

namespace Cube

def IsShared (sig : ColoredSignature k) (boundary : Fin (k - 1))
  (cube : Cube sig) : Prop :=
  LiteralList.IsShared sig boundary cube.literals

def IsColor (sig : ColoredSignature k) (partition : Fin k)
  (cube : Cube sig) : Prop :=
  LiteralList.IsColor sig partition cube.literals

end Cube

end EUF
