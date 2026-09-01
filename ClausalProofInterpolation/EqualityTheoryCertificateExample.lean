-- SPDX-License-Identifier: MIT

import ClausalProofInterpolation.ClausalInterpolationTrace
import ClausalProofInterpolation.TheoryLemmaCertificate
import EUFInterpolation.InterpolationCertificate

/-!
A vertical slice for an LRAT-style EUF theory leaf.

The colored clause

  x != y  or  F(x) = F(y)

is valid by congruence.  Its falsifying conjunction puts `x = y` on color 0
and `F(x) != F(y)` on color 1.  A finite indexed equality certificate derives
the shared equality, communicates it, applies congruence, and closes the
color-1 conflict.  The checked result constructs both the theory lemma and the
partial-interpolant annotation consumed by the existing clausal trace.
-/

namespace EUF.EqualityTheoryCertificateExample

inductive Function : Nat → Type
  | x : Function 0
  | y : Function 0
  | F : Function 1

def signature : ColoredSignature 2 where
  Function := Function
  colorOf := fun _ => .sharedAB

def x : Term signature := .constant .x
def y : Term signature := .constant .y
def F (term : Term signature) : Term signature := .unary .F term

def xy : Equality signature := ⟨x, y⟩
def Fxy : Equality signature := ⟨F x, F y⟩

private theorem shared_allows (partition : Fin 2) :
    Color.sharedAB.Allows partition := by
  change partition.val = 0 ∨ partition.val = 1
  omega

private theorem xy_hasColor :
    (Literal.eq x y).HasColor signature .sharedAB := by
  intro partition
  have sides : partition = 0 ∨ partition = 1 := by omega
  rcases sides with rfl | rfl <;>
    simp [Literal.AvailableIn, Term.AvailableIn, Term.constant,
      signature, Color.Allows, Color.sharedAB, x, y]

private theorem Fxy_hasColor :
    (Literal.eq (F x) (F y)).HasColor signature .sharedAB := by
  intro partition
  have sides : partition = 0 ∨ partition = 1 := by omega
  rcases sides with rfl | rfl <;>
    simp [Literal.AvailableIn, Term.AvailableIn, Term.constant, Term.unary,
      signature, Color.Allows, Color.sharedAB, x, y, F]

private theorem coloredAt
    {partition : Fin 2} {literal : Literal signature}
    (hasColor : literal.HasColor signature .sharedAB) :
    literal.Colorable signature ∧ literal.AvailableIn signature partition :=
  ⟨⟨.sharedAB, hasColor⟩,
    (hasColor partition).mpr (shared_allows partition)⟩

def clause : ColoredClause signature where
  part
    | 0 => Clausal.Clause.ofList [.ne x y]
    | 1 => Clausal.Clause.ofList [.eq (F x) (F y)]
  part_color := by
    intro partition literal member
    have sides : partition = 0 ∨ partition = 1 := by omega
    rcases sides with rfl | rfl
    · simp at member
      subst literal
      apply coloredAt
      exact (Literal.hasColor_negate_iff signature
        (Literal.eq x y) .sharedAB).mpr xy_hasColor
    · simp at member
      subst literal
      exact coloredAt Fxy_hasColor

def formulas : InterpolationColor → Cube signature :=
  fun color => clause.falsifyingPart color

inductive Name
  | x | y

def naming : TermNaming signature where
  Name := Name
  representative
    | .x => x
    | .y => y

private theorem xy_shared : xy.IsShared signature 0 := by
  intro partition
  simpa [xy, Equality.literal, Literal.AvailableIn, Color.sharedAB] using
    (xy_hasColor partition)

def edgeXY : SharedEqualityEdge naming where
  left := .x
  right := .y
  isShared := by simpa [naming, xy] using xy_shared

/-- The color-0 local proof database contains one checked assumption. -/
def certificateXY : EqualityCertificate (formulas 0) [xy] :=
  .add .empty (.assumption xy (by
    change Literal.eq x y ∈ [Literal.eq x y]
    simp))

def proofXY : EqualityExchangeProof formulas 0 edgeXY :=
  .ofCertificate 0 edgeXY [] (.nil 1) certificateXY

def dependenciesXY :
    EqualityExchangeDependencies (naming := naming) formulas 0 [xy] :=
  .cons proofXY (.nil 0)

/-- Color 1 first admits the communicated shared equality as an assumption. -/
def certificateFxyAssumption :
    EqualityCertificate (Cube.append (formulas 1) (Cube.singleton xy.literal)) [xy] :=
  .add .empty (.assumption xy (by
    simp [Cube.mem_append_iff, Cube.singleton, xy, Equality.literal]))

/-- Color 1 consumes `x = y` and checks one congruence step. -/
def certificateFxy :
    EqualityCertificate (Cube.append (formulas 1) (Cube.singleton xy.literal)) [Fxy, xy] :=
  .add certificateFxyAssumption
    (EqualityCertificateStep.congr (sig := signature)
      (formula := Cube.append (formulas 1) (Cube.singleton xy.literal))
      (previous := [xy]) Function.F
      (fun _ => (0 : Fin 1)))

def conflict : EqualityInterpolationConflict signature naming formulas :=
  .atColorOneOfCertificate (F x) (F y)
    (by
      change Literal.ne (F x) (F y) ∈ [Literal.ne (F x) (F y)]
      simp)
    [xy] dependenciesXY certificateFxy

/-- The complete checked theory-leaf certificate. -/
def certificate : EqualityTheoryCertificate signature where
  clause := clause
  naming := naming
  conflict := conflict

def expectedInterpolant : EqualityHornFormula signature :=
  [{ premises := [], conclusion := some xy }]

theorem calculated_interpolant :
    certificate.annotation.interpolant = expectedInterpolant := by
  rfl

theorem checked_theory_lemma_valid :
    EUF.Clause.Valid (Clausal.Clause.append
      (certificate.theoryLemma.part 0) (certificate.theoryLemma.part 1)) :=
  certificate.theoryLemma.valid

def emptyInputs : ColoredCNF signature where
  part := fun _ => []
  part_color := by
    intro _ _ member
    exact nomatch member

/-- No special mixed rule is needed: the checked EUF result is an ordinary
annotated theory leaf for the existing LRAT-style clausal interpolation fold. -/
def clausalAnnotation : ClauseAnnotation emptyInputs 0
    certificate.theoryLemma.toClause :=
  ClauseAnnotation.theory certificate.annotation rfl

end EUF.EqualityTheoryCertificateExample
