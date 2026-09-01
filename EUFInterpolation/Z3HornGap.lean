-- SPDX-License-Identifier: MIT

import EUFInterpolation.InterpolationProcedure

/-!
The ground-EUF pair from `Z3HornGap.smt2`.  Its interpolant requires a
conditional shared equality:

  A = { u = F(x), v = F(y) }
  B = { x = y, u != v }
  I = { x = y -> u = v }

The alternating equality-exchange certificate records that B supplies
`x = y`, after which A derives `u = v` by congruence.  Extraction turns that
dependency into the Horn clause above, and the general soundness theorem proves
the result is a Craig interpolant.
-/

namespace EUF.Z3HornGap

inductive Function : Nat → Type
  | x : Function 0
  | y : Function 0
  | u : Function 0
  | v : Function 0
  | F : Function 1

def signature : ColoredSignature 2 where
  Function := Function
  colorOf
    | .F => .A
    | .x | .y | .u | .v => .sharedAB

def x : Term signature := .constant .x
def y : Term signature := .constant .y
def u : Term signature := .constant .u
def v : Term signature := .constant .v
def F (term : Term signature) : Term signature := .unary .F term

def xy : Equality signature := ⟨x, y⟩
def uv : Equality signature := ⟨u, v⟩

def formulaA : Cube signature :=
  Cube.ofList [Literal.eq u (F x), Literal.eq v (F y)]

def formulaB : Cube signature :=
  Cube.ofList [Literal.eq x y, Literal.ne u v]

def formulas : InterpolationColor → Cube signature
  | 0 => formulaA
  | 1 => formulaB

/-- The shared Horn interpolant `x = y → u = v`. -/
def interpolant : EqualityHornFormula signature :=
  [{ premises := [xy], conclusion := some uv }]

inductive SharedName
  | x | y | u | v

def naming : TermNaming signature where
  Name := SharedName
  representative
    | .x => x
    | .y => y
    | .u => u
    | .v => v

private theorem sharedAB_allows (partition : Fin 2) :
    Color.sharedAB.Allows partition := by
  change partition.val = 0 ∨ partition.val = 1
  omega

private theorem xy_shared : xy.IsShared signature 0 := by
  intro partition
  have sides : partition = 0 ∨ partition = 1 := by omega
  rcases sides with rfl | rfl <;>
    simp [xy, Equality.literal, Literal.AvailableIn, Term.AvailableIn,
      Term.constant, signature, x, y, Color.Allows, Color.sharedAB]

private theorem uv_shared : uv.IsShared signature 0 := by
  intro partition
  have sides : partition = 0 ∨ partition = 1 := by omega
  rcases sides with rfl | rfl <;>
    simp [uv, Equality.literal, Literal.AvailableIn, Term.AvailableIn,
      Term.constant, signature, u, v, Color.Allows, Color.sharedAB]

def edgeXY : SharedEqualityEdge naming where
  left := .x
  right := .y
  isShared := by simpa [naming, xy] using xy_shared

def edgeUV : SharedEqualityEdge naming where
  left := .u
  right := .v
  isShared := by simpa [naming, uv] using uv_shared

private theorem deriveXY : DerivesEq (formulas 1) x y := by
  apply DerivesEq.assumption
  simp [formulas, formulaB]

private theorem deriveUV :
    DerivesEq (Cube.append (formulas 0) (Cube.singleton xy.literal)) u v := by
  have hux : DerivesEq (Cube.append (formulas 0) (Cube.singleton xy.literal)) u (F x) := by
    apply DerivesEq.assumption
    simp [formulas, formulaA]
  have hxy : DerivesEq (Cube.append (formulas 0) (Cube.singleton xy.literal)) x y := by
    apply DerivesEq.assumption
    simp [Cube.mem_append_iff, Cube.singleton, xy, Equality.literal]
  have hFxy : DerivesEq (Cube.append (formulas 0) (Cube.singleton xy.literal)) (F x) (F y) := by
    apply DerivesEq.congr Function.F
    intro _
    exact hxy
  have hFyv : DerivesEq (Cube.append (formulas 0) (Cube.singleton xy.literal)) (F y) v := by
    apply DerivesEq.symm
    apply DerivesEq.assumption
    simp [formulas, formulaA]
  exact hux.trans (hFxy.trans hFyv)

/-- B produces the shared premise `x = y` without dependencies. -/
def proofXY : EqualityExchangeProof formulas 1 edgeXY :=
  .derive 1 edgeXY [] (.nil 0) (by
    change DerivesEq (formulas 1) x y
    exact deriveXY)

def dependenciesXY :
    EqualityExchangeDependencies (naming := naming) formulas 1 [xy] := by
  change EqualityExchangeDependencies formulas 1 [edgeXY.equality]
  exact .cons proofXY (.nil 1)

/-- A consumes `x = y` and produces `u = v` by congruence through local F. -/
def proofUV : EqualityExchangeProof formulas 0 edgeUV :=
  .derive 0 edgeUV [xy] dependenciesXY (by
    change DerivesEq (Cube.append (formulas 0) (Cube.singleton xy.literal)) u v
    exact deriveUV)

def dependenciesUV :
    EqualityExchangeDependencies (naming := naming) formulas 0 [uv] := by
  change EqualityExchangeDependencies formulas 0 [edgeUV.equality]
  exact .cons proofUV (.nil 0)

private theorem conflictDerivation :
    DerivesEq (Cube.append (formulas 1) (Cube.singleton uv.literal)) u v := by
  apply DerivesEq.assumption
  simp [Cube.mem_append_iff, Cube.singleton, uv, Equality.literal]

/-- B owns `u != v`; the communicated `u = v` closes the conflict. -/
def conflict : EqualityInterpolationConflict signature naming formulas :=
  .atColorOne u v (by simp [formulas, formulaB])
    [uv] dependenciesUV conflictDerivation

theorem calculated_interpolant :
    conflict.interpolant = interpolant := by
  rfl

private theorem hasColor_A_uFx :
    (Literal.eq u (F x)).HasColor signature .A := by
  intro partition
  have sides : partition = 0 ∨ partition = 1 := by omega
  rcases sides with rfl | rfl <;>
    simp [Literal.AvailableIn, Term.AvailableIn, Term.constant, Term.unary,
      signature, Color.Allows, Color.A, Color.sharedAB, u, F, x]

private theorem hasColor_A_vFy :
    (Literal.eq v (F y)).HasColor signature .A := by
  intro partition
  have sides : partition = 0 ∨ partition = 1 := by omega
  rcases sides with rfl | rfl <;>
    simp [Literal.AvailableIn, Term.AvailableIn, Term.constant, Term.unary,
      signature, Color.Allows, Color.A, Color.sharedAB, v, F, y]

private theorem hasColor_shared_xy :
    (Literal.eq x y).HasColor signature .sharedAB := by
  simpa [xy, Equality.IsShared, Equality.literal, Color.sharedAB] using
    xy_shared

private theorem hasColor_shared_uv :
    (Literal.ne u v).HasColor signature .sharedAB := by
  change (Literal.eq u v).negate.HasColor signature .sharedAB
  apply (Literal.hasColor_negate_iff signature
    (Literal.eq u v) .sharedAB).mpr
  simpa [uv, Equality.IsShared, Equality.literal, Color.sharedAB] using
    uv_shared

private theorem coloredAt
    {partition : Fin 2} {literal : Literal signature} {color : Color 2}
    (hasColor : literal.HasColor signature color)
    (allowed : color.Allows partition) :
    literal.Colorable signature ∧ literal.AvailableIn signature partition :=
  ⟨⟨color, hasColor⟩, (hasColor partition).mpr allowed⟩

private theorem formulaA_color : Cube.IsColor signature 0 formulaA := by
  intro literal member
  simp [formulaA] at member
  rcases member with rfl | rfl
  · exact coloredAt hasColor_A_uFx rfl
  · exact coloredAt hasColor_A_vFy rfl

private theorem formulaB_color : Cube.IsColor signature 1 formulaB := by
  intro literal member
  simp [formulaB] at member
  rcases member with rfl | rfl
  · exact coloredAt hasColor_shared_xy (sharedAB_allows 1)
  · exact coloredAt hasColor_shared_uv (sharedAB_allows 1)

/-- The extracted Horn clause is a Craig interpolant for the counterexample. -/
theorem isInterpolant :
    IsInterpolant signature formulaA formulaB interpolant := by
  rw [← calculated_interpolant]
  exact conflict.sound (fun color => by
    rcases InterpolationColor.eq_zero_or_eq_one color with rfl | rfl
    · exact formulaA_color
    · exact formulaB_color)

end EUF.Z3HornGap
