-- SPDX-License-Identifier: MIT

import ClausalProofInterpolation.Specification

/-!
A semantic compatibility test for Z3's `iuc_cubes-043.smt2` / `proof_43.smt2`
example.  Z3 returns `not (= (F b) (F d))`; below that formula is represented
as the unit CNF `[[.ne (F b) (F d)]]` and checked against the same A/B input.
-/

namespace EUF.Z3Proof43

inductive Function : Nat → Type
  | a : Function 0
  | b : Function 0
  | c : Function 0
  | d : Function 0
  | F : Function 1

def signature : ColoredSignature 2 where
  Function := Function
  colorOf
    | .a => .A
    | .c => .B
    | .b | .d | .F => .sharedAB

def a : Term signature := .constant .a
def b : Term signature := .constant .b
def c : Term signature := .constant .c
def d : Term signature := .constant .d
def F (term : Term signature) : Term signature := .unary .F term

def inputA : CNF signature :=
  [Clausal.Clause.ofList [.ne (F b) (F d), .eq a b, .eq a d],
   Clausal.Clause.ofList [.ne (F a) (F b), .ne (F a) (F d)],
   Clausal.Clause.ofList [.ne (F a) (F d), .ne (F b) (F d)],
   Clausal.Clause.ofList [.ne (F a) (F d)]]

def inputB : CNF signature :=
  [Clausal.Clause.ofList [.eq b c],
   Clausal.Clause.ofList [.eq (F c) (F d)]]

@[simp] private theorem sharedAB_allows (partition : Fin 2) :
    Color.sharedAB.Allows partition := by
  change partition.val = 0 ∨ partition.val = 1
  omega

private theorem hasColor_shared_FbFd :
    (Literal.ne (F b) (F d)).HasColor signature .sharedAB := by
  intro partition
  have h : partition = 0 ∨ partition = 1 := by omega
  rcases h with rfl | rfl <;>
    simp [Literal.AvailableIn, Term.AvailableIn, Term.unary, Term.constant,
      Color.Allows, Color.sharedAB,
      signature, b, d, F] <;> exact sharedAB_allows _

private theorem hasColor_A_ab :
    (Literal.eq a b).HasColor signature .A := by
  intro partition
  have h : partition = 0 ∨ partition = 1 := by omega
  rcases h with rfl | rfl <;>
    simp [Literal.AvailableIn, Term.AvailableIn, Term.constant,
      Color.Allows, Color.A,
      signature, a, b] <;> exact Or.inl rfl

private theorem hasColor_A_ad :
    (Literal.eq a d).HasColor signature .A := by
  intro partition
  have h : partition = 0 ∨ partition = 1 := by omega
  rcases h with rfl | rfl <;>
    simp [Literal.AvailableIn, Term.AvailableIn, Term.constant,
      Color.Allows, Color.A,
      signature, a, d] <;> exact Or.inl rfl

private theorem hasColor_A_FaFb :
    (Literal.ne (F a) (F b)).HasColor signature .A := by
  intro partition
  have h : partition = 0 ∨ partition = 1 := by omega
  rcases h with rfl | rfl <;>
    simp [Literal.AvailableIn, Term.AvailableIn, Term.unary, Term.constant,
      Color.Allows, Color.A,
      signature, a, b, F] <;> exact Or.inl rfl

private theorem hasColor_A_FaFd :
    (Literal.ne (F a) (F d)).HasColor signature .A := by
  intro partition
  have h : partition = 0 ∨ partition = 1 := by omega
  rcases h with rfl | rfl <;>
    simp [Literal.AvailableIn, Term.AvailableIn, Term.unary, Term.constant,
      Color.Allows, Color.A,
      signature, a, d, F] <;> exact Or.inl rfl

private theorem hasColor_B_bc :
    (Literal.eq b c).HasColor signature .B := by
  intro partition
  have h : partition = 0 ∨ partition = 1 := by omega
  rcases h with rfl | rfl <;>
    simp [Literal.AvailableIn, Term.AvailableIn, Term.constant,
      Color.Allows, Color.B,
      signature, b, c] <;> exact Or.inr rfl

private theorem hasColor_B_FcFd :
    (Literal.eq (F c) (F d)).HasColor signature .B := by
  intro partition
  have h : partition = 0 ∨ partition = 1 := by omega
  rcases h with rfl | rfl <;>
    simp [Literal.AvailableIn, Term.AvailableIn, Term.unary, Term.constant,
      Color.Allows, Color.B,
      signature, c, d, F] <;> exact Or.inr rfl

private theorem coloredAt {partition : Fin 2} {literal : Literal signature}
    {color : Color 2} (hasColor : literal.HasColor signature color)
    (allowed : color.Allows partition) :
    literal.Colorable signature ∧ literal.AvailableIn signature partition :=
  ⟨⟨color, hasColor⟩, (hasColor partition).mpr allowed⟩

def inputs : ColoredCNF signature where
  part partition := if partition = 0 then inputA else inputB
  part_color := by
    intro partition clause member literal literalMember
    by_cases h : partition = 0
    · subst partition
      simp [inputA] at member
      rcases member with rfl | rfl | rfl | rfl <;> simp at literalMember
      · rcases literalMember with rfl | rfl | rfl
        · exact coloredAt hasColor_shared_FbFd
            (by simp [Color.Allows, Color.sharedAB])
        · exact coloredAt hasColor_A_ab rfl
        · exact coloredAt hasColor_A_ad rfl
      · rcases literalMember with rfl | rfl
        · exact coloredAt hasColor_A_FaFb rfl
        · exact coloredAt hasColor_A_FaFd rfl
      · rcases literalMember with rfl | rfl
        · exact coloredAt hasColor_A_FaFd rfl
        · exact coloredAt hasColor_shared_FbFd
            (by simp [Color.Allows, Color.sharedAB])
      · subst literal
        exact coloredAt hasColor_A_FaFd rfl
    · have equal : partition = 1 := by omega
      subst partition
      simp [h, inputB] at member
      rcases member with rfl | rfl <;> simp at literalMember
      · subst literal
        exact coloredAt hasColor_B_bc rfl
      · subst literal
        exact coloredAt hasColor_B_FcFd rfl

/-- The exact clausal form of Z3's `(not (= (F b) (F d)))`. -/
def interpolant : CNF signature :=
  [Clausal.Clause.ofList [.ne (F b) (F d)]]

private theorem eval_F_congr (interpretation : Interpretation signature)
    {left right : Term signature}
    (equal : interpretation.eval left = interpretation.eval right) :
    interpretation.eval (F left) = interpretation.eval (F right) := by
  change interpretation.function Function.F (fun _ => interpretation.eval left) =
    interpretation.function Function.F (fun _ => interpretation.eval right)
  exact congrArg (fun x => interpretation.function Function.F (fun _ => x)) equal

private theorem satisfies_inputA_implies_interpolant
    (interpretation : Interpretation signature)
    (satisfies : inputA.Satisfied interpretation) :
    interpolant.Satisfied interpretation := by
  have first := satisfies
    (Clausal.Clause.ofList [.ne (F b) (F d), .eq a b, .eq a d])
      (by simp [inputA])
  have last := satisfies (Clausal.Clause.ofList [.ne (F a) (F d)])
    (by simp [inputA])
  simp [Clause.Satisfied, SatisfiesLiteral] at first last
  simp [interpolant, CNF.Satisfied, Clause.Satisfied, SatisfiesLiteral]
  rcases first with hne | hab | had
  · exact hne
  · intro hFbd
    exact last ((eval_F_congr interpretation hab).trans hFbd)
  · intro _
    exact last (eval_F_congr interpretation had)

private theorem interpolant_and_inputB_false
    (interpretation : Interpretation signature)
    (satisfiesInterpolant : interpolant.Satisfied interpretation)
    (satisfiesB : inputB.Satisfied interpretation) : False := by
  have hne := satisfiesInterpolant
    (Clausal.Clause.ofList [.ne (F b) (F d)]) (by simp [interpolant])
  have hbc := satisfiesB (Clausal.Clause.ofList [.eq b c]) (by simp [inputB])
  have hFcd := satisfiesB (Clausal.Clause.ofList [.eq (F c) (F d)])
    (by simp [inputB])
  simp [Clause.Satisfied, SatisfiesLiteral] at hne hbc hFcd
  have hFbc := eval_F_congr interpretation hbc
  exact hne (hFbc.trans hFcd)

theorem z3_interpolant : IsClausalInterpolantAt inputs 0 interpolant where
  inputs_unsatisfiable := by
    rintro ⟨interpretation, satisfies⟩
    exact interpolant_and_inputB_false interpretation
      (satisfies_inputA_implies_interpolant interpretation (satisfies 0))
      (satisfies 1)
  interpolant_shared := by
    intro clause clauseMember literal literalMember
    simp [interpolant] at clauseMember
    subst clause
    simp at literalMember
    subst literal
    exact hasColor_shared_FbFd
  side_entails := by
    intro interpretation satisfies
    exact satisfies_inputA_implies_interpolant interpretation satisfies
  interpolant_other_unsatisfiable := by
    rintro ⟨interpretation, satisfiesInterpolant, satisfiesB⟩
    exact interpolant_and_inputB_false interpretation satisfiesInterpolant satisfiesB

end EUF.Z3Proof43
