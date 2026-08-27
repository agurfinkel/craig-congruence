-- SPDX-License-Identifier: MIT

import ClausalProofInterpolation.ClausalInterpolationTrace
import ClausalProofInterpolation.Z3Proof43

/-!
The normalized eleven-clause trace delivered to Z3's interpolation visitor
for `proof_43.smt2`.  This file is deliberately a manual vertical slice: it
records the proof after trimming and RUP reconstruction, which is the level
at which the current Lean `ClauseTrace` interface begins.
-/

namespace EUF.Z3Proof43Trace

open Z3Proof43

abbrev Sig := Z3Proof43.signature

def q : Literal Sig := .eq b c
def r : Literal Sig := .eq (F c) (F d)
def p : Literal Sig := .eq (F b) (F d)
def s : Literal Sig := .eq a b
def t : Literal Sig := .eq a d
def u : Literal Sig := .eq (F a) (F d)

private theorem F_injective : Function.Injective F := by
  intro left right equal
  have appInjective := Term.app.inj equal
  have argumentsEqual :
      (fun _ : Fin 1 => left) = (fun _ : Fin 1 => right) :=
    eq_of_heq appInjective.2.2
  exact congrFun argumentsEqual 0

private theorem constant_injective :
    Function.Injective
      (Term.constant : Z3Proof43.Function 0 → Term Sig) := by
  intro left right equal
  exact eq_of_heq (Term.app.inj equal).2.1

@[simp] private theorem constant_eq_constant_iff
    (left right : Z3Proof43.Function 0) :
    (Term.constant left : Term Sig) = Term.constant right ↔ left = right :=
  ⟨fun equal => constant_injective equal, congrArg Term.constant⟩

@[simp] private theorem F_eq_F_iff (left right : Term Sig) :
    F left = F right ↔ left = right :=
  ⟨fun equal => F_injective equal, congrArg F⟩

@[simp] private theorem a_ne_b : a ≠ b := by
  intro equal
  have : Z3Proof43.Function.a = Z3Proof43.Function.b :=
    constant_injective equal
  contradiction

@[simp] private theorem a_ne_c : a ≠ c := by
  intro equal
  have : Z3Proof43.Function.a = Z3Proof43.Function.c :=
    constant_injective equal
  contradiction

@[simp] private theorem a_ne_d : a ≠ d := by
  intro equal
  have : Z3Proof43.Function.a = Z3Proof43.Function.d :=
    constant_injective equal
  contradiction

@[simp] private theorem b_ne_c : b ≠ c := by
  intro equal
  have : Z3Proof43.Function.b = Z3Proof43.Function.c :=
    constant_injective equal
  contradiction

@[simp] private theorem b_ne_d : b ≠ d := by
  intro equal
  have : Z3Proof43.Function.b = Z3Proof43.Function.d :=
    constant_injective equal
  contradiction

@[simp] private theorem c_ne_d : c ≠ d := by
  intro equal
  have : Z3Proof43.Function.c = Z3Proof43.Function.d :=
    constant_injective equal
  contradiction

@[simp] private theorem constant_ne_F
    (symbol : Z3Proof43.Function 0) (term : Term Sig) :
    (Term.constant symbol : Term Sig) ≠ F term := by
  intro equal
  have arityEqual := (Term.app.inj equal).1
  omega

@[simp] private theorem F_ne_constant
    (term : Term Sig) (symbol : Z3Proof43.Function 0) :
    F term ≠ (Term.constant symbol : Term Sig) := by
  exact Ne.symm (constant_ne_F symbol term)

@[simp] private theorem Fb_ne_Fc : F b ≠ F c := by
  intro equal
  exact b_ne_c (F_injective equal)

@[simp] private theorem Fa_ne_Fc : F a ≠ F c := by
  intro equal
  exact a_ne_c (F_injective equal)

@[simp] private theorem a_ne_Fc : a ≠ F c := by
  exact constant_ne_F Z3Proof43.Function.a c

@[simp] private theorem p_ne_r_neg : p ≠ r.negate := by
  simp [p, r, Literal.negate]

@[simp] private theorem q_neg_ne_r_neg : q.negate ≠ r.negate := by
  intro equal
  have termsEqual : b = F c := (Literal.ne.inj equal).1
  exact (constant_ne_F Z3Proof43.Function.b c) termsEqual

@[simp] private theorem t_neg_ne_r_neg : t.negate ≠ r.negate := by
  intro equal
  have termsEqual : a = F c := (Literal.ne.inj equal).1
  exact a_ne_Fc termsEqual

@[simp] private theorem s_ne_t : s ≠ t := by
  intro equal
  have termsEqual : b = d := (Literal.eq.inj equal).2
  exact b_ne_d termsEqual

@[simp] private theorem s_neg_ne_q_neg : s.negate ≠ q.negate := by
  intro equal
  have termsEqual : a = b := (Literal.ne.inj equal).1
  exact a_ne_b termsEqual

@[simp] private theorem s_neg_ne_r_neg : s.negate ≠ r.negate := by
  intro equal
  have termsEqual : a = F c := (Literal.ne.inj equal).1
  exact a_ne_Fc termsEqual

@[simp] private theorem raw_qr :
    Literal.ne b c ≠ Literal.ne (F c) (F d) := by
  intro equal
  have termsEqual : b = F c := (Literal.ne.inj equal).1
  exact (constant_ne_F Z3Proof43.Function.b c) termsEqual

@[simp] private theorem raw_rq :
    Literal.ne (F c) (F d) ≠ Literal.ne b c :=
  Ne.symm raw_qr

@[simp] private theorem raw_tr :
    Literal.ne a d ≠ Literal.ne (F c) (F d) := by
  intro equal
  have termsEqual : a = F c := (Literal.ne.inj equal).1
  exact a_ne_Fc termsEqual

@[simp] private theorem raw_st :
    Literal.eq a b ≠ Literal.eq a d := by
  intro equal
  have termsEqual : b = d := (Literal.eq.inj equal).2
  exact b_ne_d termsEqual

@[simp] private theorem raw_sq :
    Literal.ne a b ≠ Literal.ne b c := by
  intro equal
  have termsEqual : a = b := (Literal.ne.inj equal).1
  exact a_ne_b termsEqual

@[simp] private theorem raw_sr :
    Literal.ne a b ≠ Literal.ne (F c) (F d) := by
  intro equal
  have termsEqual : a = F c := (Literal.ne.inj equal).1
  exact a_ne_Fc termsEqual

@[simp] private theorem raw_ur :
    Literal.eq (F a) (F d) ≠ Literal.ne (F c) (F d) := by
  simp

def inputQ : Clause Sig := [q]
def inputR : Clause Sig := [r]
def inputA : Clause Sig := [p.negate, s, t]
def inputNotU : Clause Sig := [u.negate]

def theory1 : Clause Sig := [p, q.negate, r.negate]
def unitP : Clause Sig := [p]
def theory2 : Clause Sig := [u, t.negate, r.negate]
def unitNotT : Clause Sig := [t.negate]
def unitS : Clause Sig := [s]
def theory3 : Clause Sig := [u, s.negate, q.negate, r.negate]

private theorem eval_F_congr (interpretation : Interpretation Sig)
    {left right : Term Sig}
    (equal : interpretation.eval left = interpretation.eval right) :
    interpretation.eval (F left) = interpretation.eval (F right) := by
  change interpretation.function Z3Proof43.Function.F
      (fun _ => interpretation.eval left) =
    interpretation.function Z3Proof43.Function.F
      (fun _ => interpretation.eval right)
  exact congrArg
    (fun value => interpretation.function Z3Proof43.Function.F
      (fun _ => value)) equal

private theorem atomColor
    {side : Fin 2} {clause : Clause Sig} {literal : Literal Sig}
    (clauseMember : clause ∈ Z3Proof43.inputs.part side)
    (literalMember : literal ∈ clause) :
    literal.Colorable Sig ∧ literal.AvailableIn Sig side :=
  Z3Proof43.inputs.part_color side clause clauseMember literal literalMember

private theorem negateColor
    {side : Fin 2} {literal : Literal Sig}
    (color : literal.Colorable Sig ∧ literal.AvailableIn Sig side) :
    literal.negate.Colorable Sig ∧ literal.negate.AvailableIn Sig side :=
  ⟨(Literal.colorable_negate_iff Sig literal).mpr color.1,
   (Literal.availableIn_negate_iff Sig side literal).mpr color.2⟩

private theorem q_color : q.Colorable Sig ∧ q.AvailableIn Sig 1 := by
  apply atomColor (clause := inputQ)
  · simp [Z3Proof43.inputs, Z3Proof43.inputB, inputQ, q]
  · simp [inputQ]

private theorem q_neg_owner {owner : Fin 2}
    (available : q.negate.AvailableIn Sig owner) : owner = 1 := by
  have sides : owner = 0 ∨ owner = 1 := by omega
  rcases sides with rfl | rfl
  · have cAvailable := available.2
    simp [c, Term.constant, Term.AvailableIn, Sig, Z3Proof43.signature,
      Color.B, Color.Allows] at cAvailable
  · rfl

private theorem r_color : r.Colorable Sig ∧ r.AvailableIn Sig 1 := by
  apply atomColor (clause := inputR)
  · simp [Z3Proof43.inputs, Z3Proof43.inputB, inputR, r]
  · simp [inputR]

private theorem r_neg_owner {owner : Fin 2}
    (available : r.negate.AvailableIn Sig owner) : owner = 1 := by
  have sides : owner = 0 ∨ owner = 1 := by omega
  rcases sides with rfl | rfl
  · have cAvailable := available.1.2
    have cTermAvailable := cAvailable 0
    simp [c, Term.constant, Term.AvailableIn, Sig, Z3Proof43.signature,
      Color.B, Color.Allows] at cTermAvailable
  · rfl

private theorem p_color : p.Colorable Sig ∧ p.AvailableIn Sig 0 := by
  have negative := atomColor (side := 0) (clause := inputA)
    (literal := p.negate)
    (by simp [Z3Proof43.inputs, Z3Proof43.inputA, inputA, p, s, t,
      Literal.negate])
    (by simp [inputA])
  simpa using negateColor negative

private theorem s_color : s.Colorable Sig ∧ s.AvailableIn Sig 0 := by
  apply atomColor (clause := inputA)
  · simp [Z3Proof43.inputs, Z3Proof43.inputA, inputA, p, s, t,
      Literal.negate]
  · simp [inputA]

private theorem t_color : t.Colorable Sig ∧ t.AvailableIn Sig 0 := by
  apply atomColor (clause := inputA)
  · simp [Z3Proof43.inputs, Z3Proof43.inputA, inputA, p, s, t,
      Literal.negate]
  · simp [inputA]

private theorem u_color : u.Colorable Sig ∧ u.AvailableIn Sig 0 := by
  have negative := atomColor (side := 0) (clause := inputNotU)
    (literal := u.negate)
    (by simp [Z3Proof43.inputs, Z3Proof43.inputA, inputNotU, u,
      Literal.negate])
    (by simp [inputNotU])
  simpa using negateColor negative

def lemma1 : TheoryLemma Sig where
  part
    | 0 => [p]
    | 1 => [q.negate, r.negate]
  part_color := by
    intro side literal member
    have sides : side = 0 ∨ side = 1 := by omega
    rcases sides with rfl | rfl
    · simp at member
      subst literal
      exact p_color
    · simp at member
      rcases member with rfl | rfl
      · exact negateColor q_color
      · exact negateColor r_color
  valid := by
    intro interpretation
    by_cases hp : SatisfiesLiteral interpretation p
    · exact ⟨p, by simp, hp⟩
    by_cases hq : SatisfiesLiteral interpretation q
    · by_cases hr : SatisfiesLiteral interpretation r
      · exfalso
        apply hp
        exact (eval_F_congr interpretation hq).trans hr
      · exact ⟨r.negate, by simp,
          (Literal.satisfies_negate_iff_not interpretation r).mpr hr⟩
    · exact ⟨q.negate, by simp,
        (Literal.satisfies_negate_iff_not interpretation q).mpr hq⟩

def lemma2 : TheoryLemma Sig where
  part
    | 0 => [u, t.negate]
    | 1 => [r.negate]
  part_color := by
    intro side literal member
    have sides : side = 0 ∨ side = 1 := by omega
    rcases sides with rfl | rfl
    · simp at member
      rcases member with rfl | rfl
      · exact u_color
      · exact negateColor t_color
    · simp at member
      subst literal
      exact negateColor r_color
  valid := by
    intro interpretation
    by_cases hu : SatisfiesLiteral interpretation u
    · exact ⟨u, by simp, hu⟩
    by_cases ht : SatisfiesLiteral interpretation t
    · exfalso
      apply hu
      exact eval_F_congr interpretation ht
    · exact ⟨t.negate, by simp,
        (Literal.satisfies_negate_iff_not interpretation t).mpr ht⟩

def lemma3 : TheoryLemma Sig where
  part
    | 0 => [u, s.negate]
    | 1 => [q.negate, r.negate]
  part_color := by
    intro side literal member
    have sides : side = 0 ∨ side = 1 := by omega
    rcases sides with rfl | rfl
    · simp at member
      rcases member with rfl | rfl
      · exact u_color
      · exact negateColor s_color
    · simp at member
      rcases member with rfl | rfl
      · exact negateColor q_color
      · exact negateColor r_color
  valid := by
    intro interpretation
    by_cases hu : SatisfiesLiteral interpretation u
    · exact ⟨u, by simp, hu⟩
    by_cases hs : SatisfiesLiteral interpretation s
    · by_cases hq : SatisfiesLiteral interpretation q
      · by_cases hr : SatisfiesLiteral interpretation r
        · exfalso
          apply hu
          exact (eval_F_congr interpretation (hs.trans hq)).trans hr
        · exact ⟨r.negate, by simp,
            (Literal.satisfies_negate_iff_not interpretation r).mpr hr⟩
      · exact ⟨q.negate, by simp,
          (Literal.satisfies_negate_iff_not interpretation q).mpr hq⟩
    · exact ⟨s.negate, by simp,
        (Literal.satisfies_negate_iff_not interpretation s).mpr hs⟩

@[simp] theorem lemma1_clause : lemma1.toClause = theory1 := by
  simp [lemma1, theory1, ColoredClause.toClause]

@[simp] theorem lemma2_clause : lemma2.toClause = theory2 := by
  simp [lemma2, theory2, ColoredClause.toClause]

@[simp] theorem lemma3_clause : lemma3.toClause = theory3 := by
  simp [lemma3, theory3, ColoredClause.toClause]

private def resolutionStep
    (left right resolvent : Clause Sig) (pivot : Literal Sig)
    (pivotMem : pivot ∈ left)
    (notPivotMem : pivot.negate ∈ right)
    (membership : ∀ candidate,
      candidate ∈ resolvent ↔
        (candidate ≠ pivot ∧ candidate ∈ left) ∨
        (candidate ≠ pivot.negate ∧ candidate ∈ right))
    (nodup : resolvent.Nodup) :
    ResolutionStep left right resolvent where
  pivot := pivot
  pivot_mem_left := pivotMem
  not_pivot_mem_right := by
    change pivot.negate ∈ right
    exact notPivotMem
  mem_resolvent_iff := membership
  resolvent_nodup := nodup

def t1ResolveQ : ResolutionStep theory1 inputQ [p, r.negate] :=
  resolutionStep theory1 inputQ [p, r.negate] q.negate
    (by simp [theory1, q, r, p])
    (by simp [inputQ, q])
    (by
      intro candidate
      have hqr := raw_qr
      have hrq := raw_rq
      simp [theory1, inputQ, q, r, p, Literal.negate] <;> grind)
    (by simp [r, p, Literal.negate])

def t1ResolveR : ResolutionStep [p, r.negate] inputR unitP :=
  resolutionStep [p, r.negate] inputR unitP r.negate
    (by simp)
    (by simp [inputR, r])
    (by
      intro candidate
      have hrq := raw_rq
      simp [unitP, inputR, p, r, Literal.negate] <;> grind)
    (by simp [unitP])

def t2ResolveR : ResolutionStep theory2 inputR [u, t.negate] :=
  resolutionStep theory2 inputR [u, t.negate] r.negate
    (by simp [theory2])
    (by simp [inputR, r])
    (by
      intro candidate
      have htr := raw_tr
      simp [theory2, inputR, u, t, r, Literal.negate] <;> grind)
    (by simp [u, t, Literal.negate])

def t2ResolveU : ResolutionStep [u, t.negate] inputNotU unitNotT :=
  resolutionStep [u, t.negate] inputNotU unitNotT u
    (by simp)
    (by simp [inputNotU])
    (by intro candidate; simp [unitNotT, inputNotU, u, t, Literal.negate] <;> grind)
    (by simp [unitNotT])

def inputAResolveP : ResolutionStep inputA unitP [s, t] :=
  resolutionStep inputA unitP [s, t] p.negate
    (by simp [inputA])
    (by simp [unitP])
    (by
      intro candidate
      have hst := raw_st
      simp [inputA, unitP, p, s, t, Literal.negate] <;> grind)
    (by simp [s, t])

def inputAResolveT : ResolutionStep [s, t] unitNotT unitS :=
  resolutionStep [s, t] unitNotT unitS t
    (by simp)
    (by simp [unitNotT])
    (by
      intro candidate
      have hst := raw_st
      simp [unitS, unitNotT, s, t, Literal.negate] <;> grind)
    (by simp [unitS])

def t3ResolveR : ResolutionStep theory3 inputR [u, s.negate, q.negate] :=
  resolutionStep theory3 inputR [u, s.negate, q.negate] r.negate
    (by simp [theory3])
    (by simp [inputR])
    (by
      intro candidate
      have hsr := raw_sr
      have hqr := raw_qr
      simp [theory3, inputR, u, s, q, r, Literal.negate] <;> grind)
    (by simp [u, s, q, Literal.negate])

def t3ResolveU :
    ResolutionStep [u, s.negate, q.negate] inputNotU [s.negate, q.negate] :=
  resolutionStep [u, s.negate, q.negate] inputNotU [s.negate, q.negate] u
    (by simp)
    (by simp [inputNotU])
    (by
      intro candidate
      simp [inputNotU, u, s, q, Literal.negate] <;> grind)
    (by simp [s, q, Literal.negate])

def t3ResolveS : ResolutionStep [s.negate, q.negate] unitS [q.negate] :=
  resolutionStep [s.negate, q.negate] unitS [q.negate] s.negate
    (by simp)
    (by simp [unitS])
    (by
      intro candidate
      have hsq := raw_sq
      simp [unitS, s, q, Literal.negate] <;> grind)
    (by simp [q])

def t3ResolveQ : ResolutionStep [q.negate] inputQ [] :=
  resolutionStep [q.negate] inputQ [] q.negate
    (by simp)
    (by simp [inputQ])
    (by intro candidate; simp [inputQ])
    (by simp)

private def inputQLeaf : ColoredProofLeaf Z3Proof43.inputs inputQ :=
  .input 1 (by simp [Z3Proof43.inputs, Z3Proof43.inputB, inputQ, q])

private def inputRLeaf : ColoredProofLeaf Z3Proof43.inputs inputR :=
  .input 1 (by simp [Z3Proof43.inputs, Z3Proof43.inputB, inputR, r])

private def inputALeaf : ColoredProofLeaf Z3Proof43.inputs inputA :=
  .input 0 (by simp [Z3Proof43.inputs, Z3Proof43.inputA, inputA, p, s, t,
    Literal.negate])

private def inputNotULeaf : ColoredProofLeaf Z3Proof43.inputs inputNotU :=
  .input 0 (by simp [Z3Proof43.inputs, Z3Proof43.inputA, inputNotU, u,
    Literal.negate])

def clauses5 : CNF Sig := [inputQ, inputR, inputA, inputNotU, theory1]

def trace5 : ClauseTrace (ColoredProofLeaf Z3Proof43.inputs) clauses5 := by
  let trace0 : ClauseTrace (ColoredProofLeaf Z3Proof43.inputs) [] := .empty
  let trace1 := ClauseTrace.addLeaf trace0 inputQLeaf
  let trace2 := ClauseTrace.addLeaf trace1 inputRLeaf
  let trace3 := ClauseTrace.addLeaf trace2 inputALeaf
  let trace4 := ClauseTrace.addLeaf trace3 inputNotULeaf
  let trace5 := ClauseTrace.addLeaf trace4
    (ColoredProofLeaf.theory 0 lemma1)
  simpa [clauses5, trace0, trace1, trace2, trace3, trace4, lemma1_clause]
    using trace5

def chainP : ResolutionChain clauses5 theory1 unitP :=
  .resolve
    (.resolve .start ⟨0, by simp [clauses5]⟩
      (by simpa [clauses5] using t1ResolveQ))
    ⟨1, by simp [clauses5]⟩
    (by simpa [clauses5] using t1ResolveR)

def justificationP : ChainJustification clauses5 unitP where
  anchor := ⟨4, by simp [clauses5]⟩
  chain := by
    change ResolutionChain clauses5 theory1 unitP
    exact chainP

def clauses7 : CNF Sig := clauses5 ++ [unitP, theory2]

def trace7 : ClauseTrace (ColoredProofLeaf Z3Proof43.inputs) clauses7 := by
  let trace6 := ClauseTrace.addDerived trace5 justificationP
  let trace7 := ClauseTrace.addLeaf trace6
    (ColoredProofLeaf.theory 0 lemma2)
  simpa [clauses7, clauses5, trace6, lemma2_clause] using trace7

def chainNotT : ResolutionChain clauses7 theory2 unitNotT :=
  .resolve
    (.resolve .start ⟨1, by simp [clauses7, clauses5]⟩
      (by simpa [clauses7, clauses5] using t2ResolveR))
    ⟨3, by simp [clauses7, clauses5]⟩
    (by
      change ResolutionStep [u, t.negate] inputNotU unitNotT
      exact t2ResolveU)

def justificationNotT : ChainJustification clauses7 unitNotT where
  anchor := ⟨6, by simp [clauses7, clauses5]⟩
  chain := by
    change ResolutionChain clauses7 theory2 unitNotT
    exact chainNotT

def clauses8 : CNF Sig := clauses7 ++ [unitNotT]

def trace8 : ClauseTrace (ColoredProofLeaf Z3Proof43.inputs) clauses8 :=
  .addDerived trace7 justificationNotT

def chainS : ResolutionChain clauses8 inputA unitS :=
  .resolve
    (.resolve .start ⟨5, by simp [clauses8, clauses7, clauses5]⟩
      (by
        change ResolutionStep inputA unitP [s, t]
        exact inputAResolveP))
    ⟨7, by simp [clauses8, clauses7, clauses5]⟩
    (by
      change ResolutionStep [s, t] unitNotT unitS
      exact inputAResolveT)

def justificationS : ChainJustification clauses8 unitS where
  anchor := ⟨2, by simp [clauses8, clauses7, clauses5]⟩
  chain := by simpa [clauses8, clauses7, clauses5] using chainS

def clauses10 : CNF Sig := clauses8 ++ [unitS, theory3]

def trace10 : ClauseTrace (ColoredProofLeaf Z3Proof43.inputs) clauses10 := by
  let trace9 := ClauseTrace.addDerived trace8 justificationS
  let trace10 := ClauseTrace.addLeaf trace9
    (ColoredProofLeaf.theory 0 lemma3)
  simpa [clauses10, clauses8, clauses7, clauses5, trace9, lemma3_clause]
    using trace10

def chainEmpty : ResolutionChain clauses10 theory3 [] :=
  .resolve
    (.resolve
      (.resolve
        (.resolve .start ⟨1, by simp [clauses10, clauses8, clauses7, clauses5]⟩
          (by simpa [clauses10, clauses8, clauses7, clauses5] using t3ResolveR))
        ⟨3, by simp [clauses10, clauses8, clauses7, clauses5]⟩
        (by
          change ResolutionStep [u, s.negate, q.negate] inputNotU
            [s.negate, q.negate]
          exact t3ResolveU))
      ⟨8, by simp [clauses10, clauses8, clauses7, clauses5]⟩
      (by
        change ResolutionStep [s.negate, q.negate] unitS [q.negate]
        exact t3ResolveS))
    ⟨0, by simp [clauses10, clauses8, clauses7, clauses5]⟩
    (by simpa [clauses10, clauses8, clauses7, clauses5] using t3ResolveQ)

def justificationEmpty : ChainJustification clauses10 [] where
  anchor := ⟨9, by simp [clauses10, clauses8, clauses7, clauses5]⟩
  chain := by
    change ResolutionChain clauses10 theory3 []
    exact chainEmpty

def trace : ClauseTrace (ColoredProofLeaf Z3Proof43.inputs)
    (clauses10 ++ [[]]) :=
  .addDerived trace10 justificationEmpty

def refutation : ColoredClauseRefutation Z3Proof43.inputs where
  clauses := clauses10 ++ [[]]
  trace := trace
  contradiction := by simp

/- The eleven retained clauses, in visitor order. -/
def clauses : CNF Sig :=
  [inputQ, inputR, inputA, inputNotU, theory1, unitP,
   theory2, unitNotT, unitS, theory3, []]

theorem refutation_clauses : refutation.clauses = clauses := by
  simp [refutation, clauses, clauses10, clauses8, clauses7, clauses5]

def pEquality : Equality Sig := ⟨F b, F d⟩

private theorem sharedAB_allows (partition : Fin 2) :
    Color.sharedAB.Allows partition := by
  change partition.val = 0 ∨ partition.val = 1
  omega

private theorem p_shared : p.HasColor Sig .sharedAB := by
  have negativeShared : p.negate.HasColor Sig .sharedAB := by
    apply Z3Proof43.z3_interpolant.interpolant_shared [p.negate]
    · simp [Z3Proof43.interpolant, p, Literal.negate]
    · simp
  exact (Literal.hasColor_negate_iff Sig p .sharedAB).mp negativeShared

/- Z3's `not (= (F b) (F d))`, represented in the Horn fragment. -/
def notPHorn : EqualityHornFormula Sig :=
  [{ premises := [pEquality], conclusion := none }]

@[simp] theorem notPHorn_toCNF : notPHorn.toCNF = [[p.negate]] := by
  simp [notPHorn, pEquality, p, EqualityHornFormula.toCNF,
    EqualityHornClause.toClause, Equality.negatedLiteral,
    Literal.negate]

private theorem notPHorn_shared : EqualityHornFormula.IsShared Sig 0 notPHorn := by
  intro clause clauseMember
  simp [notPHorn] at clauseMember
  subst clause
  constructor
  · intro equality equalityMember
    simp [pEquality] at equalityMember
    subst equality
    exact p_shared
  · intro equality equalityMember
    simp at equalityMember

private theorem satisfies_notPHorn_iff
    (interpretation : Interpretation Sig) :
    SatisfiesEqualityHornFormula interpretation notPHorn ↔
      ¬SatisfiesLiteral interpretation p := by
  simp [notPHorn, pEquality, SatisfiesEqualityHornFormula,
    EqualityHornClause.Satisfied, Equality.Satisfied, p, SatisfiesLiteral]

def annotation1 : TheoryLemmaAnnotation Sig where
  lemma := lemma1
  side := 0
  interpolant := notPHorn
  correct := by
    constructor
    · exact notPHorn_shared
    · intro interpretation satisfiesA
      apply (satisfies_notPHorn_iff interpretation).mpr
      intro hp
      have hnotp := satisfiesA p.negate (by
        simp [lemma1, ColoredClause.falsifyingPart, Clause.negate])
      exact (Literal.satisfies_negate_iff_not interpretation p).mp hnotp hp
    · rintro ⟨interpretation, satisfiesInterpolant, satisfiesB⟩
      have hnotp := (satisfies_notPHorn_iff interpretation).mp
        satisfiesInterpolant
      have hq := satisfiesB q (by
        simp [lemma1, ColoredClause.falsifyingPart, Clause.negate])
      have hr := satisfiesB r (by
        simp [lemma1, ColoredClause.falsifyingPart, Clause.negate])
      exact hnotp ((eval_F_congr interpretation hq).trans hr)

def annotation2 : TheoryLemmaAnnotation Sig where
  lemma := lemma2
  side := 0
  interpolant := EqualityHornFormula.falsum
  correct := by
    constructor
    · exact EqualityHornFormula.isShared_falsum Sig 0
    · intro interpretation satisfiesA
      exfalso
      have hnotu := satisfiesA u.negate (by
        simp [lemma2, ColoredClause.falsifyingPart, Clause.negate])
      have ht := satisfiesA t (by
        simp [lemma2, ColoredClause.falsifyingPart, Clause.negate])
      exact (Literal.satisfies_negate_iff_not interpretation u).mp hnotu
        (eval_F_congr interpretation ht)
    · rintro ⟨interpretation, satisfiesFalse, _⟩
      exact EqualityHornFormula.not_satisfies_falsum interpretation
        satisfiesFalse

def annotation3 : TheoryLemmaAnnotation Sig where
  lemma := lemma3
  side := 0
  interpolant := notPHorn
  correct := by
    constructor
    · exact notPHorn_shared
    · intro interpretation satisfiesA
      apply (satisfies_notPHorn_iff interpretation).mpr
      intro hp
      have hnotu := satisfiesA u.negate (by
        simp [lemma3, ColoredClause.falsifyingPart, Clause.negate])
      have hs := satisfiesA s (by
        simp [lemma3, ColoredClause.falsifyingPart, Clause.negate])
      apply (Literal.satisfies_negate_iff_not interpretation u).mp hnotu
      exact (eval_F_congr interpretation hs).trans hp
    · rintro ⟨interpretation, satisfiesInterpolant, satisfiesB⟩
      have hnotp := (satisfies_notPHorn_iff interpretation).mp
        satisfiesInterpolant
      have hq := satisfiesB q (by
        simp [lemma3, ColoredClause.falsifyingPart, Clause.negate])
      have hr := satisfiesB r (by
        simp [lemma3, ColoredClause.falsifyingPart, Clause.negate])
      exact hnotp ((eval_F_congr interpretation hq).trans hr)

private def ownedA (clause : Clause Sig)
    (color : Formula.IsColor Sig 0 clause) : ClausePartition Sig clause :=
  ClausePartition.owned 0 clause color

private def ownedB (clause : Clause Sig)
    (color : Formula.IsColor Sig 1 clause) : ClausePartition Sig clause :=
  ClausePartition.owned 1 clause color

def partitionPR : ClausePartition Sig [p, r.negate] where
  part
    | 0 => [p]
    | 1 => [r.negate]
  part_color := by
    intro side literal member
    have sides : side = 0 ∨ side = 1 := by omega
    rcases sides with rfl | rfl
    · simp at member; subst literal; exact p_color
    · simp at member; subst literal; exact negateColor r_color
  reconstructs := by simp [ColoredClause.toClause]

def partitionP : ClausePartition Sig unitP := ownedA unitP (by
  intro literal member
  simp [unitP] at member
  subst literal
  exact p_color)

def partitionUT : ClausePartition Sig [u, t.negate] := ownedA _ (by
  intro literal member
  simp at member
  rcases member with rfl | rfl
  · exact u_color
  · exact negateColor t_color)

def partitionNotT : ClausePartition Sig unitNotT := ownedA _ (by
  intro literal member
  simp [unitNotT] at member
  subst literal
  exact negateColor t_color)

def partitionST : ClausePartition Sig [s, t] := ownedA _ (by
  intro literal member
  simp at member
  rcases member with rfl | rfl
  · exact s_color
  · exact t_color)

def partitionS : ClausePartition Sig unitS := ownedA _ (by
  intro literal member
  simp [unitS] at member
  subst literal
  exact s_color)

def partitionUSQ : ClausePartition Sig [u, s.negate, q.negate] where
  part
    | 0 => [u, s.negate]
    | 1 => [q.negate]
  part_color := by
    intro side literal member
    have sides : side = 0 ∨ side = 1 := by omega
    rcases sides with rfl | rfl
    · simp at member
      rcases member with rfl | rfl
      · exact u_color
      · exact negateColor s_color
    · simp at member
      subst literal
      exact negateColor q_color
  reconstructs := by simp [ColoredClause.toClause]

def partitionSQ : ClausePartition Sig [s.negate, q.negate] where
  part
    | 0 => [s.negate]
    | 1 => [q.negate]
  part_color := by
    intro side literal member
    have sides : side = 0 ∨ side = 1 := by omega
    rcases sides with rfl | rfl
    · simp at member; subst literal; exact negateColor s_color
    · simp at member; subst literal; exact negateColor q_color
  reconstructs := by simp [ColoredClause.toClause]

def partitionNotQ : ClausePartition Sig [q.negate] := ownedB _ (by
  intro literal member
  simp at member
  subst literal
  exact negateColor q_color)

private def projectionT1Q : PartitionedResolutionStep Sig t1ResolveQ
    (ClausePartition.ofTheoryLemma lemma1)
    (ClausePartition.owned 1 inputQ
      (Z3Proof43.inputs.part_color 1 inputQ
        (by simp [Z3Proof43.inputs, Z3Proof43.inputB, inputQ, q])))
    partitionPR where
  pivotOwner := 1
  pivot_available := (negateColor q_color).2
  owner_left_of_not_pivot := by
    intro interpretation satisfiesResult notPivot
    change Satisfies interpretation [r] at satisfiesResult
    change ¬SatisfiesLiteral interpretation q.negate at notPivot
    change Satisfies interpretation [q, r]
    intro literal member
    simp at member
    rcases member with rfl | rfl
    · exact Classical.byContradiction fun notQ => notPivot
        ((Literal.satisfies_negate_iff_not interpretation q).mpr notQ)
    · exact satisfiesResult r (by simp)
  owner_right_of_pivot := by
    intro interpretation _ pivotSatisfied
    change SatisfiesLiteral interpretation q.negate at pivotSatisfied
    change Satisfies interpretation [q.negate]
    intro literal member
    simp at member
    subst literal
    exact pivotSatisfied
  other_left := by
    intro interpretation satisfiesResult
    change Satisfies interpretation [p.negate] at satisfiesResult ⊢
    intro literal member
    simp at member
    subst literal
    exact satisfiesResult p.negate (by simp)
  other_right := by
    intro interpretation _
    change Satisfies interpretation []
    intro literal member
    exact nomatch member

private def projectionT1R : PartitionedResolutionStep Sig t1ResolveR
    partitionPR
    (ClausePartition.owned 1 inputR
      (Z3Proof43.inputs.part_color 1 inputR
        (by simp [Z3Proof43.inputs, Z3Proof43.inputB, inputR, r])))
    partitionP where
  pivotOwner := 1
  pivot_available := (negateColor r_color).2
  owner_left_of_not_pivot := by
    intro interpretation _ notPivot
    change ¬SatisfiesLiteral interpretation r.negate at notPivot
    change Satisfies interpretation [r]
    intro literal member
    simp at member
    subst literal
    exact Classical.byContradiction fun notR => notPivot
      ((Literal.satisfies_negate_iff_not interpretation r).mpr notR)
  owner_right_of_pivot := by
    intro interpretation _ pivotSatisfied
    change SatisfiesLiteral interpretation r.negate at pivotSatisfied
    change Satisfies interpretation [r.negate]
    intro literal member
    simp at member
    subst literal
    exact pivotSatisfied
  other_left := by
    intro interpretation satisfiesResult
    change Satisfies interpretation [p.negate] at satisfiesResult ⊢
    intro literal member
    simp at member
    subst literal
    exact satisfiesResult p.negate (by simp)
  other_right := by
    intro interpretation _
    change Satisfies interpretation []
    intro literal member
    exact nomatch member

private def projectionT2R : PartitionedResolutionStep Sig t2ResolveR
    (ClausePartition.ofTheoryLemma lemma2)
    (ClausePartition.owned 1 inputR
      (Z3Proof43.inputs.part_color 1 inputR
        (by simp [Z3Proof43.inputs, Z3Proof43.inputB, inputR, r])))
    partitionUT where
  pivotOwner := 1
  pivot_available := (negateColor r_color).2
  owner_left_of_not_pivot := by
    intro interpretation _ notPivot
    change ¬SatisfiesLiteral interpretation r.negate at notPivot
    change Satisfies interpretation [r]
    intro literal member
    simp at member
    subst literal
    exact Classical.byContradiction fun notR => notPivot
      ((Literal.satisfies_negate_iff_not interpretation r).mpr notR)
  owner_right_of_pivot := by
    intro interpretation _ pivotSatisfied
    change SatisfiesLiteral interpretation r.negate at pivotSatisfied
    change Satisfies interpretation [r.negate]
    intro literal member
    simp at member
    subst literal
    exact pivotSatisfied
  other_left := by
    intro interpretation satisfiesResult
    change Satisfies interpretation [u.negate, t] at satisfiesResult ⊢
    exact satisfiesResult
  other_right := by
    intro interpretation _
    change Satisfies interpretation []
    intro literal member
    exact nomatch member

private def projectionT2U : PartitionedResolutionStep Sig t2ResolveU
    partitionUT
    (ClausePartition.owned 0 inputNotU
      (Z3Proof43.inputs.part_color 0 inputNotU
        (by simp [Z3Proof43.inputs, Z3Proof43.inputA, inputNotU, u,
          Literal.negate])))
    partitionNotT where
  pivotOwner := 0
  pivot_available := u_color.2
  owner_left_of_not_pivot := by
    intro interpretation satisfiesResult notPivot
    change Satisfies interpretation [t] at satisfiesResult
    change ¬SatisfiesLiteral interpretation u at notPivot
    change Satisfies interpretation [u.negate, t]
    intro literal member
    simp at member
    rcases member with rfl | rfl
    · exact (Literal.satisfies_negate_iff_not interpretation u).mpr notPivot
    · exact satisfiesResult t (by simp)
  owner_right_of_pivot := by
    intro interpretation _ pivotSatisfied
    change SatisfiesLiteral interpretation u at pivotSatisfied
    change Satisfies interpretation [u]
    intro literal member
    simp at member
    subst literal
    exact pivotSatisfied
  other_left := by
    intro interpretation _
    change Satisfies interpretation []
    intro literal member
    exact nomatch member
  other_right := by
    intro interpretation _
    change Satisfies interpretation []
    intro literal member
    exact nomatch member

private def projectionInputP : PartitionedResolutionStep Sig inputAResolveP
    (ClausePartition.owned 0 inputA
      (Z3Proof43.inputs.part_color 0 inputA
        (by simp [Z3Proof43.inputs, Z3Proof43.inputA, inputA, p, s, t,
          Literal.negate])))
    partitionP partitionST where
  pivotOwner := 0
  pivot_available := (negateColor p_color).2
  owner_left_of_not_pivot := by
    intro interpretation satisfiesResult notPivot
    change Satisfies interpretation [s.negate, t.negate] at satisfiesResult
    change ¬SatisfiesLiteral interpretation p.negate at notPivot
    change Satisfies interpretation [p, s.negate, t.negate]
    intro literal member
    simp at member
    rcases member with rfl | rfl | rfl
    · exact Classical.byContradiction fun notP => notPivot
        ((Literal.satisfies_negate_iff_not interpretation p).mpr notP)
    · exact satisfiesResult s.negate (by simp)
    · exact satisfiesResult t.negate (by simp)
  owner_right_of_pivot := by
    intro interpretation _ pivotSatisfied
    change SatisfiesLiteral interpretation p.negate at pivotSatisfied
    change Satisfies interpretation [p.negate]
    intro literal member
    simp at member
    subst literal
    exact pivotSatisfied
  other_left := by
    intro interpretation _
    change Satisfies interpretation []
    intro literal member
    exact nomatch member
  other_right := by
    intro interpretation _
    change Satisfies interpretation []
    intro literal member
    exact nomatch member

private def projectionInputT : PartitionedResolutionStep Sig inputAResolveT
    partitionST partitionNotT partitionS where
  pivotOwner := 0
  pivot_available := t_color.2
  owner_left_of_not_pivot := by
    intro interpretation satisfiesResult notPivot
    change Satisfies interpretation [s.negate] at satisfiesResult
    change ¬SatisfiesLiteral interpretation t at notPivot
    change Satisfies interpretation [s.negate, t.negate]
    intro literal member
    simp at member
    rcases member with rfl | rfl
    · exact satisfiesResult s.negate (by simp)
    · exact (Literal.satisfies_negate_iff_not interpretation t).mpr notPivot
  owner_right_of_pivot := by
    intro interpretation _ pivotSatisfied
    change SatisfiesLiteral interpretation t at pivotSatisfied
    change Satisfies interpretation [t]
    intro literal member
    simp at member
    subst literal
    exact pivotSatisfied
  other_left := by
    intro interpretation _
    change Satisfies interpretation []
    intro literal member
    exact nomatch member
  other_right := by
    intro interpretation _
    change Satisfies interpretation []
    intro literal member
    exact nomatch member

private def projectionT3R : PartitionedResolutionStep Sig t3ResolveR
    (ClausePartition.ofTheoryLemma lemma3)
    (ClausePartition.owned 1 inputR
      (Z3Proof43.inputs.part_color 1 inputR
        (by simp [Z3Proof43.inputs, Z3Proof43.inputB, inputR, r])))
    partitionUSQ where
  pivotOwner := 1
  pivot_available := (negateColor r_color).2
  owner_left_of_not_pivot := by
    intro interpretation satisfiesResult notPivot
    change Satisfies interpretation [q] at satisfiesResult
    change ¬SatisfiesLiteral interpretation r.negate at notPivot
    change Satisfies interpretation [q, r]
    intro literal member
    simp at member
    rcases member with rfl | rfl
    · exact satisfiesResult q (by simp)
    · exact Classical.byContradiction fun notR => notPivot
        ((Literal.satisfies_negate_iff_not interpretation r).mpr notR)
  owner_right_of_pivot := by
    intro interpretation _ pivotSatisfied
    change SatisfiesLiteral interpretation r.negate at pivotSatisfied
    change Satisfies interpretation [r.negate]
    intro literal member
    simp at member
    subst literal
    exact pivotSatisfied
  other_left := by
    intro interpretation satisfiesResult
    change Satisfies interpretation [u.negate, s] at satisfiesResult ⊢
    exact satisfiesResult
  other_right := by
    intro interpretation _
    change Satisfies interpretation []
    intro literal member
    exact nomatch member

private def projectionT3U : PartitionedResolutionStep Sig t3ResolveU
    partitionUSQ
    (ClausePartition.owned 0 inputNotU
      (Z3Proof43.inputs.part_color 0 inputNotU
        (by simp [Z3Proof43.inputs, Z3Proof43.inputA, inputNotU, u,
          Literal.negate])))
    partitionSQ where
  pivotOwner := 0
  pivot_available := u_color.2
  owner_left_of_not_pivot := by
    intro interpretation satisfiesResult notPivot
    change Satisfies interpretation [s] at satisfiesResult
    change ¬SatisfiesLiteral interpretation u at notPivot
    change Satisfies interpretation [u.negate, s]
    intro literal member
    simp at member
    rcases member with rfl | rfl
    · exact (Literal.satisfies_negate_iff_not interpretation u).mpr notPivot
    · exact satisfiesResult s (by simp)
  owner_right_of_pivot := by
    intro interpretation _ pivotSatisfied
    change SatisfiesLiteral interpretation u at pivotSatisfied
    change Satisfies interpretation [u]
    intro literal member
    simp at member
    subst literal
    exact pivotSatisfied
  other_left := by
    intro interpretation satisfiesResult
    change Satisfies interpretation [q] at satisfiesResult ⊢
    exact satisfiesResult
  other_right := by
    intro interpretation _
    change Satisfies interpretation []
    intro literal member
    exact nomatch member

private def projectionT3S : PartitionedResolutionStep Sig t3ResolveS
    partitionSQ partitionS partitionNotQ where
  pivotOwner := 0
  pivot_available := (negateColor s_color).2
  owner_left_of_not_pivot := by
    intro interpretation _ notPivot
    change ¬SatisfiesLiteral interpretation s.negate at notPivot
    change Satisfies interpretation [s]
    intro literal member
    simp at member
    subst literal
    exact Classical.byContradiction fun notS => notPivot
      ((Literal.satisfies_negate_iff_not interpretation s).mpr notS)
  owner_right_of_pivot := by
    intro interpretation _ pivotSatisfied
    change SatisfiesLiteral interpretation s.negate at pivotSatisfied
    change Satisfies interpretation [s.negate]
    intro literal member
    simp at member
    subst literal
    exact pivotSatisfied
  other_left := by
    intro interpretation satisfiesResult
    change Satisfies interpretation [q] at satisfiesResult ⊢
    exact satisfiesResult
  other_right := by
    intro interpretation _
    change Satisfies interpretation []
    intro literal member
    exact nomatch member

private def projectionT3Q : PartitionedResolutionStep Sig t3ResolveQ
    partitionNotQ
    (ClausePartition.owned 1 inputQ
      (Z3Proof43.inputs.part_color 1 inputQ
        (by simp [Z3Proof43.inputs, Z3Proof43.inputB, inputQ, q])))
    (ClausePartition.empty Sig) where
  pivotOwner := 1
  pivot_available := (negateColor q_color).2
  owner_left_of_not_pivot := by
    intro interpretation _ notPivot
    change ¬SatisfiesLiteral interpretation q.negate at notPivot
    change Satisfies interpretation [q]
    intro literal member
    simp at member
    subst literal
    exact Classical.byContradiction fun notQ => notPivot
      ((Literal.satisfies_negate_iff_not interpretation q).mpr notQ)
  owner_right_of_pivot := by
    intro interpretation _ pivotSatisfied
    change SatisfiesLiteral interpretation q.negate at pivotSatisfied
    change Satisfies interpretation [q.negate]
    intro literal member
    simp at member
    subst literal
    exact pivotSatisfied
  other_left := by
    intro interpretation _
    change Satisfies interpretation []
    intro literal member
    exact nomatch member
  other_right := by
    intro interpretation _
    change Satisfies interpretation []
    intro literal member
    exact nomatch member

private def annotationQ : ClauseAnnotation Z3Proof43.inputs 0 inputQ :=
  ClauseAnnotation.inputOnOtherSide (owner := 1) (side := 0)
    (by simp [Z3Proof43.inputs, Z3Proof43.inputB, inputQ, q])
    (by simp)

private def annotationR : ClauseAnnotation Z3Proof43.inputs 0 inputR :=
  ClauseAnnotation.inputOnOtherSide (owner := 1) (side := 0)
    (by simp [Z3Proof43.inputs, Z3Proof43.inputB, inputR, r])
    (by simp)

private def annotationInputA : ClauseAnnotation Z3Proof43.inputs 0 inputA :=
  ClauseAnnotation.inputOnSide
    (by simp [Z3Proof43.inputs, Z3Proof43.inputA, inputA, p, s, t,
      Literal.negate]) rfl

private def annotationNotU : ClauseAnnotation Z3Proof43.inputs 0 inputNotU :=
  ClauseAnnotation.inputOnSide
    (by simp [Z3Proof43.inputs, Z3Proof43.inputA, inputNotU, u,
      Literal.negate]) rfl

private def annotationT1 : ClauseAnnotation Z3Proof43.inputs 0 theory1 :=
  by
    change ClauseAnnotation Z3Proof43.inputs 0 lemma1.toClause
    exact ClauseAnnotation.theory annotation1 rfl

noncomputable def annotationPR :
    ClauseAnnotation Z3Proof43.inputs 0 [p, r.negate] := by
  let projection : PartitionedResolutionStep Sig t1ResolveQ
      annotationT1.partition annotationQ.partition partitionPR := by
    simpa [annotationT1, annotationQ, annotation1,
      ClauseAnnotation.theory, ClauseAnnotation.inputOnOtherSide]
      using projectionT1Q
  exact ClauseAnnotation.resolve annotationT1 annotationQ partitionPR projection
    (.onOtherSide (by
      have owner := q_neg_owner projection.pivot_available
      simpa using owner))

noncomputable def annotationP : ClauseAnnotation Z3Proof43.inputs 0 unitP := by
  let projection : PartitionedResolutionStep Sig t1ResolveR
      annotationPR.partition annotationR.partition partitionP := by
    simpa [annotationPR, annotationR, ClauseAnnotation.resolve,
      ClauseAnnotation.inputOnOtherSide] using projectionT1R
  exact ClauseAnnotation.resolve annotationPR annotationR partitionP projection
    (.onOtherSide (by
      have owner := r_neg_owner projection.pivot_available
      simpa using owner))

private def annotationT2 : ClauseAnnotation Z3Proof43.inputs 0 theory2 := by
  change ClauseAnnotation Z3Proof43.inputs 0 lemma2.toClause
  exact ClauseAnnotation.theory annotation2 rfl

noncomputable def annotationUT :
    ClauseAnnotation Z3Proof43.inputs 0 [u, t.negate] := by
  let projection : PartitionedResolutionStep Sig t2ResolveR
      annotationT2.partition annotationR.partition partitionUT := by
    simpa [annotationT2, annotationR, annotation2,
      ClauseAnnotation.theory, ClauseAnnotation.inputOnOtherSide]
      using projectionT2R
  exact ClauseAnnotation.resolve annotationT2 annotationR partitionUT projection
    (.onOtherSide (by
      have owner := r_neg_owner projection.pivot_available
      simpa using owner))

noncomputable def annotationNotT :
    ClauseAnnotation Z3Proof43.inputs 0 unitNotT := by
  let projection : PartitionedResolutionStep Sig t2ResolveU
      annotationUT.partition annotationNotU.partition partitionNotT := by
    change PartitionedResolutionStep Sig t2ResolveU partitionUT
      annotationNotU.partition partitionNotT
    simpa [annotationNotU, ClauseAnnotation.inputOnSide]
      using projectionT2U
  exact ClauseAnnotation.resolve annotationUT annotationNotU partitionNotT
    projection (.onSide (by
      change projection.pivotOwner = (0 : Fin 2)
      dsimp [projection]
      rfl))

noncomputable def annotationST :
    ClauseAnnotation Z3Proof43.inputs 0 [s, t] := by
  let projection : PartitionedResolutionStep Sig inputAResolveP
      annotationInputA.partition annotationP.partition partitionST := by
    change PartitionedResolutionStep Sig inputAResolveP
      annotationInputA.partition partitionP partitionST
    simpa [annotationInputA, ClauseAnnotation.inputOnSide]
      using projectionInputP
  exact ClauseAnnotation.resolve annotationInputA annotationP partitionST projection
    (.onSide (by
      change projection.pivotOwner = (0 : Fin 2)
      dsimp [projection]
      rfl))

noncomputable def annotationS : ClauseAnnotation Z3Proof43.inputs 0 unitS := by
  let projection : PartitionedResolutionStep Sig inputAResolveT
      annotationST.partition annotationNotT.partition partitionS := by
    change PartitionedResolutionStep Sig inputAResolveT partitionST
      partitionNotT partitionS
    exact projectionInputT
  exact ClauseAnnotation.resolve annotationST annotationNotT partitionS projection
    (.onSide (by
      change projection.pivotOwner = (0 : Fin 2)
      dsimp [projection]
      rfl))

private def annotationT3 : ClauseAnnotation Z3Proof43.inputs 0 theory3 := by
  change ClauseAnnotation Z3Proof43.inputs 0 lemma3.toClause
  exact ClauseAnnotation.theory annotation3 rfl

@[simp] private theorem annotationQ_interpolant :
    annotationQ.interpolant = [] := by rfl

@[simp] private theorem annotationR_interpolant :
    annotationR.interpolant = [] := by rfl

@[simp] private theorem annotationInputA_interpolant :
    annotationInputA.interpolant = CNF.falsum := by rfl

@[simp] private theorem annotationNotU_interpolant :
    annotationNotU.interpolant = CNF.falsum := by rfl

@[simp] private theorem annotationT1_interpolant :
    annotationT1.interpolant = [[p.negate]] := by rfl

@[simp] private theorem annotationT2_interpolant :
    annotationT2.interpolant = CNF.falsum := by rfl

@[simp] private theorem annotationT3_interpolant :
    annotationT3.interpolant = [[p.negate]] := by rfl

noncomputable def annotationUSQ :
    ClauseAnnotation Z3Proof43.inputs 0 [u, s.negate, q.negate] := by
  let projection : PartitionedResolutionStep Sig t3ResolveR
      annotationT3.partition annotationR.partition partitionUSQ := by
    simpa [annotationT3, annotationR, annotation3,
      ClauseAnnotation.theory, ClauseAnnotation.inputOnOtherSide]
      using projectionT3R
  exact ClauseAnnotation.resolve annotationT3 annotationR partitionUSQ projection
    (.onOtherSide (by
      have owner := r_neg_owner projection.pivot_available
      simpa using owner))

noncomputable def annotationSQ :
    ClauseAnnotation Z3Proof43.inputs 0 [s.negate, q.negate] := by
  let projection : PartitionedResolutionStep Sig t3ResolveU
      annotationUSQ.partition annotationNotU.partition partitionSQ := by
    change PartitionedResolutionStep Sig t3ResolveU partitionUSQ
      annotationNotU.partition partitionSQ
    simpa [annotationNotU, ClauseAnnotation.inputOnSide]
      using projectionT3U
  exact ClauseAnnotation.resolve annotationUSQ annotationNotU partitionSQ projection
    (.onSide (by
      change projection.pivotOwner = (0 : Fin 2)
      dsimp [projection]
      rfl))

noncomputable def annotationNotQ :
    ClauseAnnotation Z3Proof43.inputs 0 [q.negate] := by
  let projection : PartitionedResolutionStep Sig t3ResolveS
      annotationSQ.partition annotationS.partition partitionNotQ := by
    change PartitionedResolutionStep Sig t3ResolveS partitionSQ partitionS
      partitionNotQ
    exact projectionT3S
  exact ClauseAnnotation.resolve annotationSQ annotationS partitionNotQ projection
    (.onSide (by
      change projection.pivotOwner = (0 : Fin 2)
      dsimp [projection]
      rfl))

noncomputable def annotationEmpty :
    ClauseAnnotation Z3Proof43.inputs 0 [] := by
  let projection : PartitionedResolutionStep Sig t3ResolveQ
      annotationNotQ.partition annotationQ.partition (ClausePartition.empty Sig) := by
    change PartitionedResolutionStep Sig t3ResolveQ partitionNotQ
      annotationQ.partition (ClausePartition.empty Sig)
    simpa [annotationQ, ClauseAnnotation.inputOnOtherSide]
      using projectionT3Q
  exact ClauseAnnotation.resolve annotationNotQ annotationQ
    (ClausePartition.empty Sig) projection
    (.onOtherSide (by
      have owner := q_neg_owner projection.pivot_available
      simpa using owner))

theorem trace_interpolant_sound :
    IsClausalInterpolantAt Z3Proof43.inputs 0 annotationEmpty.interpolant :=
  annotationEmpty.correct.atAnyContradictionPartition
    refutation.inputs_unsatisfiable

theorem calculated_interpolant :
    annotationEmpty.interpolant = [[p.negate]] := by
  classical
  simp [annotationEmpty, annotationNotQ, annotationSQ, annotationUSQ,
    annotationS, annotationST, annotationNotT, annotationUT, annotationP,
    annotationPR, ClauseAnnotation.resolve, ClauseAnnotation.resolveAt,
    CNF.disjoin, CNF.falsum]

theorem calculated_interpolant_matches_z3
    (interpretation : Interpretation Sig) :
    annotationEmpty.interpolant.Satisfied interpretation ↔
      Z3Proof43.interpolant.Satisfied interpretation := by
  rw [calculated_interpolant]
  simp [Z3Proof43.interpolant, CNF.Satisfied, Clause.Satisfied, p,
    Literal.negate, SatisfiesLiteral]


end EUF.Z3Proof43Trace
