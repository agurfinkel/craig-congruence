-- SPDX-License-Identifier: MIT

import Basic.Clause

/-!
A proof-relevant clausal resolution calculus. Its proof objects are generic in
the literal type and require only an involutive negation operation. The EUF
soundness theorems instantiate this generic calculus with EUF literals.
-/

namespace Clausal

/-- A clause is a list representing a disjunction of literals. Resolution
steps below enforce that their produced clauses contain no duplicates. -/
abbrev Clause (Literal : Type) := List Literal

/-- A CNF is a list representing a conjunction of clauses. -/
abbrev CNF (Literal : Type) := List (Clause Literal)

/-- The syntax required by resolution: every literal has an involutive
complement. No decidable equality or solver representation is assumed. -/
class Negation (Literal : Type) where
  negate : Literal → Literal
  negate_negate : ∀ literal, negate (negate literal) = literal

end Clausal

namespace EUF

instance : Clausal.Negation (Literal signature) where
  negate := Literal.negate
  negate_negate := Literal.negate_negate

/-- A normalized binary resolution step. The pivot occurs in the left parent
and its complement occurs in the right parent. The resolvent contains exactly
the non-pivot literals of both parents, without duplicates. The membership
specification avoids requiring decidable equality or imposing a list order. -/
structure ResolutionStep [Clausal.Negation literal]
    (left right resolvent : Clausal.Clause literal) where
  pivot : literal
  pivot_mem_left : pivot ∈ left
  not_pivot_mem_right : Clausal.Negation.negate pivot ∈ right
  mem_resolvent_iff : ∀ candidate,
    candidate ∈ resolvent ↔
      (candidate ≠ pivot ∧ candidate ∈ left) ∨
      (candidate ≠ Clausal.Negation.negate pivot ∧ candidate ∈ right)
  resolvent_nodup : resolvent.Nodup

namespace ResolutionStep

/-- The complement of the resolution pivot. -/
def not_pivot
    {literal : Type} [Clausal.Negation literal]
    {left right resolvent : Clausal.Clause literal}
    (step : ResolutionStep left right resolvent) : literal :=
  Clausal.Negation.negate step.pivot

/-- Binary resolution preserves clause satisfaction. -/
theorem sound {signature : Signature}
    {left right resolvent : Clause signature}
    (step : ResolutionStep left right resolvent)
    (interpretation : Interpretation signature)
    (satisfiesLeft : left.Satisfied interpretation)
    (satisfiesRight : right.Satisfied interpretation) :
    resolvent.Satisfied interpretation := by
  by_cases satisfiesPivot : SatisfiesLiteral interpretation step.pivot
  · obtain ⟨literal, member, satisfiesLiteral⟩ := satisfiesRight
    have notComplement : literal ≠ step.not_pivot := by
      intro equal
      subst literal
      exact (Literal.satisfies_negate_iff_not interpretation step.pivot).mp
        satisfiesLiteral satisfiesPivot
    exact ⟨literal, (step.mem_resolvent_iff literal).mpr
      (Or.inr ⟨notComplement, member⟩), satisfiesLiteral⟩
  · obtain ⟨literal, member, satisfiesLiteral⟩ := satisfiesLeft
    have notPivot : literal ≠ step.pivot := by
      intro equal
      subst literal
      exact satisfiesPivot satisfiesLiteral
    exact ⟨literal, (step.mem_resolvent_iff literal).mpr
      (Or.inl ⟨notPivot, member⟩), satisfiesLiteral⟩

end ResolutionStep

/-- A left-to-right resolution chain over an already available clause
database. The anchor and every subsequent parent are earlier clauses; each
binary resolvent is recorded explicitly, so checking requires no unit
propagation. -/
inductive ResolutionChain [Clausal.Negation literal]
    (available : Clausal.CNF literal)
    (anchor : Clausal.Clause literal) : Clausal.Clause literal → Type where
  | start : ResolutionChain available anchor anchor
  | resolve
      (previous : ResolutionChain available anchor current)
      (parent : Fin available.length)
      (step : ResolutionStep current (available.get parent) next) :
      ResolutionChain available anchor next

namespace ResolutionChain

/-- A predicate holds for every non-anchor parent referenced by a resolution
chain. -/
inductive ParentsSatisfy
    {literal : Type} [Clausal.Negation literal]
    {available : Clausal.CNF literal}
    (predicate : Fin available.length → Prop) :
    {anchor result : Clausal.Clause literal} →
    ResolutionChain available anchor result → Prop where
  | start : ParentsSatisfy predicate .start
  | resolve
      {anchor current next : Clausal.Clause literal}
      {chain : ResolutionChain available anchor current}
      {parent : Fin available.length}
      (previous : ParentsSatisfy predicate chain)
      (step : ResolutionStep current (available.get parent) next)
      (parentSatisfies : predicate parent) :
      ParentsSatisfy predicate (.resolve chain parent step)

/-- Soundness using only the parent indices actually referenced by the
resolution chain. -/
theorem sound_of_parents
    {signature : Signature} {available : CNF signature}
    {predicate : Fin available.length → Prop}
    {anchor result : Clause signature}
    {chain : ResolutionChain available anchor result}
    (parents : ParentsSatisfy predicate chain)
    (interpretation : Interpretation signature)
    (satisfiesAnchor : anchor.Satisfied interpretation)
    (satisfiesParent : ∀ index, predicate index →
      (available.get index).Satisfied interpretation) :
    result.Satisfied interpretation := by
  induction parents with
  | start => exact satisfiesAnchor
  | resolve previous step parentSatisfies previousSound =>
      exact ResolutionStep.sound step interpretation previousSound
        (satisfiesParent _ parentSatisfies)

/-- Every chain records that the constantly true predicate holds of each
referenced parent. -/
theorem parentsSatisfy_true
    {literal : Type} [Clausal.Negation literal]
    {available : Clausal.CNF literal}
    {anchor result : Clausal.Clause literal}
    (chain : ResolutionChain available anchor result) :
    ParentsSatisfy (fun _ => True) chain := by
  induction chain with
  | start => exact .start
  | resolve previous parent step previousParents =>
      exact .resolve previousParents step trivial

/-- Soundness when every available clause is satisfied. -/
theorem sound {signature : Signature}
    {available : CNF signature} {anchor result : Clause signature}
    (chain : ResolutionChain available anchor result)
    (interpretation : Interpretation signature)
    (satisfiesAvailable : available.Satisfied interpretation)
    (satisfiesAnchor : anchor.Satisfied interpretation) :
    result.Satisfied interpretation :=
  sound_of_parents chain.parentsSatisfy_true interpretation satisfiesAnchor
    (fun index _ => satisfiesAvailable _ (List.get_mem available index))

end ResolutionChain

/-- The LRAT-like annotation on a derived clause: an earlier anchor followed
by an explicit ordered resolution chain using earlier clauses. -/
structure ChainJustification [Clausal.Negation literal]
    (available : Clausal.CNF literal)
    (derived : Clausal.Clause literal) where
  anchor : Fin available.length
  chain : ResolutionChain available (available.get anchor) derived

namespace ChainJustification

theorem sound {signature : Signature}
    {available : CNF signature} {derived : Clause signature}
    (justification : ChainJustification available derived)
    (interpretation : Interpretation signature)
    (satisfiesAvailable : available.Satisfied interpretation) :
    derived.Satisfied interpretation :=
  justification.chain.sound interpretation satisfiesAvailable
    (satisfiesAvailable _ (List.get_mem available justification.anchor))

end ChainJustification

/-- An ordered clausal trace. Every non-leaf clause carries an explicit chain
justification over the preceding database. There is no active-clause state,
BCP reconstruction, or deletion operation. -/
inductive ClauseTrace [Clausal.Negation literal]
    (Leaf : Clausal.Clause literal → Type) : Clausal.CNF literal → Type 1 where
  | empty : ClauseTrace Leaf []
  | addLeaf
      (trace : ClauseTrace Leaf available)
      (leaf : Leaf clause) :
      ClauseTrace Leaf (available ++ [clause])
  | addDerived
      (trace : ClauseTrace Leaf available)
      (justification : ChainJustification available clause) :
      ClauseTrace Leaf (available ++ [clause])

namespace ClauseTrace

/-- Forward validation of an explicit trace. -/
theorem sound {signature : Signature}
    {Leaf : Clause signature → Type} {clauses : CNF signature}
    (trace : ClauseTrace Leaf clauses)
    (interpretation : Interpretation signature)
    (leafSound : ∀ clause, Leaf clause → clause.Satisfied interpretation) :
    clauses.Satisfied interpretation := by
  induction trace with
  | empty => exact CNF.satisfied_nil interpretation
  | addLeaf trace leaf traceSound =>
      apply (CNF.satisfied_append_iff interpretation _ _).mpr
      exact ⟨traceSound, fun clause member => by
        rw [List.mem_singleton] at member
        subst clause
        exact leafSound _ leaf⟩
  | addDerived trace justification traceSound =>
      apply (CNF.satisfied_append_iff interpretation _ _).mpr
      exact ⟨traceSound, fun clause member => by
        rw [List.mem_singleton] at member
        subst clause
        exact justification.sound interpretation traceSound⟩

end ClauseTrace

/-- A refutation is an explicit trace containing the empty clause. -/
structure ClauseRefutation [Clausal.Negation literal]
    (Leaf : Clausal.Clause literal → Type) where
  clauses : Clausal.CNF literal
  trace : ClauseTrace Leaf clauses
  contradiction : ([] : Clausal.Clause literal) ∈ clauses

namespace CNF

/-- Leaves consisting of input clauses and semantically valid theory lemmas. -/
inductive InputOrTheory (cnf : CNF signature) : Clause signature → Type where
  | input (member : clause ∈ cnf) : InputOrTheory cnf clause
  | theory (valid : clause.Valid) : InputOrTheory cnf clause

/-- A resolution refutation from input clauses and valid theory lemmas proves
the input CNF unsatisfiable. -/
theorem unsatisfiable_of_refutation
    {signature : Signature} {cnf : CNF signature}
    (refutation : ClauseRefutation (InputOrTheory cnf)) :
    cnf.Unsatisfiable := by
  rintro ⟨interpretation, satisfiesCnf⟩
  have satisfiesTrace := refutation.trace.sound interpretation (by
    intro clause leaf
    cases leaf with
    | input member => exact satisfiesCnf clause member
    | theory valid => exact valid interpretation)
  have satisfiesEmpty := satisfiesTrace [] refutation.contradiction
  exact Clause.not_satisfied_nil interpretation satisfiesEmpty

end CNF

end EUF

namespace Clausal

/-- A generic normalized resolution step. The existing `EUF`-namespaced API
is retained for compatibility with the interpolation development. -/
abbrev ResolutionStep [Negation literal]
    (left right resolvent : Clause literal) :=
  EUF.ResolutionStep left right resolvent

/-- A generic ordered resolution chain. -/
abbrev ResolutionChain [Negation literal]
    (available : CNF literal) (anchor : Clause literal) :=
  EUF.ResolutionChain available anchor

namespace ResolutionChain

/-- A predicate holds for every parent referenced by a generic chain. -/
abbrev ParentsSatisfy
    {literal : Type} [Negation literal] {available : CNF literal}
    (predicate : Fin available.length → Prop)
    {anchor result : Clause literal}
    (chain : ResolutionChain available anchor result) :=
  EUF.ResolutionChain.ParentsSatisfy predicate chain

/-- The constantly true parent predicate holds for every generic chain. -/
theorem parentsSatisfy_true
    {literal : Type} [Negation literal] {available : CNF literal}
    {anchor result : Clause literal}
    (chain : ResolutionChain available anchor result) :
    ParentsSatisfy (fun _ => True) chain :=
  EUF.ResolutionChain.parentsSatisfy_true chain

end ResolutionChain

/-- A generic chain justification for a derived clause. -/
abbrev ChainJustification [Negation literal]
    (available : CNF literal) (derived : Clause literal) :=
  EUF.ChainJustification available derived

/-- A generic ordered clausal proof trace. -/
abbrev ClauseTrace [Negation literal]
    (Leaf : Clause literal → Type) :=
  EUF.ClauseTrace Leaf

/-- A generic clausal refutation ending in the empty clause. -/
abbrev ClauseRefutation [Negation literal]
    (Leaf : Clause literal → Type) :=
  EUF.ClauseRefutation Leaf

end Clausal
