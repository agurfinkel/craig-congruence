-- SPDX-License-Identifier: MIT

import Basic.Horn
import Basic.Clause

/-!
The semantics-preserving translation from equality Horn clauses and formulas
to ordinary EUF clauses and CNFs. Sharedness is shown to be preserved by the
translation.
-/

namespace EUF

namespace Equality

/-- The negative literal corresponding to an equality atom. -/
def negatedLiteral (equality : Equality signature) : Literal signature :=
  .ne equality.left equality.right

@[simp]
theorem satisfies_negatedLiteral_iff_not
    (interpretation : Interpretation signature)
    (equality : Equality signature) :
    SatisfiesLiteral interpretation equality.negatedLiteral ↔
      ¬equality.Satisfied interpretation :=
  Iff.rfl

end Equality

namespace EqualityHornClause

/-- Read an equality Horn implication as an ordinary disjunctive EUF clause. -/
def toClause (horn : EqualityHornClause signature) : Clause signature :=
  Clausal.Clause.ofList (horn.premises.map Equality.negatedLiteral ++
    horn.conclusion.toList.map Equality.literal)

@[simp]
theorem satisfied_toClause_iff
    (interpretation : Interpretation signature)
    (horn : EqualityHornClause signature) :
    horn.toClause.Satisfied interpretation ↔ horn.Satisfied interpretation := by
  classical
  constructor
  · rintro ⟨literal, member, satisfiesLiteral⟩ satisfiesPremises
    rcases List.mem_append.mp member with premiseMember | conclusionMember
    · obtain ⟨equality, equalityMember, rfl⟩ :=
        List.mem_map.mp premiseMember
      exact False.elim
        ((Equality.satisfies_negatedLiteral_iff_not interpretation equality).mp
          satisfiesLiteral (satisfiesPremises equality equalityMember))
    · cases conclusion : horn.conclusion with
      | none => simp [conclusion] at conclusionMember
      | some equality =>
          have literalEqual : literal = equality.literal := by
            simpa [conclusion] using conclusionMember
          subst literal
          simpa [EqualityHornClause.Satisfied, conclusion] using satisfiesLiteral
  · intro satisfiesHorn
    by_cases satisfiesPremises :
        ∀ equality ∈ horn.premises, equality.Satisfied interpretation
    · have satisfiesConclusion := satisfiesHorn satisfiesPremises
      cases conclusion : horn.conclusion with
      | none =>
          simp [conclusion] at satisfiesConclusion
      | some equality =>
          refine ⟨equality.literal, ?_, ?_⟩
          · apply List.mem_append.mpr
            exact Or.inr (by simp [conclusion])
          · simpa [EqualityHornClause.Satisfied, conclusion] using
              satisfiesConclusion
    · have counterexample :
          ∃ equality, equality ∈ horn.premises ∧
            ¬equality.Satisfied interpretation := by
          exact Classical.byContradiction fun noCounterexample =>
            satisfiesPremises fun equality equalityMember =>
              Classical.byContradiction fun notSatisfied =>
                noCounterexample ⟨equality, equalityMember, notSatisfied⟩
      obtain ⟨equality, equalityMember, notSatisfied⟩ := counterexample
      refine ⟨equality.negatedLiteral, ?_, ?_⟩
      · apply List.mem_append.mpr
        exact Or.inl (List.mem_map.mpr ⟨equality, equalityMember, rfl⟩)
      · exact (Equality.satisfies_negatedLiteral_iff_not
          interpretation equality).mpr notSatisfied

end EqualityHornClause

namespace EqualityHornFormula

/-- Embed a conjunction of equality Horn clauses into an ordinary CNF. -/
def toCNF (horn : EqualityHornFormula signature) : CNF signature :=
  horn.map EqualityHornClause.toClause

@[simp]
theorem satisfies_toCNF_iff
    (interpretation : Interpretation signature)
    (horn : EqualityHornFormula signature) :
    (horn.toCNF).Satisfied interpretation ↔
      SatisfiesEqualityHornFormula interpretation horn := by
  simp only [toCNF, CNF.Satisfied, List.mem_map,
    SatisfiesEqualityHornFormula]
  constructor
  · intro satisfies clause member
    exact (EqualityHornClause.satisfied_toClause_iff interpretation clause).mp
      (satisfies clause.toClause ⟨clause, member, rfl⟩)
  · rintro satisfies clause ⟨hornClause, member, rfl⟩
    exact (EqualityHornClause.satisfied_toClause_iff
      interpretation hornClause).mpr (satisfies hornClause member)

end EqualityHornFormula

namespace CNF

def IsShared (sig : ColoredSignature k) (boundary : Fin (k - 1))
  (cnf : CNF sig) : Prop :=
  ∀ clause ∈ cnf, Clause.IsShared sig boundary clause

@[simp]
theorem isShared_nil (sig : ColoredSignature k)
    (boundary : Fin (k - 1)) :
    IsShared sig boundary [] := by
  intro clause member
  exact nomatch member

@[simp]
theorem isShared_falsum (sig : ColoredSignature k)
    (boundary : Fin (k - 1)) :
    IsShared sig boundary (falsum : CNF sig) := by
  intro clause clauseMember literal literalMember
  have clauseEmpty : clause = Clausal.Clause.empty := by
    simpa [falsum] using clauseMember
  subst clause
  simp at literalMember

@[simp]
theorem isShared_append (sig : ColoredSignature k)
    (boundary : Fin (k - 1))
    (left right : CNF sig) :
    IsShared sig boundary (left ++ right) ↔
      IsShared sig boundary left ∧ IsShared sig boundary right := by
  constructor
  · intro shared
    exact ⟨fun clause member => shared clause
        (List.mem_append.mpr (Or.inl member)),
      fun clause member => shared clause
        (List.mem_append.mpr (Or.inr member))⟩
  · rintro ⟨sharedLeft, sharedRight⟩ clause member
    rcases List.mem_append.mp member with member | member
    · exact sharedLeft clause member
    · exact sharedRight clause member

theorem isShared_disjoin (sharedLeft : IsShared sig boundary left)
    (sharedRight : IsShared sig boundary right) :
    IsShared sig boundary (disjoin left right) := by
  intro clause clauseMember literal literalMember
  simp only [disjoin, List.mem_flatMap, List.mem_map] at clauseMember
  obtain ⟨leftClause, leftMember, rightClause, rightMember, rfl⟩ := clauseMember
  have combinedMember := (Clause.mem_unique literal _).mp literalMember
  rcases List.mem_append.mp combinedMember with member | member
  · exact sharedLeft leftClause leftMember literal member
  · exact sharedRight rightClause rightMember literal member

end CNF

namespace EqualityHornFormula

theorem toCNF_isShared
    (shared : EqualityHornFormula.IsShared sig boundary horn) :
    CNF.IsShared sig boundary horn.toCNF := by
  intro clause clauseMember literal literalMember
  obtain ⟨hornClause, hornMember, rfl⟩ := List.mem_map.mp clauseMember
  have hornShared := shared hornClause hornMember
  rcases List.mem_append.mp literalMember with premiseMember | conclusionMember
  · obtain ⟨equality, equalityMember, rfl⟩ :=
      List.mem_map.mp premiseMember
    exact (Literal.hasColor_negate_iff sig equality.literal
      (.shared boundary)).mpr (hornShared.1 equality equalityMember)
  · obtain ⟨equality, equalityMember, rfl⟩ :=
      List.mem_map.mp conclusionMember
    exact hornShared.2 equality (Option.mem_toList.mp equalityMember)

end EqualityHornFormula

end EUF
