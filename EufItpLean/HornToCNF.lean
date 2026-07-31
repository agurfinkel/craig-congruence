import EufItpLean.ClausalProof

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
  horn.premises.map Equality.negatedLiteral ++
    horn.conclusion.toList.map Equality.literal

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

namespace Clause

def IsShared (colored : ColoredSignature k) (boundary : Fin (k - 1))
    (clause : Clause colored.toSignature) : Prop :=
  ∀ literal ∈ clause, literal.HasColor colored (.shared boundary)

end Clause

namespace CNF

def IsShared (colored : ColoredSignature k) (boundary : Fin (k - 1))
    (cnf : CNF colored.toSignature) : Prop :=
  ∀ clause ∈ cnf, clause.IsShared colored boundary

@[simp]
theorem isShared_nil (colored : ColoredSignature k)
    (boundary : Fin (k - 1)) :
    IsShared colored boundary [] := by
  intro clause member
  exact nomatch member

@[simp]
theorem isShared_falsum (colored : ColoredSignature k)
    (boundary : Fin (k - 1)) :
    IsShared colored boundary (falsum : CNF colored.toSignature) := by
  intro clause clauseMember literal literalMember
  have clauseEmpty : clause = [] := by
    simpa [falsum] using clauseMember
  subst clause
  exact nomatch literalMember

@[simp]
theorem isShared_append (colored : ColoredSignature k)
    (boundary : Fin (k - 1))
    (left right : CNF colored.toSignature) :
    IsShared colored boundary (left ++ right) ↔
      IsShared colored boundary left ∧ IsShared colored boundary right := by
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

theorem isShared_disjoin (sharedLeft : IsShared colored boundary left)
    (sharedRight : IsShared colored boundary right) :
    IsShared colored boundary (disjoin left right) := by
  intro clause clauseMember literal literalMember
  simp only [disjoin, List.mem_flatMap, List.mem_map] at clauseMember
  obtain ⟨leftClause, leftMember, rightClause, rightMember, rfl⟩ := clauseMember
  rcases List.mem_append.mp literalMember with member | member
  · exact sharedLeft leftClause leftMember literal member
  · exact sharedRight rightClause rightMember literal member

end CNF

namespace EqualityHornFormula

theorem toCNF_isShared
    (shared : EqualityHornFormula.IsShared colored boundary horn) :
    CNF.IsShared colored boundary horn.toCNF := by
  intro clause clauseMember literal literalMember
  obtain ⟨hornClause, hornMember, rfl⟩ := List.mem_map.mp clauseMember
  have hornShared := shared hornClause hornMember
  rcases List.mem_append.mp literalMember with premiseMember | conclusionMember
  · obtain ⟨equality, equalityMember, rfl⟩ :=
      List.mem_map.mp premiseMember
    exact (Literal.hasColor_negate_iff colored equality.literal
      (.shared boundary)).mpr (hornShared.1 equality equalityMember)
  · obtain ⟨equality, equalityMember, rfl⟩ :=
      List.mem_map.mp conclusionMember
    exact hornShared.2 equality (Option.mem_toList.mp equalityMember)

end EqualityHornFormula

end EUF
