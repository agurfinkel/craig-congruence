import EufItpLean.ClausalInterpolation

namespace EUF

/-- A clausal formula is a conjunction of disjunctive clauses. -/
abbrev CNF (signature : Signature) := List (Clause signature)

namespace Clause

@[simp]
theorem not_satisfied_nil (interpretation : Interpretation signature) :
    ¬Satisfied interpretation ([] : Clause signature) := by
  simp [Satisfied]

@[simp]
theorem satisfied_cons_iff (interpretation : Interpretation signature)
    (literal : Literal signature) (clause : Clause signature) :
    Satisfied interpretation (literal :: clause) ↔
      SatisfiesLiteral interpretation literal ∨
        Satisfied interpretation clause := by
  simp [Satisfied]

@[simp]
theorem satisfied_append_iff (interpretation : Interpretation signature)
    (left right : Clause signature) :
    Satisfied interpretation (left ++ right) ↔
      Satisfied interpretation left ∨ Satisfied interpretation right := by
  constructor
  · rintro ⟨literal, member, satisfies⟩
    rcases List.mem_append.mp member with member | member
    · exact Or.inl ⟨literal, member, satisfies⟩
    · exact Or.inr ⟨literal, member, satisfies⟩
  · rintro (⟨literal, member, satisfies⟩ | ⟨literal, member, satisfies⟩)
    · exact ⟨literal, List.mem_append.mpr (Or.inl member), satisfies⟩
    · exact ⟨literal, List.mem_append.mpr (Or.inr member), satisfies⟩

/-- `stronger` subsumes `weaker`: every literal of the stronger clause also
occurs in the weaker one. This permits an explicit resolution chain to finish
with a subclause of the learned clause, as in LRAT/RUP witnesses. -/
def Subsumes (stronger weaker : Clause signature) : Prop :=
  ∀ literal ∈ stronger, literal ∈ weaker

theorem satisfied_of_subsumes (subsumes : Subsumes stronger weaker)
    (satisfies : stronger.Satisfied interpretation) :
    weaker.Satisfied interpretation := by
  obtain ⟨literal, member, satisfiesLiteral⟩ := satisfies
  exact ⟨literal, subsumes literal member, satisfiesLiteral⟩

/-- A clause cannot be satisfied together with the conjunction negating all
of its literals. -/
theorem contradicts_falsifying_formula
    {signature : Signature} {clause : Clause signature}
    {interpretation : Interpretation signature}
    (satisfiesClause : clause.Satisfied interpretation)
    (satisfiesFalsification :
      Satisfies interpretation (clause.map Literal.negate)) : False := by
  obtain ⟨literal, member, satisfiesLiteral⟩ := satisfiesClause
  have satisfiesNegation := satisfiesFalsification literal.negate
    (List.mem_map.mpr ⟨literal, member, rfl⟩)
  exact (Literal.satisfies_negate_iff_not interpretation literal).mp
    satisfiesNegation satisfiesLiteral

/-- A selected occurrence of `literal` in a clause. Using an explicit prefix
and suffix avoids imposing decidable equality on function symbols or terms. -/
structure Occurrence (literal : Literal signature)
    (clause : Clause signature) where
  before : Clause signature
  after : Clause signature
  clause_eq : clause = before ++ literal :: after

namespace Occurrence

/-- Remove exactly the selected literal occurrence. -/
def without {signature : Signature}
    {literal : Literal signature} {clause : Clause signature}
    (occurrence : Occurrence literal clause) : Clause signature :=
  occurrence.before ++ occurrence.after

end Occurrence

end Clause

/-- An exact binary resolution step. The selected occurrence of `pivot` is
removed from the left parent, the selected occurrence of its complement is
removed from the right parent, and the remaining literals are concatenated.

Duplicate-literal normalization is handled by subsumption at the end of a
chain. -/
structure ResolutionStep (left right resolvent : Clause signature) where
  pivot : Literal signature
  leftOccurrence : Clause.Occurrence pivot left
  rightOccurrence : Clause.Occurrence pivot.negate right
  resolvent_eq :
    resolvent = leftOccurrence.without ++ rightOccurrence.without

namespace ResolutionStep

/-- Binary resolution preserves clause satisfaction. -/
theorem sound {signature : Signature}
    {left right resolvent : Clause signature}
    (step : ResolutionStep left right resolvent)
    (interpretation : Interpretation signature)
    (satisfiesLeft : left.Satisfied interpretation)
    (satisfiesRight : right.Satisfied interpretation) :
    resolvent.Satisfied interpretation := by
  rw [step.leftOccurrence.clause_eq,
    Clause.satisfied_append_iff,
    Clause.satisfied_cons_iff] at satisfiesLeft
  rw [step.rightOccurrence.clause_eq,
    Clause.satisfied_append_iff,
    Clause.satisfied_cons_iff] at satisfiesRight
  rw [step.resolvent_eq, Clause.satisfied_append_iff]
  classical
  by_cases satisfiesPivot : SatisfiesLiteral interpretation step.pivot
  · right
    rw [Clause.Occurrence.without, Clause.satisfied_append_iff]
    rcases satisfiesRight with rightPrefix | complementOrSuffix
    · exact Or.inl rightPrefix
    · rcases complementOrSuffix with satisfiesComplement | rightSuffix
      · exact False.elim
          ((Literal.satisfies_negate_iff_not interpretation step.pivot).mp
            satisfiesComplement satisfiesPivot)
      · exact Or.inr rightSuffix
  · left
    rw [Clause.Occurrence.without, Clause.satisfied_append_iff]
    rcases satisfiesLeft with leftPrefix | pivotOrSuffix
    · exact Or.inl leftPrefix
    · rcases pivotOrSuffix with satisfiesPivot' | leftSuffix
      · exact False.elim (satisfiesPivot satisfiesPivot')
      · exact Or.inr leftSuffix

end ResolutionStep

namespace CNF

def Satisfied (interpretation : Interpretation signature)
    (cnf : CNF signature) : Prop :=
  ∀ clause ∈ cnf, clause.Satisfied interpretation

def Satisfiable (cnf : CNF signature) : Prop :=
  ∃ interpretation : Interpretation signature, cnf.Satisfied interpretation

def Unsatisfiable (cnf : CNF signature) : Prop :=
  ¬cnf.Satisfiable

/-- The false CNF, consisting of the empty clause. -/
def falsum : CNF signature := [[]]

@[simp]
theorem not_satisfied_falsum (interpretation : Interpretation signature) :
    ¬Satisfied interpretation (falsum : CNF signature) := by
  intro satisfies
  exact Clause.not_satisfied_nil interpretation
    (satisfies [] (by simp [falsum]))

@[simp]
theorem satisfied_nil (interpretation : Interpretation signature) :
    Satisfied interpretation ([] : CNF signature) := by
  intro clause member
  exact nomatch member

@[simp]
theorem satisfied_append_iff (interpretation : Interpretation signature)
    (left right : CNF signature) :
    Satisfied interpretation (left ++ right) ↔
      Satisfied interpretation left ∧ Satisfied interpretation right := by
  constructor
  · intro satisfies
    exact ⟨fun clause member => satisfies clause (List.mem_append.mpr (Or.inl member)),
      fun clause member => satisfies clause (List.mem_append.mpr (Or.inr member))⟩
  · rintro ⟨satisfiesLeft, satisfiesRight⟩ clause member
    rcases List.mem_append.mp member with member | member
    · exact satisfiesLeft clause member
    · exact satisfiesRight clause member

/-- CNF representation of disjunction, obtained by distributing every clause
of the left CNF over every clause of the right CNF. -/
def disjoin (left right : CNF signature) : CNF signature :=
  left.flatMap fun leftClause =>
    right.map fun rightClause => leftClause ++ rightClause

@[simp]
theorem satisfied_disjoin_iff (interpretation : Interpretation signature)
    (left right : CNF signature) :
    Satisfied interpretation (disjoin left right) ↔
      Satisfied interpretation left ∨ Satisfied interpretation right := by
  classical
  constructor
  · intro satisfiesDisjunction
    by_cases satisfiesLeft : Satisfied interpretation left
    · exact Or.inl satisfiesLeft
    · right
      have counterexample :
          ∃ clause, clause ∈ left ∧ ¬clause.Satisfied interpretation := by
        exact Classical.byContradiction fun noCounterexample =>
          satisfiesLeft fun clause member =>
            Classical.byContradiction fun notSatisfied =>
              noCounterexample ⟨clause, member, notSatisfied⟩
      obtain ⟨leftClause, leftMember, leftUnsatisfied⟩ := counterexample
      intro rightClause rightMember
      have combined := satisfiesDisjunction (leftClause ++ rightClause) (by
        simp only [disjoin, List.mem_flatMap, List.mem_map]
        exact ⟨leftClause, leftMember,
          ⟨rightClause, rightMember, rfl⟩⟩)
      rcases (Clause.satisfied_append_iff interpretation _ _).mp combined with
        satisfiesLeftClause | satisfiesRightClause
      · exact False.elim (leftUnsatisfied satisfiesLeftClause)
      · exact satisfiesRightClause
  · rintro (satisfiesLeft | satisfiesRight) clause member
    · simp only [disjoin, List.mem_flatMap, List.mem_map] at member
      obtain ⟨leftClause, leftMember, rightClause, rightMember, rfl⟩ := member
      exact (Clause.satisfied_append_iff interpretation _ _).mpr
        (Or.inl (satisfiesLeft leftClause leftMember))
    · simp only [disjoin, List.mem_flatMap, List.mem_map] at member
      obtain ⟨leftClause, leftMember, rightClause, rightMember, rfl⟩ := member
      exact (Clause.satisfied_append_iff interpretation _ _).mpr
        (Or.inr (satisfiesRight rightClause rightMember))

end CNF

/-- A left-to-right resolution chain over an already available clause
database. The anchor and every subsequent parent are earlier clauses; each
binary resolvent is recorded explicitly, so checking requires no unit
propagation. -/
inductive ResolutionChain (available : CNF signature)
    (anchor : Clause signature) : Clause signature → Type where
  | start : ResolutionChain available anchor anchor
  | resolve
      (previous : ResolutionChain available anchor current)
      (parent : Fin available.length)
      (step : ResolutionStep current (available.get parent) next) :
      ResolutionChain available anchor next

namespace ResolutionChain

theorem sound {signature : Signature}
    {available : CNF signature} {anchor result : Clause signature}
    (chain : ResolutionChain available anchor result)
    (interpretation : Interpretation signature)
    (satisfiesAvailable : available.Satisfied interpretation)
    (satisfiesAnchor : anchor.Satisfied interpretation) :
    result.Satisfied interpretation := by
  induction chain with
  | start => exact satisfiesAnchor
  | resolve previous parent step previousSound =>
      exact step.sound interpretation previousSound
        (satisfiesAvailable _ (List.get_mem available parent))

end ResolutionChain

/-- The LRAT-like annotation on a derived clause: an earlier anchor followed
by an explicit ordered resolution chain using earlier clauses. -/
structure ChainJustification (available : CNF signature)
    (derived : Clause signature) where
  anchor : Fin available.length
  resolvent : Clause signature
  chain : ResolutionChain available (available.get anchor) resolvent
  subsumes : Clause.Subsumes resolvent derived

namespace ChainJustification

theorem sound {signature : Signature}
    {available : CNF signature} {derived : Clause signature}
    (justification : ChainJustification available derived)
    (interpretation : Interpretation signature)
    (satisfiesAvailable : available.Satisfied interpretation) :
    derived.Satisfied interpretation := by
  apply Clause.satisfied_of_subsumes justification.subsumes
  exact justification.chain.sound interpretation satisfiesAvailable
    (satisfiesAvailable _ (List.get_mem available justification.anchor))

end ChainJustification

/-- An ordered clausal trace. Every non-leaf clause carries an explicit chain
justification over the preceding database. There is no active-clause state,
BCP reconstruction, or deletion operation. -/
inductive ClauseTrace
    (Leaf : Clause signature → Type) : CNF signature → Type 1 where
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
structure ClauseRefutation (Leaf : Clause signature → Type) where
  clauses : CNF signature
  trace : ClauseTrace Leaf clauses
  contradiction : ([] : Clause signature) ∈ clauses

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
