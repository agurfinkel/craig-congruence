import EufItpLean.HornToCNF

namespace EUF

/-- A two-part clausal EUF input. Every clause in a part contains only local
symbols of that part and symbols shared across boundary `0`. -/
structure ColoredCNF (colored : ColoredSignature 2) where
  part : Fin 2 → CNF colored.toSignature
  part_color : ∀ side clause, clause ∈ part side →
    Formula.IsColor colored side clause

namespace ColoredCNF

def Satisfied (inputs : ColoredCNF colored)
    (interpretation : Interpretation colored.toSignature) : Prop :=
  ∀ side, (inputs.part side).Satisfied interpretation

def Satisfiable (inputs : ColoredCNF colored) : Prop :=
  ∃ interpretation : Interpretation colored.toSignature,
    inputs.Satisfied interpretation

def Unsatisfiable (inputs : ColoredCNF colored) : Prop :=
  ¬inputs.Satisfiable

end ColoredCNF

/-- A theory lemma together with one chosen color orientation and its shared
partial interpolant. The same semantic definition covers the conventional
A- and B-oriented annotations. -/
structure TheoryLemmaAnnotation (colored : ColoredSignature 2) where
  lemma : TheoryLemma colored
  side : Fin 2
  interpolant : EqualityHornFormula colored.toSignature
  correct : lemma.IsInterpolantAt side interpolant

/-- Leaves admitted by a colored clausal proof. Input clauses retain their
partition index. A theory leaf retains its color-indexed EUF summary rather
than merely a proof of semantic validity. -/
inductive ColoredProofLeaf (inputs : ColoredCNF colored) :
    Clause colored.toSignature → Type where
  | input (side : Fin 2) (member : clause ∈ inputs.part side) :
      ColoredProofLeaf inputs clause
  | theory (annotation : TheoryLemmaAnnotation colored) :
      ColoredProofLeaf inputs annotation.lemma.toColoredClause.literals

namespace ColoredProofLeaf

theorem sound {colored : ColoredSignature 2}
    {inputs : ColoredCNF colored}
    {clause : Clause colored.toSignature}
    (leaf : ColoredProofLeaf inputs clause)
    (interpretation : Interpretation colored.toSignature)
    (satisfiesInputs : inputs.Satisfied interpretation) :
    clause.Satisfied interpretation := by
  cases leaf with
  | input side member => exact satisfiesInputs side _ member
  | theory annotation => exact annotation.lemma.valid interpretation

end ColoredProofLeaf

/-- An LRAT-like refutation whose leaves preserve all information needed for
interpolation. -/
abbrev ColoredClauseRefutation (inputs : ColoredCNF colored) :=
  ClauseRefutation (ColoredProofLeaf inputs)

namespace ColoredClauseRefutation

theorem inputs_unsatisfiable
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    (refutation : ColoredClauseRefutation inputs) :
    inputs.Unsatisfiable := by
  rintro ⟨interpretation, satisfiesInputs⟩
  have satisfiesTrace := refutation.trace.sound interpretation (by
    intro clause leaf
    exact leaf.sound interpretation satisfiesInputs)
  exact Clause.not_satisfied_nil interpretation
    (satisfiesTrace [] refutation.contradiction)

end ColoredClauseRefutation

/-- An occurrence-level partition of a derived clause. `reconstructs` permits
the two colored parts to reorder the original literal occurrences. -/
structure ClausePartition (colored : ColoredSignature 2)
    (clause : Clause colored.toSignature)
    extends ColoredClause colored where
  reconstructs : toColoredClause.literals.Perm clause

namespace ClausePartition

private theorem fin_two_eq_zero_or_one (side : Fin 2) :
    side = 0 ∨ side = 1 := by
  refine Fin.cases (Or.inl rfl) ?_ side
  intro predecessor
  have equal : predecessor = 0 := Subsingleton.elim _ _
  subst predecessor
  exact Or.inr rfl

/-- The unique empty-clause partition. -/
def empty (colored : ColoredSignature 2) :
    ClausePartition colored [] where
  part := fun _ => []
  part_color := by
    intro side literal member
    exact nomatch member
  reconstructs := List.Perm.nil

/-- Put every occurrence of an input clause in its owning color. Shared
literals are deliberately owned by the input partition at this leaf. -/
def owned (owner : Fin 2) (clause : Clause colored.toSignature)
    (clauseColor : Formula.IsColor colored owner clause) :
    ClausePartition colored clause where
  part := fun side => if side = owner then clause else []
  part_color := by
    intro side literal member
    by_cases same : side = owner
    · subst side
      exact clauseColor literal (by simpa using member)
    · simp [same] at member
  reconstructs := by
    rcases fin_two_eq_zero_or_one owner with equal | equal
    · subst owner
      simp [ColoredClause.literals]
    · subst owner
      simp [ColoredClause.literals]

@[simp]
theorem falsifyingPart_owned_owner
    (owner : Fin 2) (clause : Clause colored.toSignature)
    (clauseColor : Formula.IsColor colored owner clause) :
    (owned owner clause clauseColor).toColoredClause.falsifyingPart owner =
      clause.map Literal.negate := by
  simp [owned, ColoredClause.falsifyingPart]

/-- The partition already stored by a theory lemma reconstructs its own
underlying clause. -/
def ofTheoryLemma (lemma : TheoryLemma colored) :
    ClausePartition colored lemma.toColoredClause.literals where
  toColoredClause := lemma.toColoredClause
  reconstructs := List.Perm.refl _

end ClausePartition

/-- The occurrence-coloring facts needed to transport falsifying assignments
through one resolution step. On the pivot's owning side, the pivot value
selects which parent is falsified. On the other side, both parent projections
are falsified because the pivot has no occurrence there. -/
structure PartitionedResolutionStep (colored : ColoredSignature 2)
    {left right resolvent : Clause colored.toSignature}
    (step : ResolutionStep left right resolvent)
    (leftPartition : ClausePartition colored left)
    (rightPartition : ClausePartition colored right)
    (resolventPartition : ClausePartition colored resolvent) where
  pivotOwner : Fin 2
  pivot_available : step.pivot.AvailableIn colored pivotOwner
  owner_left_of_not_pivot :
    ∀ interpretation : Interpretation colored.toSignature,
      Satisfies interpretation
        (resolventPartition.toColoredClause.falsifyingPart pivotOwner) →
      ¬SatisfiesLiteral interpretation step.pivot →
      Satisfies interpretation
        (leftPartition.toColoredClause.falsifyingPart pivotOwner)
  owner_right_of_pivot :
    ∀ interpretation : Interpretation colored.toSignature,
      Satisfies interpretation
        (resolventPartition.toColoredClause.falsifyingPart pivotOwner) →
      SatisfiesLiteral interpretation step.pivot →
      Satisfies interpretation
        (rightPartition.toColoredClause.falsifyingPart pivotOwner)
  other_left :
    ∀ interpretation : Interpretation colored.toSignature,
      Satisfies interpretation
        (resolventPartition.toColoredClause.falsifyingPart pivotOwner.rev) →
      Satisfies interpretation
        (leftPartition.toColoredClause.falsifyingPart pivotOwner.rev)
  other_right :
    ∀ interpretation : Interpretation colored.toSignature,
      Satisfies interpretation
        (resolventPartition.toColoredClause.falsifyingPart pivotOwner.rev) →
      Satisfies interpretation
        (rightPartition.toColoredClause.falsifyingPart pivotOwner.rev)

/-- A partial interpolant at an arbitrary proof clause. Falsifying the clause
part owned by `side`, together with that input partition, entails the shared
summary. The summary similarly refutes the other input partition when its
part of the proof clause is falsified.

At the empty clause both falsifying parts are empty, leaving precisely the
Craig interpolation conditions for the two input CNFs. -/
structure IsPartialInterpolantAt (inputs : ColoredCNF colored)
    (clause : Clause colored.toSignature)
    (partition : ClausePartition colored clause)
    (side : Fin 2)
    (interpolant : CNF colored.toSignature) : Prop where
  interpolant_shared :
    CNF.IsShared colored 0 interpolant
  side_entails :
    ∀ interpretation : Interpretation colored.toSignature,
      (inputs.part side).Satisfied interpretation →
      Satisfies interpretation
        (partition.toColoredClause.falsifyingPart side) →
      interpolant.Satisfied interpretation
  interpolant_other_unsatisfiable :
    ¬∃ interpretation : Interpretation colored.toSignature,
      interpolant.Satisfied interpretation ∧
      (inputs.part side.rev).Satisfied interpretation ∧
      Satisfies interpretation
        (partition.toColoredClause.falsifyingPart side.rev)

/-- The final semantic specification for interpolation between two colored
clausal EUF inputs, indexed by the side whose contribution is summarized. -/
structure IsClausalInterpolantAt (inputs : ColoredCNF colored)
    (side : Fin 2)
    (interpolant : CNF colored.toSignature) : Prop where
  inputs_unsatisfiable : inputs.Unsatisfiable
  interpolant_shared :
    CNF.IsShared colored 0 interpolant
  side_entails :
    ∀ interpretation : Interpretation colored.toSignature,
      (inputs.part side).Satisfied interpretation →
      interpolant.Satisfied interpretation
  interpolant_other_unsatisfiable :
    ¬∃ interpretation : Interpretation colored.toSignature,
      interpolant.Satisfied interpretation ∧
      (inputs.part side.rev).Satisfied interpretation

namespace TheoryLemmaAnnotation

/-- A valid theory-lemma annotation is also a valid partial interpolant at
that leaf in any surrounding clausal problem. The surrounding input clauses
are irrelevant to this local argument. -/
def toPartialInterpolant (annotation : TheoryLemmaAnnotation colored)
    (inputs : ColoredCNF colored) :
    IsPartialInterpolantAt inputs
      annotation.lemma.toColoredClause.literals
      (ClausePartition.ofTheoryLemma annotation.lemma)
      annotation.side annotation.interpolant.toCNF where
  interpolant_shared := EqualityHornFormula.toCNF_isShared
    annotation.correct.interpolant_shared
  side_entails := by
    intro interpretation _ satisfiesFalsifyingPart
    exact (EqualityHornFormula.satisfies_toCNF_iff
      interpretation annotation.interpolant).mpr
        (annotation.correct.side_entails interpretation
          satisfiesFalsifyingPart)
  interpolant_other_unsatisfiable := by
    rintro ⟨interpretation, satisfiesInterpolant, _, satisfiesFalsifyingPart⟩
    exact annotation.correct.interpolant_other_unsatisfiable
      ⟨interpretation,
        (EqualityHornFormula.satisfies_toCNF_iff
          interpretation annotation.interpolant).mp satisfiesInterpolant,
        satisfiesFalsifyingPart⟩

end TheoryLemmaAnnotation

namespace IsPartialInterpolantAt

/-- An input clause owned by the summarized side has partial interpolant
`false`: the input clause contradicts its own falsifying assignment. -/
def ofInputOnSide
    {colored : ColoredSignature 2} (inputs : ColoredCNF colored)
    (side : Fin 2) (clause : Clause colored.toSignature)
    (member : clause ∈ inputs.part side) :
    IsPartialInterpolantAt inputs clause
      (ClausePartition.owned side clause
        (inputs.part_color side clause member))
      side CNF.falsum where
  interpolant_shared := CNF.isShared_falsum colored 0
  side_entails := by
    intro interpretation satisfiesInputs satisfiesFalsification
    exact False.elim (Clause.contradicts_falsifying_formula
      (satisfiesInputs clause member)
      (by simpa using satisfiesFalsification))
  interpolant_other_unsatisfiable := by
    rintro ⟨interpretation, satisfiesFalsum, _, _⟩
    exact CNF.not_satisfied_falsum interpretation satisfiesFalsum

/-- An input clause owned by the opposite side has partial interpolant `true`.
The opposite input clause contradicts its own falsifying assignment. -/
def ofInputOnOtherSide
    {colored : ColoredSignature 2} (inputs : ColoredCNF colored)
    (owner : Fin 2) (clause : Clause colored.toSignature)
    (member : clause ∈ inputs.part owner) :
    IsPartialInterpolantAt inputs clause
      (ClausePartition.owned owner clause
        (inputs.part_color owner clause member))
      owner.rev [] where
  interpolant_shared := CNF.isShared_nil colored 0
  side_entails := by
    intro interpretation _ _
    exact CNF.satisfied_nil interpretation
  interpolant_other_unsatisfiable := by
    rintro ⟨interpretation, _, satisfiesInputs, satisfiesFalsification⟩
    have satisfiesOwner : (inputs.part owner).Satisfied interpretation := by
      simpa using satisfiesInputs
    apply Clause.contradicts_falsifying_formula
      (satisfiesOwner clause member)
    simpa using satisfiesFalsification

/-- Resolution on a pivot owned by the summarized side combines partial
interpolants by disjunction. `CNF.disjoin` keeps the result in CNF. -/
def resolveOnSide
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {left right resolvent : Clause colored.toSignature}
    {leftPartition : ClausePartition colored left}
    {rightPartition : ClausePartition colored right}
    {resolventPartition : ClausePartition colored resolvent}
    {step : ResolutionStep left right resolvent}
    (projection : PartitionedResolutionStep colored step leftPartition
      rightPartition resolventPartition)
    (side : Fin 2) (owner : projection.pivotOwner = side)
    {leftInterpolant rightInterpolant : CNF colored.toSignature}
    (leftInvariant : IsPartialInterpolantAt inputs left leftPartition
      side leftInterpolant)
    (rightInvariant : IsPartialInterpolantAt inputs right rightPartition
      side rightInterpolant) :
    IsPartialInterpolantAt inputs resolvent resolventPartition side
      (CNF.disjoin leftInterpolant rightInterpolant) where
  interpolant_shared := CNF.isShared_disjoin
    leftInvariant.interpolant_shared rightInvariant.interpolant_shared
  side_entails := by
    intro interpretation satisfiesInputs satisfiesResolvent
    apply (CNF.satisfied_disjoin_iff interpretation _ _).mpr
    by_cases satisfiesPivot : SatisfiesLiteral interpretation step.pivot
    · right
      apply rightInvariant.side_entails interpretation satisfiesInputs
      simpa [owner] using
        projection.owner_right_of_pivot interpretation
          (by simpa [owner] using satisfiesResolvent) satisfiesPivot
    · left
      apply leftInvariant.side_entails interpretation satisfiesInputs
      simpa [owner] using
        projection.owner_left_of_not_pivot interpretation
          (by simpa [owner] using satisfiesResolvent) satisfiesPivot
  interpolant_other_unsatisfiable := by
    rintro ⟨interpretation, satisfiesInterpolant, satisfiesInputs,
      satisfiesResolvent⟩
    rcases (CNF.satisfied_disjoin_iff interpretation _ _).mp
      satisfiesInterpolant with satisfiesLeft | satisfiesRight
    · apply leftInvariant.interpolant_other_unsatisfiable
      refine ⟨interpretation, satisfiesLeft, satisfiesInputs, ?_⟩
      have := projection.other_left interpretation
      simpa [owner] using this (by simpa [owner] using satisfiesResolvent)
    · apply rightInvariant.interpolant_other_unsatisfiable
      refine ⟨interpretation, satisfiesRight, satisfiesInputs, ?_⟩
      have := projection.other_right interpretation
      simpa [owner] using this (by simpa [owner] using satisfiesResolvent)

/-- Resolution on a pivot owned by the opposite side combines partial
interpolants by conjunction, represented by CNF append. -/
def resolveOnOtherSide
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {left right resolvent : Clause colored.toSignature}
    {leftPartition : ClausePartition colored left}
    {rightPartition : ClausePartition colored right}
    {resolventPartition : ClausePartition colored resolvent}
    {step : ResolutionStep left right resolvent}
    (projection : PartitionedResolutionStep colored step leftPartition
      rightPartition resolventPartition)
    (side : Fin 2) (owner : projection.pivotOwner = side.rev)
    {leftInterpolant rightInterpolant : CNF colored.toSignature}
    (leftInvariant : IsPartialInterpolantAt inputs left leftPartition
      side leftInterpolant)
    (rightInvariant : IsPartialInterpolantAt inputs right rightPartition
      side rightInterpolant) :
    IsPartialInterpolantAt inputs resolvent resolventPartition side
      (leftInterpolant ++ rightInterpolant) where
  interpolant_shared := (CNF.isShared_append colored 0 _ _).mpr
    ⟨leftInvariant.interpolant_shared, rightInvariant.interpolant_shared⟩
  side_entails := by
    intro interpretation satisfiesInputs satisfiesResolvent
    apply (CNF.satisfied_append_iff interpretation _ _).mpr
    constructor
    · apply leftInvariant.side_entails interpretation satisfiesInputs
      have := projection.other_left interpretation
      simpa [owner] using this (by simpa [owner] using satisfiesResolvent)
    · apply rightInvariant.side_entails interpretation satisfiesInputs
      have := projection.other_right interpretation
      simpa [owner] using this (by simpa [owner] using satisfiesResolvent)
  interpolant_other_unsatisfiable := by
    rintro ⟨interpretation, satisfiesInterpolant, satisfiesInputs,
      satisfiesResolvent⟩
    have interpolantParts :=
      (CNF.satisfied_append_iff interpretation _ _).mp satisfiesInterpolant
    by_cases satisfiesPivot : SatisfiesLiteral interpretation step.pivot
    · apply rightInvariant.interpolant_other_unsatisfiable
      refine ⟨interpretation, interpolantParts.2, satisfiesInputs, ?_⟩
      simpa [owner] using
        projection.owner_right_of_pivot interpretation
          (by simpa [owner] using satisfiesResolvent) satisfiesPivot
    · apply leftInvariant.interpolant_other_unsatisfiable
      refine ⟨interpretation, interpolantParts.1, satisfiesInputs, ?_⟩
      simpa [owner] using
        projection.owner_left_of_not_pivot interpretation
          (by simpa [owner] using satisfiesResolvent) satisfiesPivot

/-- At a refutation's empty clause, the partial-interpolant invariant becomes
the final clausal interpolation theorem. -/
def atContradiction
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2}
    {interpolant : CNF colored.toSignature}
    (invariant : IsPartialInterpolantAt inputs []
      (ClausePartition.empty colored) side interpolant)
    (inputsUnsatisfiable : inputs.Unsatisfiable) :
    IsClausalInterpolantAt inputs side interpolant where
  inputs_unsatisfiable := inputsUnsatisfiable
  interpolant_shared := invariant.interpolant_shared
  side_entails := by
    intro interpretation satisfiesSide
    exact invariant.side_entails interpretation satisfiesSide (by
      intro literal member
      exact nomatch member)
  interpolant_other_unsatisfiable := by
    rintro ⟨interpretation, satisfiesInterpolant, satisfiesOther⟩
    exact invariant.interpolant_other_unsatisfiable
      ⟨interpretation, satisfiesInterpolant, satisfiesOther, by
        intro literal member
        exact nomatch member⟩

end IsPartialInterpolantAt

end EUF
