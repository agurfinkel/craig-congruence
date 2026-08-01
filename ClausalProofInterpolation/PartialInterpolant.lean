-- SPDX-License-Identifier: MIT

import Basic.Colored
import ClausalProofInterpolation.TheoryLemmaInterpolation
import ClausalProofs.ClausalProof
import Basic.HornToCNF

/-!
Local partial-interpolant invariants for colored clausal proofs. This module
defines annotated theory leaves, occurrence-level clause partitions, and the
rules that propagate partial interpolants across partitioned resolution steps
and contradictions.
-/

namespace EUF

/-- A theory lemma together with one chosen color orientation and its shared
partial interpolant. The same semantic definition covers the conventional
A- and B-oriented annotations. -/
structure TheoryLemmaAnnotation (sig : ColoredSignature 2) where
  lemma : TheoryLemma sig
  side : Fin 2
  interpolant : EqualityHornFormula sig
  correct : lemma.IsInterpolantAt side interpolant

/-- Leaves admitted by a colored clausal proof. Input clauses retain their
partition index. A theory leaf retains its color-indexed EUF summary rather
than merely a proof of semantic validity. -/
inductive ColoredProofLeaf (inputs : ColoredCNF sig) :
    Clause sig → Type where
  | input (side : Fin 2) (member : clause ∈ inputs.part side) :
      ColoredProofLeaf inputs clause
  | theory (annotation : TheoryLemmaAnnotation sig) :
      ColoredProofLeaf inputs annotation.lemma

namespace ColoredProofLeaf

/-- Leaf clauses are satisfied by an interpretation that satisfies all input clauses.

    Follows from: theory lemmas are valid
-/
theorem sound {sig : ColoredSignature 2}
    {inputs : ColoredCNF sig}
    {clause : Clause sig}
    (leaf : ColoredProofLeaf inputs clause)
    (interpretation : Interpretation sig)
    (satisfiesInputs : inputs.Satisfied interpretation) :
    clause.Satisfied interpretation := by
  cases leaf with
  | input side member => exact satisfiesInputs side _ member
  | theory annotation => exact annotation.lemma.valid interpretation

end ColoredProofLeaf

/-- An LRAT-like refutation whose leaves preserve all information needed for
interpolation. -/
abbrev ColoredClauseRefutation (inputs : ColoredCNF sig) :=
  ClauseRefutation (ColoredProofLeaf inputs)

namespace ColoredClauseRefutation

/-- existence of colored refutation implies that inputs are unsat -/
theorem inputs_unsatisfiable
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
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
structure ClausePartition (sig : ColoredSignature 2)
    (clause : Clause sig)
    extends ColoredClause sig where
  reconstructs : toColoredClause.toClause.Perm clause

namespace ClausePartition

private theorem fin_two_eq_zero_or_one (side : Fin 2) :
    side = 0 ∨ side = 1 := by
  refine Fin.cases (Or.inl rfl) ?_ side
  intro predecessor
  have equal : predecessor = 0 := Subsingleton.elim _ _
  subst predecessor
  exact Or.inr rfl

/-- The unique empty-clause partition. -/
def empty (sig : ColoredSignature 2) :
    ClausePartition sig [] where
  part := fun _ => []
  part_color := by
    intro side literal member
    exact nomatch member
  reconstructs := List.Perm.nil

/-- Put every occurrence of an input clause in its owning color. Shared
literals are deliberately owned by the input partition at this leaf. -/
def owned {sig : ColoredSignature 2} (owner : Fin 2) (clause : Clause sig)
    (clauseColor : Formula.IsColor sig owner clause) :
    ClausePartition sig clause where
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
      simp [ColoredClause.toClause]
    · subst owner
      simp [ColoredClause.toClause]

@[simp]
theorem falsifyingPart_owned_owner
    {sig : ColoredSignature 2} (owner : Fin 2) (clause : Clause sig)
    (clauseColor : Formula.IsColor sig owner clause) :
    (owned owner clause clauseColor).toColoredClause.falsifyingPart owner =
      clause.map Literal.negate := by
  simp [owned, ColoredClause.falsifyingPart]

theorem part_eq_nil_of_empty
    (partition : ClausePartition sig []) (side : Fin 2) :
    partition.part side = [] := by
  have concatenated : partition.part 0 ++ partition.part 1 = [] :=
    partition.reconstructs.eq_nil
  have parts := List.append_eq_nil_iff.mp concatenated
  refine Fin.cases parts.1 ?_ side
  intro predecessor
  have equal : predecessor = 0 := Subsingleton.elim _ _
  subst predecessor
  exact parts.2

/-- The partition already stored by a theory lemma reconstructs its own
underlying clause. -/
def ofTheoryLemma (lemma : TheoryLemma sig) :
    ClausePartition sig lemma.toClause where
  toColoredClause := lemma
  reconstructs := List.Perm.refl _

end ClausePartition

/-- The occurrence-coloring facts needed to transport falsifying assignments
through one resolution step. On the pivot's owning side, the pivot value
selects which parent is falsified. On the other side, both parent projections
are falsified because the pivot has no occurrence there. -/
structure PartitionedResolutionStep (sig : ColoredSignature 2)
    {left right resolvent : Clause sig}
    (step : ResolutionStep left right resolvent)
    (leftPartition : ClausePartition sig left)
    (rightPartition : ClausePartition sig right)
    (resolventPartition : ClausePartition sig resolvent) where
  pivotOwner : Fin 2
  pivot_available : step.pivot.AvailableIn sig pivotOwner
  owner_left_of_not_pivot :
    ∀ interpretation : Interpretation sig,
      Satisfies interpretation
        (resolventPartition.toColoredClause.falsifyingPart pivotOwner) →
      ¬SatisfiesLiteral interpretation step.pivot →
      Satisfies interpretation
        (leftPartition.toColoredClause.falsifyingPart pivotOwner)
  owner_right_of_pivot :
    ∀ interpretation : Interpretation sig,
      Satisfies interpretation
        (resolventPartition.toColoredClause.falsifyingPart pivotOwner) →
      SatisfiesLiteral interpretation step.pivot →
      Satisfies interpretation
        (rightPartition.toColoredClause.falsifyingPart pivotOwner)
  other_left :
    ∀ interpretation : Interpretation sig,
      Satisfies interpretation
        (resolventPartition.toColoredClause.falsifyingPart pivotOwner.rev) →
      Satisfies interpretation
        (leftPartition.toColoredClause.falsifyingPart pivotOwner.rev)
  other_right :
    ∀ interpretation : Interpretation sig,
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
structure IsPartialInterpolantAt (inputs : ColoredCNF sig)
    (clause : Clause sig)
    (partition : ClausePartition sig clause)
    (side : Fin 2)
    (interpolant : CNF sig) : Prop where
  interpolant_shared :
    CNF.IsShared sig 0 interpolant
  side_entails :
    ∀ interpretation : Interpretation sig,
      (inputs.part side).Satisfied interpretation →
      Satisfies interpretation
        (partition.toColoredClause.falsifyingPart side) →
      interpolant.Satisfied interpretation
  interpolant_other_unsatisfiable :
    ¬∃ interpretation : Interpretation sig,
      interpolant.Satisfied interpretation ∧
      (inputs.part side.rev).Satisfied interpretation ∧
      Satisfies interpretation
        (partition.toColoredClause.falsifyingPart side.rev)

/-- The final semantic specification for interpolation between two colored
clausal EUF inputs, indexed by the side whose contribution is summarized. -/
structure IsClausalInterpolantAt (inputs : ColoredCNF sig)
    (side : Fin 2)
    (interpolant : CNF sig) : Prop where
  inputs_unsatisfiable : inputs.Unsatisfiable
  interpolant_shared :
    CNF.IsShared sig 0 interpolant
  side_entails :
    ∀ interpretation : Interpretation sig,
      (inputs.part side).Satisfied interpretation →
      interpolant.Satisfied interpretation
  interpolant_other_unsatisfiable :
    ¬∃ interpretation : Interpretation sig,
      interpolant.Satisfied interpretation ∧
      (inputs.part side.rev).Satisfied interpretation

namespace TheoryLemmaAnnotation

/-- A valid theory-lemma annotation is also a valid partial interpolant at
that leaf in any surrounding clausal problem. The surrounding input clauses
are irrelevant to this local argument. -/
def toPartialInterpolant (annotation : TheoryLemmaAnnotation sig)
    (inputs : ColoredCNF sig) :
  IsPartialInterpolantAt inputs
      annotation.lemma.toClause
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
    {sig : ColoredSignature 2} (inputs : ColoredCNF sig)
    (side : Fin 2) (clause : Clause sig)
    (member : clause ∈ inputs.part side) :
    IsPartialInterpolantAt inputs clause
      (ClausePartition.owned side clause
        (inputs.part_color side clause member))
      side CNF.falsum where
  interpolant_shared := CNF.isShared_falsum sig 0
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
    {sig : ColoredSignature 2} (inputs : ColoredCNF sig)
    (owner : Fin 2) (clause : Clause sig)
    (member : clause ∈ inputs.part owner) :
    IsPartialInterpolantAt inputs clause
      (ClausePartition.owned owner clause
        (inputs.part_color owner clause member))
      owner.rev [] where
  interpolant_shared := CNF.isShared_nil sig 0
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
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {left right resolvent : Clause sig}
    {leftPartition : ClausePartition sig left}
    {rightPartition : ClausePartition sig right}
    {resolventPartition : ClausePartition sig resolvent}
    {step : ResolutionStep left right resolvent}
    (projection : PartitionedResolutionStep sig step leftPartition
      rightPartition resolventPartition)
    (side : Fin 2) (owner : projection.pivotOwner = side)
    {leftInterpolant rightInterpolant : CNF sig}
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
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {left right resolvent : Clause sig}
    {leftPartition : ClausePartition sig left}
    {rightPartition : ClausePartition sig right}
    {resolventPartition : ClausePartition sig resolvent}
    {step : ResolutionStep left right resolvent}
    (projection : PartitionedResolutionStep sig step leftPartition
      rightPartition resolventPartition)
    (side : Fin 2) (owner : projection.pivotOwner = side.rev)
    {leftInterpolant rightInterpolant : CNF sig}
    (leftInvariant : IsPartialInterpolantAt inputs left leftPartition
      side leftInterpolant)
    (rightInvariant : IsPartialInterpolantAt inputs right rightPartition
      side rightInterpolant) :
    IsPartialInterpolantAt inputs resolvent resolventPartition side
      (leftInterpolant ++ rightInterpolant) where
  interpolant_shared := (CNF.isShared_append sig 0 _ _).mpr
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
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {side : Fin 2}
    {interpolant : CNF sig}
    (invariant : IsPartialInterpolantAt inputs []
      (ClausePartition.empty sig) side interpolant)
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

/-- The empty-clause result does not depend on using the canonical empty
partition: reconstruction forces both parts of every empty-clause partition
to be empty. -/
def atAnyContradictionPartition
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {side : Fin 2} {partition : ClausePartition sig []}
    {interpolant : CNF sig}
    (invariant : IsPartialInterpolantAt inputs [] partition side interpolant)
    (inputsUnsatisfiable : inputs.Unsatisfiable) :
    IsClausalInterpolantAt inputs side interpolant where
  inputs_unsatisfiable := inputsUnsatisfiable
  interpolant_shared := invariant.interpolant_shared
  side_entails := by
    intro interpretation satisfiesSide
    apply invariant.side_entails interpretation satisfiesSide
    simp [ColoredClause.falsifyingPart,
      ClausePartition.part_eq_nil_of_empty partition side, Satisfies]
  interpolant_other_unsatisfiable := by
    rintro ⟨interpretation, satisfiesInterpolant, satisfiesOther⟩
    apply invariant.interpolant_other_unsatisfiable
    refine ⟨interpretation, satisfiesInterpolant, satisfiesOther, ?_⟩
    simp [ColoredClause.falsifyingPart,
      ClausePartition.part_eq_nil_of_empty partition side.rev, Satisfies]

end IsPartialInterpolantAt

end EUF
