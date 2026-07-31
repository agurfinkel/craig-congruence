import EufItpLean.ClausalProof

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
    (interpolant : EqualityHornFormula colored.toSignature) : Prop where
  interpolant_shared :
    EqualityHornFormula.IsShared colored 0 interpolant
  side_entails :
    ∀ interpretation : Interpretation colored.toSignature,
      (inputs.part side).Satisfied interpretation →
      Satisfies interpretation
        (partition.toColoredClause.falsifyingPart side) →
      SatisfiesEqualityHornFormula interpretation interpolant
  interpolant_other_unsatisfiable :
    ¬∃ interpretation : Interpretation colored.toSignature,
      SatisfiesEqualityHornFormula interpretation interpolant ∧
      (inputs.part side.rev).Satisfied interpretation ∧
      Satisfies interpretation
        (partition.toColoredClause.falsifyingPart side.rev)

/-- The final semantic specification for interpolation between two colored
clausal EUF inputs, indexed by the side whose contribution is summarized. -/
structure IsClausalInterpolantAt (inputs : ColoredCNF colored)
    (side : Fin 2)
    (interpolant : EqualityHornFormula colored.toSignature) : Prop where
  inputs_unsatisfiable : inputs.Unsatisfiable
  interpolant_shared :
    EqualityHornFormula.IsShared colored 0 interpolant
  side_entails :
    ∀ interpretation : Interpretation colored.toSignature,
      (inputs.part side).Satisfied interpretation →
      SatisfiesEqualityHornFormula interpretation interpolant
  interpolant_other_unsatisfiable :
    ¬∃ interpretation : Interpretation colored.toSignature,
      SatisfiesEqualityHornFormula interpretation interpolant ∧
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
      annotation.side annotation.interpolant where
  interpolant_shared := annotation.correct.interpolant_shared
  side_entails := by
    intro interpretation _ satisfiesFalsifyingPart
    exact annotation.correct.side_entails interpretation
      satisfiesFalsifyingPart
  interpolant_other_unsatisfiable := by
    rintro ⟨interpretation, satisfiesInterpolant, _, satisfiesFalsifyingPart⟩
    exact annotation.correct.interpolant_other_unsatisfiable
      ⟨interpretation, satisfiesInterpolant, satisfiesFalsifyingPart⟩

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
      side EqualityHornFormula.falsum where
  interpolant_shared := EqualityHornFormula.isShared_falsum colored 0
  side_entails := by
    intro interpretation satisfiesInputs satisfiesFalsification
    exact False.elim (Clause.contradicts_falsifying_formula
      (satisfiesInputs clause member)
      (by simpa using satisfiesFalsification))
  interpolant_other_unsatisfiable := by
    rintro ⟨interpretation, satisfiesFalsum, _, _⟩
    exact EqualityHornFormula.not_satisfies_falsum interpretation
      satisfiesFalsum

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
  interpolant_shared := EqualityHornFormula.isShared_nil colored 0
  side_entails := by
    intro interpretation _ _
    exact EqualityHornFormula.satisfies_nil interpretation
  interpolant_other_unsatisfiable := by
    rintro ⟨interpretation, _, satisfiesInputs, satisfiesFalsification⟩
    have satisfiesOwner : (inputs.part owner).Satisfied interpretation := by
      simpa using satisfiesInputs
    apply Clause.contradicts_falsifying_formula
      (satisfiesOwner clause member)
    simpa using satisfiesFalsification

/-- At a refutation's empty clause, the partial-interpolant invariant becomes
the final clausal interpolation theorem. -/
def atContradiction
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2}
    {interpolant : EqualityHornFormula colored.toSignature}
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
