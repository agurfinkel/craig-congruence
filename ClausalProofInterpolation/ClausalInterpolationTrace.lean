-- SPDX-License-Identifier: MIT

import ClausalProofInterpolation.PartialInterpolant

/-!
An annotation fold over clausal resolution traces. It constructs clause
partitions and partial interpolants for inputs, theory lemmas, and derived
clauses, and proves that the annotation at an explicit contradiction is a
sound clausal interpolant.
-/

namespace EUF

/-- Everything established about one clause while traversing a colored proof. -/
structure ClauseAnnotation (inputs : ColoredCNF sig) (side : Fin 2)
    (clause : Clause sig) where
  partition : ClausePartition sig clause
  interpolant : CNF sig
  correct : IsPartialInterpolantAt inputs clause partition side interpolant

/-- Partial-interpolant annotations for every clause already present in the
ordered LRAT database. -/
abbrev ClauseAnnotationDatabase (inputs : ColoredCNF sig) (side : Fin 2)
    (clauses : CNF sig) :=
  ∀ index : Fin clauses.length,
    ClauseAnnotation inputs side (clauses.get index)

namespace ClauseAnnotationDatabase

def empty (inputs : ColoredCNF sig) (side : Fin 2) :
    ClauseAnnotationDatabase inputs side [] :=
  fun index => nomatch index

/-- Extend an annotation database in the same snoc order as `ClauseTrace`. -/
noncomputable def snoc
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {side : Fin 2} {clauses : CNF sig}
    (database : ClauseAnnotationDatabase inputs side clauses)
    {clause : Clause sig}
    (annotation : ClauseAnnotation inputs side clause) :
    ClauseAnnotationDatabase inputs side (clauses ++ [clause]) := by
  intro index
  let normalized : Fin (clauses.length + 1) :=
    ⟨index.val, by simpa using index.isLt⟩
  let result := Fin.lastCases
    (motive := fun position =>
      ClauseAnnotation inputs side
        ((clauses ++ [clause]).get
          ⟨position.val, by
            simpa only [List.length_append, List.length_singleton] using
              position.isLt⟩))
    (by simpa using annotation)
    (fun previous => by simpa using database previous)
    normalized
  simpa [normalized] using result

end ClauseAnnotationDatabase

/-- In a two-color proof, a pivot is owned either by the summarized side or
by its opposite. Keeping this choice as proof data avoids hidden coloring
decisions during interpolation. -/
inductive PivotLocation (owner side : Fin 2) : Type where
  | onSide (equal : owner = side) : PivotLocation owner side
  | onOtherSide (equal : owner = side.rev) : PivotLocation owner side

namespace ClauseAnnotation

def cast {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {side : Fin 2} {left right : Clause sig}
    (equal : left = right)
    (annotation : ClauseAnnotation inputs side left) :
    ClauseAnnotation inputs side right :=
  equal ▸ annotation

@[simp]
theorem cast_interpolant
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {side : Fin 2} {left right : Clause sig}
    (equal : left = right)
    (annotation : ClauseAnnotation inputs side left) :
    (annotation.cast equal).interpolant = annotation.interpolant := by
  cases equal
  rfl

/-- Annotation of an input clause owned by the summarized side. -/
def inputOnSide
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {owner side : Fin 2} {clause : Clause sig}
    (member : clause ∈ inputs.part owner) (equal : owner = side) :
    ClauseAnnotation inputs side clause := by
  subst side
  exact ClauseAnnotation.mk
    (ClausePartition.owned owner clause
      (inputs.part_color owner clause member))
    CNF.falsum
    (IsPartialInterpolantAt.ofInputOnSide inputs owner clause member)

/-- Annotation of an input clause owned by the side opposite the summarized
one. -/
def inputOnOtherSide
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {owner side : Fin 2} {clause : Clause sig}
    (member : clause ∈ inputs.part owner) (equal : owner = side.rev) :
    ClauseAnnotation inputs side clause := by
  have reversed : owner.rev = side := by
    rw [equal]
    simp
  subst side
  exact ClauseAnnotation.mk
    (ClausePartition.owned owner clause
      (inputs.part_color owner clause member))
    []
    (IsPartialInterpolantAt.ofInputOnOtherSide inputs owner clause member)

/-- Embed a theory leaf whose EUF annotation has the chosen global
orientation. -/
def theory
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {side : Fin 2} (annotation : TheoryLemmaAnnotation sig)
    (equal : annotation.side = side) :
    ClauseAnnotation inputs side
      (ColoredClause.literals annotation.lemma) := by
  subst side
  exact ClauseAnnotation.mk
    (ClausePartition.ofTheoryLemma annotation.lemma)
    annotation.interpolant.toCNF
    (annotation.toPartialInterpolant inputs)

/-- The resolution combination with its result partition fixed in the return
type. This dependent form is convenient when folding a chain. -/
def resolveAt
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {side : Fin 2} {left right resolvent : Clause sig}
    (leftAnnotation : ClauseAnnotation inputs side left)
    (rightAnnotation : ClauseAnnotation inputs side right)
    (resolventPartition : ClausePartition sig resolvent)
    {step : ResolutionStep left right resolvent}
    (projection : PartitionedResolutionStep sig step
      leftAnnotation.partition rightAnnotation.partition resolventPartition)
    (location : PivotLocation projection.pivotOwner side) :
    { interpolant : CNF sig //
      IsPartialInterpolantAt inputs resolvent resolventPartition side
        interpolant } :=
  match location with
  | .onSide equal =>
      ⟨CNF.disjoin leftAnnotation.interpolant rightAnnotation.interpolant,
        IsPartialInterpolantAt.resolveOnSide projection side equal
          leftAnnotation.correct rightAnnotation.correct⟩
  | .onOtherSide equal =>
      ⟨leftAnnotation.interpolant ++ rightAnnotation.interpolant,
        IsPartialInterpolantAt.resolveOnOtherSide projection side equal
          leftAnnotation.correct rightAnnotation.correct⟩

/-- Combine the annotations of a single explicitly partitioned resolution
step. -/
def resolve
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {side : Fin 2} {left right resolvent : Clause sig}
    (leftAnnotation : ClauseAnnotation inputs side left)
    (rightAnnotation : ClauseAnnotation inputs side right)
    (resolventPartition : ClausePartition sig resolvent)
    {step : ResolutionStep left right resolvent}
    (projection : PartitionedResolutionStep sig step
      leftAnnotation.partition rightAnnotation.partition resolventPartition)
    (location : PivotLocation projection.pivotOwner side) :
    ClauseAnnotation inputs side resolvent := by
  let result := leftAnnotation.resolveAt rightAnnotation resolventPartition
    projection location
  exact ClauseAnnotation.mk resolventPartition result.val result.property

end ClauseAnnotation

/-- A coloring witness parallel to an explicit resolution chain. It supplies
the occurrence partition of every intermediate resolvent and the ownership
choice for every pivot. Parent partitions come from the earlier-clause
annotation database. -/
inductive ResolutionChainPartitioning
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {side : Fin 2} {available : CNF sig}
    (database : ClauseAnnotationDatabase inputs side available) :
    {anchor result : Clause sig} →
    (chain : ResolutionChain available anchor result) →
    ClausePartition sig anchor →
    ClausePartition sig result → Type 1 where
  | start (partition : ClausePartition sig anchor) :
      ResolutionChainPartitioning database (.start :
        ResolutionChain available anchor anchor) partition partition
  | resolve
      {chain : ResolutionChain available anchor current}
      {anchorPartition : ClausePartition sig anchor}
      {currentPartition : ClausePartition sig current}
      (previous : ResolutionChainPartitioning database chain
        anchorPartition currentPartition)
      (parent : Fin available.length)
      {next : Clause sig}
      {step : ResolutionStep current (available.get parent) next}
      (nextPartition : ClausePartition sig next)
      (projection : PartitionedResolutionStep sig step currentPartition
        (database parent).partition nextPartition)
      (location : PivotLocation projection.pivotOwner side) :
      ResolutionChainPartitioning database
        (.resolve chain parent step) anchorPartition nextPartition

namespace ResolutionChainPartitioning

/-- Fold binary partial-interpolant construction over the explicit chain. -/
noncomputable def interpolate
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {side : Fin 2} {available : CNF sig}
    {database : ClauseAnnotationDatabase inputs side available}
    {anchor result : Clause sig}
    {chain : ResolutionChain available anchor result}
    {anchorPartition : ClausePartition sig anchor}
    {resultPartition : ClausePartition sig result}
    (partitioning : ResolutionChainPartitioning database chain
      anchorPartition resultPartition)
    (anchorInterpolant : CNF sig)
    (anchorCorrect : IsPartialInterpolantAt inputs anchor anchorPartition
      side anchorInterpolant) :
    { interpolant : CNF sig //
      IsPartialInterpolantAt inputs result resultPartition side interpolant } := by
  induction partitioning with
  | start anchorPart =>
      exact ⟨anchorInterpolant, anchorCorrect⟩
  | resolve previous parent nextPartition projection location previousResult =>
      have currentResult := previousResult anchorCorrect
      let currentAnnotation :=
        ClauseAnnotation.mk _ currentResult.val currentResult.property
      let nextAnnotation := currentAnnotation.resolveAt
        (database parent) nextPartition projection location
      exact nextAnnotation

end ResolutionChainPartitioning

/-- Interpolation information for the resolution chain inside one learned
clause's LRAT-like justification. -/
structure InterpolatedChainJustification
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {side : Fin 2} {available : CNF sig}
    (database : ClauseAnnotationDatabase inputs side available)
    {derived : Clause sig}
    (justification : ChainJustification available derived) where
  derivedPartition : ClausePartition sig derived
  partitioning : ResolutionChainPartitioning database justification.chain
    (database justification.anchor).partition derivedPartition

namespace InterpolatedChainJustification

/-- Compute the annotation of the clause derived by the exact resolution
chain. -/
noncomputable def derivedAnnotation
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {side : Fin 2} {available : CNF sig}
    {database : ClauseAnnotationDatabase inputs side available}
    {derived : Clause sig}
    {justification : ChainJustification available derived}
    (interpolation : InterpolatedChainJustification database justification) :
    ClauseAnnotation inputs side derived := by
  let result := interpolation.partitioning.interpolate
    (database justification.anchor).interpolant
    (database justification.anchor).correct
  exact ClauseAnnotation.mk interpolation.derivedPartition
    result.val result.property

end InterpolatedChainJustification

/-- Incremental construction of the annotation database alongside the
snoc-ordered LRAT trace. Leaf annotations use the input/theory constructors;
derived annotations are computed from their explicit chain witnesses. -/
inductive ClauseTraceInterpolation
    {sig : ColoredSignature 2} (inputs : ColoredCNF sig)
    (side : Fin 2) :
    {clauses : CNF sig} →
    (trace : ClauseTrace (ColoredProofLeaf inputs) clauses) →
    ClauseAnnotationDatabase inputs side clauses → Type 1 where
  | empty : ClauseTraceInterpolation inputs side .empty
      (ClauseAnnotationDatabase.empty inputs side)
  | addLeaf
      {available : CNF sig}
      {trace : ClauseTrace (ColoredProofLeaf inputs) available}
      {database : ClauseAnnotationDatabase inputs side available}
      (previous : ClauseTraceInterpolation inputs side trace database)
      {clause : Clause sig}
      (leaf : ColoredProofLeaf inputs clause)
      (annotation : ClauseAnnotation inputs side clause) :
      ClauseTraceInterpolation inputs side (.addLeaf trace leaf)
        (database.snoc annotation)
  | addDerived
      {available : CNF sig}
      {trace : ClauseTrace (ColoredProofLeaf inputs) available}
      {database : ClauseAnnotationDatabase inputs side available}
      (previous : ClauseTraceInterpolation inputs side trace database)
      {clause : Clause sig}
      (justification : ChainJustification available clause)
      (interpolation : InterpolatedChainJustification database justification) :
      ClauseTraceInterpolation inputs side (.addDerived trace justification)
        (database.snoc interpolation.derivedAnnotation)

/-- A completed interpolation certificate for a colored LRAT-like
refutation. The database annotations can be built incrementally using the
leaf constructors and `InterpolatedChainJustification.derivedAnnotation`. -/
structure InterpolatedClauseRefutation
    {sig : ColoredSignature 2} (inputs : ColoredCNF sig)
    (side : Fin 2) (refutation : ColoredClauseRefutation inputs) where
  database : ClauseAnnotationDatabase inputs side refutation.clauses
  contradictionIndex : Fin refutation.clauses.length
  contradiction_eq : refutation.clauses.get contradictionIndex = []

namespace InterpolatedClauseRefutation

/-- Package an incrementally constructed database as a completed refutation
certificate once the empty-clause occurrence is identified. -/
def ofTrace
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {side : Fin 2} {refutation : ColoredClauseRefutation inputs}
    {database : ClauseAnnotationDatabase inputs side refutation.clauses}
    (_construction : ClauseTraceInterpolation inputs side
      refutation.trace database)
    (contradictionIndex : Fin refutation.clauses.length)
    (contradiction_eq : refutation.clauses.get contradictionIndex = []) :
    InterpolatedClauseRefutation inputs side refutation where
  database := database
  contradictionIndex := contradictionIndex
  contradiction_eq := contradiction_eq

/-- The CNF annotation stored at the explicit empty-clause occurrence. -/
def interpolant
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {side : Fin 2} {refutation : ColoredClauseRefutation inputs}
    (certificate : InterpolatedClauseRefutation inputs side refutation) :
    CNF sig :=
  (certificate.database certificate.contradictionIndex).interpolant

/-- Soundness of the complete clausal interpolation certificate. -/
theorem sound
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {side : Fin 2} {refutation : ColoredClauseRefutation inputs}
    (certificate : InterpolatedClauseRefutation inputs side refutation) :
    IsClausalInterpolantAt inputs side certificate.interpolant := by
  let annotation := certificate.database certificate.contradictionIndex
  let emptyAnnotation := annotation.cast certificate.contradiction_eq
  have result := emptyAnnotation.correct.atAnyContradictionPartition
      refutation.inputs_unsatisfiable
  simpa [interpolant, emptyAnnotation] using result

end InterpolatedClauseRefutation

end EUF
