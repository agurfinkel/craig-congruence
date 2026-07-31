import CraigCongruence.ColoredClausalProof

namespace EUF

/-- Everything established about one clause while traversing a colored proof. -/
structure ClauseAnnotation (inputs : ColoredCNF colored) (side : Fin 2)
    (clause : Clause colored.toSignature) where
  partition : ClausePartition colored clause
  interpolant : CNF colored.toSignature
  correct : IsPartialInterpolantAt inputs clause partition side interpolant

/-- Partial-interpolant annotations for every clause already present in the
ordered LRAT database. -/
abbrev ClauseAnnotationDatabase (inputs : ColoredCNF colored) (side : Fin 2)
    (clauses : CNF colored.toSignature) :=
  ∀ index : Fin clauses.length,
    ClauseAnnotation inputs side (clauses.get index)

namespace ClauseAnnotationDatabase

def empty (inputs : ColoredCNF colored) (side : Fin 2) :
    ClauseAnnotationDatabase inputs side [] :=
  fun index => nomatch index

/-- Extend an annotation database in the same snoc order as `ClauseTrace`. -/
noncomputable def snoc
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2} {clauses : CNF colored.toSignature}
    (database : ClauseAnnotationDatabase inputs side clauses)
    {clause : Clause colored.toSignature}
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

def cast {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2} {left right : Clause colored.toSignature}
    (equal : left = right)
    (annotation : ClauseAnnotation inputs side left) :
    ClauseAnnotation inputs side right :=
  equal ▸ annotation

@[simp]
theorem cast_interpolant
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2} {left right : Clause colored.toSignature}
    (equal : left = right)
    (annotation : ClauseAnnotation inputs side left) :
    (annotation.cast equal).interpolant = annotation.interpolant := by
  cases equal
  rfl

/-- Annotation of an input clause owned by the summarized side. -/
def inputOnSide
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {owner side : Fin 2} {clause : Clause colored.toSignature}
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
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {owner side : Fin 2} {clause : Clause colored.toSignature}
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
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2} (annotation : TheoryLemmaAnnotation colored)
    (equal : annotation.side = side) :
    ClauseAnnotation inputs side
      annotation.lemma.toColoredClause.literals := by
  subst side
  exact ClauseAnnotation.mk
    (ClausePartition.ofTheoryLemma annotation.lemma)
    annotation.interpolant.toCNF
    (annotation.toPartialInterpolant inputs)

/-- The resolution combination with its result partition fixed in the return
type. This dependent form is convenient when folding a chain. -/
def resolveAt
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2} {left right resolvent : Clause colored.toSignature}
    (leftAnnotation : ClauseAnnotation inputs side left)
    (rightAnnotation : ClauseAnnotation inputs side right)
    (resolventPartition : ClausePartition colored resolvent)
    {step : ResolutionStep left right resolvent}
    (projection : PartitionedResolutionStep colored step
      leftAnnotation.partition rightAnnotation.partition resolventPartition)
    (location : PivotLocation projection.pivotOwner side) :
    { interpolant : CNF colored.toSignature //
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
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2} {left right resolvent : Clause colored.toSignature}
    (leftAnnotation : ClauseAnnotation inputs side left)
    (rightAnnotation : ClauseAnnotation inputs side right)
    (resolventPartition : ClausePartition colored resolvent)
    {step : ResolutionStep left right resolvent}
    (projection : PartitionedResolutionStep colored step
      leftAnnotation.partition rightAnnotation.partition resolventPartition)
    (location : PivotLocation projection.pivotOwner side) :
    ClauseAnnotation inputs side resolvent := by
  let result := leftAnnotation.resolveAt rightAnnotation resolventPartition
    projection location
  exact ClauseAnnotation.mk resolventPartition result.val result.property

end ClauseAnnotation

/-- A subsumption witness that also preserves the occurrence partition. The
ordinary clause relation says that `stronger` implies `weaker`; this field
transports the two falsifying projections used by interpolation. -/
structure PartitionedSubsumption
    {colored : ColoredSignature 2}
    {stronger weaker : Clause colored.toSignature}
    (subsumes : Clause.Subsumes stronger weaker)
    (strongerPartition : ClausePartition colored stronger)
    (weakerPartition : ClausePartition colored weaker) where
  falsifyingPart :
    ∀ side (interpretation : Interpretation colored.toSignature),
      Satisfies interpretation
        (weakerPartition.toColoredClause.falsifyingPart side) →
      Satisfies interpretation
        (strongerPartition.toColoredClause.falsifyingPart side)

namespace ClauseAnnotation

/-- Transport a partial interpolant from a subsuming chain result to the
possibly weaker learned clause. -/
def ofSubsumption
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2} {stronger weaker : Clause colored.toSignature}
    (strongerAnnotation : ClauseAnnotation inputs side stronger)
    (weakerPartition : ClausePartition colored weaker)
    {subsumes : Clause.Subsumes stronger weaker}
    (partitioned : PartitionedSubsumption subsumes
      strongerAnnotation.partition weakerPartition) :
    ClauseAnnotation inputs side weaker where
  partition := weakerPartition
  interpolant := strongerAnnotation.interpolant
  correct := {
    interpolant_shared := strongerAnnotation.correct.interpolant_shared
    side_entails := by
      intro interpretation satisfiesInputs satisfiesWeaker
      apply strongerAnnotation.correct.side_entails interpretation
        satisfiesInputs
      exact partitioned.falsifyingPart side interpretation satisfiesWeaker
    interpolant_other_unsatisfiable := by
      rintro ⟨interpretation, satisfiesInterpolant, satisfiesInputs,
        satisfiesWeaker⟩
      exact strongerAnnotation.correct.interpolant_other_unsatisfiable
        ⟨interpretation, satisfiesInterpolant, satisfiesInputs,
          partitioned.falsifyingPart side.rev interpretation satisfiesWeaker⟩ }

end ClauseAnnotation

/-- A coloring witness parallel to an explicit resolution chain. It supplies
the occurrence partition of every intermediate resolvent and the ownership
choice for every pivot. Parent partitions come from the earlier-clause
annotation database. -/
inductive ResolutionChainPartitioning
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2} {available : CNF colored.toSignature}
    (database : ClauseAnnotationDatabase inputs side available) :
    {anchor result : Clause colored.toSignature} →
    (chain : ResolutionChain available anchor result) →
    ClausePartition colored anchor →
    ClausePartition colored result → Type 1 where
  | start (partition : ClausePartition colored anchor) :
      ResolutionChainPartitioning database (.start :
        ResolutionChain available anchor anchor) partition partition
  | resolve
      {chain : ResolutionChain available anchor current}
      {anchorPartition : ClausePartition colored anchor}
      {currentPartition : ClausePartition colored current}
      (previous : ResolutionChainPartitioning database chain
        anchorPartition currentPartition)
      (parent : Fin available.length)
      {next : Clause colored.toSignature}
      {step : ResolutionStep current (available.get parent) next}
      (nextPartition : ClausePartition colored next)
      (projection : PartitionedResolutionStep colored step currentPartition
        (database parent).partition nextPartition)
      (location : PivotLocation projection.pivotOwner side) :
      ResolutionChainPartitioning database
        (.resolve chain parent step) anchorPartition nextPartition

namespace ResolutionChainPartitioning

/-- Fold binary partial-interpolant construction over the explicit chain. -/
noncomputable def interpolate
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2} {available : CNF colored.toSignature}
    {database : ClauseAnnotationDatabase inputs side available}
    {anchor result : Clause colored.toSignature}
    {chain : ResolutionChain available anchor result}
    {anchorPartition : ClausePartition colored anchor}
    {resultPartition : ClausePartition colored result}
    (partitioning : ResolutionChainPartitioning database chain
      anchorPartition resultPartition)
    (anchorInterpolant : CNF colored.toSignature)
    (anchorCorrect : IsPartialInterpolantAt inputs anchor anchorPartition
      side anchorInterpolant) :
    { interpolant : CNF colored.toSignature //
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
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2} {available : CNF colored.toSignature}
    (database : ClauseAnnotationDatabase inputs side available)
    {derived : Clause colored.toSignature}
    (justification : ChainJustification available derived) where
  resolventPartition : ClausePartition colored justification.resolvent
  partitioning : ResolutionChainPartitioning database justification.chain
    (database justification.anchor).partition resolventPartition
  derivedPartition : ClausePartition colored derived
  partitionedSubsumption : PartitionedSubsumption justification.subsumes
    resolventPartition derivedPartition

namespace InterpolatedChainJustification

/-- Compute the annotation of the chain's exact final resolvent. The learned
clause's final subsumption step is handled separately. -/
noncomputable def resolventAnnotation
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2} {available : CNF colored.toSignature}
    {database : ClauseAnnotationDatabase inputs side available}
    {derived : Clause colored.toSignature}
    {justification : ChainJustification available derived}
    (interpolation : InterpolatedChainJustification database justification) :
    ClauseAnnotation inputs side justification.resolvent := by
  let result := interpolation.partitioning.interpolate
    (database justification.anchor).interpolant
    (database justification.anchor).correct
  exact ClauseAnnotation.mk interpolation.resolventPartition
    result.val result.property

/-- Compute the annotation of the learned clause, including the final
subsumption step recorded by its LRAT-like justification. -/
noncomputable def derivedAnnotation
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2} {available : CNF colored.toSignature}
    {database : ClauseAnnotationDatabase inputs side available}
    {derived : Clause colored.toSignature}
    {justification : ChainJustification available derived}
    (interpolation : InterpolatedChainJustification database justification) :
    ClauseAnnotation inputs side derived :=
  interpolation.resolventAnnotation.ofSubsumption
    interpolation.derivedPartition interpolation.partitionedSubsumption

end InterpolatedChainJustification

/-- Incremental construction of the annotation database alongside the
snoc-ordered LRAT trace. Leaf annotations use the input/theory constructors;
derived annotations are computed from their explicit chain witnesses. -/
inductive ClauseTraceInterpolation
    {colored : ColoredSignature 2} (inputs : ColoredCNF colored)
    (side : Fin 2) :
    {clauses : CNF colored.toSignature} →
    (trace : ClauseTrace (ColoredProofLeaf inputs) clauses) →
    ClauseAnnotationDatabase inputs side clauses → Type 1 where
  | empty : ClauseTraceInterpolation inputs side .empty
      (ClauseAnnotationDatabase.empty inputs side)
  | addLeaf
      {available : CNF colored.toSignature}
      {trace : ClauseTrace (ColoredProofLeaf inputs) available}
      {database : ClauseAnnotationDatabase inputs side available}
      (previous : ClauseTraceInterpolation inputs side trace database)
      {clause : Clause colored.toSignature}
      (leaf : ColoredProofLeaf inputs clause)
      (annotation : ClauseAnnotation inputs side clause) :
      ClauseTraceInterpolation inputs side (.addLeaf trace leaf)
        (database.snoc annotation)
  | addDerived
      {available : CNF colored.toSignature}
      {trace : ClauseTrace (ColoredProofLeaf inputs) available}
      {database : ClauseAnnotationDatabase inputs side available}
      (previous : ClauseTraceInterpolation inputs side trace database)
      {clause : Clause colored.toSignature}
      (justification : ChainJustification available clause)
      (interpolation : InterpolatedChainJustification database justification) :
      ClauseTraceInterpolation inputs side (.addDerived trace justification)
        (database.snoc interpolation.derivedAnnotation)

/-- A completed interpolation certificate for a colored LRAT-like
refutation. The database annotations can be built incrementally using the
leaf constructors and `InterpolatedChainJustification.derivedAnnotation`. -/
structure InterpolatedClauseRefutation
    {colored : ColoredSignature 2} (inputs : ColoredCNF colored)
    (side : Fin 2) (refutation : ColoredClauseRefutation inputs) where
  database : ClauseAnnotationDatabase inputs side refutation.clauses
  contradictionIndex : Fin refutation.clauses.length
  contradiction_eq : refutation.clauses.get contradictionIndex = []

namespace InterpolatedClauseRefutation

/-- Package an incrementally constructed database as a completed refutation
certificate once the empty-clause occurrence is identified. -/
def ofTrace
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
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
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2} {refutation : ColoredClauseRefutation inputs}
    (certificate : InterpolatedClauseRefutation inputs side refutation) :
    CNF colored.toSignature :=
  (certificate.database certificate.contradictionIndex).interpolant

/-- Soundness of the complete clausal interpolation certificate. -/
theorem sound
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
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
