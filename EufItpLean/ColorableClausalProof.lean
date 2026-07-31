import EufItpLean.ClausalInterpolationTrace

namespace EUF

namespace CNF

/-- Semantic entailment of one clause by a CNF in EUF. -/
def EntailsClause (cnf : CNF signature) (clause : Clause signature) : Prop :=
  ∀ interpretation : Interpretation signature,
    cnf.Satisfied interpretation → clause.Satisfied interpretation

end CNF

/-- An explicit LRAT-like derivation of one distinguished clause from input
clauses and valid theory lemmas. -/
structure ClauseConsequence (cnf : CNF signature)
    (conclusion : Clause signature) where
  clauses : CNF signature
  trace : ClauseTrace (CNF.InputOrTheory cnf) clauses
  conclusionIndex : Fin clauses.length
  conclusion_eq : clauses.get conclusionIndex = conclusion

namespace ClauseConsequence

theorem sound
    {signature : Signature} {cnf : CNF signature}
    {conclusion : Clause signature}
    (derivation : ClauseConsequence cnf conclusion) :
    cnf.EntailsClause conclusion := by
  intro interpretation satisfiesInputs
  have satisfiesTrace := derivation.trace.sound interpretation (by
    intro clause leaf
    cases leaf with
    | input member => exact satisfiesInputs clause member
    | theory valid => exact valid interpretation)
  have satisfiesConclusion :=
    satisfiesTrace _ (List.get_mem derivation.clauses derivation.conclusionIndex)
  rw [derivation.conclusion_eq] at satisfiesConclusion
  exact satisfiesConclusion

end ClauseConsequence

/-- An owner for every clause in an ordered trace. -/
abbrev ClauseOwnerDatabase (clauses : CNF signature) :=
  Fin clauses.length → Fin 2

namespace ClauseOwnerDatabase

def empty : ClauseOwnerDatabase ([] : CNF signature) :=
  fun index => nomatch index

def snoc (owners : ClauseOwnerDatabase clauses) (owner : Fin 2) :
    ClauseOwnerDatabase (clauses ++ [clause]) := by
  intro index
  let normalized : Fin (clauses.length + 1) :=
    ⟨index.val, by simpa using index.isLt⟩
  exact Fin.lastCases owner owners normalized

end ClauseOwnerDatabase

/-- The dependency restriction at the A/B cut. A clause may use a parent of
the same owner. A target-side clause may additionally consume a source-owned
parent, but only when that parent is shared. -/
def ParentAllowed (colored : ColoredSignature 2) (source : Fin 2)
    (resultOwner parentOwner : Fin 2)
    (parent : Clause colored.toSignature) : Prop :=
  parentOwner = resultOwner ∨
    (resultOwner = source.rev ∧ parentOwner = source ∧
      parent.IsShared colored 0)

namespace ResolutionChain

/-- A predicate holds for every non-anchor parent referenced by a resolution
chain. -/
inductive ParentsSatisfy
    {signature : Signature} {available : CNF signature}
    (predicate : Fin available.length → Prop) :
    {anchor result : Clause signature} →
    ResolutionChain available anchor result → Prop where
  | start : ParentsSatisfy predicate .start
  | resolve
      (previous : ParentsSatisfy predicate chain)
      (parentSatisfies : predicate parent) :
      ParentsSatisfy predicate (.resolve chain parent step)

end ResolutionChain

/-- A coloring witness parallel to an LRAT trace. Theory leaves take the
orientation of their EUF annotation. Ordinary and learned clauses are
colorable in their owning partition, and learned-clause dependencies obey the
shared-interface restriction. -/
inductive ColorableClauseTrace
    {colored : ColoredSignature 2} (inputs : ColoredCNF colored)
    (source : Fin 2) :
    {clauses : CNF colored.toSignature} →
    (trace : ClauseTrace (ColoredProofLeaf inputs) clauses) →
    ClauseOwnerDatabase clauses → Type 1 where
  | empty : ColorableClauseTrace inputs source .empty
      ClauseOwnerDatabase.empty
  | addInput
      {available : CNF colored.toSignature}
      {trace : ClauseTrace (ColoredProofLeaf inputs) available}
      {owners : ClauseOwnerDatabase available}
      (previous : ColorableClauseTrace inputs source trace owners)
      (owner : Fin 2) {clause : Clause colored.toSignature}
      (member : clause ∈ inputs.part owner) :
      ColorableClauseTrace inputs source
        (.addLeaf trace (.input owner member)) (owners.snoc owner)
  | addTheory
      {available : CNF colored.toSignature}
      {trace : ClauseTrace (ColoredProofLeaf inputs) available}
      {owners : ClauseOwnerDatabase available}
      (previous : ColorableClauseTrace inputs source trace owners)
      (annotation : TheoryLemmaAnnotation colored) :
      ColorableClauseTrace inputs source
        (.addLeaf trace (.theory annotation))
        (owners.snoc annotation.side)
  | addDerived
      {available : CNF colored.toSignature}
      {trace : ClauseTrace (ColoredProofLeaf inputs) available}
      {owners : ClauseOwnerDatabase available}
      (previous : ColorableClauseTrace inputs source trace owners)
      {clause : Clause colored.toSignature}
      (justification : ChainJustification available clause)
      (owner : Fin 2)
      (clauseColor : Formula.IsColor colored owner clause)
      (anchorAllowed : ParentAllowed colored source owner
        (owners justification.anchor)
        (available.get justification.anchor))
      (parentsAllowed : justification.chain.ParentsSatisfy fun parent =>
        ParentAllowed colored source owner (owners parent)
          (available.get parent)) :
      ColorableClauseTrace inputs source
        (.addDerived trace justification) (owners.snoc owner)

/-- The semantic cut exposed by a two-color colorable proof.

Every interface clause has an explicit source-side derivation. The target
side, together with those interface clauses, has an explicit refutation. A
trace-coloring pass will construct this certificate by cutting every shared
source clause consumed by target reasoning. -/
structure SharedInterfaceCertificate (inputs : ColoredCNF colored)
    (side : Fin 2) where
  interface : CNF colored.toSignature
  interface_shared : CNF.IsShared colored 0 interface
  sourceDerivation : ∀ clause, clause ∈ interface →
    ClauseConsequence (inputs.part side) clause
  targetRefutation :
    ClauseRefutation
      (CNF.InputOrTheory (interface ++ inputs.part side.rev))

namespace SharedInterfaceCertificate

theorem side_entails
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2}
    (certificate : SharedInterfaceCertificate inputs side) :
    ∀ interpretation : Interpretation colored.toSignature,
      (inputs.part side).Satisfied interpretation →
      certificate.interface.Satisfied interpretation := by
  intro interpretation satisfiesSide clause member
  exact (certificate.sourceDerivation clause member).sound
    interpretation satisfiesSide

theorem interface_other_unsatisfiable
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2}
    (certificate : SharedInterfaceCertificate inputs side) :
    ¬∃ interpretation : Interpretation colored.toSignature,
      certificate.interface.Satisfied interpretation ∧
      (inputs.part side.rev).Satisfied interpretation := by
  rintro ⟨interpretation, satisfiesInterface, satisfiesOther⟩
  have targetUnsatisfiable :
      (certificate.interface ++ inputs.part side.rev).Unsatisfiable :=
    CNF.unsatisfiable_of_refutation certificate.targetRefutation
  apply targetUnsatisfiable
  exact ⟨interpretation,
    (CNF.satisfied_append_iff interpretation _ _).mpr
      ⟨satisfiesInterface, satisfiesOther⟩⟩

theorem inputs_unsatisfiable
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2}
    (certificate : SharedInterfaceCertificate inputs side) :
    inputs.Unsatisfiable := by
  rintro ⟨interpretation, satisfiesInputs⟩
  apply certificate.interface_other_unsatisfiable
  exact ⟨interpretation,
    certificate.side_entails interpretation (satisfiesInputs side),
    satisfiesInputs side.rev⟩

/-- Direct shared-clause extraction from a colorable proof cut is a clausal
EUF interpolant. No partial-interpolant resolution calculation is needed. -/
def interpolant
    {colored : ColoredSignature 2} {inputs : ColoredCNF colored}
    {side : Fin 2}
    (certificate : SharedInterfaceCertificate inputs side) :
    IsClausalInterpolantAt inputs side certificate.interface where
  inputs_unsatisfiable := certificate.inputs_unsatisfiable
  interpolant_shared := certificate.interface_shared
  side_entails := certificate.side_entails
  interpolant_other_unsatisfiable :=
    certificate.interface_other_unsatisfiable

end SharedInterfaceCertificate

end EUF
