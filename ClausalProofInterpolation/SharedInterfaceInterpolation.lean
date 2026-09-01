-- SPDX-License-Identifier: MIT

import ClausalProofInterpolation.Specification

/-!
Whole-trace interpolation by shared-interface extraction. The module records
clause owners and permitted dependencies, constructs semantic entailment
witnesses, prunes a colorable trace to shared source clauses, and proves that
the selected interface is a clausal Craig interpolant. This alternative avoids
local theory-lemma interpolation when the proof exposes a suitable shared cut.
-/

namespace EUF

namespace CNF

/-- Semantic entailment of one clause by a CNF in EUF. -/
def EntailsClause (cnf : CNF signature) (clause : Clause signature) : Prop :=
  ∀ interpretation : Interpretation signature,
    CNF.Satisfied interpretation cnf →
      Clause.Satisfied interpretation clause

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

def castConclusion
    (derivation : ClauseConsequence cnf left) (equal : left = right) :
    ClauseConsequence cnf right where
  clauses := derivation.clauses
  trace := derivation.trace
  conclusionIndex := derivation.conclusionIndex
  conclusion_eq := derivation.conclusion_eq.trans equal

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

@[simp]
theorem snoc_last (owners : ClauseOwnerDatabase clauses) (owner : Fin 2) :
    owners.snoc (clause := clause) owner
      ⟨clauses.length, by simp⟩ = owner := by
  unfold snoc
  have equal :
      (⟨clauses.length, by simp⟩ : Fin (clauses.length + 1)) =
        Fin.last clauses.length := Fin.ext rfl
  rw [equal]
  simp

@[simp]
theorem snoc_previous (owners : ClauseOwnerDatabase clauses) (owner : Fin 2)
    (index : Fin clauses.length) :
    owners.snoc (clause := clause) owner
      ⟨index.val, by
        simpa only [List.length_append, List.length_singleton] using
          Nat.lt_succ_of_lt index.isLt⟩ = owners index := by
  unfold snoc
  have equal :
      (⟨index.val, Nat.lt_succ_of_lt index.isLt⟩ : Fin (clauses.length + 1)) =
        Fin.castSucc index := Fin.ext rfl
  rw [equal]
  simp

end ClauseOwnerDatabase

/-- The dependency restriction at the A/B cut. A clause may use a parent of
the same owner. A target-side clause may additionally consume a source-owned
parent, but only when that parent is shared. -/
def ParentAllowed (sig : ColoredSignature 2) (source : Fin 2)
    (resultOwner parentOwner : Fin 2)
    (parent : Clause sig) : Prop :=
  parentOwner = resultOwner ∨
    (resultOwner = source.rev ∧ parentOwner = source ∧
      Clause.IsShared sig 0 parent)

private theorem fin_two_eq_zero_or_one (side : Fin 2) :
    side = 0 ∨ side = 1 := by
  refine Fin.cases (Or.inl rfl) ?_ side
  intro predecessor
  have equal : predecessor = 0 := Subsingleton.elim _ _
  subst predecessor
  exact Or.inr rfl

theorem fin_two_ne_rev (side : Fin 2) : side ≠ side.rev := by
  rcases fin_two_eq_zero_or_one side with equal | equal
  · subst side
    decide
  · subst side
    decide

theorem fin_two_eq_or_eq_rev (owner source : Fin 2) :
    owner = source ∨ owner = source.rev := by
  rcases fin_two_eq_zero_or_one owner with ownerEqual | ownerEqual <;>
    rcases fin_two_eq_zero_or_one source with sourceEqual | sourceEqual
  · exact Or.inl (ownerEqual.trans sourceEqual.symm)
  · right
    subst owner
    subst source
    rfl
  · right
    subst owner
    subst source
    rfl
  · exact Or.inl (ownerEqual.trans sourceEqual.symm)

theorem parent_eq_source_of_result_source
    (allowed : ParentAllowed sig source source parentOwner parent) :
    parentOwner = source := by
  rcases allowed with equal | ⟨impossible, _, _⟩
  · exact equal
  · exact False.elim (fin_two_ne_rev source impossible)

theorem parent_of_result_other
    (allowed : ParentAllowed sig source source.rev parentOwner parent) :
    parentOwner = source.rev ∨
      (parentOwner = source ∧ Clause.IsShared sig 0 parent) := by
  rcases allowed with equal | ⟨_, ownerEqual, shared⟩
  · exact Or.inl equal
  · exact Or.inr ⟨ownerEqual, shared⟩

/-- A coloring witness parallel to an LRAT trace. Theory leaves retain their
explicit proof owner. Ordinary and learned clauses are colorable in their
owning partition, and learned-clause dependencies obey the shared-interface
restriction. -/
inductive ColorableClauseTrace
    {sig : ColoredSignature 2} (inputs : ColoredCNF sig)
    (source : Fin 2) :
    {clauses : CNF sig} →
    (trace : ClauseTrace (ColoredProofLeaf inputs) clauses) →
    ClauseOwnerDatabase clauses → Type 1 where
  | empty : ColorableClauseTrace inputs source .empty
      ClauseOwnerDatabase.empty
  | addInput
      {available : CNF sig}
      {trace : ClauseTrace (ColoredProofLeaf inputs) available}
      {owners : ClauseOwnerDatabase available}
      (previous : ColorableClauseTrace inputs source trace owners)
      (owner : Fin 2) {clause : Clause sig}
      (member : clause ∈ inputs.part owner) :
      ColorableClauseTrace inputs source
        (.addLeaf trace (.input owner member)) (owners.snoc owner)
  | addTheory
      {available : CNF sig}
      {trace : ClauseTrace (ColoredProofLeaf inputs) available}
      {owners : ClauseOwnerDatabase available}
      (previous : ColorableClauseTrace inputs source trace owners)
      (owner : Fin 2) (lemma : TheoryLemma sig) :
      ColorableClauseTrace inputs source
        (.addLeaf trace (.theory owner lemma))
        (owners.snoc owner)
  | addDerived
      {available : CNF sig}
      {trace : ClauseTrace (ColoredProofLeaf inputs) available}
      {owners : ClauseOwnerDatabase available}
      (previous : ColorableClauseTrace inputs source trace owners)
      {clause : Clause sig}
      (justification : ChainJustification available clause)
      (owner : Fin 2)
      (clauseColor : Clause.IsColor sig owner clause)
      (anchorAllowed : ParentAllowed sig source owner
        (owners justification.anchor)
        (available.get justification.anchor))
      (parentsAllowed : justification.chain.ParentsSatisfy fun parent =>
        ParentAllowed sig source owner (owners parent)
          (available.get parent)) :
      ColorableClauseTrace inputs source
        (.addDerived trace justification) (owners.snoc owner)

/-- Semantic consequence associated with one owned trace clause relative to a
fixed shared interface. -/
structure OwnedClauseEntailment (inputs : ColoredCNF sig)
    (source owner : Fin 2) (interface : CNF sig)
    (clause : Clause sig) : Prop where
  fromSource : owner = source →
    (inputs.part source).EntailsClause clause
  fromTarget : owner = source.rev →
    (interface ++ inputs.part source.rev).EntailsClause clause

abbrev OwnedEntailmentDatabase (inputs : ColoredCNF sig)
    (source : Fin 2) (interface : CNF sig)
    (clauses : CNF sig)
    (owners : ClauseOwnerDatabase clauses) :=
  ∀ index : Fin clauses.length,
    OwnedClauseEntailment inputs source (owners index) interface
      (clauses.get index)

namespace OwnedEntailmentDatabase

def empty (inputs : ColoredCNF sig) (source : Fin 2)
    (interface : CNF sig) :
    OwnedEntailmentDatabase inputs source interface []
      ClauseOwnerDatabase.empty :=
  fun index => nomatch index

def snoc
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {source : Fin 2} {interface clauses : CNF sig}
    {owners : ClauseOwnerDatabase clauses}
    (database : OwnedEntailmentDatabase inputs source interface clauses owners)
    {clause : Clause sig} {owner : Fin 2}
    (entailment : OwnedClauseEntailment inputs source owner interface clause) :
    OwnedEntailmentDatabase inputs source interface (clauses ++ [clause])
      (owners.snoc owner) := by
  intro index
  by_cases previousPosition : index.val < clauses.length
  · let previous : Fin clauses.length := ⟨index.val, previousPosition⟩
    have ownerEqual : owners.snoc owner index = owners previous := by
      simpa only [previous] using
        ClauseOwnerDatabase.snoc_previous
          (clause := clause) owners owner previous
    have clauseEqual : (clauses ++ [clause]).get index =
        clauses.get previous := by
      simp [previous, List.get_eq_getElem,
        List.getElem_append_left previousPosition]
    rw [ownerEqual, clauseEqual]
    exact database previous
  · have atLast : index.val = clauses.length :=
      Nat.eq_of_lt_succ_of_not_lt (by simpa using index.isLt)
        previousPosition
    have indexEqual : index = ⟨clauses.length, by simp⟩ := Fin.ext atLast
    subst index
    simpa only [ClauseOwnerDatabase.snoc_last, List.get_eq_getElem,
      List.getElem_concat_length] using entailment

end OwnedEntailmentDatabase

namespace OwnedClauseEntailment

def ofInput (inputs : ColoredCNF sig) (source owner : Fin 2)
    (interface : CNF sig)
    (member : clause ∈ inputs.part owner) :
    OwnedClauseEntailment inputs source owner interface clause where
  fromSource := by
    intro equal interpretation satisfiesSource
    subst owner
    exact satisfiesSource clause member
  fromTarget := by
    intro equal interpretation satisfiesTarget
    subst owner
    exact ((CNF.satisfied_append_iff interpretation _ _).mp
      satisfiesTarget).2 clause member

def ofTheory (inputs : ColoredCNF sig) (source owner : Fin 2)
    (interface : CNF sig) (valid : Clause.Valid clause) :
    OwnedClauseEntailment inputs source owner interface clause where
  fromSource := fun _ interpretation _ => valid interpretation
  fromTarget := fun _ interpretation _ => valid interpretation

/-- Semantic pruning step for a learned clause. Only the parents referenced by
the explicit chain are used. Shared source parents are read from the interface
when proving a target-owned result. -/
def ofDerived
    {sig : ColoredSignature 2} (inputs : ColoredCNF sig)
    (source owner : Fin 2) (interface : CNF sig)
    {available : CNF sig}
    (owners : ClauseOwnerDatabase available)
    (database : OwnedEntailmentDatabase inputs source interface
      available owners)
    {clause : Clause sig}
    (justification : ChainJustification available clause)
    (anchorAllowed : ParentAllowed sig source owner
      (owners justification.anchor)
      (available.get justification.anchor))
    (parentsAllowed : justification.chain.ParentsSatisfy fun parent =>
      ParentAllowed sig source owner (owners parent)
        (available.get parent))
    (containsSharedSource : ∀ index : Fin available.length,
      owners index = source →
      Clause.IsShared sig 0 (available.get index) →
      available.get index ∈ interface) :
    OwnedClauseEntailment inputs source owner interface clause where
  fromSource := by
    intro ownerEqual interpretation satisfiesSource
    have satisfiesParent : ∀ index,
        ParentAllowed sig source owner (owners index)
          (available.get index) →
        Clause.Satisfied interpretation (available.get index) := by
      intro index allowed
      apply (database index).fromSource
        (by simpa [ownerEqual] using
          parent_eq_source_of_result_source (by
            simpa [ownerEqual] using allowed))
      exact satisfiesSource
    have satisfiesAnchor := satisfiesParent justification.anchor anchorAllowed
    exact ResolutionChain.sound_of_parents parentsAllowed interpretation
      satisfiesAnchor satisfiesParent
  fromTarget := by
    intro ownerEqual interpretation satisfiesTarget
    have targetParts :=
      (CNF.satisfied_append_iff interpretation _ _).mp satisfiesTarget
    have satisfiesParent : ∀ index,
        ParentAllowed sig source owner (owners index)
          (available.get index) →
        Clause.Satisfied interpretation (available.get index) := by
      intro index allowed
      have classified := parent_of_result_other (by
        simpa [ownerEqual] using allowed)
      rcases classified with targetOwned | ⟨sourceOwned, shared⟩
      · apply (database index).fromTarget targetOwned
        exact satisfiesTarget
      · exact targetParts.1 _
          (containsSharedSource index sourceOwned shared)
    have satisfiesAnchor := satisfiesParent justification.anchor anchorAllowed
    exact ResolutionChain.sound_of_parents parentsAllowed interpretation
      satisfiesAnchor satisfiesParent

end OwnedClauseEntailment

/-- Incremental semantic pruning proof for a colorable trace and a fixed
interface. Each derived step supplies the fact that every shared source parent
it may cross is present in that interface. -/
inductive ColorableTraceEntailment
    {sig : ColoredSignature 2} (inputs : ColoredCNF sig)
    (source : Fin 2) (interface : CNF sig) :
    {clauses : CNF sig} →
    {trace : ClauseTrace (ColoredProofLeaf inputs) clauses} →
    {owners : ClauseOwnerDatabase clauses} →
    (coloring : ColorableClauseTrace inputs source trace owners) →
    OwnedEntailmentDatabase inputs source interface clauses owners → Type 1 where
  | empty : ColorableTraceEntailment inputs source interface .empty
      (OwnedEntailmentDatabase.empty inputs source interface)
  | addInput
      {available : CNF sig}
      {trace : ClauseTrace (ColoredProofLeaf inputs) available}
      {owners : ClauseOwnerDatabase available}
      {coloring : ColorableClauseTrace inputs source trace owners}
      {database : OwnedEntailmentDatabase inputs source interface
        available owners}
      (previous : ColorableTraceEntailment inputs source interface
        coloring database)
      (owner : Fin 2) {clause : Clause sig}
      (member : clause ∈ inputs.part owner) :
      ColorableTraceEntailment inputs source interface
        (.addInput coloring owner member)
        (database.snoc
          (OwnedClauseEntailment.ofInput inputs source owner interface member))
  | addTheory
      {available : CNF sig}
      {trace : ClauseTrace (ColoredProofLeaf inputs) available}
      {owners : ClauseOwnerDatabase available}
      {coloring : ColorableClauseTrace inputs source trace owners}
      {database : OwnedEntailmentDatabase inputs source interface
        available owners}
      (previous : ColorableTraceEntailment inputs source interface
        coloring database)
      (owner : Fin 2) (lemma : TheoryLemma sig) :
      ColorableTraceEntailment inputs source interface
        (.addTheory coloring owner lemma)
        (database.snoc (OwnedClauseEntailment.ofTheory inputs source
          owner interface lemma.valid))
  | addDerived
      {available : CNF sig}
      {trace : ClauseTrace (ColoredProofLeaf inputs) available}
      {owners : ClauseOwnerDatabase available}
      {coloring : ColorableClauseTrace inputs source trace owners}
      {database : OwnedEntailmentDatabase inputs source interface
        available owners}
      (previous : ColorableTraceEntailment inputs source interface
        coloring database)
      {clause : Clause sig}
      (justification : ChainJustification available clause)
      (owner : Fin 2)
      (clauseColor : Clause.IsColor sig owner clause)
      (anchorAllowed : ParentAllowed sig source owner
        (owners justification.anchor)
        (available.get justification.anchor))
      (parentsAllowed : justification.chain.ParentsSatisfy fun parent =>
        ParentAllowed sig source owner (owners parent)
          (available.get parent))
      (containsSharedSource : ∀ index : Fin available.length,
        owners index = source →
        Clause.IsShared sig 0 (available.get index) →
        available.get index ∈ interface) :
      ColorableTraceEntailment inputs source interface
        (.addDerived coloring justification owner clauseColor
          anchorAllowed parentsAllowed)
        (database.snoc (OwnedClauseEntailment.ofDerived inputs source owner
          interface owners database justification anchorAllowed parentsAllowed
          containsSharedSource))

/-- Every shared source-owned clause in a database occurs in the proposed
interface. -/
def SharedSourceCovered
    {sig : ColoredSignature 2} (source : Fin 2)
    (clauses : CNF sig)
    (owners : ClauseOwnerDatabase clauses)
    (interface : CNF sig) : Prop :=
  ∀ index : Fin clauses.length,
    owners index = source →
    Clause.IsShared sig 0 (clauses.get index) →
    clauses.get index ∈ interface

namespace SharedSourceCovered

/-- Coverage of a snoc database restricts to its previous prefix. -/
theorem previous
    {sig : ColoredSignature 2} {source : Fin 2}
    {clauses interface : CNF sig}
    {owners : ClauseOwnerDatabase clauses}
    {clause : Clause sig} {owner : Fin 2}
    (covered : SharedSourceCovered source (clauses ++ [clause])
      (owners.snoc owner) interface) :
    SharedSourceCovered source clauses owners interface := by
  intro index sourceOwned shared
  let lifted : Fin (clauses ++ [clause]).length :=
    ⟨index.val, by
      simpa only [List.length_append, List.length_singleton] using
        Nat.lt_succ_of_lt index.isLt⟩
  have liftedOwner : owners.snoc owner lifted = owners index := by
    simpa only [lifted] using
      ClauseOwnerDatabase.snoc_previous
        (clause := clause) owners owner index
  have liftedClause : (clauses ++ [clause]).get lifted =
      clauses.get index := by
    simp [lifted, List.get_eq_getElem,
      List.getElem_append_left index.isLt]
  have member := covered lifted (by
      rw [liftedOwner]
      exact sourceOwned) (by
      rw [liftedClause]
      exact shared)
  rw [liftedClause] at member
  exact member

end SharedSourceCovered

/-- The entailment database produced by traversing a colorable trace. -/
structure TraceEntailmentConstruction
    {sig : ColoredSignature 2} (inputs : ColoredCNF sig)
    (source : Fin 2) (interface : CNF sig)
    {clauses : CNF sig}
    {trace : ClauseTrace (ColoredProofLeaf inputs) clauses}
    {owners : ClauseOwnerDatabase clauses}
    (coloring : ColorableClauseTrace inputs source trace owners) where
  database : OwnedEntailmentDatabase inputs source interface clauses owners
  correct : ColorableTraceEntailment inputs source interface coloring database

namespace ColorableClauseTrace

/-- Traverse the explicit LRAT-like trace and retain only the side-relative
semantic consequence associated with each owned clause. -/
noncomputable def buildEntailment
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {source : Fin 2} {clauses : CNF sig}
    {trace : ClauseTrace (ColoredProofLeaf inputs) clauses}
    {owners : ClauseOwnerDatabase clauses}
    (coloring : ColorableClauseTrace inputs source trace owners)
    (interface : CNF sig)
    (covered : SharedSourceCovered source clauses owners interface) :
    TraceEntailmentConstruction inputs source interface coloring := by
  induction coloring with
  | empty =>
      exact
        { database := OwnedEntailmentDatabase.empty inputs source interface
          correct := .empty }
  | addInput previous owner member inductionHypothesis =>
      let prior := inductionHypothesis covered.previous
      exact
        { database := prior.database.snoc
            (OwnedClauseEntailment.ofInput inputs source owner interface member)
          correct := .addInput prior.correct owner member }
  | addTheory previous owner lemma inductionHypothesis =>
      let prior := inductionHypothesis covered.previous
      exact
        { database := prior.database.snoc
            (OwnedClauseEntailment.ofTheory inputs source owner
              interface lemma.valid)
          correct := .addTheory prior.correct owner lemma }
  | addDerived previous justification owner clauseColor anchorAllowed
      parentsAllowed inductionHypothesis =>
      let prior := inductionHypothesis covered.previous
      exact
        { database := prior.database.snoc
            (OwnedClauseEntailment.ofDerived inputs source owner interface _
              prior.database justification anchorAllowed parentsAllowed
              covered.previous)
          correct := .addDerived prior.correct justification owner clauseColor
            anchorAllowed parentsAllowed covered.previous }

end ColorableClauseTrace

/-- A proof-relevant selection of the shared source clauses forming the cut.
It contains every shared source-owned trace clause and no unrelated clauses. -/
structure SharedInterfaceSelection
    {sig : ColoredSignature 2} (source : Fin 2)
    (clauses : CNF sig)
    (owners : ClauseOwnerDatabase clauses) where
  interface : CNF sig
  interface_shared : CNF.IsShared sig 0 interface
  selected_from_source : ∀ clause, clause ∈ interface →
    { index : Fin clauses.length //
      clauses.get index = clause ∧ owners index = source }
  contains_shared_source : ∀ index : Fin clauses.length,
    owners index = source →
    Clause.IsShared sig 0 (clauses.get index) →
    clauses.get index ∈ interface

namespace SharedInterfaceSelection

/-- Select every shared source-owned occurrence in a finite trace. This is
noncomputable only because signatures intentionally carry no decidable
equality or executable color checker; the selected index list itself is
finite and fixed once the trace has been built. -/
noncomputable def allSharedSource
    {sig : ColoredSignature 2} (source : Fin 2)
    (clauses : CNF sig)
    (owners : ClauseOwnerDatabase clauses) :
    SharedInterfaceSelection source clauses owners := by
  classical
  let selected := (List.finRange clauses.length).filter fun index =>
    owners index = source ∧ Clause.IsShared sig 0 (clauses.get index)
  refine
    { interface := selected.map clauses.get
      interface_shared := ?_
      selected_from_source := ?_
      contains_shared_source := ?_ }
  · intro clause member
    obtain ⟨index, indexMember, rfl⟩ := List.mem_map.mp member
    have properties : owners index = source ∧
        Clause.IsShared sig 0 (clauses.get index) := by
      simpa [selected] using indexMember
    exact properties.2
  · intro clause member
    let index := Classical.choose (List.mem_map.mp member)
    have indexProperties := Classical.choose_spec (List.mem_map.mp member)
    have selectedProperties : owners index = source ∧
        Clause.IsShared sig 0 (clauses.get index) := by
      simpa [selected, index] using indexProperties.1
    exact ⟨index, indexProperties.2, selectedProperties.1⟩
  · intro index owner shared
    apply List.mem_map.mpr
    refine ⟨index, ?_, rfl⟩
    have properties : owners index = source ∧
        Clause.IsShared sig 0 (clauses.get index) := ⟨owner, shared⟩
    simpa [selected] using properties

end SharedInterfaceSelection

/-- A colorable refutation together with its incrementally checked semantic
pruning database. Unlike `PrunedColorableTrace`, this certificate does not
rebuild two separate resolution traces: it records exactly the entailment
needed on each side of the shared cut. -/
structure SemanticallyPrunedColorableTrace
    {sig : ColoredSignature 2} (inputs : ColoredCNF sig)
    (source : Fin 2)
    {clauses : CNF sig}
    {trace : ClauseTrace (ColoredProofLeaf inputs) clauses}
    {owners : ClauseOwnerDatabase clauses}
    (coloring : ColorableClauseTrace inputs source trace owners) where
  selection : SharedInterfaceSelection source clauses owners
  database : OwnedEntailmentDatabase inputs source selection.interface
    clauses owners
  construction : ColorableTraceEntailment inputs source selection.interface
    coloring database
  contradiction : (Clausal.Clause.empty : Clause sig) ∈ clauses

namespace SemanticallyPrunedColorableTrace

variable {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
  {source : Fin 2} {clauses : CNF sig}
  {trace : ClauseTrace (ColoredProofLeaf inputs) clauses}
  {owners : ClauseOwnerDatabase clauses}
  {coloring : ColorableClauseTrace inputs source trace owners}

theorem side_entails
    (pruned : SemanticallyPrunedColorableTrace inputs source coloring) :
    ∀ interpretation : Interpretation sig,
      CNF.Satisfied interpretation (inputs.part source) →
      CNF.Satisfied interpretation pruned.selection.interface := by
  intro interpretation satisfiesSource clause member
  obtain ⟨index, equal, owner⟩ :=
    pruned.selection.selected_from_source clause member
  rw [← equal]
  exact (pruned.database index).fromSource owner interpretation
    satisfiesSource

theorem interface_other_unsatisfiable
    (pruned : SemanticallyPrunedColorableTrace inputs source coloring) :
    ¬∃ interpretation : Interpretation sig,
      CNF.Satisfied interpretation pruned.selection.interface ∧
      CNF.Satisfied interpretation (inputs.part source.rev) := by
  rintro ⟨interpretation, satisfiesInterface, satisfiesOther⟩
  obtain ⟨index, emptyEqual⟩ := List.get_of_mem pruned.contradiction
  have satisfiesTarget :
      CNF.Satisfied interpretation
        (pruned.selection.interface ++ inputs.part source.rev) :=
    (CNF.satisfied_append_iff interpretation _ _).mpr
      ⟨satisfiesInterface, satisfiesOther⟩
  rcases fin_two_eq_or_eq_rev (owners index) source with
      sourceOwned | targetOwned
  · have emptyShared : Clause.IsShared sig 0 (clauses.get index) := by
      rw [emptyEqual]
      intro literal member
      exact nomatch member
    have emptyMember := pruned.selection.contains_shared_source index
      sourceOwned emptyShared
    have satisfiesEmpty := satisfiesInterface _ emptyMember
    rw [emptyEqual] at satisfiesEmpty
    exact Clause.not_satisfied_nil interpretation satisfiesEmpty
  · have satisfiesEmpty := (pruned.database index).fromTarget targetOwned
      interpretation satisfiesTarget
    rw [emptyEqual] at satisfiesEmpty
    exact Clause.not_satisfied_nil interpretation satisfiesEmpty

theorem inputs_unsatisfiable
    (pruned : SemanticallyPrunedColorableTrace inputs source coloring) :
    inputs.Unsatisfiable := by
  rintro ⟨interpretation, satisfiesInputs⟩
  apply pruned.interface_other_unsatisfiable
  exact ⟨interpretation,
    pruned.side_entails interpretation (satisfiesInputs source),
    satisfiesInputs source.rev⟩

/-- Semantic pruning of a colorable LRAT-like refutation yields a clausal
Craig interpolant: the conjunction of the selected shared source clauses. -/
def interpolant
    (pruned : SemanticallyPrunedColorableTrace inputs source coloring) :
    IsClausalInterpolantAt inputs source
      pruned.selection.interface where
  inputs_unsatisfiable := pruned.inputs_unsatisfiable
  interpolant_shared := pruned.selection.interface_shared
  side_entails := pruned.side_entails
  interpolant_other_unsatisfiable :=
    pruned.interface_other_unsatisfiable

end SemanticallyPrunedColorableTrace

namespace ColorableClauseTrace

/-- Perform the finite shared-interface selection and semantic pruning pass
for a colorable trace containing the empty clause. -/
noncomputable def prune
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {source : Fin 2} {clauses : CNF sig}
    {trace : ClauseTrace (ColoredProofLeaf inputs) clauses}
    {owners : ClauseOwnerDatabase clauses}
    (coloring : ColorableClauseTrace inputs source trace owners)
    (contradiction : (Clausal.Clause.empty : Clause sig) ∈ clauses) :
    SemanticallyPrunedColorableTrace inputs source coloring := by
  let selection := SharedInterfaceSelection.allSharedSource source clauses owners
  let construction := coloring.buildEntailment selection.interface
    selection.contains_shared_source
  exact
    { selection := selection
      database := construction.database
      construction := construction.correct
      contradiction := contradiction }

/-- The complete soundness endpoint of the colorable-proof procedure. -/
noncomputable def interpolantOfRefutation
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {source : Fin 2} {clauses : CNF sig}
    {trace : ClauseTrace (ColoredProofLeaf inputs) clauses}
    {owners : ClauseOwnerDatabase clauses}
    (coloring : ColorableClauseTrace inputs source trace owners)
    (contradiction : (Clausal.Clause.empty : Clause sig) ∈ clauses) :
    IsClausalInterpolantAt inputs source
      (coloring.prune contradiction).selection.interface :=
  (coloring.prune contradiction).interpolant

end ColorableClauseTrace

/-- A refutation whose clauses and explicit dependencies satisfy the
two-color cut discipline. -/
structure ColorableClauseRefutation
    {sig : ColoredSignature 2} (inputs : ColoredCNF sig)
    (source : Fin 2) where
  refutation : ClauseRefutation (ColoredProofLeaf inputs)
  owners : ClauseOwnerDatabase refutation.clauses
  coloring : ColorableClauseTrace inputs source refutation.trace owners

namespace ColorableClauseRefutation

variable {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
  {source : Fin 2}

noncomputable def prune
    (refutation : ColorableClauseRefutation inputs source) :
    SemanticallyPrunedColorableTrace inputs source refutation.coloring :=
  refutation.coloring.prune refutation.refutation.contradiction

/-- The finite conjunction of all shared source-owned clauses selected from
the refutation. -/
noncomputable def interface
    (refutation : ColorableClauseRefutation inputs source) :
    CNF sig :=
  refutation.prune.selection.interface

/-- A bundled colorable EUF refutation computes a sound clausal Craig
interpolant at the requested color cut. -/
noncomputable def interpolant
    (refutation : ColorableClauseRefutation inputs source) :
    IsClausalInterpolantAt inputs source refutation.interface := by
  unfold interface
  exact refutation.prune.interpolant

end ColorableClauseRefutation

/-- Output of pruning a colorable LRAT trace at its shared A/B cut. Source
nodes retain explicit source-only derivations; the target slice becomes a
refutation whose additional inputs are precisely the selected interface. -/
structure PrunedColorableTrace
    {sig : ColoredSignature 2} (inputs : ColoredCNF sig)
    (source : Fin 2)
    {clauses : CNF sig}
    {trace : ClauseTrace (ColoredProofLeaf inputs) clauses}
    {owners : ClauseOwnerDatabase clauses}
    (coloring : ColorableClauseTrace inputs source trace owners) where
  selection : SharedInterfaceSelection source clauses owners
  sourceDerivation : ∀ index : Fin clauses.length,
    owners index = source →
    ClauseConsequence (inputs.part source) (clauses.get index)
  targetRefutation : ClauseRefutation
    (CNF.InputOrTheory
      (selection.interface ++ inputs.part source.rev))

/-- The semantic cut exposed by a two-color colorable proof.

Every interface clause has an explicit source-side derivation. The target
side, together with those interface clauses, has an explicit refutation. A
trace-coloring pass will construct this certificate by cutting every shared
source clause consumed by target reasoning. -/
structure SharedInterfaceCertificate (inputs : ColoredCNF sig)
    (side : Fin 2) where
  interface : CNF sig
  /-- interface clauses are AB-shared --/
  interface_shared : CNF.IsShared sig 0 interface
  /-- interface clauses are EUF consequences of A-side of inputs --/
  sourceDerivation : ∀ clause, clause ∈ interface →
    ClauseConsequence (inputs.part side) clause
  /-- The interface is inconsistent with the opposite-side inputs in EUF. -/
  targetRefutation :
    ClauseRefutation
      (CNF.InputOrTheory (interface ++ inputs.part side.rev))

namespace PrunedColorableTrace

/-- Forget the pruning bookkeeping and expose the semantic shared cut. -/
def toSharedInterfaceCertificate
    (pruned : PrunedColorableTrace inputs source coloring) :
    SharedInterfaceCertificate inputs source where
  interface := pruned.selection.interface
  interface_shared := pruned.selection.interface_shared
  sourceDerivation := by
    intro clause member
    obtain ⟨index, equal, owner⟩ :=
      pruned.selection.selected_from_source clause member
    exact (pruned.sourceDerivation index owner).castConclusion equal
  targetRefutation := pruned.targetRefutation

end PrunedColorableTrace

namespace SharedInterfaceCertificate

theorem side_entails
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {side : Fin 2}
    (certificate : SharedInterfaceCertificate inputs side) :
    ∀ interpretation : Interpretation sig,
      CNF.Satisfied interpretation (inputs.part side) →
      CNF.Satisfied interpretation certificate.interface := by
  intro interpretation satisfiesSide clause member
  exact (certificate.sourceDerivation clause member).sound
    interpretation satisfiesSide

theorem interface_other_unsatisfiable
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
    {side : Fin 2}
    (certificate : SharedInterfaceCertificate inputs side) :
    ¬∃ interpretation : Interpretation sig,
      CNF.Satisfied interpretation certificate.interface ∧
      CNF.Satisfied interpretation (inputs.part side.rev) := by
  rintro ⟨interpretation, satisfiesInterface, satisfiesOther⟩
  have targetUnsatisfiable :
      CNF.Unsatisfiable
        (certificate.interface ++ inputs.part side.rev) :=
    CNF.unsatisfiable_of_refutation certificate.targetRefutation
  apply targetUnsatisfiable
  exact ⟨interpretation,
    (CNF.satisfied_append_iff interpretation _ _).mpr
      ⟨satisfiesInterface, satisfiesOther⟩⟩

theorem inputs_unsatisfiable
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
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
    {sig : ColoredSignature 2} {inputs : ColoredCNF sig}
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
