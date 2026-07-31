import Std
import EufItpLean.AbstractCongruenceClosure
import EufItpLean.Interpolation

namespace EUF

/-- The side that produced an equality during cooperative congruence closure. -/
inductive InterpolationSide where
  | A
  | B
  deriving DecidableEq

namespace InterpolationSide

def other : InterpolationSide → InterpolationSide
  | .A => .B
  | .B => .A

@[simp]
theorem other_A : other .A = .B := rfl

@[simp]
theorem other_B : other .B = .A := rfl

def formula (side : InterpolationSide)
    (phiA phiB : Formula signature) : Formula signature :=
  match side with
  | .A => phiA
  | .B => phiB

end InterpolationSide

/-- The immutable finite extension used throughout an interpolation run. Every
abstract name has a chosen original-term representative, used to translate
internal shared edges back into interpolant atoms. -/
structure FiniteNameBasis (colored : ColoredSignature 2) where
  Name : Type
  names : List Name
  complete : ∀ name, name ∈ names
  representative : Name → Term colored.toSignature

namespace FiniteNameBasis

/-- The finite universe of directed abstract equality edges. Alternating
saturation may add members of this list but cannot enlarge it. -/
def edgePairs (basis : FiniteNameBasis colored) :
    List (basis.Name × basis.Name) :=
  basis.names.flatMap (fun left =>
    basis.names.map (fun right => (left, right)))

theorem mem_edgePairs (basis : FiniteNameBasis colored)
    (left right : basis.Name) :
    (left, right) ∈ basis.edgePairs := by
  simp [edgePairs, basis.complete]

/-- The fixed representatives agree with the names used by an abstract rewrite
system. -/
def RealizedBy (basis : FiniteNameBasis colored)
    (system : AbstractRewriteSystem colored.toSignature basis.Name) : Prop :=
  ∀ name, system.Represents name (basis.representative name)

end FiniteNameBasis

/-- A shared equality edge in the fixed abstract signature. -/
structure SharedEqualityEdge (colored : ColoredSignature 2)
    (basis : FiniteNameBasis colored) where
  left : basis.Name
  right : basis.Name
  isShared : Equality.IsShared colored 0
    ⟨basis.representative left, basis.representative right⟩

namespace SharedEqualityEdge

def equality (edge : SharedEqualityEdge colored basis) :
    Equality colored.toSignature :=
  ⟨basis.representative edge.left, basis.representative edge.right⟩

def literal (edge : SharedEqualityEdge colored basis) :
    Literal colored.toSignature :=
  edge.equality.literal

end SharedEqualityEdge

mutual

  /-- A proof-producing communication step. An equality produced by one side
  is derived from that side's input formula and finitely many shared equalities
  previously produced by the other side. -/
  inductive EqualityExchangeProof (colored : ColoredSignature 2)
      (basis : FiniteNameBasis colored)
      (phiA phiB : Formula colored.toSignature) :
      InterpolationSide → SharedEqualityEdge colored basis → Type where
    | derive (side : InterpolationSide)
        (edge : SharedEqualityEdge colored basis)
        (premises : Formula colored.toSignature)
        (dependencies : EqualityExchangeDependencies
          colored basis phiA phiB side.other premises)
        (derivation : DerivesEq
          (side.formula phiA phiB ++ premises)
          edge.equality.left edge.equality.right) :
        EqualityExchangeProof colored basis phiA phiB side edge

  /-- A finite list of communicated equality proofs, indexed by the formula of
  equality literals that they supply to the receiving closure. -/
  inductive EqualityExchangeDependencies (colored : ColoredSignature 2)
      (basis : FiniteNameBasis colored)
      (phiA phiB : Formula colored.toSignature) :
      InterpolationSide → Formula colored.toSignature → Type where
    | nil (side : InterpolationSide) :
        EqualityExchangeDependencies colored basis phiA phiB side []
    | cons {side : InterpolationSide} {edge : SharedEqualityEdge colored basis}
        {premises : Formula colored.toSignature}
        (head : EqualityExchangeProof colored basis phiA phiB side edge)
        (tail : EqualityExchangeDependencies colored basis phiA phiB side premises) :
        EqualityExchangeDependencies colored basis phiA phiB side
          (edge.literal :: premises)

end

namespace EqualityExchangeProof

def producedEquality
    (_proof : EqualityExchangeProof colored basis phiA phiB side edge) :
    Equality colored.toSignature :=
  edge.equality

/-- Build a communication step from an edge recognized by an abstract
congruence closure over the same fixed name basis. No signature extension takes
place here: the edge endpoints are existing names in `basis`. -/
def ofAbstractClosure
    (system : AbstractRewriteSystem colored.toSignature basis.Name)
    (realized : basis.RealizedBy system)
    (edge : SharedEqualityEdge colored basis)
    (premises : Formula colored.toSignature)
    (dependencies : EqualityExchangeDependencies
      colored basis phiA phiB side.other premises)
    (closure : AbstractCongruenceClosure
      (side.formula phiA phiB ++ premises) system)
    (edgeJoinable : system.Joinable
      (ExtendedSignature.constant edge.left)
      (ExtendedSignature.constant edge.right)) :
    EqualityExchangeProof colored basis phiA phiB side edge := by
  have leftEquivalent := realized edge.left
  have rightEquivalent := realized edge.right
  have namesEquivalent :=
    AbstractRewriteSystem.equivalent_of_joinable edgeJoinable
  have representativesEquivalent : system.Equivalent
      (ExtendedSignature.term (basis.representative edge.left))
      (ExtendedSignature.term (basis.representative edge.right)) :=
    leftEquivalent.trans (namesEquivalent.trans rightEquivalent.symm)
  have representativesJoinable :=
    AbstractRewriteSystem.joinable_of_equivalent closure.ground_convergent.2
      representativesEquivalent
  exact .derive side edge premises dependencies
    ((closure.conservative _ _).mpr representativesJoinable)

/-- The Horn clause contributed by an A-produced equality. -/
def justification (edge : SharedEqualityEdge colored basis)
    (premises : List (Equality colored.toSignature)) :
    EqualityHornClause colored.toSignature where
  premises := premises
  conclusion := some edge.equality

end EqualityExchangeProof

namespace EqualityExchangeDependencies

def equalities :
    EqualityExchangeDependencies colored basis phiA phiB side premises →
      List (Equality colored.toSignature)
  | .nil _ => []
  | .cons head tail => head.producedEquality :: equalities tail

theorem literals_equalities
    : (dependencies : EqualityExchangeDependencies
        colored basis phiA phiB side premises) →
      dependencies.equalities.map Equality.literal = premises
  | .nil _ => rfl
  | @EqualityExchangeDependencies.cons _ _ _ _ _ edge _ head tail => by
      simp only [equalities, EqualityExchangeProof.producedEquality,
        SharedEqualityEdge.equality, Equality.literal,
        SharedEqualityEdge.literal]
      exact congrArg (edge.literal :: ·) (literals_equalities tail)

theorem satisfies_of_equalities
    (dependencies : EqualityExchangeDependencies
      colored basis phiA phiB side premises)
    (interpretation : Interpretation colored.toSignature)
    (satisfies : ∀ equality ∈ dependencies.equalities,
      equality.Satisfied interpretation) :
    Satisfies interpretation premises := by
  rw [← dependencies.literals_equalities]
  exact (satisfies_equality_literals interpretation dependencies.equalities).mpr
    satisfies

theorem equalities_shared :
    (dependencies : EqualityExchangeDependencies
      colored basis phiA phiB side premises) →
    ∀ equality ∈ dependencies.equalities,
      equality.IsShared colored 0
  | .nil _, _, member => nomatch member
  | @EqualityExchangeDependencies.cons _ _ _ _ _ edge _ head tail,
      equality, member => by
      simp only [equalities, List.mem_cons] at member
      rcases member with equal | member
      · subst equality
        exact edge.isShared
      · exact equalities_shared tail equality member

end EqualityExchangeDependencies

mutual

  /-- Recursively collect all A-justifications needed for an exchanged
  equality. B-produced nodes contribute no clause of their own. -/
  def EqualityExchangeProof.interpolant :
      EqualityExchangeProof colored basis phiA phiB side edge →
        EqualityHornFormula colored.toSignature
    | .derive side edge _ dependencies _ =>
        dependencies.interpolant ++
        match side with
        | .A =>
            [EqualityExchangeProof.justification edge dependencies.equalities]
        | .B => []

  def EqualityExchangeDependencies.interpolant :
      EqualityExchangeDependencies colored basis phiA phiB side premises →
        EqualityHornFormula colored.toSignature
    | .nil _ => []
    | .cons head tail => head.interpolant ++ tail.interpolant

end

theorem EqualityExchangeProof.interpolant_entailed_by_A
    (proof : EqualityExchangeProof colored basis phiA phiB side edge) :
    EntailsEqualityHornFormula phiA proof.interpolant := by
  refine EqualityExchangeProof.rec
    (motive_2 := fun _ _ dependencies =>
      EntailsEqualityHornFormula phiA dependencies.interpolant)
    ?_ ?_ ?_ proof
  · intro producer produced premises dependencies derivation dependenciesIH
    intro interpretation satisfiesA
    apply (EqualityHornFormula.satisfies_append interpretation _ _).mpr
    constructor
    · exact dependenciesIH interpretation satisfiesA
    · cases producer with
      | B => exact EqualityHornFormula.satisfies_nil interpretation
      | A =>
        apply (EqualityHornFormula.satisfies_singleton interpretation _).mpr
        intro satisfiesEqualities
        have satisfiesPremises : Satisfies interpretation premises :=
          dependencies.satisfies_of_equalities interpretation satisfiesEqualities
        exact derivation.sound
          ((satisfies_append interpretation phiA premises).mpr
            ⟨satisfiesA, satisfiesPremises⟩)
  · intro _ interpretation _
    exact EqualityHornFormula.satisfies_nil interpretation
  · intro _ _ _ _ _ headIH tailIH interpretation satisfiesA
    exact (EqualityHornFormula.satisfies_append interpretation _ _).mpr
      ⟨headIH interpretation satisfiesA, tailIH interpretation satisfiesA⟩

theorem EqualityExchangeDependencies.interpolant_entailed_by_A
    (dependencies : EqualityExchangeDependencies
      colored basis phiA phiB side premises) :
    EntailsEqualityHornFormula phiA dependencies.interpolant := by
  refine EqualityExchangeDependencies.rec
    (motive_1 := fun _ _ proof =>
      EntailsEqualityHornFormula phiA proof.interpolant)
    ?_ ?_ ?_ dependencies
  · intro producer produced localPremises localDependencies derivation dependenciesIH
    intro interpretation satisfiesA
    apply (EqualityHornFormula.satisfies_append interpretation _ _).mpr
    constructor
    · exact dependenciesIH interpretation satisfiesA
    · cases producer with
      | B => exact EqualityHornFormula.satisfies_nil interpretation
      | A =>
        apply (EqualityHornFormula.satisfies_singleton interpretation _).mpr
        intro satisfiesEqualities
        have satisfiesPremises : Satisfies interpretation localPremises :=
          localDependencies.satisfies_of_equalities interpretation satisfiesEqualities
        exact derivation.sound
          ((satisfies_append interpretation phiA localPremises).mpr
            ⟨satisfiesA, satisfiesPremises⟩)
  · intro _ interpretation _
    exact EqualityHornFormula.satisfies_nil interpretation
  · intro _ _ _ _ _ headIH tailIH interpretation satisfiesA
    exact (EqualityHornFormula.satisfies_append interpretation _ _).mpr
      ⟨headIH interpretation satisfiesA, tailIH interpretation satisfiesA⟩

theorem EqualityExchangeProof.equality_entailed_by_B
    (proof : EqualityExchangeProof colored basis phiA phiB side edge)
    (interpretation : Interpretation colored.toSignature)
    (satisfiesB : Satisfies interpretation phiB)
    (satisfiesInterpolant :
      SatisfiesEqualityHornFormula interpretation proof.interpolant) :
    edge.equality.Satisfied interpretation := by
  refine EqualityExchangeProof.rec
    (motive_2 := fun _ premises dependencies =>
      ∀ interpretation : Interpretation colored.toSignature,
        Satisfies interpretation phiB →
        SatisfiesEqualityHornFormula interpretation dependencies.interpolant →
        Satisfies interpretation premises)
    ?_ ?_ ?_ proof interpretation satisfiesB satisfiesInterpolant
  · intro producer produced premises dependencies derivation dependenciesIH
      interpretation satisfiesB satisfiesInterpolant
    have parts :=
      (EqualityHornFormula.satisfies_append interpretation _ _).mp
        satisfiesInterpolant
    have satisfiesPremises : Satisfies interpretation premises :=
      dependenciesIH interpretation satisfiesB parts.1
    cases producer with
    | B =>
        exact derivation.sound
          ((satisfies_append interpretation phiB premises).mpr
            ⟨satisfiesB, satisfiesPremises⟩)
    | A =>
        have satisfiesClause :=
          (EqualityHornFormula.satisfies_singleton interpretation _).mp parts.2
        apply satisfiesClause
        exact (satisfies_equality_literals interpretation
          dependencies.equalities).mp (by
            rw [dependencies.literals_equalities]
            exact satisfiesPremises)
  · intro _ interpretation _ _ literal member
    exact nomatch member
  · intro _ edge _ head tail headIH tailIH interpretation satisfiesB
      satisfiesInterpolant
    have parts :=
      (EqualityHornFormula.satisfies_append interpretation _ _).mp
        satisfiesInterpolant
    have headSatisfied := headIH interpretation satisfiesB parts.1
    have tailSatisfied := tailIH interpretation satisfiesB parts.2
    intro literal member
    simp only [List.mem_cons] at member
    rcases member with equal | member
    · subst literal
      exact (head.producedEquality.satisfied_iff_satisfies_literal
        interpretation).mp headSatisfied
    · exact tailSatisfied literal member

theorem EqualityExchangeDependencies.equalities_entailed_by_B
    (dependencies : EqualityExchangeDependencies
      colored basis phiA phiB side premises)
    (interpretation : Interpretation colored.toSignature)
    (satisfiesB : Satisfies interpretation phiB)
    (satisfiesInterpolant :
      SatisfiesEqualityHornFormula interpretation dependencies.interpolant) :
    Satisfies interpretation premises := by
  refine EqualityExchangeDependencies.rec
    (motive_1 := fun _ edge proof =>
      ∀ interpretation : Interpretation colored.toSignature,
        Satisfies interpretation phiB →
        SatisfiesEqualityHornFormula interpretation proof.interpolant →
        edge.equality.Satisfied interpretation)
    ?_ ?_ ?_ dependencies interpretation satisfiesB satisfiesInterpolant
  · intro producer produced localPremises localDependencies derivation dependenciesIH
      interpretation satisfiesB satisfiesInterpolant
    have parts :=
      (EqualityHornFormula.satisfies_append interpretation _ _).mp
        satisfiesInterpolant
    have satisfiesPremises : Satisfies interpretation localPremises :=
      dependenciesIH interpretation satisfiesB parts.1
    cases producer with
    | B =>
        exact derivation.sound
          ((satisfies_append interpretation phiB localPremises).mpr
            ⟨satisfiesB, satisfiesPremises⟩)
    | A =>
        have satisfiesClause :=
          (EqualityHornFormula.satisfies_singleton interpretation _).mp parts.2
        apply satisfiesClause
        exact (satisfies_equality_literals interpretation
          localDependencies.equalities).mp (by
            rw [localDependencies.literals_equalities]
            exact satisfiesPremises)
  · intro _ interpretation _ _ literal member
    exact nomatch member
  · intro _ edge _ head tail headIH tailIH interpretation satisfiesB
      satisfiesInterpolant
    have parts :=
      (EqualityHornFormula.satisfies_append interpretation _ _).mp
        satisfiesInterpolant
    have headSatisfied := headIH interpretation satisfiesB parts.1
    have tailSatisfied := tailIH interpretation satisfiesB parts.2
    intro literal member
    simp only [List.mem_cons] at member
    rcases member with equal | member
    · subst literal
      exact (head.producedEquality.satisfied_iff_satisfies_literal
        interpretation).mp headSatisfied
    · exact tailSatisfied literal member

theorem EqualityExchangeProof.interpolant_shared
    (proof : EqualityExchangeProof colored basis phiA phiB side edge) :
    EqualityHornFormula.IsShared colored 0 proof.interpolant := by
  refine EqualityExchangeProof.rec
    (motive_2 := fun _ _ dependencies =>
      EqualityHornFormula.IsShared colored 0 dependencies.interpolant)
    ?_ ?_ ?_ proof
  · intro producer produced _ dependencies _ dependenciesIH
    apply (EqualityHornFormula.isShared_append colored 0 _ _).mpr
    constructor
    · exact dependenciesIH
    · cases producer with
      | B => exact EqualityHornFormula.isShared_nil colored 0
      | A =>
        apply (EqualityHornFormula.isShared_singleton colored 0 _).mpr
        constructor
        · exact dependencies.equalities_shared
        · intro equality member
          have equalSome : some produced.equality = some equality := by
            simpa only [EqualityExchangeProof.justification,
              Option.mem_def] using member
          have equal : equality = produced.equality :=
            (Option.some.inj equalSome).symm
          subst equality
          exact produced.isShared
  · intro _
    exact EqualityHornFormula.isShared_nil colored 0
  · intro _ _ _ _ _ headIH tailIH
    exact (EqualityHornFormula.isShared_append colored 0 _ _).mpr
      ⟨headIH, tailIH⟩

theorem EqualityExchangeDependencies.interpolant_shared
    (dependencies : EqualityExchangeDependencies
      colored basis phiA phiB side premises) :
    EqualityHornFormula.IsShared colored 0 dependencies.interpolant := by
  refine EqualityExchangeDependencies.rec
    (motive_1 := fun _ _ proof =>
      EqualityHornFormula.IsShared colored 0 proof.interpolant)
    ?_ ?_ ?_ dependencies
  · intro producer produced _ localDependencies _ dependenciesIH
    apply (EqualityHornFormula.isShared_append colored 0 _ _).mpr
    constructor
    · exact dependenciesIH
    · cases producer with
      | B => exact EqualityHornFormula.isShared_nil colored 0
      | A =>
        apply (EqualityHornFormula.isShared_singleton colored 0 _).mpr
        constructor
        · exact localDependencies.equalities_shared
        · intro equality member
          have equalSome : some produced.equality = some equality := by
            simpa only [EqualityExchangeProof.justification,
              Option.mem_def] using member
          have equal : equality = produced.equality :=
            (Option.some.inj equalSome).symm
          subst equality
          exact produced.isShared
  · intro _
    exact EqualityHornFormula.isShared_nil colored 0
  · intro _ _ _ _ _ headIH tailIH
    exact (EqualityHornFormula.isShared_append colored 0 _ _).mpr
      ⟨headIH, tailIH⟩

/-- A final conflict found by one of the two closures. If A owns the explicit
disequality, its opposite-side dependencies become a negative Horn clause. If
B owns it, the A-produced dependencies suffice for B to close the conflict. -/
inductive EqualityInterpolationConflict (colored : ColoredSignature 2)
    (basis : FiniteNameBasis colored)
    (phiA phiB : Formula colored.toSignature) : Type where
  | inA (left right : Term colored.toSignature)
      (disequality : Literal.ne left right ∈ phiA)
      (premises : Formula colored.toSignature)
      (dependencies : EqualityExchangeDependencies
        colored basis phiA phiB .B premises)
      (derivation : DerivesEq
        (phiA ++ premises) left right) :
      EqualityInterpolationConflict colored basis phiA phiB
  | inB (left right : Term colored.toSignature)
      (disequality : Literal.ne left right ∈ phiB)
      (premises : Formula colored.toSignature)
      (dependencies : EqualityExchangeDependencies
        colored basis phiA phiB .A premises)
      (derivation : DerivesEq
        (phiB ++ premises) left right) :
      EqualityInterpolationConflict colored basis phiA phiB

namespace EqualityInterpolationConflict

def negativeJustification {colored : ColoredSignature 2}
    (premises : List (Equality colored.toSignature)) :
    EqualityHornClause colored.toSignature where
  premises := premises
  conclusion := none

/-- Extract the conjunction of A-justifications from the recursively expanded
conflict. -/
def interpolant : EqualityInterpolationConflict colored basis phiA phiB →
    EqualityHornFormula colored.toSignature
  | .inA _ _ _ _ dependencies _ =>
      dependencies.interpolant ++
      [negativeJustification dependencies.equalities]
  | .inB _ _ _ _ dependencies _ =>
      dependencies.interpolant

theorem interpolant_shared
    (conflict : EqualityInterpolationConflict colored basis phiA phiB) :
    EqualityHornFormula.IsShared colored 0 conflict.interpolant := by
  cases conflict with
  | inB _ _ _ _ dependencies _ =>
      exact dependencies.interpolant_shared
  | inA _ _ _ _ dependencies _ =>
      apply (EqualityHornFormula.isShared_append colored 0 _ _).mpr
      constructor
      · exact dependencies.interpolant_shared
      · apply (EqualityHornFormula.isShared_singleton colored 0 _).mpr
        constructor
        · exact dependencies.equalities_shared
        · intro equality member
          exact nomatch member

theorem interpolant_entailed_by_A
    (conflict : EqualityInterpolationConflict colored basis phiA phiB) :
    EntailsEqualityHornFormula phiA conflict.interpolant := by
  cases conflict with
  | inB _ _ _ _ dependencies _ =>
      exact dependencies.interpolant_entailed_by_A
  | inA left right disequality _ dependencies derivation =>
      intro interpretation satisfiesA
      apply (EqualityHornFormula.satisfies_append interpretation _ _).mpr
      constructor
      · exact dependencies.interpolant_entailed_by_A interpretation satisfiesA
      · apply (EqualityHornFormula.satisfies_singleton interpretation _).mpr
        intro satisfiesEqualities
        have satisfiesPremises :=
          dependencies.satisfies_of_equalities interpretation satisfiesEqualities
        have equal : interpretation.eval left = interpretation.eval right :=
          derivation.sound
            ((satisfies_append interpretation phiA _).mpr
              ⟨satisfiesA, satisfiesPremises⟩)
        exact (satisfiesA _ disequality) equal

theorem interpolant_unsatisfiable_with_B
    (conflict : EqualityInterpolationConflict colored basis phiA phiB) :
    UnsatisfiableWithEqualityHornFormula conflict.interpolant phiB := by
  rintro ⟨interpretation, satisfiesInterpolant, satisfiesB⟩
  cases conflict with
  | inB left right disequality _ dependencies derivation =>
      have satisfiesPremises := dependencies.equalities_entailed_by_B
        interpretation satisfiesB satisfiesInterpolant
      have equal : interpretation.eval left = interpretation.eval right :=
        derivation.sound
          ((satisfies_append interpretation phiB _).mpr
            ⟨satisfiesB, satisfiesPremises⟩)
      exact (satisfiesB _ disequality) equal
  | inA _ _ _ _ dependencies _ =>
      have parts :=
        (EqualityHornFormula.satisfies_append interpretation _ _).mp
          satisfiesInterpolant
      have satisfiesPremises := dependencies.equalities_entailed_by_B
        interpretation satisfiesB parts.1
      have satisfiesNegative :=
        (EqualityHornFormula.satisfies_singleton interpretation _).mp parts.2
      apply satisfiesNegative
      exact (satisfies_equality_literals interpretation
        dependencies.equalities).mp (by
          rw [dependencies.literals_equalities]
          exact satisfiesPremises)

/-- Soundness of the fixed-signature alternating EUF interpolation procedure.
The certificate supplies the finite exchange provenance and final conflict;
constructing such a certificate for every inconsistent input is the separate
completeness problem. -/
theorem sound
    (conflict : EqualityInterpolationConflict colored basis phiA phiB)
    (phiAColor : Formula.IsColor colored 0 phiA)
    (phiBColor : Formula.IsColor colored 1 phiB) :
    IsInterpolant colored phiA phiB conflict.interpolant := by
  have entails := conflict.interpolant_entailed_by_A
  have unsatisfiableWithB := conflict.interpolant_unsatisfiable_with_B
  have inputsUnsatisfiable : Unsatisfiable (phiA ++ phiB) := by
    rintro ⟨interpretation, satisfiesInputs⟩
    have parts := (satisfies_append interpretation phiA phiB).mp satisfiesInputs
    apply unsatisfiableWithB
    exact ⟨interpretation, entails interpretation parts.1, parts.2⟩
  exact {
    phi1_color := phiAColor
    phi2_color := phiBColor
    inputs_unsatisfiable := inputsUnsatisfiable
    interpolant_shared := conflict.interpolant_shared
    phi1_entails := entails
    interpolant_phi2_unsatisfiable := unsatisfiableWithB
  }

end EqualityInterpolationConflict

end EUF
