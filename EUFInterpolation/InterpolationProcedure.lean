-- SPDX-License-Identifier: MIT

import Std
import CongruenceClosure.AbstractCongruenceClosure
import EUFInterpolation.Interpolation

/-!
A certificate-driven EUF interpolation procedure based on alternating
congruence closures. It tracks finite shared names and equality-exchange
provenance, extracts an equality Horn interpolant from a final conflict, and
proves the extracted formula satisfies the semantic interpolation
specification.
-/

namespace EUF

/-- The local color that produced an equality during cooperative congruence
closure. In the two-formula procedure this is a member of `Fin 2`; the familiar
names A and B are only aliases for colors `0` and `1`. -/
abbrev InterpolationColor := Fin 2

namespace InterpolationColor

def other (color : InterpolationColor) : InterpolationColor :=
  if color = 0 then 1 else 0

@[simp]
theorem other_zero : other 0 = 1 := rfl

@[simp]
theorem other_one : other 1 = 0 := by
  simp [other]

theorem eq_zero_or_eq_one (color : InterpolationColor) :
    color = 0 ∨ color = 1 := by
  rcases color with ⟨value, less⟩
  have cases : value = 0 ∨ value = 1 := by omega
  rcases cases with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Convenience name for local color `0`. -/
def A : InterpolationColor := 0

/-- Convenience name for local color `1`. -/
def B : InterpolationColor := 1

end InterpolationColor

/-- The immutable term naming used throughout an interpolation run. Every
abstract name has a chosen original-term representative, used to translate
internal shared edges back into interpolant atoms. -/
structure TermNaming (sig : ColoredSignature 2) where
  Name : Type
  representative : Name → Term sig

namespace TermNaming

/-- The fixed representatives agree with the names used by an abstract rewrite
system. -/
def RealizedBy (naming : TermNaming sig)
    (system : AbstractRewriteSystem sig naming.Name) : Prop :=
  ∀ name, system.Represents name (naming.representative name)

end TermNaming

/-- A shared equality edge in the fixed abstract signature. -/
structure SharedEqualityEdge {sig : ColoredSignature 2}
    (naming : TermNaming sig) where
  left : naming.Name
  right : naming.Name
  isShared : Equality.IsShared sig 0
    ⟨naming.representative left, naming.representative right⟩

namespace SharedEqualityEdge

def equality {sig : ColoredSignature 2} {naming : TermNaming sig}
    (edge : SharedEqualityEdge naming) : Equality sig :=
  ⟨naming.representative edge.left, naming.representative edge.right⟩

def literal {sig : ColoredSignature 2} {naming : TermNaming sig}
    (edge : SharedEqualityEdge naming) : Literal sig :=
  edge.equality.literal

end SharedEqualityEdge

mutual

  /-- A proof-producing communication step. An equality produced by one local
  color is derived from that color's input formula and finitely many shared
  equalities previously produced by the other local color. -/
  inductive EqualityExchangeProof {sig : ColoredSignature 2}
      (naming : TermNaming sig)
      (formulas : InterpolationColor → Formula sig) :
      InterpolationColor → SharedEqualityEdge naming → Type where
    | derive (producer : InterpolationColor)
        (edge : SharedEqualityEdge naming)
        (premises : Formula sig)
        (dependencies : EqualityExchangeDependencies
          naming formulas producer.other premises)
        (derivation : DerivesEq
          (formulas producer ++ premises)
          edge.equality.left edge.equality.right) :
        EqualityExchangeProof naming formulas producer edge

  /-- A finite list of communicated equality proofs, indexed by the formula of
  equality literals that they supply to the receiving closure. -/
  inductive EqualityExchangeDependencies {sig : ColoredSignature 2}
      (naming : TermNaming sig)
      (formulas : InterpolationColor → Formula sig) :
      InterpolationColor → Formula sig → Type where
    | nil (producer : InterpolationColor) :
        EqualityExchangeDependencies naming formulas producer []
    | cons {producer : InterpolationColor}
        {edge : SharedEqualityEdge naming}
        {premises : Formula sig}
        (head : EqualityExchangeProof naming formulas producer edge)
        (tail : EqualityExchangeDependencies naming formulas producer premises) :
        EqualityExchangeDependencies naming formulas producer
          (edge.literal :: premises)

end

variable {sig : ColoredSignature 2}
  {naming : TermNaming sig}
  {formulas : InterpolationColor → Formula sig}

namespace EqualityExchangeProof

def producedEquality
    (_proof : EqualityExchangeProof naming formulas producer edge) :
    Equality sig :=
  edge.equality

/-- Build a communication step from an edge recognized by an abstract
congruence closure over the same fixed term naming. No signature extension
takes place here: the edge endpoints are existing names in `naming`. -/
def ofAbstractClosure
    {sig : ColoredSignature 2}
    {naming : TermNaming sig}
    {formulas : InterpolationColor → Formula sig}
    {producer : InterpolationColor}
    (system : AbstractRewriteSystem sig naming.Name)
    (realized : naming.RealizedBy system)
    (edge : SharedEqualityEdge naming)
    (premises : Formula sig)
    (dependencies : EqualityExchangeDependencies
      naming formulas producer.other premises)
    (closure : AbstractCongruenceClosure
      (formulas producer ++ premises) system)
    (edgeJoinable : system.Joinable
      (ExtendedSignature.constant edge.left)
      (ExtendedSignature.constant edge.right)) :
    EqualityExchangeProof naming formulas producer edge := by
  have leftEquivalent := realized edge.left
  have rightEquivalent := realized edge.right
  have namesEquivalent :=
    AbstractRewriteSystem.equivalent_of_joinable edgeJoinable
  have representativesEquivalent : system.Equivalent
      (ExtendedSignature.term (naming.representative edge.left))
      (ExtendedSignature.term (naming.representative edge.right)) :=
    leftEquivalent.trans (namesEquivalent.trans rightEquivalent.symm)
  have representativesJoinable :=
    AbstractRewriteSystem.joinable_of_equivalent closure.ground_convergent.2
      representativesEquivalent
  exact .derive producer edge premises dependencies
    ((closure.conservative _ _).mpr representativesJoinable)

/-- The Horn clause contributed by a color-`0` equality. -/
def justification {sig : ColoredSignature 2} {naming : TermNaming sig}
    (edge : SharedEqualityEdge naming)
    (premises : List (Equality sig)) :
    EqualityHornClause sig where
  premises := premises
  conclusion := some edge.equality

end EqualityExchangeProof

namespace EqualityExchangeDependencies

def equalities :
    EqualityExchangeDependencies naming formulas producer premises →
      List (Equality sig)
  | .nil _ => []
  | .cons head tail => head.producedEquality :: equalities tail

theorem literals_equalities
    : (dependencies : EqualityExchangeDependencies
        naming formulas producer premises) →
      dependencies.equalities.map Equality.literal = premises
  | .nil _ => rfl
  | @EqualityExchangeDependencies.cons _ _ _ _ edge _ head tail => by
      simp only [equalities, EqualityExchangeProof.producedEquality,
        SharedEqualityEdge.equality, Equality.literal,
        SharedEqualityEdge.literal]
      exact congrArg (edge.literal :: ·) (literals_equalities tail)

theorem satisfies_of_equalities
    (dependencies : EqualityExchangeDependencies
      naming formulas producer premises)
    (interpretation : Interpretation sig)
    (satisfies : ∀ equality ∈ dependencies.equalities,
      equality.Satisfied interpretation) :
    Satisfies interpretation premises := by
  rw [← dependencies.literals_equalities]
  exact (satisfies_equality_literals interpretation dependencies.equalities).mpr
    satisfies

theorem equalities_shared :
    (dependencies : EqualityExchangeDependencies
      naming formulas producer premises) →
    ∀ equality ∈ dependencies.equalities,
      equality.IsShared sig 0
  | .nil _, _, member => nomatch member
  | @EqualityExchangeDependencies.cons _ _ _ _ edge _ head tail,
      equality, member => by
      simp only [equalities, List.mem_cons] at member
      rcases member with equal | member
      · subst equality
        exact edge.isShared
      · exact equalities_shared tail equality member

end EqualityExchangeDependencies

mutual

  /-- Recursively collect all color-`0` justifications needed for an exchanged
  equality. Color-`1` nodes contribute no clause of their own. -/
  def EqualityExchangeProof.interpolant :
      EqualityExchangeProof naming formulas producer edge →
        EqualityHornFormula sig
    | .derive producer edge _ dependencies _ =>
        dependencies.interpolant ++
        if producer = 0 then
          [EqualityExchangeProof.justification edge dependencies.equalities]
        else []

  def EqualityExchangeDependencies.interpolant :
      EqualityExchangeDependencies naming formulas producer premises →
        EqualityHornFormula sig
    | .nil _ => []
    | .cons head tail => head.interpolant ++ tail.interpolant

end

theorem EqualityExchangeProof.interpolant_entailed_by_color_zero
    (proof : EqualityExchangeProof naming formulas producer edge) :
    EntailsEqualityHornFormula (formulas 0) proof.interpolant := by
  refine EqualityExchangeProof.rec
    (motive_2 := fun _ _ dependencies =>
      EntailsEqualityHornFormula (formulas 0) dependencies.interpolant)
    ?_ ?_ ?_ proof
  · intro producer produced premises dependencies derivation dependenciesIH
    intro interpretation satisfiesColorZero
    apply (EqualityHornFormula.satisfies_append interpretation _ _).mpr
    constructor
    · exact dependenciesIH interpretation satisfiesColorZero
    · rcases producer.eq_zero_or_eq_one with rfl | rfl
      · apply (EqualityHornFormula.satisfies_singleton interpretation _).mpr
        intro satisfiesEqualities
        have satisfiesPremises : Satisfies interpretation premises :=
          dependencies.satisfies_of_equalities interpretation satisfiesEqualities
        exact derivation.sound
          ((satisfies_append interpretation (formulas 0) premises).mpr
            ⟨satisfiesColorZero, satisfiesPremises⟩)
      · exact EqualityHornFormula.satisfies_nil interpretation
  · intro _ interpretation _
    exact EqualityHornFormula.satisfies_nil interpretation
  · intro _ _ _ _ _ headIH tailIH interpretation satisfiesColorZero
    exact (EqualityHornFormula.satisfies_append interpretation _ _).mpr
      ⟨headIH interpretation satisfiesColorZero,
        tailIH interpretation satisfiesColorZero⟩

theorem EqualityExchangeDependencies.interpolant_entailed_by_color_zero
    (dependencies : EqualityExchangeDependencies
      naming formulas producer premises) :
    EntailsEqualityHornFormula (formulas 0) dependencies.interpolant := by
  refine EqualityExchangeDependencies.rec
    (motive_1 := fun _ _ proof =>
      EntailsEqualityHornFormula (formulas 0) proof.interpolant)
    ?_ ?_ ?_ dependencies
  · intro producer produced localPremises localDependencies derivation dependenciesIH
    intro interpretation satisfiesColorZero
    apply (EqualityHornFormula.satisfies_append interpretation _ _).mpr
    constructor
    · exact dependenciesIH interpretation satisfiesColorZero
    · rcases producer.eq_zero_or_eq_one with rfl | rfl
      · apply (EqualityHornFormula.satisfies_singleton interpretation _).mpr
        intro satisfiesEqualities
        have satisfiesPremises : Satisfies interpretation localPremises :=
          localDependencies.satisfies_of_equalities interpretation satisfiesEqualities
        exact derivation.sound
          ((satisfies_append interpretation (formulas 0) localPremises).mpr
            ⟨satisfiesColorZero, satisfiesPremises⟩)
      · exact EqualityHornFormula.satisfies_nil interpretation
  · intro _ interpretation _
    exact EqualityHornFormula.satisfies_nil interpretation
  · intro _ _ _ _ _ headIH tailIH interpretation satisfiesColorZero
    exact (EqualityHornFormula.satisfies_append interpretation _ _).mpr
      ⟨headIH interpretation satisfiesColorZero,
        tailIH interpretation satisfiesColorZero⟩

theorem EqualityExchangeProof.equality_entailed_by_color_one
    (proof : EqualityExchangeProof naming formulas producer edge)
    (interpretation : Interpretation sig)
    (satisfiesColorOne : Satisfies interpretation (formulas 1))
    (satisfiesInterpolant :
      SatisfiesEqualityHornFormula interpretation proof.interpolant) :
    edge.equality.Satisfied interpretation := by
  refine EqualityExchangeProof.rec
    (motive_2 := fun _ premises dependencies =>
      ∀ interpretation : Interpretation sig,
        Satisfies interpretation (formulas 1) →
        SatisfiesEqualityHornFormula interpretation dependencies.interpolant →
        Satisfies interpretation premises)
    ?_ ?_ ?_ proof interpretation satisfiesColorOne satisfiesInterpolant
  · intro producer produced premises dependencies derivation dependenciesIH
      interpretation satisfiesColorOne satisfiesInterpolant
    have parts :=
      (EqualityHornFormula.satisfies_append interpretation _ _).mp
        satisfiesInterpolant
    have satisfiesPremises : Satisfies interpretation premises :=
      dependenciesIH interpretation satisfiesColorOne parts.1
    rcases producer.eq_zero_or_eq_one with rfl | rfl
    ·
        have satisfiesClause :=
          (EqualityHornFormula.satisfies_singleton interpretation _).mp parts.2
        apply satisfiesClause
        exact (satisfies_equality_literals interpretation
          dependencies.equalities).mp (by
            rw [dependencies.literals_equalities]
            exact satisfiesPremises)
    ·
        exact derivation.sound
          ((satisfies_append interpretation (formulas 1) premises).mpr
            ⟨satisfiesColorOne, satisfiesPremises⟩)
  · intro _ interpretation _ _ literal member
    exact nomatch member
  · intro _ edge _ head tail headIH tailIH interpretation satisfiesColorOne
      satisfiesInterpolant
    have parts :=
      (EqualityHornFormula.satisfies_append interpretation _ _).mp
        satisfiesInterpolant
    have headSatisfied := headIH interpretation satisfiesColorOne parts.1
    have tailSatisfied := tailIH interpretation satisfiesColorOne parts.2
    intro literal member
    simp only [List.mem_cons] at member
    rcases member with equal | member
    · subst literal
      exact (head.producedEquality.satisfied_iff_satisfies_literal
        interpretation).mp headSatisfied
    · exact tailSatisfied literal member

theorem EqualityExchangeDependencies.equalities_entailed_by_color_one
    (dependencies : EqualityExchangeDependencies
      naming formulas producer premises)
    (interpretation : Interpretation sig)
    (satisfiesColorOne : Satisfies interpretation (formulas 1))
    (satisfiesInterpolant :
      SatisfiesEqualityHornFormula interpretation dependencies.interpolant) :
    Satisfies interpretation premises := by
  refine EqualityExchangeDependencies.rec
    (motive_1 := fun _ edge proof =>
      ∀ interpretation : Interpretation sig,
        Satisfies interpretation (formulas 1) →
        SatisfiesEqualityHornFormula interpretation proof.interpolant →
        edge.equality.Satisfied interpretation)
    ?_ ?_ ?_ dependencies interpretation satisfiesColorOne satisfiesInterpolant
  · intro producer produced localPremises localDependencies derivation dependenciesIH
      interpretation satisfiesColorOne satisfiesInterpolant
    have parts :=
      (EqualityHornFormula.satisfies_append interpretation _ _).mp
        satisfiesInterpolant
    have satisfiesPremises : Satisfies interpretation localPremises :=
      dependenciesIH interpretation satisfiesColorOne parts.1
    rcases producer.eq_zero_or_eq_one with rfl | rfl
    ·
        have satisfiesClause :=
          (EqualityHornFormula.satisfies_singleton interpretation _).mp parts.2
        apply satisfiesClause
        exact (satisfies_equality_literals interpretation
          localDependencies.equalities).mp (by
            rw [localDependencies.literals_equalities]
            exact satisfiesPremises)
    ·
        exact derivation.sound
          ((satisfies_append interpretation (formulas 1) localPremises).mpr
            ⟨satisfiesColorOne, satisfiesPremises⟩)
  · intro _ interpretation _ _ literal member
    exact nomatch member
  · intro _ edge _ head tail headIH tailIH interpretation satisfiesColorOne
      satisfiesInterpolant
    have parts :=
      (EqualityHornFormula.satisfies_append interpretation _ _).mp
        satisfiesInterpolant
    have headSatisfied := headIH interpretation satisfiesColorOne parts.1
    have tailSatisfied := tailIH interpretation satisfiesColorOne parts.2
    intro literal member
    simp only [List.mem_cons] at member
    rcases member with equal | member
    · subst literal
      exact (head.producedEquality.satisfied_iff_satisfies_literal
        interpretation).mp headSatisfied
    · exact tailSatisfied literal member

theorem EqualityExchangeProof.interpolant_shared
    (proof : EqualityExchangeProof naming formulas producer edge) :
    EqualityHornFormula.IsShared sig 0 proof.interpolant := by
  refine EqualityExchangeProof.rec
    (motive_2 := fun _ _ dependencies =>
      EqualityHornFormula.IsShared sig 0 dependencies.interpolant)
    ?_ ?_ ?_ proof
  · intro producer produced _ dependencies _ dependenciesIH
    apply (EqualityHornFormula.isShared_append sig 0 _ _).mpr
    constructor
    · exact dependenciesIH
    · rcases producer.eq_zero_or_eq_one with rfl | rfl
      ·
        apply (EqualityHornFormula.isShared_singleton sig 0 _).mpr
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
      · exact EqualityHornFormula.isShared_nil sig 0
  · intro _
    exact EqualityHornFormula.isShared_nil sig 0
  · intro _ _ _ _ _ headIH tailIH
    exact (EqualityHornFormula.isShared_append sig 0 _ _).mpr
      ⟨headIH, tailIH⟩

theorem EqualityExchangeDependencies.interpolant_shared
    (dependencies : EqualityExchangeDependencies
      naming formulas producer premises) :
    EqualityHornFormula.IsShared sig 0 dependencies.interpolant := by
  refine EqualityExchangeDependencies.rec
    (motive_1 := fun _ _ proof =>
      EqualityHornFormula.IsShared sig 0 proof.interpolant)
    ?_ ?_ ?_ dependencies
  · intro producer produced _ localDependencies _ dependenciesIH
    apply (EqualityHornFormula.isShared_append sig 0 _ _).mpr
    constructor
    · exact dependenciesIH
    · rcases producer.eq_zero_or_eq_one with rfl | rfl
      ·
        apply (EqualityHornFormula.isShared_singleton sig 0 _).mpr
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
      · exact EqualityHornFormula.isShared_nil sig 0
  · intro _
    exact EqualityHornFormula.isShared_nil sig 0
  · intro _ _ _ _ _ headIH tailIH
    exact (EqualityHornFormula.isShared_append sig 0 _ _).mpr
      ⟨headIH, tailIH⟩

/-- A final conflict found by one of the two closures. If color `0` owns the
explicit disequality, its color-`1` dependencies become a negative Horn clause.
If color `1` owns it, the color-`0` dependencies suffice to close the conflict. -/
inductive EqualityInterpolationConflict (sig : ColoredSignature 2)
    (naming : TermNaming sig)
    (formulas : InterpolationColor → Formula sig) : Type where
  | atColorZero (left right : Term sig)
      (disequality : Literal.ne left right ∈ formulas 0)
      (premises : Formula sig)
      (dependencies : EqualityExchangeDependencies
        naming formulas 1 premises)
      (derivation : DerivesEq
        (formulas 0 ++ premises) left right) :
      EqualityInterpolationConflict sig naming formulas
  | atColorOne (left right : Term sig)
      (disequality : Literal.ne left right ∈ formulas 1)
      (premises : Formula sig)
      (dependencies : EqualityExchangeDependencies
        naming formulas 0 premises)
      (derivation : DerivesEq
        (formulas 1 ++ premises) left right) :
      EqualityInterpolationConflict sig naming formulas

namespace EqualityInterpolationConflict

def negativeJustification {sig : ColoredSignature 2}
    (premises : List (Equality sig)) :
    EqualityHornClause sig where
  premises := premises
  conclusion := none

/-- Extract the conjunction of color-`0` justifications from the recursively
expanded conflict. -/
def interpolant : EqualityInterpolationConflict sig naming formulas →
    EqualityHornFormula sig
  | .atColorZero _ _ _ _ dependencies _ =>
      dependencies.interpolant ++
      [negativeJustification dependencies.equalities]
  | .atColorOne _ _ _ _ dependencies _ =>
      dependencies.interpolant

theorem interpolant_shared
    (conflict : EqualityInterpolationConflict sig naming formulas) :
    EqualityHornFormula.IsShared sig 0 conflict.interpolant := by
  cases conflict with
  | atColorOne _ _ _ _ dependencies _ =>
      exact dependencies.interpolant_shared
  | atColorZero _ _ _ _ dependencies _ =>
      apply (EqualityHornFormula.isShared_append sig 0 _ _).mpr
      constructor
      · exact dependencies.interpolant_shared
      · apply (EqualityHornFormula.isShared_singleton sig 0 _).mpr
        constructor
        · exact dependencies.equalities_shared
        · intro equality member
          exact nomatch member

theorem interpolant_entailed_by_color_zero
    (conflict : EqualityInterpolationConflict sig naming formulas) :
    EntailsEqualityHornFormula (formulas 0) conflict.interpolant := by
  cases conflict with
  | atColorOne _ _ _ _ dependencies _ =>
      exact dependencies.interpolant_entailed_by_color_zero
  | atColorZero left right disequality _ dependencies derivation =>
      intro interpretation satisfiesColorZero
      apply (EqualityHornFormula.satisfies_append interpretation _ _).mpr
      constructor
      · exact dependencies.interpolant_entailed_by_color_zero
          interpretation satisfiesColorZero
      · apply (EqualityHornFormula.satisfies_singleton interpretation _).mpr
        intro satisfiesEqualities
        have satisfiesPremises :=
          dependencies.satisfies_of_equalities interpretation satisfiesEqualities
        have equal : interpretation.eval left = interpretation.eval right :=
          derivation.sound
            ((satisfies_append interpretation (formulas 0) _).mpr
              ⟨satisfiesColorZero, satisfiesPremises⟩)
        exact (satisfiesColorZero _ disequality) equal

theorem interpolant_unsatisfiable_with_color_one
    (conflict : EqualityInterpolationConflict sig naming formulas) :
    UnsatisfiableWithEqualityHornFormula conflict.interpolant (formulas 1) := by
  rintro ⟨interpretation, satisfiesInterpolant, satisfiesColorOne⟩
  cases conflict with
  | atColorOne left right disequality _ dependencies derivation =>
      have satisfiesPremises := dependencies.equalities_entailed_by_color_one
        interpretation satisfiesColorOne satisfiesInterpolant
      have equal : interpretation.eval left = interpretation.eval right :=
        derivation.sound
          ((satisfies_append interpretation (formulas 1) _).mpr
            ⟨satisfiesColorOne, satisfiesPremises⟩)
      exact (satisfiesColorOne _ disequality) equal
  | atColorZero _ _ _ _ dependencies _ =>
      have parts :=
        (EqualityHornFormula.satisfies_append interpretation _ _).mp
          satisfiesInterpolant
      have satisfiesPremises := dependencies.equalities_entailed_by_color_one
        interpretation satisfiesColorOne parts.1
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
    (conflict : EqualityInterpolationConflict sig naming formulas)
    (formulaColors : ∀ color, Formula.IsColor sig color (formulas color)) :
    IsInterpolant sig (formulas 0) (formulas 1) conflict.interpolant := by
  have entails := conflict.interpolant_entailed_by_color_zero
  have unsatisfiableWithColorOne :=
    conflict.interpolant_unsatisfiable_with_color_one
  have inputsUnsatisfiable : Unsatisfiable (formulas 0 ++ formulas 1) := by
    rintro ⟨interpretation, satisfiesInputs⟩
    have parts :=
      (satisfies_append interpretation (formulas 0) (formulas 1)).mp
        satisfiesInputs
    apply unsatisfiableWithColorOne
    exact ⟨interpretation, entails interpretation parts.1, parts.2⟩
  exact {
    phi1_color := formulaColors 0
    phi2_color := formulaColors 1
    inputs_unsatisfiable := inputsUnsatisfiable
    interpolant_shared := conflict.interpolant_shared
    phi1_entails := entails
    interpolant_phi2_unsatisfiable := unsatisfiableWithColorOne
  }

end EqualityInterpolationConflict

end EUF
