import CraigCongruence.Interpolation

namespace EUF

/-- A clause is a disjunction of EUF literals. This is intentionally distinct
from `Formula`, whose list structure denotes conjunction. -/
abbrev Clause (signature : Signature) := List (Literal signature)

namespace Clause

/-- An interpretation satisfies a clause when it satisfies one of its
literals. -/
def Satisfied (interpretation : Interpretation signature)
    (clause : Clause signature) : Prop :=
  ∃ literal ∈ clause, SatisfiesLiteral interpretation literal

/-- Semantic EUF validity of a clause. -/
def Valid (clause : Clause signature) : Prop :=
  ∀ interpretation : Interpretation signature,
    clause.Satisfied interpretation

end Clause

namespace Literal

@[simp]
theorem satisfies_negate_iff_not (interpretation : Interpretation signature)
    (literal : Literal signature) :
    SatisfiesLiteral interpretation literal.negate ↔
      ¬SatisfiesLiteral interpretation literal := by
  cases literal <;> simp [Literal.negate, SatisfiesLiteral]

end Literal

/-- A coloring of a clause assigns every literal occurrence to one formula
position. Shared literals may be put in either part; a local literal can only
be put in its owning part because of `part_color`.

Keeping the two parts separately is also exactly what is needed to negate the
clause into the pair of conjunctive inputs used for theory interpolation. -/
structure ColoredClause (colored : ColoredSignature 2) where
  part : Fin 2 → Clause colored.toSignature
  part_color : ∀ i, Formula.IsColor colored i (part i)

namespace ColoredClause

/-- The underlying disjunctive clause, forgetting ownership. -/
def literals (clause : ColoredClause colored) : Clause colored.toSignature :=
  clause.part 0 ++ clause.part 1

/-- The conjunction which falsifies the literals owned by one color. -/
def falsifyingPart (clause : ColoredClause colored) (side : Fin 2) :
    Formula colored.toSignature :=
  (clause.part side).map Literal.negate

theorem falsifyingPart_color (clause : ColoredClause colored) (side : Fin 2) :
    Formula.IsColor colored side (clause.falsifyingPart side) := by
  intro literal member
  simp only [falsifyingPart, List.mem_map] at member
  obtain ⟨original, originalMember, rfl⟩ := member
  have originalColor := clause.part_color side original originalMember
  exact ⟨(Literal.colorable_negate_iff colored original).mpr originalColor.1,
    (Literal.availableIn_negate_iff colored side original).mpr originalColor.2⟩

end ColoredClause

/-- A theory lemma is a colorable clause which is valid in EUF. Mixed theory
lemmas are allowed, but no literal occurrence itself is mixed. -/
structure TheoryLemma (colored : ColoredSignature 2)
    extends ColoredClause colored where
  valid : toColoredClause.literals.Valid

namespace TheoryLemma

/-- Negating a valid theory clause produces an inconsistent conjunction of
its two colored parts. -/
theorem falsifyingParts_unsatisfiable (lemma : TheoryLemma colored) :
    Unsatisfiable
      (lemma.toColoredClause.falsifyingPart 0 ++
        lemma.toColoredClause.falsifyingPart 1) := by
  rintro ⟨interpretation, satisfiesNegation⟩
  have parts := (satisfies_append interpretation _ _).mp satisfiesNegation
  obtain ⟨literal, member, satisfiesLiteral⟩ := lemma.valid interpretation
  change literal ∈ lemma.part 0 ++ lemma.part 1 at member
  rcases List.mem_append.mp member with member | member
  · have satisfiesNegated := parts.1 literal.negate (by
      exact List.mem_map.mpr ⟨literal, member, rfl⟩)
    exact (Literal.satisfies_negate_iff_not interpretation literal).mp
      satisfiesNegated satisfiesLiteral
  · have satisfiesNegated := parts.2 literal.negate (by
      exact List.mem_map.mpr ⟨literal, member, rfl⟩)
    exact (Literal.satisfies_negate_iff_not interpretation literal).mp
      satisfiesNegated satisfiesLiteral

/-- A color-indexed partial interpolant for a theory lemma. It eliminates the
local symbols from the falsifying conjunction owned by `side`, leaving a
shared Horn formula sufficient to contradict the other side.

`Fin.rev side` is the other formula position in the two-color setting. -/
structure IsInterpolantAt (lemma : TheoryLemma colored) (side : Fin 2)
    (interpolant : EqualityHornFormula colored.toSignature) : Prop where
  interpolant_shared :
    EqualityHornFormula.IsShared colored 0 interpolant
  side_entails :
    EntailsEqualityHornFormula
      (lemma.toColoredClause.falsifyingPart side) interpolant
  interpolant_other_unsatisfiable :
    UnsatisfiableWithEqualityHornFormula interpolant
      (lemma.toColoredClause.falsifyingPart side.rev)

/-- A color-0 theory-lemma annotation is an ordinary interpolant between the
two parts of the negated clause. -/
def IsInterpolantAt.toIsInterpolant
    {colored : ColoredSignature 2}
    {lemma : TheoryLemma colored}
    {interpolant : EqualityHornFormula colored.toSignature}
    (annotation : IsInterpolantAt lemma 0 interpolant) :
    IsInterpolant colored
      (ColoredClause.falsifyingPart lemma.toColoredClause 0)
      (ColoredClause.falsifyingPart lemma.toColoredClause 1)
      interpolant where
  phi1_color := ColoredClause.falsifyingPart_color lemma.toColoredClause 0
  phi2_color := ColoredClause.falsifyingPart_color lemma.toColoredClause 1
  inputs_unsatisfiable := falsifyingParts_unsatisfiable lemma
  interpolant_shared := annotation.interpolant_shared
  phi1_entails := annotation.side_entails
  interpolant_phi2_unsatisfiable := by
    simpa using annotation.interpolant_other_unsatisfiable

/-- Any ordinary interpolant for the two falsifying parts supplies the
color-0 annotation required at a theory-lemma leaf. In particular, the
existing congruence-closure interpolation procedure can be used unchanged. -/
def IsInterpolantAt.ofIsInterpolant
    {colored : ColoredSignature 2}
    {lemma : TheoryLemma colored}
    {interpolant : EqualityHornFormula colored.toSignature}
    (isInterpolant :
      IsInterpolant colored
        (ColoredClause.falsifyingPart lemma.toColoredClause 0)
        (ColoredClause.falsifyingPart lemma.toColoredClause 1)
        interpolant) :
    IsInterpolantAt lemma 0 interpolant where
  interpolant_shared := isInterpolant.interpolant_shared
  side_entails := isInterpolant.phi1_entails
  interpolant_other_unsatisfiable := by
    simpa using isInterpolant.interpolant_phi2_unsatisfiable

theorem isInterpolantAt_zero_iff
    {colored : ColoredSignature 2}
    {lemma : TheoryLemma colored}
    {interpolant : EqualityHornFormula colored.toSignature} :
    IsInterpolantAt lemma 0 interpolant ↔
      IsInterpolant colored
        (ColoredClause.falsifyingPart lemma.toColoredClause 0)
        (ColoredClause.falsifyingPart lemma.toColoredClause 1)
        interpolant :=
  ⟨IsInterpolantAt.toIsInterpolant, IsInterpolantAt.ofIsInterpolant⟩

/-- Convenience name for the color-0 orientation. The primary definition is
the color-indexed `IsInterpolantAt`. -/
abbrev IsAInterpolant (lemma : TheoryLemma colored)
    (interpolant : EqualityHornFormula colored.toSignature) : Prop :=
  IsInterpolantAt lemma 0 interpolant

/-- Convenience name for the color-1 orientation. -/
abbrev IsBInterpolant (lemma : TheoryLemma colored)
    (interpolant : EqualityHornFormula colored.toSignature) : Prop :=
  IsInterpolantAt lemma 1 interpolant

end TheoryLemma

end EUF
