import Basic.Colored
import EUFInterpolation.Interpolation

namespace EUF

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
