-- SPDX-License-Identifier: MIT

import ClausalProofInterpolation.TheoryLemmaInterpolation
import EUFInterpolation.InterpolationProcedure

/-!
EUF theory leaves constructed from an already-checked colored equality
conflict.

An `EqualityTheoryCertificate` packages a colored clause with an explicit
equality-exchange conflict over the conjunction that falsifies that clause.
The conflict constructs both facts needed downstream: semantic validity of the
theory clause and its partial-interpolant annotation.  This module is
independent of how the conflict was produced; the optional adapters from the
indexed equality-certificate prototype live in
`EUFInterpolation.InterpolationCertificate`.
-/

namespace EUF

namespace ColoredClause

/-- If the conjunction falsifying a colored clause is inconsistent, the
underlying disjunctive clause is valid. -/
theorem valid_of_falsifyingParts_unsatisfiable
    (clause : ColoredClause sig)
    (unsatisfiable : Unsatisfiable
      (clause.falsifyingPart 0 ++ clause.falsifyingPart 1)) :
    clause.toClause.Valid := by
  classical
  intro interpretation
  by_cases satisfied : clause.toClause.Satisfied interpretation
  · exact satisfied
  · exact False.elim (unsatisfiable ⟨interpretation, by
      intro literal member
      rcases List.mem_append.mp member with member | member
      · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        apply (Literal.satisfies_negate_iff_not interpretation original).mpr
        intro satisfiesOriginal
        apply satisfied
        exact ⟨original, List.mem_append.mpr (Or.inl originalMember),
          satisfiesOriginal⟩
      · obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        apply (Literal.satisfies_negate_iff_not interpretation original).mpr
        intro satisfiesOriginal
        apply satisfied
        exact ⟨original, List.mem_append.mpr (Or.inr originalMember),
          satisfiesOriginal⟩⟩)

end ColoredClause

/-- A theory-leaf bridge: the clause syntax is paired with an already-checked
colored congruence-closure conflict. -/
structure EqualityTheoryCertificate (sig : ColoredSignature 2) where
  clause : ColoredClause sig
  naming : TermNaming sig
  conflict : EqualityInterpolationConflict sig naming
    (fun color => clause.falsifyingPart color)

namespace EqualityTheoryCertificate

/-- The checked conflict proves semantic validity of the theory clause. -/
def theoryLemma (certificate : EqualityTheoryCertificate sig) :
    TheoryLemma sig where
  toColoredClause := certificate.clause
  valid := certificate.clause.valid_of_falsifyingParts_unsatisfiable (by
    have result := certificate.conflict.sound
      certificate.clause.falsifyingPart_color
    exact result.inputs_unsatisfiable)

/-- Compute the theory-leaf annotation from the same checked conflict. -/
def annotation (certificate : EqualityTheoryCertificate sig) :
    TheoryLemmaAnnotation sig where
  lemma := certificate.theoryLemma
  side := 0
  interpolant := certificate.conflict.interpolant
  correct := by
    apply TheoryLemma.IsInterpolantAt.ofIsInterpolant
    simpa [theoryLemma] using
      certificate.conflict.sound certificate.clause.falsifyingPart_color

end EqualityTheoryCertificate

end EUF
