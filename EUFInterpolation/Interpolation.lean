-- SPDX-License-Identifier: MIT

import Basic.Color
import Basic.Horn

/-!
The semantic specification of an interpolant between two colored conjunctive
EUF formulas. It packages input color conditions, inconsistency, sharedness,
entailment from the first side, and inconsistency with the second side.
-/

namespace EUF

/-- `interpolant` is an interpolant between two colored conjunctive EUF
cubes when it satisfies the standard two-cube interpolation conditions.

The signature has exactly two cube positions: position `0` is A, position
`1` is B, and boundary `0` is their shared color. -/
structure IsInterpolant (sig : ColoredSignature 2)
    (phi1 phi2 : Cube sig)
    (interpolant : EqualityHornFormula sig) : Prop where
  /-- The first input contains only A-local and shared literals. -/
  phi1_color : Cube.IsColor sig 0 phi1
  /-- The second input contains only B-local and shared literals. -/
  phi2_color : Cube.IsColor sig 1 phi2
  /-- The conjunction of the two inputs is inconsistent. -/
  inputs_unsatisfiable : Unsatisfiable (Cube.append phi1 phi2)
  /-- Every equality atom in the interpolant uses only shared symbols. -/
  interpolant_shared : EqualityHornFormula.IsShared sig 0 interpolant
  /-- The first input semantically entails the interpolant. -/
  phi1_entails : EntailsEqualityHornFormula phi1 interpolant
  /-- The interpolant is inconsistent with the second input. -/
  interpolant_phi2_unsatisfiable :
    UnsatisfiableWithEqualityHornFormula interpolant phi2

namespace IsInterpolant

/-- The input-unsatisfiability field is logically implied by entailment and
inconsistency with the second input. It remains an explicit field of
`IsInterpolant` so the definition directly records all six requested
conditions. -/
theorem inputs_unsatisfiable_from_interpolant
    (isInterpolant : IsInterpolant sig phi1 phi2 interpolant) :
    Unsatisfiable (Cube.append phi1 phi2) := by
  rintro ⟨interpretation, satisfiesInputs⟩
  have satisfiesPair :=
    (satisfies_append interpretation phi1 phi2).mp satisfiesInputs
  apply isInterpolant.interpolant_phi2_unsatisfiable
  exact ⟨interpretation,
    isInterpolant.phi1_entails interpretation satisfiesPair.1,
    satisfiesPair.2⟩

end IsInterpolant

end EUF
