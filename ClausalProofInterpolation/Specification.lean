-- SPDX-License-Identifier: MIT

import ClausalProofs.ColoredProof
import Basic.HornToCNF

/-!
The semantic specification shared by the alternative clausal interpolation
procedures.
-/

namespace EUF

/-- A clausal Craig interpolant between two colored EUF inputs, indexed by the
side whose contribution is summarized. -/
structure IsClausalInterpolantAt (inputs : ColoredCNF sig)
    (side : Fin 2) (interpolant : CNF sig) : Prop where
  inputs_unsatisfiable : inputs.Unsatisfiable
  interpolant_shared :
    CNF.IsShared sig 0 interpolant
  side_entails :
    ∀ interpretation : Interpretation sig,
      (inputs.part side).Satisfied interpretation →
      interpolant.Satisfied interpretation
  interpolant_other_unsatisfiable :
    ¬∃ interpretation : Interpretation sig,
      interpolant.Satisfied interpretation ∧
      (inputs.part side.rev).Satisfied interpretation

end EUF
