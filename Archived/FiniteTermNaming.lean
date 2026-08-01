-- SPDX-License-Identifier: MIT

import EUFInterpolation.InterpolationProcedure

/-!
The finite enumeration formerly carried by `TermNaming`. It is not needed by
the certificate-based interpolation development, but may be useful for a
future executable saturation procedure and its termination proof.
-/

namespace EUF

/-- A finite enumeration of every name in a term naming. -/
structure FiniteTermNaming (naming : TermNaming sig) where
  names : List naming.Name
  complete : ∀ name, name ∈ names

namespace FiniteTermNaming

/-- The finite universe of directed abstract equality edges. -/
def edgePairs (finiteNaming : FiniteTermNaming naming) :
  List (naming.Name × naming.Name) :=
  finiteNaming.names.flatMap (fun left =>
    finiteNaming.names.map (fun right => (left, right)))

theorem mem_edgePairs (finiteNaming : FiniteTermNaming naming)
    (left right : naming.Name) :
    (left, right) ∈ finiteNaming.edgePairs := by
  simp [edgePairs, finiteNaming.complete]

end FiniteTermNaming

end EUF
