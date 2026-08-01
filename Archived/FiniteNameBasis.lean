-- SPDX-License-Identifier: MIT

import EUFInterpolation.InterpolationProcedure

/-!
The finite enumeration formerly carried by `NameBasis`. It is not needed by
the certificate-based interpolation development, but may be useful for a
future executable saturation procedure and its termination proof.
-/

namespace EUF

/-- A finite enumeration of every name in an abstract-name basis. -/
structure FiniteNameBasis (basis : NameBasis sig) where
  names : List basis.Name
  complete : ∀ name, name ∈ names

namespace FiniteNameBasis

/-- The finite universe of directed abstract equality edges. -/
def edgePairs (finiteBasis : FiniteNameBasis basis) :
  List (basis.Name × basis.Name) :=
  finiteBasis.names.flatMap (fun left =>
    finiteBasis.names.map (fun right => (left, right)))

theorem mem_edgePairs (finiteBasis : FiniteNameBasis basis)
    (left right : basis.Name) :
    (left, right) ∈ finiteBasis.edgePairs := by
  simp [edgePairs, finiteBasis.complete]

end FiniteNameBasis

end EUF
