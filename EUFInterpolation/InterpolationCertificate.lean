-- SPDX-License-Identifier: MIT

import CongruenceClosure.EqualityCertificate
import EUFInterpolation.InterpolationProcedure

/-!
Adapters from finite indexed equality certificates to the existing colored
equality-exchange interpolation proof objects.

The producer supplies both the colored exchange structure and a locally
checkable equality DAG for each derivation.  Lean checks the DAG and reuses the
existing interpolation soundness proof unchanged.
-/

namespace EUF

namespace EqualityExchangeProof

/-- Produce one shared equality exchange from a finite checked equality DAG. -/
def ofCertificate
    {sig : ColoredSignature 2} {naming : TermNaming sig}
    {formulas : InterpolationColor → Formula sig}
    (producer : InterpolationColor)
    (edge : SharedEqualityEdge naming)
    (premises : List (Equality sig))
    (dependencies : EqualityExchangeDependencies
      (naming := naming) formulas producer.other premises)
    {earlier : List (Equality sig)}
    (certificate : EqualityCertificate
      (formulas producer ++ premises.map Equality.literal)
      (edge.equality :: earlier)) :
    EqualityExchangeProof formulas producer edge :=
  .derive producer edge premises dependencies certificate.conclusion

end EqualityExchangeProof

namespace EqualityInterpolationConflict

/-- Close a color-0 disequality conflict using an indexed equality proof. -/
def atColorZeroOfCertificate
    {sig : ColoredSignature 2} {naming : TermNaming sig}
    {formulas : InterpolationColor → Formula sig}
    (left right : Term sig)
    (disequality : Literal.ne left right ∈ formulas 0)
    (premises : List (Equality sig))
    (dependencies : EqualityExchangeDependencies
      (naming := naming) formulas 1 premises)
    {earlier : List (Equality sig)}
    (certificate : EqualityCertificate
      (formulas 0 ++ premises.map Equality.literal)
      (⟨left, right⟩ :: earlier)) :
    EqualityInterpolationConflict sig naming formulas :=
  .atColorZero left right disequality premises dependencies
    certificate.conclusion

/-- Close a color-1 disequality conflict using an indexed equality proof. -/
def atColorOneOfCertificate
    {sig : ColoredSignature 2} {naming : TermNaming sig}
    {formulas : InterpolationColor → Formula sig}
    (left right : Term sig)
    (disequality : Literal.ne left right ∈ formulas 1)
    (premises : List (Equality sig))
    (dependencies : EqualityExchangeDependencies
      (naming := naming) formulas 0 premises)
    {earlier : List (Equality sig)}
    (certificate : EqualityCertificate
      (formulas 1 ++ premises.map Equality.literal)
      (⟨left, right⟩ :: earlier)) :
    EqualityInterpolationConflict sig naming formulas :=
  .atColorOne left right disequality premises dependencies
    certificate.conclusion

end EqualityInterpolationConflict

end EUF
