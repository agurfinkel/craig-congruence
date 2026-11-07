import VersoManual
import ClausalProofInterpolation
import ClausalProofInterpolation.Z3Proof43Trace

open Verso.Genre Manual

-- Show fields and constructors whose parent has prose but whose children do not.
set_option verso.docstring.allowMissing true

#doc (Manual) "Declarations for the audit" =>

Verso reads these declarations from the imported Lean environment. They are
the contracts behind the preceding argument. The linked source files contain
their complete definitions and proofs; the displayed statements do not
replace inspection of their hypotheses.

# The semantic endpoints

The cube endpoint makes the Horn fragment explicit. The clausal endpoint
lets either input be the summarized side.

[Source: cube specification](source/EUFInterpolation/Interpolation.lean.html)
and [clausal specification](source/ClausalProofInterpolation/Specification.lean.html).

{docstring EUF.IsInterpolant}

{docstring EUF.IsClausalInterpolantAt}

# Equality evidence and extraction

Start with the local equality rules, then inspect the shared edge and the
exchange constructor. The final theorem assumes a supplied conflict and
correct input colors.

[Source: equality rules](source/CongruenceClosure/EquationalTheory.lean.html),
[indexed replay](source/CongruenceClosure/EqualityCertificate.lean.html), and
[exchange extraction](source/EUFInterpolation/InterpolationProcedure.lean.html).

{docstring EUF.DerivesEq}

{docstring EUF.DerivesEq.sound}

{docstring EUF.EqualityCertificateStep}

{docstring EUF.EqualityCertificate.derivation}

{docstring EUF.TermNaming}

{docstring EUF.SharedEqualityEdge}

{docstring EUF.EqualityExchangeProof}

{docstring EUF.EqualityExchangeDependencies}

{docstring EUF.EqualityInterpolationConflict}

{docstring EUF.EqualityInterpolationConflict.sound}

The abstract closure route adds convergence and conservativity hypotheses.

[Source: abstract closure](source/CongruenceClosure/AbstractCongruenceClosure.lean.html).

{docstring EUF.AbstractCongruenceClosure}

{docstring EUF.EqualityExchangeProof.ofAbstractClosure}

# The theory-leaf bridge

The certificate derives validity and annotation from one conflict. Its
annotation can then enter the local invariant in any surrounding CNF problem.

[Source: bridge](source/ClausalProofInterpolation/TheoryLemmaCertificate.lean.html)
and [embedding](source/ClausalProofInterpolation/PartialInterpolant.lean.html).

{docstring EUF.EqualityTheoryCertificate}

{docstring EUF.EqualityTheoryCertificate.theoryLemma}

{docstring EUF.EqualityTheoryCertificate.annotation}

{docstring EUF.TheoryLemmaAnnotation.toPartialInterpolant}

# Local interpolation over resolution

The resolution certificate states exact membership of the result. The
projection witness then states the extra ownership obligations required
for interpolation. Audit these as distinct contracts.

[Source: resolution](source/ClausalProofs/ClausalProof.lean.html),
[partial invariant](source/ClausalProofInterpolation/PartialInterpolant.lean.html),
and [fold](source/ClausalProofInterpolation/ClausalInterpolationTrace.lean.html).

{docstring EUF.ResolutionStep}

{docstring EUF.ClausePartition}

{docstring EUF.PartitionedResolutionStep}

{docstring EUF.IsPartialInterpolantAt}

{docstring EUF.IsPartialInterpolantAt.resolveOnSide}

{docstring EUF.IsPartialInterpolantAt.resolveOnOtherSide}

{docstring EUF.InterpolatedClauseRefutation}

{docstring EUF.InterpolatedClauseRefutation.ofTrace}

{docstring EUF.InterpolatedClauseRefutation.sound}

# Shared-interface extraction

The parent restriction and supplied trace coloring justify the automatic
semantic pass. The explicit cut certificate has a separate soundness endpoint.

[Source: shared-interface procedure](source/ClausalProofInterpolation/SharedInterfaceInterpolation.lean.html).

{docstring EUF.ParentAllowed}

{docstring EUF.ColorableClauseTrace}

{docstring EUF.SharedInterfaceSelection.allSharedSource}

{docstring EUF.ColorableClauseRefutation.interpolant}

{docstring EUF.SharedInterfaceCertificate}

{docstring EUF.SharedInterfaceCertificate.interpolant}
