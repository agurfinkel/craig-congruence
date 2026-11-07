import ClausalProofInterpolation
import ClausalProofInterpolation.Z3Proof43Trace

-- Keep the audited endpoints explicit. The build script rejects any dependency
-- outside Lean's standard logical axioms, including sorryAx.
#print axioms EUF.DerivesEq.sound
#print axioms EUF.EqualityCertificate.derivation
#print axioms EUF.EqualityInterpolationConflict.sound
#print axioms EUF.EqualityTheoryCertificate.annotation
#print axioms EUF.InterpolatedClauseRefutation.sound
#print axioms EUF.ColorableClauseRefutation.interpolant
#print axioms EUF.SharedInterfaceCertificate.interpolant
#print axioms EUF.Z3HornGap.isInterpolant
#print axioms EUF.Z3Proof43Trace.trace_interpolant_sound
