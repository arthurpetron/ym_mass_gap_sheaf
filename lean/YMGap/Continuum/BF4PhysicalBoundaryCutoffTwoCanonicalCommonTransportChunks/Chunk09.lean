/- Checked common-factor transport chunk 9. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def cutoffTwoCanonicalCommonChunk09Check : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    cutoffTwoCanonicalCommonSourceChunk09 cutoffTwoCanonicalCommonTargetChunk09

theorem cutoffTwoCanonicalCommonChunk09Check_checked :
    cutoffTwoCanonicalCommonChunk09Check = true := by
  decide

theorem cutoffTwoCanonicalCommonChunk09Transport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      cutoffTwoCanonicalCommonSourceChunk09 cutoffTwoCanonicalCommonTargetChunk09 :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    cutoffTwoCanonicalCommonSourceChunk09 cutoffTwoCanonicalCommonTargetChunk09
    cutoffTwoCanonicalCommonChunk09Check_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.cutoffTwoCanonicalCommonChunk09Transport
