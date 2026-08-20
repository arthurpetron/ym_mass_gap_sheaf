/- Checked common-factor transport chunk 6. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def cutoffTwoCanonicalCommonChunk06Check : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    cutoffTwoCanonicalCommonSourceChunk06 cutoffTwoCanonicalCommonTargetChunk06

theorem cutoffTwoCanonicalCommonChunk06Check_checked :
    cutoffTwoCanonicalCommonChunk06Check = true := by
  decide

theorem cutoffTwoCanonicalCommonChunk06Transport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      cutoffTwoCanonicalCommonSourceChunk06 cutoffTwoCanonicalCommonTargetChunk06 :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    cutoffTwoCanonicalCommonSourceChunk06 cutoffTwoCanonicalCommonTargetChunk06
    cutoffTwoCanonicalCommonChunk06Check_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.cutoffTwoCanonicalCommonChunk06Transport
