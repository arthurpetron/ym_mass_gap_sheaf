/- Checked common-factor transport chunk 10. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def cutoffTwoCanonicalCommonChunk10Check : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    cutoffTwoCanonicalCommonSourceChunk10 cutoffTwoCanonicalCommonTargetChunk10

theorem cutoffTwoCanonicalCommonChunk10Check_checked :
    cutoffTwoCanonicalCommonChunk10Check = true := by
  decide

theorem cutoffTwoCanonicalCommonChunk10Transport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      cutoffTwoCanonicalCommonSourceChunk10 cutoffTwoCanonicalCommonTargetChunk10 :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    cutoffTwoCanonicalCommonSourceChunk10 cutoffTwoCanonicalCommonTargetChunk10
    cutoffTwoCanonicalCommonChunk10Check_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.cutoffTwoCanonicalCommonChunk10Transport
