/- Checked common-factor transport chunk 5. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def cutoffTwoCanonicalCommonChunk05Check : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    cutoffTwoCanonicalCommonSourceChunk05 cutoffTwoCanonicalCommonTargetChunk05

theorem cutoffTwoCanonicalCommonChunk05Check_checked :
    cutoffTwoCanonicalCommonChunk05Check = true := by
  decide

theorem cutoffTwoCanonicalCommonChunk05Transport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      cutoffTwoCanonicalCommonSourceChunk05 cutoffTwoCanonicalCommonTargetChunk05 :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    cutoffTwoCanonicalCommonSourceChunk05 cutoffTwoCanonicalCommonTargetChunk05
    cutoffTwoCanonicalCommonChunk05Check_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.cutoffTwoCanonicalCommonChunk05Transport
