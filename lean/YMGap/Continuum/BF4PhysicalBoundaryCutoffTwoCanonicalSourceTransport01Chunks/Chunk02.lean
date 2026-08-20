/- Checked source-state 1 transport chunk 2. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Data

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Chunks

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Data
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def cutoffTwoCanonicalSource01Chunk02Check : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    cutoffTwoCanonicalSource01SourceChunk02 cutoffTwoCanonicalSource01TargetChunk02

theorem cutoffTwoCanonicalSource01Chunk02Check_checked :
    cutoffTwoCanonicalSource01Chunk02Check = true := by
  decide

theorem cutoffTwoCanonicalSource01Chunk02Transport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      cutoffTwoCanonicalSource01SourceChunk02 cutoffTwoCanonicalSource01TargetChunk02 :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    cutoffTwoCanonicalSource01SourceChunk02 cutoffTwoCanonicalSource01TargetChunk02
    cutoffTwoCanonicalSource01Chunk02Check_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Chunks

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Chunks.cutoffTwoCanonicalSource01Chunk02Transport
