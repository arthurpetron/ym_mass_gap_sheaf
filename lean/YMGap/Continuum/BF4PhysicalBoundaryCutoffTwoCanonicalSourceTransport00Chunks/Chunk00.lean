/- Checked source-state 0 transport chunk 0. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Data

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Data
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def cutoffTwoCanonicalSource00Chunk00Check : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    cutoffTwoCanonicalSource00SourceChunk00 cutoffTwoCanonicalSource00TargetChunk00

theorem cutoffTwoCanonicalSource00Chunk00Check_checked :
    cutoffTwoCanonicalSource00Chunk00Check = true := by
  decide

theorem cutoffTwoCanonicalSource00Chunk00Transport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      cutoffTwoCanonicalSource00SourceChunk00 cutoffTwoCanonicalSource00TargetChunk00 :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    cutoffTwoCanonicalSource00SourceChunk00 cutoffTwoCanonicalSource00TargetChunk00
    cutoffTwoCanonicalSource00Chunk00Check_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks.cutoffTwoCanonicalSource00Chunk00Transport
