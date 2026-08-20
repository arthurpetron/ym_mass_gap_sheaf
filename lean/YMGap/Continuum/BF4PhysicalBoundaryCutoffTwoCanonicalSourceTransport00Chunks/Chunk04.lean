/- Checked source-state 0 transport chunk 4. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Data

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Data
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def cutoffTwoCanonicalSource00Chunk04Check : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    cutoffTwoCanonicalSource00SourceChunk04 cutoffTwoCanonicalSource00TargetChunk04

theorem cutoffTwoCanonicalSource00Chunk04Check_checked :
    cutoffTwoCanonicalSource00Chunk04Check = true := by
  decide

theorem cutoffTwoCanonicalSource00Chunk04Transport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      cutoffTwoCanonicalSource00SourceChunk04 cutoffTwoCanonicalSource00TargetChunk04 :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    cutoffTwoCanonicalSource00SourceChunk04 cutoffTwoCanonicalSource00TargetChunk04
    cutoffTwoCanonicalSource00Chunk04Check_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks.cutoffTwoCanonicalSource00Chunk04Transport
