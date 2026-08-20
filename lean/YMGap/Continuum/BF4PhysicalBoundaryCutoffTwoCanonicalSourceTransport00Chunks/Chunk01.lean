/- Checked source-state 0 transport chunk 1. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Data

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Data
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def cutoffTwoCanonicalSource00Chunk01Check : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    cutoffTwoCanonicalSource00SourceChunk01 cutoffTwoCanonicalSource00TargetChunk01

theorem cutoffTwoCanonicalSource00Chunk01Check_checked :
    cutoffTwoCanonicalSource00Chunk01Check = true := by
  decide

theorem cutoffTwoCanonicalSource00Chunk01Transport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      cutoffTwoCanonicalSource00SourceChunk01 cutoffTwoCanonicalSource00TargetChunk01 :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    cutoffTwoCanonicalSource00SourceChunk01 cutoffTwoCanonicalSource00TargetChunk01
    cutoffTwoCanonicalSource00Chunk01Check_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks.cutoffTwoCanonicalSource00Chunk01Transport
