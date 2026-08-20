/- Checked source-state 0 transport chunk 3. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Data

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Data
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def cutoffTwoCanonicalSource00Chunk03Check : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    cutoffTwoCanonicalSource00SourceChunk03 cutoffTwoCanonicalSource00TargetChunk03

theorem cutoffTwoCanonicalSource00Chunk03Check_checked :
    cutoffTwoCanonicalSource00Chunk03Check = true := by
  decide

theorem cutoffTwoCanonicalSource00Chunk03Transport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      cutoffTwoCanonicalSource00SourceChunk03 cutoffTwoCanonicalSource00TargetChunk03 :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalTransportIdentity cutoffTwoCanonicalTransportIdentity
    cutoffTwoCanonicalSource00SourceChunk03 cutoffTwoCanonicalSource00TargetChunk03
    cutoffTwoCanonicalSource00Chunk03Check_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks.cutoffTwoCanonicalSource00Chunk03Transport
