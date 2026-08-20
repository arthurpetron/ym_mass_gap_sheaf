/- Complete sharded transport for cutoffTwoCanonicalSource00. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks.Chunk00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks.Chunk01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks.Chunk02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks.Chunk03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks.Chunk04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks.Chunk05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks.Chunk06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks.Chunk07

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Sharded

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Data
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Chunks
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate

theorem cutoffTwoCanonicalSource00Transport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 0)) (cutoffTwoCanonicalSourceFactorsAt 0) := by
  have h7 := cutoffTwoCanonicalSource00Chunk07Transport
  have h6 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalSource00SourceRest6 cutoffTwoCanonicalSource00TargetRest6 := by
    simpa only [cutoffTwoCanonicalSource00SourceChunk06,
      cutoffTwoCanonicalSource00TargetChunk06,
      cutoffTwoCanonicalSource00SourceRest7, cutoffTwoCanonicalSource00TargetRest7,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalSource00Chunk06Transport h7
  have h5 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalSource00SourceRest5 cutoffTwoCanonicalSource00TargetRest5 := by
    simpa only [cutoffTwoCanonicalSource00SourceChunk05,
      cutoffTwoCanonicalSource00TargetChunk05,
      cutoffTwoCanonicalSource00SourceRest6, cutoffTwoCanonicalSource00TargetRest6,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalSource00Chunk05Transport h6
  have h4 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalSource00SourceRest4 cutoffTwoCanonicalSource00TargetRest4 := by
    simpa only [cutoffTwoCanonicalSource00SourceChunk04,
      cutoffTwoCanonicalSource00TargetChunk04,
      cutoffTwoCanonicalSource00SourceRest5, cutoffTwoCanonicalSource00TargetRest5,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalSource00Chunk04Transport h5
  have h3 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalSource00SourceRest3 cutoffTwoCanonicalSource00TargetRest3 := by
    simpa only [cutoffTwoCanonicalSource00SourceChunk03,
      cutoffTwoCanonicalSource00TargetChunk03,
      cutoffTwoCanonicalSource00SourceRest4, cutoffTwoCanonicalSource00TargetRest4,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalSource00Chunk03Transport h4
  have h2 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalSource00SourceRest2 cutoffTwoCanonicalSource00TargetRest2 := by
    simpa only [cutoffTwoCanonicalSource00SourceChunk02,
      cutoffTwoCanonicalSource00TargetChunk02,
      cutoffTwoCanonicalSource00SourceRest3, cutoffTwoCanonicalSource00TargetRest3,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalSource00Chunk02Transport h3
  have h1 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalSource00SourceRest1 cutoffTwoCanonicalSource00TargetRest1 := by
    simpa only [cutoffTwoCanonicalSource00SourceChunk01,
      cutoffTwoCanonicalSource00TargetChunk01,
      cutoffTwoCanonicalSource00SourceRest2, cutoffTwoCanonicalSource00TargetRest2,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalSource00Chunk01Transport h2
  have h0 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalSource00SourceRest0 cutoffTwoCanonicalSource00TargetRest0 := by
    simpa only [cutoffTwoCanonicalSource00SourceChunk00,
      cutoffTwoCanonicalSource00TargetChunk00,
      cutoffTwoCanonicalSource00SourceRest1, cutoffTwoCanonicalSource00TargetRest1,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalSource00Chunk00Transport h1
  simpa only [cutoffTwoCanonicalSource00SourceRest0,
    cutoffTwoCanonicalSource00TargetRest0] using h0

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Sharded

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport00Sharded.cutoffTwoCanonicalSource00Transport
