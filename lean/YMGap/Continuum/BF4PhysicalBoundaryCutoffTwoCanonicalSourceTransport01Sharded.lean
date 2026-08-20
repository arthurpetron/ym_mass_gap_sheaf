/- Complete sharded transport for cutoffTwoCanonicalSource01. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Chunks.Chunk00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Chunks.Chunk01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Chunks.Chunk02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Chunks.Chunk03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Chunks.Chunk04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Chunks.Chunk05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Chunks.Chunk06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Chunks.Chunk07

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Sharded

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Data
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Chunks
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate

theorem cutoffTwoCanonicalSource01Transport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 1)) (cutoffTwoCanonicalSourceFactorsAt 1) := by
  have h7 := cutoffTwoCanonicalSource01Chunk07Transport
  have h6 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalSource01SourceRest6 cutoffTwoCanonicalSource01TargetRest6 := by
    simpa only [cutoffTwoCanonicalSource01SourceChunk06,
      cutoffTwoCanonicalSource01TargetChunk06,
      cutoffTwoCanonicalSource01SourceRest7, cutoffTwoCanonicalSource01TargetRest7,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalSource01Chunk06Transport h7
  have h5 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalSource01SourceRest5 cutoffTwoCanonicalSource01TargetRest5 := by
    simpa only [cutoffTwoCanonicalSource01SourceChunk05,
      cutoffTwoCanonicalSource01TargetChunk05,
      cutoffTwoCanonicalSource01SourceRest6, cutoffTwoCanonicalSource01TargetRest6,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalSource01Chunk05Transport h6
  have h4 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalSource01SourceRest4 cutoffTwoCanonicalSource01TargetRest4 := by
    simpa only [cutoffTwoCanonicalSource01SourceChunk04,
      cutoffTwoCanonicalSource01TargetChunk04,
      cutoffTwoCanonicalSource01SourceRest5, cutoffTwoCanonicalSource01TargetRest5,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalSource01Chunk04Transport h5
  have h3 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalSource01SourceRest3 cutoffTwoCanonicalSource01TargetRest3 := by
    simpa only [cutoffTwoCanonicalSource01SourceChunk03,
      cutoffTwoCanonicalSource01TargetChunk03,
      cutoffTwoCanonicalSource01SourceRest4, cutoffTwoCanonicalSource01TargetRest4,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalSource01Chunk03Transport h4
  have h2 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalSource01SourceRest2 cutoffTwoCanonicalSource01TargetRest2 := by
    simpa only [cutoffTwoCanonicalSource01SourceChunk02,
      cutoffTwoCanonicalSource01TargetChunk02,
      cutoffTwoCanonicalSource01SourceRest3, cutoffTwoCanonicalSource01TargetRest3,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalSource01Chunk02Transport h3
  have h1 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalSource01SourceRest1 cutoffTwoCanonicalSource01TargetRest1 := by
    simpa only [cutoffTwoCanonicalSource01SourceChunk01,
      cutoffTwoCanonicalSource01TargetChunk01,
      cutoffTwoCanonicalSource01SourceRest2, cutoffTwoCanonicalSource01TargetRest2,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalSource01Chunk01Transport h2
  have h0 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalSource01SourceRest0 cutoffTwoCanonicalSource01TargetRest0 := by
    simpa only [cutoffTwoCanonicalSource01SourceChunk00,
      cutoffTwoCanonicalSource01TargetChunk00,
      cutoffTwoCanonicalSource01SourceRest1, cutoffTwoCanonicalSource01TargetRest1,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalSource01Chunk00Transport h1
  simpa only [cutoffTwoCanonicalSource01SourceRest0,
    cutoffTwoCanonicalSource01TargetRest0] using h0

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Sharded

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Sharded.cutoffTwoCanonicalSource01Transport
