/- Complete sharded transport for cutoffTwoCanonicalCommon. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.Chunk00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.Chunk01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.Chunk02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.Chunk03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.Chunk04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.Chunk05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.Chunk06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.Chunk07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.Chunk08
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.Chunk09
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.Chunk10
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.Chunk11
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.Chunk12
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.Chunk13
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks.Chunk14

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportChunks
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph

theorem cutoffTwoCanonicalCommonTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      (cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors) (cutoffTwoCanonicalCommonFactors) := by
  have h14 := cutoffTwoCanonicalCommonChunk14Transport
  have h13 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalCommonSourceRest13 cutoffTwoCanonicalCommonTargetRest13 := by
    simpa only [cutoffTwoCanonicalCommonSourceChunk13,
      cutoffTwoCanonicalCommonTargetChunk13,
      cutoffTwoCanonicalCommonSourceRest14, cutoffTwoCanonicalCommonTargetRest14,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalCommonChunk13Transport h14
  have h12 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalCommonSourceRest12 cutoffTwoCanonicalCommonTargetRest12 := by
    simpa only [cutoffTwoCanonicalCommonSourceChunk12,
      cutoffTwoCanonicalCommonTargetChunk12,
      cutoffTwoCanonicalCommonSourceRest13, cutoffTwoCanonicalCommonTargetRest13,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalCommonChunk12Transport h13
  have h11 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalCommonSourceRest11 cutoffTwoCanonicalCommonTargetRest11 := by
    simpa only [cutoffTwoCanonicalCommonSourceChunk11,
      cutoffTwoCanonicalCommonTargetChunk11,
      cutoffTwoCanonicalCommonSourceRest12, cutoffTwoCanonicalCommonTargetRest12,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalCommonChunk11Transport h12
  have h10 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalCommonSourceRest10 cutoffTwoCanonicalCommonTargetRest10 := by
    simpa only [cutoffTwoCanonicalCommonSourceChunk10,
      cutoffTwoCanonicalCommonTargetChunk10,
      cutoffTwoCanonicalCommonSourceRest11, cutoffTwoCanonicalCommonTargetRest11,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalCommonChunk10Transport h11
  have h9 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalCommonSourceRest9 cutoffTwoCanonicalCommonTargetRest9 := by
    simpa only [cutoffTwoCanonicalCommonSourceChunk09,
      cutoffTwoCanonicalCommonTargetChunk09,
      cutoffTwoCanonicalCommonSourceRest10, cutoffTwoCanonicalCommonTargetRest10,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalCommonChunk09Transport h10
  have h8 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalCommonSourceRest8 cutoffTwoCanonicalCommonTargetRest8 := by
    simpa only [cutoffTwoCanonicalCommonSourceChunk08,
      cutoffTwoCanonicalCommonTargetChunk08,
      cutoffTwoCanonicalCommonSourceRest9, cutoffTwoCanonicalCommonTargetRest9,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalCommonChunk08Transport h9
  have h7 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalCommonSourceRest7 cutoffTwoCanonicalCommonTargetRest7 := by
    simpa only [cutoffTwoCanonicalCommonSourceChunk07,
      cutoffTwoCanonicalCommonTargetChunk07,
      cutoffTwoCanonicalCommonSourceRest8, cutoffTwoCanonicalCommonTargetRest8,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalCommonChunk07Transport h8
  have h6 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalCommonSourceRest6 cutoffTwoCanonicalCommonTargetRest6 := by
    simpa only [cutoffTwoCanonicalCommonSourceChunk06,
      cutoffTwoCanonicalCommonTargetChunk06,
      cutoffTwoCanonicalCommonSourceRest7, cutoffTwoCanonicalCommonTargetRest7,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalCommonChunk06Transport h7
  have h5 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalCommonSourceRest5 cutoffTwoCanonicalCommonTargetRest5 := by
    simpa only [cutoffTwoCanonicalCommonSourceChunk05,
      cutoffTwoCanonicalCommonTargetChunk05,
      cutoffTwoCanonicalCommonSourceRest6, cutoffTwoCanonicalCommonTargetRest6,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalCommonChunk05Transport h6
  have h4 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalCommonSourceRest4 cutoffTwoCanonicalCommonTargetRest4 := by
    simpa only [cutoffTwoCanonicalCommonSourceChunk04,
      cutoffTwoCanonicalCommonTargetChunk04,
      cutoffTwoCanonicalCommonSourceRest5, cutoffTwoCanonicalCommonTargetRest5,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalCommonChunk04Transport h5
  have h3 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalCommonSourceRest3 cutoffTwoCanonicalCommonTargetRest3 := by
    simpa only [cutoffTwoCanonicalCommonSourceChunk03,
      cutoffTwoCanonicalCommonTargetChunk03,
      cutoffTwoCanonicalCommonSourceRest4, cutoffTwoCanonicalCommonTargetRest4,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalCommonChunk03Transport h4
  have h2 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalCommonSourceRest2 cutoffTwoCanonicalCommonTargetRest2 := by
    simpa only [cutoffTwoCanonicalCommonSourceChunk02,
      cutoffTwoCanonicalCommonTargetChunk02,
      cutoffTwoCanonicalCommonSourceRest3, cutoffTwoCanonicalCommonTargetRest3,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalCommonChunk02Transport h3
  have h1 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalCommonSourceRest1 cutoffTwoCanonicalCommonTargetRest1 := by
    simpa only [cutoffTwoCanonicalCommonSourceChunk01,
      cutoffTwoCanonicalCommonTargetChunk01,
      cutoffTwoCanonicalCommonSourceRest2, cutoffTwoCanonicalCommonTargetRest2,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalCommonChunk01Transport h2
  have h0 :
      FactorListTransport 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalTransportIdentity
        cutoffTwoCanonicalCommonSourceRest0 cutoffTwoCanonicalCommonTargetRest0 := by
    simpa only [cutoffTwoCanonicalCommonSourceChunk00,
      cutoffTwoCanonicalCommonTargetChunk00,
      cutoffTwoCanonicalCommonSourceRest1, cutoffTwoCanonicalCommonTargetRest1,
      List.take_append_drop] using
        FactorListTransport.append cutoffTwoCanonicalCommonChunk00Transport h1
  simpa only [cutoffTwoCanonicalCommonSourceRest0,
    cutoffTwoCanonicalCommonTargetRest0] using h0

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded.cutoffTwoCanonicalCommonTransport
