/-
# The active root occupies the first canonical trivalent vertex

The root-first face presentation places the two positive cube faces at
physical positions zero and one.  The generic canonical-link result therefore
puts their selected slot-zero terminals on the `a` and `b` half-edges of
vertex zero.  This file constructs those explicit ports and proves equality
with the terminals selected through the one-point physical half-edge fibers.

This is stronger than equality of face identifiers: it identifies the full
dependent resolved-network ports, including vertex position, leg, and strand
slot.  The next local step computes their mates on the third leg from the
stretched first-channel label.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals
import YMGap.Continuum.CanonicalLinkFirstVertexPorts

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandContinuation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot
open YMGap.Continuum.CanonicalLinkFirstVertexPorts
open YMGap.Continuum.CanonicalLinkInternalStrandContinuation
open YMGap.Continuum.CanonicalLinkPhysicalTerminalPairing
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.ResolvedTrivalentNetworkHalfEdges
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2StretchedFusionWitnessLift
open YMGap.Continuum.SU2TrivalentStrandPeeling
open YMGap.Continuum.SU2TrivalentStrandPortPairing
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Bounds and the two explicit first half-edges -/

theorem rootOrderedDegree_lower
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
  (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    2 ≤ (rootSlabLinkFaceOrder carrier).faceIds.length := by
  simp [rootSlabLinkFaceOrder, rootOrderedFaceIds]

theorem rootOrderedDegree_upper
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootSlabLinkFaceOrder carrier).faceIds.length ≤ linkIncidenceBound := by
  simpa [linkIncidenceBound] using
    (rootSlabLinkFaceOrder carrier).length_le_six

/-- Positivity excludes the degenerate two-valent source: the accepted
collapsed singleton would force the stretched sum, hence both root spins, to
vanish. -/
theorem rootOrderedRest_ne_nil
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    cubeInwardMateLinkRest K physical hK hbounded
        (cubeDebtRootIncidence carrier.word) ≠ [] := by
  intro hrest
  have hcollapsed := rootAuxiliary_mem_collapsedSpins carrier
  rw [rootCollapsedSpins_eq, hrest] at hcollapsed
  unfold fusionWitnessesForSpins at hcollapsed
  obtain ⟨_, hallowed⟩ := List.mem_filter.mp hcollapsed
  have hallowedOne : canonicalLinkConditionalAllowedB 1
      (externalSpinsOfList
        [rootLeftSpin carrier + rootRightSpin carrier])
      carrier.rootAuxiliary = true := by
    simpa only [List.length_cons, List.length_nil, Nat.zero_add] using hallowed
  rw [canonicalAllowed_one] at hallowedOne
  simp [externalSpinsOfList] at hallowedOne
  rcases hallowedOne with ⟨hfusion, hzero⟩
  have haux : carrier.rootAuxiliary 1 = 0 := by
    simpa using hzero
  rw [haux] at hfusion
  obtain ⟨depth, hdepthSum, hdepthZero, hsumDepth⟩ :=
    (YMGap.Continuum.FusionBratteli.fusionOK_iff_ladder
      (rootLeftSpin carrier + rootRightSpin carrier) 0 0).mp hfusion
  have hsum : rootLeftSpin carrier + rootRightSpin carrier = 0 := by
    omega
  have hpositive : 0 < rootLeftSpin carrier := by
    simpa [rootLeftSpin] using (leftRootCopy carrier).slot.isLt
  omega

theorem rootOrderedDegree_three
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    3 ≤ (rootSlabLinkFaceOrder carrier).faceIds.length := by
  have hrest := rootOrderedRest_ne_nil carrier
  cases htail : cubeInwardMateLinkRest K physical hK hbounded
      (cubeDebtRootIncidence carrier.word) with
  | nil => exact False.elim (hrest htail)
  | cons head tail =>
      have hlength := congrArg List.length
        (rootOrderedFaceIds_map_eq_orderedSourceSpins carrier)
      simp only [List.length_map] at hlength
      rw [rootSlabLinkFaceOrder_faceIds, hlength]
      simp [rootOrderedSourceSpins, htail]

/-- If the residual word has one physical spin, collapsed two-valent
admissibility forces that final spin to equal the stretched sum. -/
theorem rootOrderedRest_singleton_eq_sum
    {K third : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (hrest : cubeInwardMateLinkRest K physical hK hbounded
      (cubeDebtRootIncidence carrier.word) = [third]) :
    third = rootLeftSpin carrier + rootRightSpin carrier := by
  have hcollapsed := rootAuxiliary_mem_collapsedSpins carrier
  rw [rootCollapsedSpins_eq, hrest] at hcollapsed
  unfold fusionWitnessesForSpins at hcollapsed
  obtain ⟨_, hallowed⟩ := List.mem_filter.mp hcollapsed
  have hallowedTwo : canonicalLinkConditionalAllowedB 2
      (externalSpinsOfList
        [rootLeftSpin carrier + rootRightSpin carrier, third])
      carrier.rootAuxiliary = true := by
    simpa only [List.length_cons, List.length_nil, Nat.zero_add] using hallowed
  rw [canonicalAllowed_two] at hallowedTwo
  simp [externalSpinsOfList] at hallowedTwo
  rcases hallowedTwo with ⟨hfusion, hzero⟩
  have haux : carrier.rootAuxiliary 2 = 0 := by
    simpa using hzero
  rw [haux] at hfusion
  obtain ⟨depth, hdepthSum, hdepthThird, hsumDepth⟩ :=
    (YMGap.Continuum.FusionBratteli.fusionOK_iff_ladder
      (rootLeftSpin carrier + rootRightSpin carrier) third 0).mp hfusion
  omega

def rootFirstAHalfEdge
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :=
  canonicalLinkFirstAHalfEdge
    (rootOrderedDegree_lower carrier)
    (rootOrderedDegree_upper carrier)
    (orderedSlabLinkFusionWitness_mem_allowed K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))

def rootFirstBHalfEdge
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :=
  canonicalLinkFirstBHalfEdge
    (rootOrderedDegree_lower carrier)
    (rootOrderedDegree_upper carrier)
    (orderedSlabLinkFusionWitness_mem_allowed K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))

@[simp] theorem rootFirstAHalfEdge_edgeId
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootFirstAHalfEdge carrier).edgeId = 0 := by
  exact canonicalLinkFirstAHalfEdge_edgeId
    (rootOrderedDegree_lower carrier)
    (rootOrderedDegree_upper carrier)
    (orderedSlabLinkFusionWitness_mem_allowed K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))

@[simp] theorem rootFirstBHalfEdge_edgeId
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootFirstBHalfEdge carrier).edgeId = 1 := by
  exact canonicalLinkFirstBHalfEdge_edgeId
    (rootOrderedDegree_lower carrier)
    (rootOrderedDegree_upper carrier)
    (orderedSlabLinkFusionWitness_mem_allowed K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))

/-! ## 2. The first third-leg label is the stretched sum -/

theorem rootFirstVertex_output_label
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    canonicalLinkLabelling
      (rootSlabLinkFaceOrder carrier).faceIds.length
      (orderedSlabLinkExternalSpins physical
        (rootSlabLinkFaceOrder carrier))
      (rootSourceAuxiliary carrier)
      (rootFirstAHalfEdge carrier).vertex.2.2 =
        rootLeftSpin carrier + rootRightSpin carrier := by
  have hcEdge : (rootFirstAHalfEdge carrier).vertex.2.2 =
      canonicalLinkFirstOutputEdge
        (rootSlabLinkFaceOrder carrier).faceIds.length := by
    exact canonicalLinkFirstAHalfEdge_vertex_c
      (rootOrderedDegree_lower carrier)
      (rootOrderedDegree_upper carrier)
      (orderedSlabLinkFusionWitness_mem_allowed K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
  rw [hcEdge]
  cases hids : cubeInwardMateLinkRestFaceIds
      (cubeDebtRootIncidence carrier.word) with
  | nil =>
      have hspinNil : cubeInwardMateLinkRest K physical hK hbounded
          (cubeDebtRootIncidence carrier.word) = [] := by
        rw [cubeInwardMateLinkRest_eq_map_restFaceIds]
        simp [hids]
      exact False.elim ((rootOrderedRest_ne_nil carrier) hspinNil)
  | cons third tail =>
      cases tail with
      | nil =>
          have hspin : cubeInwardMateLinkRest K physical hK hbounded
              (cubeDebtRootIncidence carrier.word) = [physical third] := by
            rw [cubeInwardMateLinkRest_eq_map_restFaceIds]
            simp [hids]
          have hthird := rootOrderedRest_singleton_eq_sum
            carrier hspin
          simpa [canonicalLinkFirstOutputEdge, canonicalLinkLabelling,
            orderedSlabLinkExternalSpins, rootSlabLinkFaceOrder,
            rootOrderedFaceIds, hids, externalSpinsOfList, overlayOn] using hthird
      | cons fourth tail =>
          cases tail with
          | nil =>
              simp [canonicalLinkFirstOutputEdge, canonicalLinkLabelling,
                rootSlabLinkFaceOrder, rootOrderedFaceIds, rootSourceAuxiliary,
                cubeInwardMateLinkRest_eq_map_restFaceIds, hids,
                overlayOn, stretchedFusionWitnessLift, setEdgeLabel]
          | cons fifth tail =>
              cases tail with
              | nil =>
                  simp [canonicalLinkFirstOutputEdge, canonicalLinkLabelling,
                    rootSlabLinkFaceOrder, rootOrderedFaceIds,
                    rootSourceAuxiliary,
                    cubeInwardMateLinkRest_eq_map_restFaceIds, hids,
                    overlayOn, stretchedFusionWitnessLift, setEdgeLabel]
              | cons sixth tail =>
                  cases tail with
                  | nil =>
                      simp [canonicalLinkFirstOutputEdge,
                        canonicalLinkLabelling,
                        rootSlabLinkFaceOrder, rootOrderedFaceIds,
                        rootSourceAuxiliary,
                        cubeInwardMateLinkRest_eq_map_restFaceIds, hids,
                        overlayOn, stretchedFusionWitnessLift, setEdgeLabel]
                  | cons seventh tail =>
                      have hdegree := rootOrderedDegree_upper carrier
                      simp [rootSlabLinkFaceOrder, rootOrderedFaceIds,
                        hids, linkIncidenceBound] at hdegree

theorem rootFirstVertex_a_label
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    canonicalLinkLabelling
      (rootSlabLinkFaceOrder carrier).faceIds.length
      (orderedSlabLinkExternalSpins physical
        (rootSlabLinkFaceOrder carrier))
      (rootSourceAuxiliary carrier)
      (rootFirstAHalfEdge carrier).vertex.1 = rootLeftSpin carrier := by
  change canonicalLinkLabelling
      (rootSlabLinkFaceOrder carrier).faceIds.length
      (orderedSlabLinkExternalSpins physical
        (rootSlabLinkFaceOrder carrier))
      (rootSourceAuxiliary carrier)
      (rootFirstAHalfEdge carrier).edgeId = rootLeftSpin carrier
  rw [rootFirstAHalfEdge_edgeId]
  unfold canonicalLinkLabelling
  rw [overlayOn_apply_of_mem
    (List.mem_range.mpr (by
      have hdegree := rootOrderedDegree_lower carrier
      omega))]
  simp [orderedSlabLinkExternalSpins, rootSlabLinkFaceOrder,
    rootOrderedFaceIds, externalSpinsOfList, rootLeftSpin]

theorem rootFirstAHalfEdge_vertex_eq_firstB
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootFirstAHalfEdge carrier).vertex =
      (rootFirstBHalfEdge carrier).vertex :=
  rfl

theorem rootFirstVertex_b_label
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    canonicalLinkLabelling
      (rootSlabLinkFaceOrder carrier).faceIds.length
      (orderedSlabLinkExternalSpins physical
        (rootSlabLinkFaceOrder carrier))
      (rootSourceAuxiliary carrier)
      (rootFirstAHalfEdge carrier).vertex.2.1 = rootRightSpin carrier := by
  rw [rootFirstAHalfEdge_vertex_eq_firstB carrier]
  change canonicalLinkLabelling
      (rootSlabLinkFaceOrder carrier).faceIds.length
      (orderedSlabLinkExternalSpins physical
        (rootSlabLinkFaceOrder carrier))
      (rootSourceAuxiliary carrier)
      (rootFirstBHalfEdge carrier).edgeId = rootRightSpin carrier
  rw [rootFirstBHalfEdge_edgeId]
  unfold canonicalLinkLabelling
  rw [overlayOn_apply_of_mem
    (List.mem_range.mpr (by
      have hdegree := rootOrderedDegree_lower carrier
      omega))]
  simp [orderedSlabLinkExternalSpins, rootSlabLinkFaceOrder,
    rootOrderedFaceIds, externalSpinsOfList, rootRightSpin]

/-- The three balance equations at vertex zero are therefore exactly the
stretched resolution counts. -/
theorem rootFirstResolution_stretched_counts
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    let resolution :=
      (resolvedVertexAt
        (orderedSlabLinkResolvedStrandNetwork K physical
          (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
          (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
        (rootFirstAHalfEdge carrier).vertexIndex).strands
    resolution.ab = 0 ∧
      resolution.bc = rootRightSpin carrier ∧
      resolution.ca = rootLeftSpin carrier := by
  dsimp only
  let resolution :=
    (resolvedVertexAt
      (orderedSlabLinkResolvedStrandNetwork K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
      (rootFirstAHalfEdge carrier).vertexIndex).strands
  have ha := resolution.a_balance
  have hb := resolution.b_balance
  have hc := resolution.c_balance
  have haLabel := rootFirstVertex_a_label carrier
  have hbLabel := rootFirstVertex_b_label carrier
  have hcLabel := rootFirstVertex_output_label carrier
  change canonicalLinkLabelling
      (rootSlabLinkFaceOrder carrier).faceIds.length
      (orderedSlabLinkExternalSpins physical
        (rootSlabLinkFaceOrder carrier))
      (rootSourceAuxiliary carrier)
      (rootFirstAHalfEdge carrier).vertex.1 =
        resolution.ca + resolution.ab at ha
  change canonicalLinkLabelling
      (rootSlabLinkFaceOrder carrier).faceIds.length
      (orderedSlabLinkExternalSpins physical
        (rootSlabLinkFaceOrder carrier))
      (rootSourceAuxiliary carrier)
      (rootFirstAHalfEdge carrier).vertex.2.1 =
        resolution.bc + resolution.ab at hb
  change canonicalLinkLabelling
      (rootSlabLinkFaceOrder carrier).faceIds.length
      (orderedSlabLinkExternalSpins physical
        (rootSlabLinkFaceOrder carrier))
      (rootSourceAuxiliary carrier)
      (rootFirstAHalfEdge carrier).vertex.2.2 =
        resolution.bc + resolution.ca at hc
  rw [haLabel] at ha
  rw [hbLabel] at hb
  rw [hcLabel] at hc
  have hab : resolution.ab = 0 := by omega
  refine ⟨hab, ?_, ?_⟩
  · change resolution.bc = rootRightSpin carrier
    omega
  · change resolution.ca = rootLeftSpin carrier
    omega

theorem rootFirstResolution_bc
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (resolvedVertexAt
      (orderedSlabLinkResolvedStrandNetwork K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
      (rootFirstAHalfEdge carrier).vertexIndex).strands.bc =
        rootRightSpin carrier := by
  exact (rootFirstResolution_stretched_counts carrier).2.1

theorem rootFirstResolution_ca
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (resolvedVertexAt
      (orderedSlabLinkResolvedStrandNetwork K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
      (rootFirstAHalfEdge carrier).vertexIndex).strands.ca =
        rootLeftSpin carrier := by
  exact (rootFirstResolution_stretched_counts carrier).2.2

theorem rootFirstAHalfEdge_vertexIndex_eq_firstB
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootFirstAHalfEdge carrier).vertexIndex =
      (rootFirstBHalfEdge carrier).vertexIndex :=
  rfl

/-! ## 3. Slot-zero ports at those half-edges -/

theorem rootFirstAHalfEdge_label_positive
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    0 < canonicalLinkLabelling
      (rootSlabLinkFaceOrder carrier).faceIds.length
      (orderedSlabLinkExternalSpins physical
        (rootSlabLinkFaceOrder carrier))
      (rootSourceAuxiliary carrier)
      (rootFirstAHalfEdge carrier).edgeId := by
  rw [rootFirstAHalfEdge_edgeId]
  unfold canonicalLinkLabelling
  rw [overlayOn_apply_of_mem
    (List.mem_range.mpr (by
      have hdegree := rootOrderedDegree_lower carrier
      omega))]
  simpa [orderedSlabLinkExternalSpins, externalSpinsOfList,
    rootSlabLinkFaceOrder, rootOrderedFaceIds, rootLeftSpin] using
      (leftRootCopy carrier).slot.isLt

theorem rootFirstBHalfEdge_label_positive
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    0 < canonicalLinkLabelling
      (rootSlabLinkFaceOrder carrier).faceIds.length
      (orderedSlabLinkExternalSpins physical
        (rootSlabLinkFaceOrder carrier))
      (rootSourceAuxiliary carrier)
      (rootFirstBHalfEdge carrier).edgeId := by
  rw [rootFirstBHalfEdge_edgeId]
  unfold canonicalLinkLabelling
  rw [overlayOn_apply_of_mem
    (List.mem_range.mpr (by
      have hdegree := rootOrderedDegree_lower carrier
      omega))]
  simpa [orderedSlabLinkExternalSpins, externalSpinsOfList,
    rootSlabLinkFaceOrder, rootOrderedFaceIds, rootRightSpin] using
      (rightRootCopy carrier).slot.isLt

def rootFirstAPort
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :=
  resolvedNetworkHalfEdgePortAt (rootFirstAHalfEdge carrier) 0
    (rootFirstAHalfEdge_label_positive carrier)

def rootFirstBPort
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :=
  resolvedNetworkHalfEdgePortAt (rootFirstBHalfEdge carrier) 0
    (rootFirstBHalfEdge_label_positive carrier)

theorem rootFirstAPort_localMate_leg
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootFirstAPort carrier).localMate.leg = .c := by
  have hpositive : 0 < rootLeftSpin carrier := by
    simpa [rootLeftSpin] using (leftRootCopy carrier).slot.isLt
  have hca : 0 <
      (resolvedVertexAt
        (orderedSlabLinkResolvedStrandNetwork K physical
          (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
          (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
        (rootFirstAHalfEdge carrier).vertexIndex).strands.ca := by
    rw [rootFirstResolution_ca carrier]
    exact hpositive
  unfold rootFirstAPort
  exact resolvedNetworkHalfEdgePortAt_localMate_leg_of_a
    (rootFirstAHalfEdge carrier) 0
    (rootFirstAHalfEdge_label_positive carrier)
    (canonicalLinkFirstAHalfEdge_leg
      (rootOrderedDegree_lower carrier)
      (rootOrderedDegree_upper carrier)
      (orderedSlabLinkFusionWitness_mem_allowed K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)))
    hca

theorem rootFirstBPort_localMate_leg
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootFirstBPort carrier).localMate.leg = .c := by
  have hpositive : 0 < rootRightSpin carrier := by
    simpa [rootRightSpin] using (rightRootCopy carrier).slot.isLt
  have hbc : 0 <
      (resolvedVertexAt
        (orderedSlabLinkResolvedStrandNetwork K physical
          (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
          (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
        (rootFirstBHalfEdge carrier).vertexIndex).strands.bc := by
    rw [← rootFirstAHalfEdge_vertexIndex_eq_firstB carrier]
    rw [rootFirstResolution_bc carrier]
    exact hpositive
  unfold rootFirstBPort
  exact resolvedNetworkHalfEdgePortAt_localMate_leg_of_b
    (rootFirstBHalfEdge carrier) 0
    (rootFirstBHalfEdge_label_positive carrier)
    (canonicalLinkFirstBHalfEdge_leg
      (rootOrderedDegree_lower carrier)
      (rootOrderedDegree_upper carrier)
      (orderedSlabLinkFusionWitness_mem_allowed K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)))
    hbc

theorem rootFirstAPort_localMate_slot
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootFirstAPort carrier).localMate.slot = rootRightSpin carrier := by
  have hpositive : 0 < rootLeftSpin carrier := by
    simpa [rootLeftSpin] using (leftRootCopy carrier).slot.isLt
  have hca : 0 <
      (resolvedVertexAt
        (orderedSlabLinkResolvedStrandNetwork K physical
          (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
          (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
        (rootFirstAHalfEdge carrier).vertexIndex).strands.ca := by
    rw [rootFirstResolution_ca carrier]
    exact hpositive
  exact calc
    (rootFirstAPort carrier).localMate.slot =
        (resolvedVertexAt
          (orderedSlabLinkResolvedStrandNetwork K physical
            (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
            (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
          (rootFirstAHalfEdge carrier).vertexIndex).strands.bc + 0 :=
      resolvedNetworkHalfEdgePortAt_localMate_slot_of_a
        (rootFirstAHalfEdge carrier) 0
        (rootFirstAHalfEdge_label_positive carrier)
        (canonicalLinkFirstAHalfEdge_leg
          (rootOrderedDegree_lower carrier)
          (rootOrderedDegree_upper carrier)
          (orderedSlabLinkFusionWitness_mem_allowed K physical
            (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
            (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)))
        hca
    _ = rootRightSpin carrier := by
      exact rootFirstResolution_bc carrier

theorem rootFirstBPort_localMate_slot
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootFirstBPort carrier).localMate.slot = 0 := by
  have hpositive : 0 < rootRightSpin carrier := by
    simpa [rootRightSpin] using (rightRootCopy carrier).slot.isLt
  have hbc : 0 <
      (resolvedVertexAt
        (orderedSlabLinkResolvedStrandNetwork K physical
          (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
          (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
        (rootFirstBHalfEdge carrier).vertexIndex).strands.bc := by
    rw [← rootFirstAHalfEdge_vertexIndex_eq_firstB carrier]
    rw [rootFirstResolution_bc carrier]
    exact hpositive
  unfold rootFirstBPort
  exact resolvedNetworkHalfEdgePortAt_localMate_slot_of_b
    (rootFirstBHalfEdge carrier) 0
    (rootFirstBHalfEdge_label_positive carrier)
    (canonicalLinkFirstBHalfEdge_leg
      (rootOrderedDegree_lower carrier)
      (rootOrderedDegree_upper carrier)
      (orderedSlabLinkFusionWitness_mem_allowed K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)))
    hbc

def rootFirstATerminal
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    OrderedSlabLinkPhysicalStrandTerminal K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier) :=
  ⟨rootFirstAPort carrier, by
    unfold rootFirstAPort
    rw [resolvedNetworkHalfEdgePortAt_edgeId,
      rootFirstAHalfEdge_edgeId]
    have hdegree := rootOrderedDegree_lower carrier
    omega⟩

def rootFirstBTerminal
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    OrderedSlabLinkPhysicalStrandTerminal K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier) :=
  ⟨rootFirstBPort carrier, by
    unfold rootFirstBPort
    rw [resolvedNetworkHalfEdgePortAt_edgeId,
      rootFirstBHalfEdge_edgeId]
    have hdegree := rootOrderedDegree_lower carrier
    omega⟩

/-! ## 4. Equality with the selected active-root terminals -/

theorem rootLeftOrderedTerminal_eq_firstA
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootLeftOrderedTerminal carrier).1 =
      (rootFirstATerminal carrier).1 := by
  apply resolvedNetworkPort_eq_of_halfEdge_eq_of_slot_eq
  · apply canonicalPhysicalTerminals_halfEdge_eq_of_edgeId_eq
      (rootOrderedDegree_upper carrier)
      (orderedSlabLinkFusionWitness_mem_allowed K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
    unfold rootLeftOrderedTerminal rootFirstATerminal rootFirstAPort
    rw [orderedSlabLinkPhysicalTerminalAt_edgeId,
      resolvedNetworkHalfEdgePortAt_edgeId,
      rootFirstAHalfEdge_edgeId]
    rfl
  · unfold rootLeftOrderedTerminal rootFirstATerminal rootFirstAPort
    rw [orderedSlabLinkPhysicalTerminalAt_slot,
      resolvedNetworkHalfEdgePortAt_slot]
    rfl

theorem rootRightOrderedTerminal_eq_firstB
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootRightOrderedTerminal carrier).1 =
      (rootFirstBTerminal carrier).1 := by
  apply resolvedNetworkPort_eq_of_halfEdge_eq_of_slot_eq
  · apply canonicalPhysicalTerminals_halfEdge_eq_of_edgeId_eq
      (rootOrderedDegree_upper carrier)
      (orderedSlabLinkFusionWitness_mem_allowed K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
    unfold rootRightOrderedTerminal rootFirstBTerminal rootFirstBPort
    rw [orderedSlabLinkPhysicalTerminalAt_edgeId,
      resolvedNetworkHalfEdgePortAt_edgeId,
      rootFirstBHalfEdge_edgeId]
    rfl
  · unfold rootRightOrderedTerminal rootFirstBTerminal rootFirstBPort
    rw [orderedSlabLinkPhysicalTerminalAt_slot,
      resolvedNetworkHalfEdgePortAt_slot]
    rfl

/-! ## 5. The selected terminals enter disjoint stretched-channel slots -/

theorem rootLeftOrderedTerminal_localMate_leg
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootLeftOrderedTerminal carrier).1.localMate.leg = .c := by
  rw [rootLeftOrderedTerminal_eq_firstA carrier]
  exact rootFirstAPort_localMate_leg carrier

theorem rootRightOrderedTerminal_localMate_leg
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootRightOrderedTerminal carrier).1.localMate.leg = .c := by
  rw [rootRightOrderedTerminal_eq_firstB carrier]
  exact rootFirstBPort_localMate_leg carrier

theorem rootLeftOrderedTerminal_localMate_slot
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootLeftOrderedTerminal carrier).1.localMate.slot =
      rootRightSpin carrier := by
  rw [rootLeftOrderedTerminal_eq_firstA carrier]
  exact rootFirstAPort_localMate_slot carrier

theorem rootRightOrderedTerminal_localMate_slot
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootRightOrderedTerminal carrier).1.localMate.slot = 0 := by
  rw [rootRightOrderedTerminal_eq_firstB carrier]
  exact rootFirstBPort_localMate_slot carrier

/-- The two positive root strands enter different copies of their common
stretched channel: the right root enters slot zero and the left root begins
after all `rootRightSpin` copies. -/
theorem rootOrderedTerminal_localMates_ne
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootLeftOrderedTerminal carrier).1.localMate ≠
      (rootRightOrderedTerminal carrier).1.localMate := by
  intro heq
  have hslot := congrArg ResolvedNetworkPort.slot heq
  rw [rootLeftOrderedTerminal_localMate_slot carrier,
    rootRightOrderedTerminal_localMate_slot carrier] at hslot
  have hpositive : 0 < rootRightSpin carrier := by
    simpa [rootRightSpin] using (rightRootCopy carrier).slot.isLt
  omega

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.rootFirstAHalfEdge
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.rootFirstBHalfEdge
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.rootOrderedRest_ne_nil
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.rootFirstVertex_output_label
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.rootFirstResolution_stretched_counts
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.rootFirstAPort_localMate_slot
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.rootFirstBPort_localMate_slot
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.rootLeftOrderedTerminal_eq_firstA
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.rootRightOrderedTerminal_eq_firstB
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.rootLeftOrderedTerminal_localMate_slot
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.rootRightOrderedTerminal_localMate_slot
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.rootOrderedTerminal_localMates_ne
