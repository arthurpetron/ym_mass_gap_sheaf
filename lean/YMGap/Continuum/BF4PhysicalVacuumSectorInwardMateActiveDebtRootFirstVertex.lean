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

/-! ## 2. Slot-zero ports at those half-edges -/

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

/-! ## 3. Equality with the selected active-root terminals -/

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

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.rootFirstAHalfEdge
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.rootFirstBHalfEdge
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.rootLeftOrderedTerminal_eq_firstA
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.rootRightOrderedTerminal_eq_firstB
