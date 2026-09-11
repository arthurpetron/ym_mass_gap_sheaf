/-
# The active-root first channel is physical or internally continued

The two positive active-root strands have already been identified with
slot-zero ports on the first canonical trivalent vertex, and their local
mates occupy disjoint slots on its `c` leg.  This file identifies the exact
graph edge carrying those mates and constructively exposes the only two
geometric possibilities:

* at valence three the shared channel is physical edge `2`;
* at valence four, five, or six it is the first internal fusion edge.

The case split is retained as `Type`-valued data so downstream strand
compilers can consume its witnesses.  No `Classical`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or trusted
external computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex
import YMGap.Continuum.CanonicalLinkPhysicalTerminalPartner
import YMGap.Continuum.CanonicalLinkStrandStep

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot
open YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity
open YMGap.Continuum.CanonicalLinkFirstVertexPorts
open YMGap.Continuum.CanonicalLinkInternalStrandContinuation
open YMGap.Continuum.CanonicalLinkPhysicalTerminalPartner
open YMGap.Continuum.CanonicalLinkStrandStep
open YMGap.Continuum.CanonicalLinkStrandTerminal
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. The common first-channel edge -/

theorem rootFirstAPort_localMate_edgeId
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootFirstAPort carrier).localMate.edgeId =
      canonicalLinkFirstOutputEdge
        (rootSlabLinkFaceOrder carrier).faceIds.length := by
  unfold ResolvedNetworkPort.edgeId
  rw [rootFirstAPort_localMate_leg carrier]
  change (rootFirstAHalfEdge carrier).vertex.2.2 = _
  exact canonicalLinkFirstAHalfEdge_vertex_c
    (rootOrderedDegree_lower carrier)
    (rootOrderedDegree_upper carrier)
    (orderedSlabLinkFusionWitness_mem_allowed K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))

theorem rootFirstBPort_localMate_edgeId
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootFirstBPort carrier).localMate.edgeId =
      canonicalLinkFirstOutputEdge
        (rootSlabLinkFaceOrder carrier).faceIds.length := by
  unfold ResolvedNetworkPort.edgeId
  rw [rootFirstBPort_localMate_leg carrier]
  change (rootFirstBHalfEdge carrier).vertex.2.2 = _
  exact canonicalLinkFirstBHalfEdge_vertex_c
    (rootOrderedDegree_lower carrier)
    (rootOrderedDegree_upper carrier)
    (orderedSlabLinkFusionWitness_mem_allowed K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))

theorem rootLeftOrderedTerminal_localMate_edgeId
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootLeftOrderedTerminal carrier).1.localMate.edgeId =
      canonicalLinkFirstOutputEdge
        (rootSlabLinkFaceOrder carrier).faceIds.length := by
  rw [rootLeftOrderedTerminal_eq_firstA carrier]
  exact rootFirstAPort_localMate_edgeId carrier

theorem rootRightOrderedTerminal_localMate_edgeId
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootRightOrderedTerminal carrier).1.localMate.edgeId =
      canonicalLinkFirstOutputEdge
        (rootSlabLinkFaceOrder carrier).faceIds.length := by
  rw [rootRightOrderedTerminal_eq_firstB carrier]
  exact rootFirstBPort_localMate_edgeId carrier

/-! ## 2. Constructive physical/internal branch -/

/-- Data consumed by the next strand compiler: both selected root strands
either stop immediately on physical edge two, or both require same-slot
continuation across the first internal fusion edge. -/
inductive RootFirstChannelClass
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) : Type
  | physical
      (degree_eq_three :
        (rootSlabLinkFaceOrder carrier).faceIds.length = 3)
      (left_physical :
        (rootLeftOrderedTerminal carrier).1.localMate.edgeId <
          (rootSlabLinkFaceOrder carrier).faceIds.length)
      (right_physical :
        (rootRightOrderedTerminal carrier).1.localMate.edgeId <
          (rootSlabLinkFaceOrder carrier).faceIds.length)
  | internal
      (degree_at_least_four :
        4 ≤ (rootSlabLinkFaceOrder carrier).faceIds.length)
      (left_internal :
        (rootLeftOrderedTerminal carrier).1.localMate.edgeId ∈
          canonicalInternalFusionEdges
            (rootSlabLinkFaceOrder carrier).faceIds.length)
      (right_internal :
        (rootRightOrderedTerminal carrier).1.localMate.edgeId ∈
          canonicalInternalFusionEdges
            (rootSlabLinkFaceOrder carrier).faceIds.length)

/-- Every active root constructively supplies exactly the downstream branch
witnesses appropriate to its incident valence. -/
def rootFirstChannelClass
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    RootFirstChannelClass carrier := by
  let degree := (rootSlabLinkFaceOrder carrier).faceIds.length
  by_cases hthree : degree = 3
  · apply RootFirstChannelClass.physical hthree
    · rw [rootLeftOrderedTerminal_localMate_edgeId carrier]
      exact canonicalLinkFirstOutputEdge_physical_of_degree_eq_three hthree
    · rw [rootRightOrderedTerminal_localMate_edgeId carrier]
      exact canonicalLinkFirstOutputEdge_physical_of_degree_eq_three hthree
  · have hfour : 4 ≤ degree := by
      have hlower := rootOrderedDegree_three carrier
      omega
    have hinternal : canonicalLinkFirstOutputEdge degree ∈
        canonicalInternalFusionEdges degree :=
      canonicalLinkFirstOutputEdge_mem_internal hfour
        (rootOrderedDegree_upper carrier)
    apply RootFirstChannelClass.internal hfour
    · rw [rootLeftOrderedTerminal_localMate_edgeId carrier]
      exact hinternal
    · rw [rootRightOrderedTerminal_localMate_edgeId carrier]
      exact hinternal

/-! ## 3. The first stop-or-advance compiler calls -/

def rootLeftFirstChannelStep
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :=
  canonicalLinkStrandStep
    (rootOrderedDegree_upper carrier)
    (orderedSlabLinkFusionWitness_mem_allowed K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
    (rootLeftOrderedTerminal carrier).1.localMate

def rootRightFirstChannelStep
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :=
  canonicalLinkStrandStep
    (rootOrderedDegree_upper carrier)
    (orderedSlabLinkFusionWitness_mem_allowed K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
    (rootRightOrderedTerminal carrier).1.localMate

theorem rootLeftFirstChannelStep_of_physical
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (hphysical :
      (rootLeftOrderedTerminal carrier).1.localMate.edgeId <
        (rootSlabLinkFaceOrder carrier).faceIds.length) :
    rootLeftFirstChannelStep carrier =
      Sum.inl ⟨(rootLeftOrderedTerminal carrier).1.localMate,
        hphysical⟩ := by
  unfold rootLeftFirstChannelStep
  exact canonicalLinkStrandStep_of_physical
    (rootOrderedDegree_upper carrier)
    (orderedSlabLinkFusionWitness_mem_allowed K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
    (rootLeftOrderedTerminal carrier).1.localMate hphysical

theorem rootRightFirstChannelStep_of_physical
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (hphysical :
      (rootRightOrderedTerminal carrier).1.localMate.edgeId <
        (rootSlabLinkFaceOrder carrier).faceIds.length) :
    rootRightFirstChannelStep carrier =
      Sum.inl ⟨(rootRightOrderedTerminal carrier).1.localMate,
        hphysical⟩ := by
  unfold rootRightFirstChannelStep
  exact canonicalLinkStrandStep_of_physical
    (rootOrderedDegree_upper carrier)
    (orderedSlabLinkFusionWitness_mem_allowed K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
    (rootRightOrderedTerminal carrier).1.localMate hphysical

theorem rootLeftFirstChannelStep_of_internal
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (hinternal :
      (rootLeftOrderedTerminal carrier).1.localMate.edgeId ∈
        canonicalInternalFusionEdges
          (rootSlabLinkFaceOrder carrier).faceIds.length) :
    rootLeftFirstChannelStep carrier =
      Sum.inr
        (canonicalInternalStrandContinue
          (rootOrderedDegree_upper carrier)
          (orderedSlabLinkFusionWitness_mem_allowed K physical
            (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
            (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
          hinternal
          (⟨(rootLeftOrderedTerminal carrier).1.localMate, rfl⟩ :
            CanonicalInternalStrandPort
              (rootLeftOrderedTerminal carrier).1.localMate.edgeId
              (orderedSlabLinkExternalSpins physical
                (rootSlabLinkFaceOrder carrier))
              (rootSourceAuxiliary carrier)
              (orderedSlabLinkFusionWitness_mem_allowed K physical
                (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
                (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses
                  carrier)))).1.localMate := by
  unfold rootLeftFirstChannelStep
  exact canonicalLinkStrandStep_of_internal
    (rootOrderedDegree_upper carrier)
    (orderedSlabLinkFusionWitness_mem_allowed K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
    (rootLeftOrderedTerminal carrier).1.localMate hinternal

theorem rootRightFirstChannelStep_of_internal
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded)
    (hinternal :
      (rootRightOrderedTerminal carrier).1.localMate.edgeId ∈
        canonicalInternalFusionEdges
          (rootSlabLinkFaceOrder carrier).faceIds.length) :
    rootRightFirstChannelStep carrier =
      Sum.inr
        (canonicalInternalStrandContinue
          (rootOrderedDegree_upper carrier)
          (orderedSlabLinkFusionWitness_mem_allowed K physical
            (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
            (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
          hinternal
          (⟨(rootRightOrderedTerminal carrier).1.localMate, rfl⟩ :
            CanonicalInternalStrandPort
              (rootRightOrderedTerminal carrier).1.localMate.edgeId
              (orderedSlabLinkExternalSpins physical
                (rootSlabLinkFaceOrder carrier))
              (rootSourceAuxiliary carrier)
              (orderedSlabLinkFusionWitness_mem_allowed K physical
                (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
                (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses
                  carrier)))).1.localMate := by
  unfold rootRightFirstChannelStep
  exact canonicalLinkStrandStep_of_internal
    (rootOrderedDegree_upper carrier)
    (orderedSlabLinkFusionWitness_mem_allowed K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
    (rootRightOrderedTerminal carrier).1.localMate hinternal

/-! ## 4. Retained paths to the two physical endpoints -/

/-- The physical endpoint reached from the left root terminal's local mate. -/
def rootLeftFirstChannelPartner
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :=
  canonicalPhysicalStrandPartner
    (rootOrderedDegree_upper carrier)
    (orderedSlabLinkFusionWitness_mem_allowed K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
    (rootLeftOrderedTerminal carrier)

/-- The physical endpoint reached from the right root terminal's local mate. -/
def rootRightFirstChannelPartner
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :=
  canonicalPhysicalStrandPartner
    (rootOrderedDegree_upper carrier)
    (orderedSlabLinkFusionWitness_mem_allowed K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
    (rootRightOrderedTerminal carrier)

/-- The left endpoint is accompanied by its complete internal-advance path. -/
def rootLeftFirstChannelPartnerPath
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    CanonicalStrandPathToPhysical
      (rootOrderedDegree_upper carrier)
      (orderedSlabLinkFusionWitness_mem_allowed K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
      (rootLeftOrderedTerminal carrier).1.localMate
      (rootLeftFirstChannelPartner carrier) :=
  canonicalPhysicalStrandPartner_path
    (rootOrderedDegree_upper carrier)
    (orderedSlabLinkFusionWitness_mem_allowed K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
    (rootLeftOrderedTerminal carrier)

/-- The right endpoint is accompanied by its complete internal-advance path. -/
def rootRightFirstChannelPartnerPath
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    CanonicalStrandPathToPhysical
      (rootOrderedDegree_upper carrier)
      (orderedSlabLinkFusionWitness_mem_allowed K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
      (rootRightOrderedTerminal carrier).1.localMate
      (rootRightFirstChannelPartner carrier) :=
  canonicalPhysicalStrandPartner_path
    (rootOrderedDegree_upper carrier)
    (orderedSlabLinkFusionWitness_mem_allowed K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier))
    (rootRightOrderedTerminal carrier)

/-- The two distinguished input terminals are different already at their
physical edge identifiers zero and one. -/
theorem rootOrderedTerminals_ne
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    rootLeftOrderedTerminal carrier ≠ rootRightOrderedTerminal carrier := by
  intro heq
  have hedge := congrArg
    (fun terminal => terminal.1.edgeId) heq
  change (rootLeftOrderedTerminal carrier).1.edgeId =
    (rootRightOrderedTerminal carrier).1.edgeId at hedge
  rw [rootLeftOrderedTerminal_eq_firstA carrier,
    rootRightOrderedTerminal_eq_firstB carrier] at hedge
  unfold rootFirstATerminal rootFirstBTerminal rootFirstAPort rootFirstBPort at hedge
  rw [resolvedNetworkHalfEdgePortAt_edgeId,
    resolvedNetworkHalfEdgePortAt_edgeId,
    rootFirstAHalfEdge_edgeId, rootFirstBHalfEdge_edgeId] at hedge
  omega

/-- Distinct input terminals have distinct partners because the physical
partner operation is an involution. -/
theorem rootFirstChannelPartners_ne
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    rootLeftFirstChannelPartner carrier ≠
      rootRightFirstChannelPartner carrier := by
  intro hpartners
  have hback := congrArg
    (canonicalPhysicalStrandPartner
      (rootOrderedDegree_upper carrier)
      (orderedSlabLinkFusionWitness_mem_allowed K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)))
    hpartners
  unfold rootLeftFirstChannelPartner rootRightFirstChannelPartner at hback
  rw [canonicalPhysicalStrandPartner_involutive,
    canonicalPhysicalStrandPartner_involutive] at hback
  exact rootOrderedTerminals_ne carrier hback

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.rootFirstAPort_localMate_edgeId
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.rootFirstBPort_localMate_edgeId
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.rootLeftOrderedTerminal_localMate_edgeId
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.rootRightOrderedTerminal_localMate_edgeId
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.RootFirstChannelClass
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.rootFirstChannelClass
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.rootLeftFirstChannelStep_of_physical
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.rootLeftFirstChannelStep_of_internal
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.rootLeftFirstChannelPartnerPath
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.rootRightFirstChannelPartnerPath
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.rootFirstChannelPartners_ne
