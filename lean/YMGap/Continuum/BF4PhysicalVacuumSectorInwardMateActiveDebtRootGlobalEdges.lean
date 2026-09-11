/-
# Global physical-copy edges at the active inward-mate root

The active root's two complete canonical strand paths now end at physical
terminals in a certified root-first face presentation.  This file forgets
their local fusion-tree addresses to literal global `(faceId, slot)` copies
and packages the two root pairings as global strand edges.

The source endpoints are proved equal to the previously constructed
geometric left and right root copies.  This is the first presentation-
independent interface with the global component carrier; membership in a
complete heterogeneous global edge list remains the next compiler.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch
import YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Literal global copies of the two root terminals -/

def rootLeftOrderedTerminalCopy
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    SlabFaceStrandCopy physical :=
  orderedSlabLinkPhysicalTerminalFaceStrandCopy K physical
    (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
    (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
    (rootLeftOrderedTerminal carrier)

def rootRightOrderedTerminalCopy
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    SlabFaceStrandCopy physical :=
  orderedSlabLinkPhysicalTerminalFaceStrandCopy K physical
    (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
    (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
    (rootRightOrderedTerminal carrier)

def rootLeftFirstChannelPartnerCopy
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    SlabFaceStrandCopy physical :=
  orderedSlabLinkPhysicalTerminalFaceStrandCopy K physical
    (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
    (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
    (rootLeftFirstChannelPartner carrier)

def rootRightFirstChannelPartnerCopy
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    SlabFaceStrandCopy physical :=
  orderedSlabLinkPhysicalTerminalFaceStrandCopy K physical
    (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
    (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
    (rootRightFirstChannelPartner carrier)

/-- Reindexing the left ordered terminal loses no geometric information: it
is exactly the original left root face copy. -/
theorem rootLeftOrderedTerminalCopy_eq_leftRootCopy
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    rootLeftOrderedTerminalCopy carrier = leftRootCopy carrier := by
  calc
    rootLeftOrderedTerminalCopy carrier =
        orderedSlabLinkPhysicalCopyAt
          (rootSlabLinkFaceOrder carrier)
          (rootLeftFacePosition carrier)
          (rootLeftOrderedSlot carrier) :=
      orderedSlabLinkPhysicalTerminalAtFaceStrandCopy K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
        (rootLeftFacePosition carrier) (rootLeftOrderedSlot carrier)
    _ = leftRootCopy carrier := by
      rfl

/-- Reindexing the right ordered terminal is exactly the original right root
face copy. -/
theorem rootRightOrderedTerminalCopy_eq_rightRootCopy
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    rootRightOrderedTerminalCopy carrier = rightRootCopy carrier := by
  calc
    rootRightOrderedTerminalCopy carrier =
        orderedSlabLinkPhysicalCopyAt
          (rootSlabLinkFaceOrder carrier)
          (rootRightFacePosition carrier)
          (rootRightOrderedSlot carrier) :=
      orderedSlabLinkPhysicalTerminalAtFaceStrandCopy K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
        (rootRightFacePosition carrier) (rootRightOrderedSlot carrier)
    _ = rightRootCopy carrier := by
      rfl

/-! ## 2. The two active-root global strand edges -/

def rootLeftFirstChannelEdge
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    SlabFaceStrandEdge physical :=
  orderedSlabLinkFaceStrandEdgeOfTerminal K physical
    (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
    (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
    (rootLeftOrderedTerminal carrier)

def rootRightFirstChannelEdge
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    SlabFaceStrandEdge physical :=
  orderedSlabLinkFaceStrandEdgeOfTerminal K physical
    (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
    (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
    (rootRightOrderedTerminal carrier)

@[simp] theorem rootLeftFirstChannelEdge_link
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootLeftFirstChannelEdge carrier).link =
      (cubeDebtRootIncidence carrier.word).1.link :=
  rfl

@[simp] theorem rootRightFirstChannelEdge_link
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootRightFirstChannelEdge carrier).link =
      (cubeDebtRootIncidence carrier.word).1.link :=
  rfl

theorem rootLeftFirstChannelEdge_source
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootLeftFirstChannelEdge carrier).source = leftRootCopy carrier := by
  calc
    (rootLeftFirstChannelEdge carrier).source =
        rootLeftOrderedTerminalCopy carrier :=
      orderedSlabLinkFaceStrandEdgeOfTerminal_source K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
        (rootLeftOrderedTerminal carrier)
    _ = leftRootCopy carrier :=
      rootLeftOrderedTerminalCopy_eq_leftRootCopy carrier

theorem rootRightFirstChannelEdge_source
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootRightFirstChannelEdge carrier).source = rightRootCopy carrier := by
  calc
    (rootRightFirstChannelEdge carrier).source =
        rootRightOrderedTerminalCopy carrier :=
      orderedSlabLinkFaceStrandEdgeOfTerminal_source K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
        (rootRightOrderedTerminal carrier)
    _ = rightRootCopy carrier :=
      rootRightOrderedTerminalCopy_eq_rightRootCopy carrier

theorem rootLeftFirstChannelEdge_target
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootLeftFirstChannelEdge carrier).target =
      rootLeftFirstChannelPartnerCopy carrier := by
  calc
    (rootLeftFirstChannelEdge carrier).target =
        orderedSlabLinkPhysicalTerminalFaceStrandCopy K physical
          (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
          (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
          (orderedSlabLinkPhysicalStrandPartner K physical
            (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
            (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
            (rootLeftOrderedTerminal carrier)) :=
      orderedSlabLinkFaceStrandEdgeOfTerminal_target K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
        (rootLeftOrderedTerminal carrier)
    _ = rootLeftFirstChannelPartnerCopy carrier := by
      unfold rootLeftFirstChannelPartnerCopy
      rw [← rootLeftFirstChannelPartner_eq_ordered carrier]

theorem rootRightFirstChannelEdge_target
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootRightFirstChannelEdge carrier).target =
      rootRightFirstChannelPartnerCopy carrier := by
  calc
    (rootRightFirstChannelEdge carrier).target =
        orderedSlabLinkPhysicalTerminalFaceStrandCopy K physical
          (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
          (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
          (orderedSlabLinkPhysicalStrandPartner K physical
            (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
            (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
            (rootRightOrderedTerminal carrier)) :=
      orderedSlabLinkFaceStrandEdgeOfTerminal_target K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
        (rootRightOrderedTerminal carrier)
    _ = rootRightFirstChannelPartnerCopy carrier := by
      unfold rootRightFirstChannelPartnerCopy
      rw [← rootRightFirstChannelPartner_eq_ordered carrier]

/-- The two retained terminal paths end at different literal global face
copies, not merely at different proof-indexed terminal records. -/
theorem rootFirstChannelPartnerCopies_ne
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    rootLeftFirstChannelPartnerCopy carrier ≠
      rootRightFirstChannelPartnerCopy carrier := by
  intro hcopy
  apply rootFirstChannelPartners_ne carrier
  exact orderedSlabLinkPhysicalTerminalFaceStrandCopy_injective K physical
    (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
    (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
    (rootLeftFirstChannelPartner carrier)
    (rootRightFirstChannelPartner carrier) hcopy

/-- Each root strand now has a literal global-copy endpoint distinct in face
identifier from its geometric source copy. -/
theorem rootLeftFirstChannelEdge_target_faceId_ne_root
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootLeftFirstChannelEdge carrier).target.faceId ≠
      (leftRootCopy carrier).faceId := by
  intro htarget
  apply (rootLeftFirstChannelEdge carrier).faceId_ne
  exact (congrArg SlabFaceStrandCopy.faceId
    (rootLeftFirstChannelEdge_source carrier)).trans htarget.symm

theorem rootRightFirstChannelEdge_target_faceId_ne_root
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootRightFirstChannelEdge carrier).target.faceId ≠
      (rightRootCopy carrier).faceId := by
  intro htarget
  apply (rootRightFirstChannelEdge carrier).faceId_ne
  exact (congrArg SlabFaceStrandCopy.faceId
    (rootRightFirstChannelEdge_source carrier)).trans htarget.symm

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges.rootLeftOrderedTerminalCopy_eq_leftRootCopy
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges.rootRightOrderedTerminalCopy_eq_rightRootCopy
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges.rootLeftFirstChannelEdge
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges.rootRightFirstChannelEdge
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges.rootLeftFirstChannelEdge_target
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges.rootFirstChannelPartnerCopies_ne
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges.rootLeftFirstChannelEdge_target_faceId_ne_root
