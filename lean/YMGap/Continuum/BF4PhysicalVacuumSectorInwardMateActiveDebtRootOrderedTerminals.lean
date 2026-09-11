/-
# Literal ordered-link terminals at an active cube root

The active carrier now supplies all data required by the presentation-
independent link strand compiler: a root-first order of literal incident face
identifiers and an auxiliary accepted on its physical spin word.  This file
packages that order and constructs the slot-zero physical terminal on each of
the two positive root faces.

Both terminals reindex exactly to the previously constructed geometric root
copies.  Their full canonical partners are therefore defined in the same
accepted source network and are certified to land on different literal faces.
The next bridge identifies the terminals' first-vertex ports with the explicit
stretched continuation before entering the global component tracer.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder
import YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. The active root as a certified ordered-link presentation -/

def rootSlabLinkFaceOrder
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    SlabLinkFaceOrder 1 (cubeDebtRootIncidence carrier.word).1.link where
  faceIds := rootOrderedFaceIds carrier
  production_perm := rootProductionFaceIds_perm_orderedFaceIds carrier

@[simp] theorem rootSlabLinkFaceOrder_faceIds
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rootSlabLinkFaceOrder carrier).faceIds = rootOrderedFaceIds carrier :=
  rfl

theorem rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    rootSourceAuxiliary carrier ∈ orderedSlabLinkFusionWitnesses K physical
      (rootSlabLinkFaceOrder carrier) := by
  unfold orderedSlabLinkFusionWitnesses
  rw [rootSlabLinkFaceOrder_faceIds,
    rootOrderedFaceIds_map_eq_orderedSourceSpins]
  exact rootSourceAuxiliary_mem_orderedSourceSpins carrier

/-! ## 2. The two root positions and their literal slot-zero copies -/

def rootLeftFacePosition
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    Fin (rootSlabLinkFaceOrder carrier).faceIds.length :=
  ⟨0, by simp [rootSlabLinkFaceOrder, rootOrderedFaceIds]⟩

def rootRightFacePosition
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    Fin (rootSlabLinkFaceOrder carrier).faceIds.length :=
  ⟨1, by simp [rootSlabLinkFaceOrder, rootOrderedFaceIds]⟩

def rootLeftOrderedSlot
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    Fin (physical ((rootSlabLinkFaceOrder carrier).faceIds.get
      (rootLeftFacePosition carrier))) :=
  ⟨0, by
    simpa [rootSlabLinkFaceOrder, rootOrderedFaceIds,
      rootLeftFacePosition] using (leftRootCopy carrier).slot.isLt⟩

def rootRightOrderedSlot
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    Fin (physical ((rootSlabLinkFaceOrder carrier).faceIds.get
      (rootRightFacePosition carrier))) :=
  ⟨0, by
    simpa [rootSlabLinkFaceOrder, rootOrderedFaceIds,
      rootRightFacePosition] using (rightRootCopy carrier).slot.isLt⟩

/-! ## 3. The two literal terminals in the accepted source network -/

def rootLeftOrderedTerminal
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :=
  orderedSlabLinkPhysicalTerminalAt K physical
    (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
    (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
    (rootLeftFacePosition carrier) (rootLeftOrderedSlot carrier)

def rootRightOrderedTerminal
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :=
  orderedSlabLinkPhysicalTerminalAt K physical
    (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
    (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
    (rootRightFacePosition carrier) (rootRightOrderedSlot carrier)

theorem rootLeftOrderedTerminal_occurrence_faceId
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (orderedSlabLinkPhysicalTerminalOccurrence K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
      (rootLeftOrderedTerminal carrier)).faceId =
        (leftRootCopy carrier).faceId := by
  simp [rootLeftOrderedTerminal, rootSlabLinkFaceOrder,
    rootOrderedFaceIds, rootLeftFacePosition]

theorem rootRightOrderedTerminal_occurrence_faceId
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (orderedSlabLinkPhysicalTerminalOccurrence K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
      (rootRightOrderedTerminal carrier)).faceId =
        (rightRootCopy carrier).faceId := by
  simp [rootRightOrderedTerminal, rootSlabLinkFaceOrder,
    rootOrderedFaceIds, rootRightFacePosition]

theorem rootLeftOrderedTerminal_occurrence_slot
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (orderedSlabLinkPhysicalTerminalOccurrence K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
      (rootLeftOrderedTerminal carrier)).slot.val = 0 := by
  simp [rootLeftOrderedTerminal, rootLeftOrderedSlot]

theorem rootRightOrderedTerminal_occurrence_slot
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (orderedSlabLinkPhysicalTerminalOccurrence K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
      (rootRightOrderedTerminal carrier)).slot.val = 0 := by
  simp [rootRightOrderedTerminal, rootRightOrderedSlot]

theorem rootLeftOrderedTerminal_partner_faceId_ne
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (orderedSlabLinkPhysicalTerminalOccurrence K physical
      (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
      (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
      (orderedSlabLinkPhysicalStrandPartner K physical
        (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
        (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
        (rootLeftOrderedTerminal carrier))).faceId ≠
      (leftRootCopy carrier).faceId := by
  rw [← rootLeftOrderedTerminal_occurrence_faceId carrier]
  exact orderedSlabLinkPhysicalStrandPartner_faceId_ne K physical
    (rootSlabLinkFaceOrder carrier) (rootSourceAuxiliary carrier)
    (rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses carrier)
    (rootLeftOrderedTerminal carrier)

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals.rootSourceAuxiliary_mem_orderedSlabLinkFusionWitnesses
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals.rootLeftOrderedTerminal
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals.rootRightOrderedTerminal
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals.rootLeftOrderedTerminal_occurrence_faceId
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals.rootLeftOrderedTerminal_partner_faceId_ne
