/-
# Exact physical drop for a presented strand component

The heterogeneous component compiler produces partner-closed selections in
arbitrary certified face orders.  This file proves the ordered analogue of
the production component-drop square: the canonical removal count at an
external edge is exactly the number of selected global copies on the literal
face occupying that ordered position.  Hence one common lowered physical
labelling realizes every presented link's external removal, and the compiled
lowered auxiliary is accepted in the same retained face order.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
import YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent

namespace YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkStrandTerminal
open YMGap.Continuum.CanonicalLinkPhysicalTerminalPartner
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.ResolvedTrivalentNetworkPortSelectionRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionPathZeroInsertion

/-! ## 1. Observe one ordered physical slot -/

theorem orderedSlabLinkCanonicalLabel_at_position
    {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (order : SlabLinkFaceOrder extent link)
    {auxiliary : SlabLabelling}
    (position : Fin order.faceIds.length) :
    canonicalLinkLabelling order.faceIds.length
        (orderedSlabLinkExternalSpins physical order)
        auxiliary position.val =
      physical (order.faceIds.get position) := by
  unfold canonicalLinkLabelling
  rw [overlayOn_apply_of_mem (List.mem_range.mpr position.isLt)]
  exact externalSpinsOfList_map_get order.faceIds physical position

def orderedSlabLinkCanonicalSlotAt
    {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (order : SlabLinkFaceOrder extent link)
    {auxiliary : SlabLabelling}
    (position : Fin order.faceIds.length)
    (slot : Fin (physical (order.faceIds.get position))) :
    Fin (canonicalLinkLabelling order.faceIds.length
      (orderedSlabLinkExternalSpins physical order)
      auxiliary position.val) :=
  ⟨slot.val, by
    rw [orderedSlabLinkCanonicalLabel_at_position order position]
    exact slot.isLt⟩

theorem orderedSlabLinkPhysicalSlotObservation_copy
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (witness : PresentedSlabLinkFusionWitness K extent physical link)
    (position : Fin witness.order.faceIds.length)
    (slot : Fin (physical (witness.order.faceIds.get position)))
    (observation : CanonicalPhysicalSlotObservation
      (hallowed := orderedSlabLinkFusionWitness_mem_allowed K physical
        witness.order witness.auxiliary witness.auxiliary_mem)
      position (orderedSlabLinkCanonicalSlotAt
        witness.order (auxiliary := witness.auxiliary) position slot)) :
    orderedSlabLinkPhysicalTerminalFaceStrandCopy K physical
        witness.order witness.auxiliary witness.auxiliary_mem
        observation.terminal =
      { faceId := witness.order.faceIds.get position
        slot := slot } := by
  have hposition :
      (⟨observation.terminal.1.edgeId, observation.terminal.2⟩ :
        Fin witness.order.faceIds.length) = position := by
    apply Fin.ext
    exact observation.edgeId_eq
  apply
    CompactDualSlabOrderedLinkGlobalFaceStrandEdge.slabFaceStrandCopy_eq_of_faceId_eq_of_slot_val_eq
  · rw [orderedSlabLinkPhysicalTerminalFaceStrandCopy_faceId]
    exact congrArg (List.get witness.order.faceIds) hposition
  · rw [orderedSlabLinkPhysicalTerminalFaceStrandCopy_slot_val]
    simpa [orderedSlabLinkCanonicalSlotAt] using observation.slot_eq

private theorem OrderedSlabLinkPartnerClosedFaceSelection.atPort_physical
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness K extent physical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness)
    (position : Fin witness.order.faceIds.length)
    (slot : Fin (physical (witness.order.faceIds.get position)))
    (observation : CanonicalPhysicalSlotObservation
      (hallowed := orderedSlabLinkFusionWitness_mem_allowed K physical
        witness.order witness.auxiliary witness.auxiliary_mem)
      position (orderedSlabLinkCanonicalSlotAt
        witness.order (auxiliary := witness.auxiliary) position slot)) :
    selection.toCanonical.atPort observation.terminal.1 =
      selection.selected
        { faceId := witness.order.faceIds.get position
          slot := slot } := by
  have hterminal :
      canonicalLinkStrandTerminal
          (by simpa [linkIncidenceBound] using witness.order.length_le_six)
          (orderedSlabLinkFusionWitness_mem_allowed K physical
            witness.order witness.auxiliary witness.auxiliary_mem)
          observation.terminal.1 = observation.terminal :=
    canonicalStrandPath_terminal_unique
      (canonicalLinkStrandTerminalWitness
        (by simpa [linkIncidenceBound] using witness.order.length_le_six)
        (orderedSlabLinkFusionWitness_mem_allowed K physical
          witness.order witness.auxiliary witness.auxiliary_mem)
        observation.terminal.1).2
      (CanonicalStrandPathToPhysical.stop observation.terminal)
  unfold CanonicalPhysicalPartnerClosedSelection.atPort
  rw [hterminal]
  change selection.selected
      (orderedSlabLinkPhysicalTerminalFaceStrandCopy K physical
        witness.order witness.auxiliary witness.auxiliary_mem
        observation.terminal) = _
  rw [orderedSlabLinkPhysicalSlotObservation_copy
    witness position slot observation]

/-! ## 2. The canonical and global physical counts commute -/

theorem OrderedSlabLinkPartnerClosedFaceSelection.drop_apply
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness K extent physical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness)
    (edge : Nat) :
    selection.drop edge =
      boolCountFrom
        (selection.toCanonical.toPortClosedSelection.edgeSlotValue edge)
        0
        (canonicalLinkLabelling witness.order.faceIds.length
          (orderedSlabLinkExternalSpins physical witness.order)
          witness.auxiliary edge) := rfl

theorem OrderedSlabLinkPartnerClosedFaceSelection.edgeSlotValue_at_position_slot
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness K extent physical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness)
    (position : Fin witness.order.faceIds.length)
    (slot : Fin (physical (witness.order.faceIds.get position))) :
    selection.toCanonical.toPortClosedSelection.edgeSlotValue
        position.val slot.val =
      selection.selected
        { faceId := witness.order.faceIds.get position
          slot := slot } := by
  let canonicalSlot := orderedSlabLinkCanonicalSlotAt
    witness.order (auxiliary := witness.auxiliary) position slot
  let observation := canonicalPhysicalSlotObservation
    (by simpa [linkIncidenceBound] using witness.order.length_le_six)
    (orderedSlabLinkFusionWitness_mem_allowed K physical
      witness.order witness.auxiliary witness.auxiliary_mem)
    position canonicalSlot
  have hexact :=
    selection.toCanonical.toPortClosedSelection.edgeSlotValue_at_port
      observation.terminal.1
  have hvalue := OrderedSlabLinkPartnerClosedFaceSelection.atPort_physical
    selection position slot observation
  calc
    selection.toCanonical.toPortClosedSelection.edgeSlotValue
        position.val slot.val =
        selection.toCanonical.toPortClosedSelection.edgeSlotValue
          observation.terminal.1.edgeId
          observation.terminal.1.slot := by
      rw [observation.edgeId_eq, observation.slot_eq]
      simp [canonicalSlot, orderedSlabLinkCanonicalSlotAt]
    _ = selection.toCanonical.atPort observation.terminal.1 := hexact
    _ = selection.selected
        { faceId := witness.order.faceIds.get position
          slot := slot } := hvalue

theorem OrderedSlabLinkPartnerClosedFaceSelection.drop_at_position
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness K extent physical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness)
    (position : Fin witness.order.faceIds.length) :
    selection.drop position.val =
      slabFaceStrandSelectionCount selection.selected
        (witness.order.faceIds.get position) := by
  rw [OrderedSlabLinkPartnerClosedFaceSelection.drop_apply selection]
  unfold slabFaceStrandSelectionCount
  rw [orderedSlabLinkCanonicalLabel_at_position witness.order position]
  apply boolCountFrom_congr
  intro offset hoffset
  simp only [Nat.zero_add]
  let slot : Fin (physical (witness.order.faceIds.get position)) :=
    ⟨offset, hoffset⟩
  change selection.toCanonical.toPortClosedSelection.edgeSlotValue
      position.val offset =
    slabFaceStrandSelectionAt selection.selected
      (witness.order.faceIds.get position) offset
  calc
    selection.toCanonical.toPortClosedSelection.edgeSlotValue
        position.val offset =
        selection.selected
          { faceId := witness.order.faceIds.get position
            slot := slot } :=
      OrderedSlabLinkPartnerClosedFaceSelection.edgeSlotValue_at_position_slot
        selection position slot
    _ = slabFaceStrandSelectionAt selection.selected
        (witness.order.faceIds.get position) offset := by
      symm
      exact slabFaceStrandSelectionAt_fin _ _ slot

/-! ## 3. One common lowered physical labelling -/

private theorem externalSpinsOfList_eq_zero_of_length_le
    (spins : List Nat) (position : Nat) (hlength : spins.length ≤ position) :
    externalSpinsOfList spins position = 0 := by
  unfold externalSpinsOfList
  rw [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none hlength]
  rfl

theorem OrderedSlabLinkPartnerClosedFaceSelection.externalSpins_lowerPhysical
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness K extent physical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness) :
    orderedSlabLinkExternalSpins
        (lowerSlabPhysicalByFaceStrandSelection selection.selected)
        witness.order =
      lowerEdgeLabellingBy
        (orderedSlabLinkExternalSpins physical witness.order)
        selection.drop := by
  funext edge
  by_cases hedge : edge < witness.order.faceIds.length
  · let position : Fin witness.order.faceIds.length := ⟨edge, hedge⟩
    unfold orderedSlabLinkExternalSpins
    rw [externalSpinsOfList_map_get witness.order.faceIds
      (lowerSlabPhysicalByFaceStrandSelection selection.selected) position]
    change lowerSlabPhysicalByFaceStrandSelection selection.selected
        (witness.order.faceIds.get position) =
      externalSpinsOfList (witness.order.faceIds.map physical) edge -
        selection.drop edge
    rw [externalSpinsOfList_map_get witness.order.faceIds physical position]
    rw [OrderedSlabLinkPartnerClosedFaceSelection.drop_at_position
      selection position]
    rfl
  · have hlength : witness.order.faceIds.length ≤ edge := by omega
    unfold orderedSlabLinkExternalSpins lowerEdgeLabellingBy
    rw [externalSpinsOfList_eq_zero_of_length_le _ edge (by
      simpa using hlength)]
    rw [externalSpinsOfList_eq_zero_of_length_le _ edge (by
      simpa using hlength)]
    exact (Nat.zero_sub _).symm

/-- The ordered component peel produces an actual accepted auxiliary for the
common globally lowered physical labelling. -/
theorem OrderedSlabLinkPartnerClosedFaceSelection.lower_auxiliary_mem_global
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness K extent physical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness) :
    lowerEdgeLabellingBy witness.auxiliary selection.drop ∈
      orderedSlabLinkFusionWitnesses K
        (lowerSlabPhysicalByFaceStrandSelection selection.selected)
        witness.order :=
  selection.lower_auxiliary_mem
    (OrderedSlabLinkPartnerClosedFaceSelection.externalSpins_lowerPhysical
      selection)

end YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop.orderedSlabLinkCanonicalLabel_at_position
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop.OrderedSlabLinkPartnerClosedFaceSelection.edgeSlotValue_at_position_slot
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop.OrderedSlabLinkPartnerClosedFaceSelection.drop_at_position
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop.OrderedSlabLinkPartnerClosedFaceSelection.externalSpins_lowerPhysical
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop.OrderedSlabLinkPartnerClosedFaceSelection.lower_auxiliary_mem_global
