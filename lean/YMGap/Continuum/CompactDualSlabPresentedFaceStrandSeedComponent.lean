/-
# Rooted components of a heterogeneous presented strand graph

The finite component engine depends only on the common global face-copy
carrier and its edge list.  It therefore applies unchanged when different
links use different certified fusion-tree presentations.  This file records
the missing local interface: component membership pulls back to a Boolean
selection on every presented link, and that selection is closed under the
actual ordered terminal partner.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
import YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges

namespace YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.ResolvedTrivalentNetworkPortSelectionRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Ordered local partner closure -/

/-- A global face-copy selection closed under the physical partner in one
certified ordered link presentation. -/
structure OrderedSlabLinkPartnerClosedFaceSelection
    (K : Nat) {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    (witness : PresentedSlabLinkFusionWitness
      K extent physical link) : Type where
  selected : SlabFaceStrandCopy physical → Bool
  partner_closed :
    ∀ terminal : OrderedSlabLinkPhysicalStrandTerminal
        K physical witness.order witness.auxiliary witness.auxiliary_mem,
      selected
          (orderedSlabLinkPhysicalTerminalFaceStrandCopy
            K physical witness.order witness.auxiliary
              witness.auxiliary_mem
              (orderedSlabLinkPhysicalStrandPartner
                K physical witness.order witness.auxiliary
                  witness.auxiliary_mem terminal)) =
        selected
          (orderedSlabLinkPhysicalTerminalFaceStrandCopy
            K physical witness.order witness.auxiliary
              witness.auxiliary_mem terminal)

/-- Forget the literal face identifier after evaluating it, obtaining the
generic canonical physical-terminal selection used by strand removal. -/
def OrderedSlabLinkPartnerClosedFaceSelection.toCanonical
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness K extent physical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness) :
    CanonicalPhysicalPartnerClosedSelection
      (by simpa [linkIncidenceBound] using witness.order.length_le_six)
      (orderedSlabLinkFusionWitness_mem_allowed K physical witness.order
        witness.auxiliary witness.auxiliary_mem) where
  selected := fun terminal =>
    selection.selected
      (orderedSlabLinkPhysicalTerminalFaceStrandCopy K physical
        witness.order witness.auxiliary witness.auxiliary_mem terminal)
  partner_closed := selection.partner_closed

/-- Ordered-link component closure compiles directly to one coherent removal
of the actual resolved trivalent network. -/
def OrderedSlabLinkPartnerClosedFaceSelection.toCoherentRemoval
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness K extent physical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness) :
    CoherentResolvedTrivalentRemoval
      (orderedSlabLinkResolvedStrandNetwork K physical witness.order
        witness.auxiliary witness.auxiliary_mem) :=
  selection.toCanonical.toCoherentRemoval

/-- The common canonical edge-drop compiled from the ordered physical
selection. -/
def OrderedSlabLinkPartnerClosedFaceSelection.drop
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness K extent physical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness) :
    EdgeLabelling :=
  selection.toCoherentRemoval.drop

@[simp] theorem OrderedSlabLinkPartnerClosedFaceSelection.toCoherentRemoval_drop
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness K extent physical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness) :
    selection.toCoherentRemoval.drop = selection.drop := rfl

/-- Pointwise removal of the compiled internal strand counts remains an
accepted ordered auxiliary as soon as the target physical presentation
realizes the same compiled drops on its external canonical edges. -/
theorem OrderedSlabLinkPartnerClosedFaceSelection.lower_auxiliary_mem
    {K : Nat} {extent : Nat} {sourcePhysical targetPhysical : SlabLabelling}
    {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness
      K extent sourcePhysical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness)
    (hexternal :
      orderedSlabLinkExternalSpins targetPhysical witness.order =
        lowerEdgeLabellingBy
          (orderedSlabLinkExternalSpins sourcePhysical witness.order)
          selection.drop) :
    lowerEdgeLabellingBy witness.auxiliary
        selection.drop ∈
      orderedSlabLinkFusionWitnesses K targetPhysical witness.order := by
  have hsourceMem := witness.auxiliary_mem
  unfold orderedSlabLinkFusionWitnesses fusionWitnessesForSpins at hsourceMem ⊢
  simp only [List.length_map] at hsourceMem ⊢
  obtain ⟨hbounded, hallowed⟩ := List.mem_filter.mp hsourceMem
  apply List.mem_filter.mpr
  constructor
  · exact lowerEdgeLabellingBy_mem_bounded
      (canonicalUsedAuxiliaryCoordinates witness.order.faceIds.length)
      hbounded
  · unfold orderedSlabLinkExternalSpins at hexternal
    rw [hexternal]
    exact canonicalLinkConditionalAllowedB_lower_of_plan
      hallowed
      selection.toCoherentRemoval.plan

/-! ## 2. Pull a heterogeneous component back to every presented link -/

/-- Seed data for the global edge list of a dependent field of certified link
presentations. -/
abbrev PresentedSlabFusionWitnessFaceStrandSeed
    (K extent : Nat) (physical : SlabLabelling) (links : List SlabLink)
    (assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links) :=
  SlabFaceStrandSeed
    (presentedSlabFusionWitnessAssignmentFaceStrandEdges
      K extent physical links assignment)

/-- Component closure of the common global graph is exactly ordered-partner
closure at each displayed local presentation. -/
def PresentedSlabFusionWitnessFaceStrandSeed.atLinkSelection
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (seed : PresentedSlabFusionWitnessFaceStrandSeed
      K extent physical links assignment)
    (linked : {link // link ∈ links}) :
    OrderedSlabLinkPartnerClosedFaceSelection K (assignment linked) where
  selected := seed.selected
  partner_closed := by
    intro terminal
    let edge := orderedSlabLinkFaceStrandEdgeOfTerminal K physical
      (assignment linked).order (assignment linked).auxiliary
      (assignment linked).auxiliary_mem terminal
    have hedge : edge ∈
        presentedSlabFusionWitnessAssignmentFaceStrandEdges
          K extent physical links assignment :=
      presentedSlabFusionWitnessAssignmentFaceStrandEdgeOfTerminal_mem
        K extent physical links assignment linked terminal
    exact seed.selected_eq_of_edge_mem hedge

end YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent.OrderedSlabLinkPartnerClosedFaceSelection
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent.OrderedSlabLinkPartnerClosedFaceSelection.toCanonical
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent.OrderedSlabLinkPartnerClosedFaceSelection.toCoherentRemoval
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent.OrderedSlabLinkPartnerClosedFaceSelection.drop
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent.OrderedSlabLinkPartnerClosedFaceSelection.lower_auxiliary_mem
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent.PresentedSlabFusionWitnessFaceStrandSeed
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent.PresentedSlabFusionWitnessFaceStrandSeed.atLinkSelection
