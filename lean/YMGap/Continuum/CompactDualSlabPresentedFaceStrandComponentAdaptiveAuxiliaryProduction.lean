/-
# Cutoff-independent auxiliary carrier for a presented component peel

The retained face order changes which physical label occupies each canonical
input position, but it does not change local strand conservation.  This file
transports the sharp canonical internal-drop bound through each presented
order, packages the complete link-word table in an adaptive Cartesian carrier,
and proves that carrier has size at most `4096^peelSize`.

Zero-mass links contribute singleton factors.  Thus the bound is independent
of slab volume and spin cutoff and applies to arbitrary supported selections,
including the certified two-root union.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryProduction
import YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAuxiliaryRowBound

namespace YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryPointwiseBound
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAuxiliaryRowBound
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.ResolvedTrivalentNetworkPortSelectionRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4ResidualListMultiplicityBound
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Ordered local conservation -/

theorem orderedPresentedSelectionToMateClosedSelection_drop
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness K extent physical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness) :
    (selection.toCanonical.toPortClosedSelection.toMateClosedSelection
      (orderedSlabLinkResolvedStrandNetwork K physical witness.order
        witness.auxiliary witness.auxiliary_mem)).drop =
      selection.drop := rfl

/-- Every used internal drop is bounded by the total selected physical input
mass in the retained order. -/
theorem orderedPresentedSelectionAuxiliaryDrop_le_orderedPhysicalDrop_l1
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness K extent physical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness)
    (edge : Nat)
    (hedge : edge ∈ canonicalUsedAuxiliaryCoordinates
      witness.order.faceIds.length) :
    selection.drop edge <=
      natListSum ((List.finRange witness.order.faceIds.length).map
        fun position => selection.drop position.val) := by
  let mateSelection :=
    selection.toCanonical.toPortClosedSelection.toMateClosedSelection
      (orderedSlabLinkResolvedStrandNetwork K physical witness.order
        witness.auxiliary witness.auxiliary_mem)
  have hbound := canonicalLinkSelection_auxiliaryDrop_le_physical_l1
    witness.order.length_le_six
    (orderedSlabLinkFusionWitness_mem_allowed K physical witness.order
      witness.auxiliary witness.auxiliary_mem)
    mateSelection edge hedge
  have hdrop :=
    orderedPresentedSelectionToMateClosedSelection_drop selection
  calc
    selection.drop edge = mateSelection.drop edge :=
      congrArg (fun drop => drop edge) hdrop.symm
    _ <= natListSum ((List.finRange witness.order.faceIds.length).map
        fun position => mateSelection.drop position.val) := hbound
    _ = natListSum ((List.finRange witness.order.faceIds.length).map
        fun position => selection.drop position.val) :=
      congrArg
        (fun drop => natListSum
          ((List.finRange witness.order.faceIds.length).map
            fun position => drop position.val)) hdrop

private theorem finRange_map_get {A : Type} (entries : List A) :
    (List.finRange entries.length).map entries.get = entries := by
  simpa only [List.finRange, List.map_ofFn, Function.comp_def] using
    (List.ofFn_getElem (xs := entries))

/-- The ordered physical-position sum is the same literal incident-face mass
as in the production order. -/
theorem orderedPresentedSelectionPhysicalDrop_l1_eq_incidentFace_l1
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness K extent physical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness) :
    natListSum ((List.finRange witness.order.faceIds.length).map
        fun position => selection.drop position.val) =
      natListSum ((slabIncidentPlaqIds extent link).map fun faceId =>
        slabFaceStrandSelectionCount selection.selected faceId) := by
  let weight := fun faceId =>
    slabFaceStrandSelectionCount selection.selected faceId
  calc
    natListSum ((List.finRange witness.order.faceIds.length).map
        fun position => selection.drop position.val) =
      natListSum ((List.finRange witness.order.faceIds.length).map
        fun position => weight (witness.order.faceIds.get position)) := by
          apply natListSum_map_congr
          intro position hposition
          exact OrderedSlabLinkPartnerClosedFaceSelection.drop_at_position
            selection position
    _ = natListSum (witness.order.faceIds.map weight) := by
      have hmapped := congrArg (List.map weight)
        (finRange_map_get witness.order.faceIds)
      have hsum := congrArg natListSum hmapped
      simpa only [List.map_map, Function.comp_apply] using hsum
    _ = natListSum ((slabIncidentPlaqIds extent link).map weight) :=
      (natListSum_perm (witness.order.production_perm.map weight)).symm

/-- Every entry of a presented link word is bounded by the selected physical
mass incident on that link. -/
theorem presentedSlabSupportedSelectionAuxiliaryDropWordAt_entry_le_incidentFace_l1
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (link : SlabLink) (hlink : link ∈ links)
    (value : Nat)
    (hvalue : value ∈
      presentedSlabSupportedSelectionAuxiliaryDropWordAt selection link) :
    value <= natListSum
      ((slabIncidentPlaqIds extent link).map fun faceId =>
        slabFaceStrandSelectionCount selection.closed.selected faceId) := by
  rw [presentedSlabSupportedSelectionAuxiliaryDropWordAt_of_mem
    selection link hlink] at hvalue
  obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hvalue
  let localSelection := selection.closed.atLink ⟨link, hlink⟩
  have hbound :=
    orderedPresentedSelectionAuxiliaryDrop_le_orderedPhysicalDrop_l1
      localSelection edge hedge
  rw [orderedPresentedSelectionPhysicalDrop_l1_eq_incidentFace_l1
    localSelection] at hbound
  exact hbound

/-! ## 2. Complete adaptive word carrier -/

def presentedSelectionLinkPhysicalMass
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (link : SlabLink) : Nat :=
  natListSum ((slabIncidentPlaqIds extent link).map fun faceId =>
    slabFaceStrandSelectionCount selection.closed.selected faceId)

def presentedSelectionAdaptiveAuxiliarySpecifications
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : PresentedSlabFusionWitnessAssignment K extent physical
      (boundaryCompleteSlabLinks extent)}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection K extent
      physical (boundaryCompleteSlabLinks extent) assignment) :
    List (Nat × Nat) :=
  (boundaryCompleteSlabLinks extent).map fun link =>
    (presentedSelectionLinkPhysicalMass selection link,
      (presentedSlabSupportedSelectionAuxiliaryDropWordAt
        selection link).length)

def presentedSelectionAdaptiveAuxiliaryRows
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : PresentedSlabFusionWitnessAssignment K extent physical
      (boundaryCompleteSlabLinks extent)}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection K extent
      physical (boundaryCompleteSlabLinks extent) assignment) :
    List (List Nat) :=
  (boundaryCompleteSlabLinks extent).map
    (presentedSlabSupportedSelectionAuxiliaryDropWordAt selection)

def presentedSelectionAdaptiveAuxiliaryCarrier
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : PresentedSlabFusionWitnessAssignment K extent physical
      (boundaryCompleteSlabLinks extent)}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection K extent
      physical (boundaryCompleteSlabLinks extent) assignment) :
    List (List (List Nat)) :=
  adaptiveAuxiliaryCarrier
    (presentedSelectionAdaptiveAuxiliarySpecifications selection)

theorem presentedSelectionAdaptiveAuxiliaryRows_fit
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : PresentedSlabFusionWitnessAssignment K extent physical
      (boundaryCompleteSlabLinks extent)}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection K extent
      physical (boundaryCompleteSlabLinks extent) assignment) :
    AdaptiveAuxiliaryRowsFit
      (presentedSelectionAdaptiveAuxiliarySpecifications selection)
      (presentedSelectionAdaptiveAuxiliaryRows selection) := by
  unfold presentedSelectionAdaptiveAuxiliarySpecifications
    presentedSelectionAdaptiveAuxiliaryRows
  apply adaptiveAuxiliaryRowsFit_map
  · intro link hlink
    rfl
  · intro link hlink value hvalue
    exact Nat.lt_succ_of_le
      (presentedSlabSupportedSelectionAuxiliaryDropWordAt_entry_le_incidentFace_l1
        selection link hlink value hvalue)

theorem presentedSelectionAdaptiveAuxiliaryRows_mem_carrier
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : PresentedSlabFusionWitnessAssignment K extent physical
      (boundaryCompleteSlabLinks extent)}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection K extent
      physical (boundaryCompleteSlabLinks extent) assignment) :
    presentedSelectionAdaptiveAuxiliaryRows selection ∈
      presentedSelectionAdaptiveAuxiliaryCarrier selection :=
  (presentedSelectionAdaptiveAuxiliaryRows_fit selection).mem_carrier

private theorem adaptiveAuxiliaryMass_map_eq_natListSum
    (mass width : SlabLink -> Nat) : forall links : List SlabLink,
    adaptiveAuxiliaryMass
        (links.map fun link => (mass link, width link)) =
      natListSum (links.map mass)
  | [] => rfl
  | _ :: links => by
      simp only [List.map_cons, adaptiveAuxiliaryMass, natListSum]
      rw [adaptiveAuxiliaryMass_map_eq_natListSum mass width links]

private theorem flatMap_replicate_length_eq_natListSum
    (multiplicity : Nat → Nat) : forall faceIds : List Nat,
    (faceIds.flatMap fun faceId =>
      List.replicate (multiplicity faceId) faceId).length =
      natListSum (faceIds.map multiplicity)
  | [] => rfl
  | faceId :: faceIds => by
      simp only [List.flatMap_cons, List.length_append,
        List.length_replicate, List.map_cons, natListSum]
      rw [flatMap_replicate_length_eq_natListSum multiplicity faceIds]

theorem presentedSelection_peelFaces_length_eq_physicalDrop_l1
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment) :
    selection.peelFaces.length =
      natListSum ((slabPhysicalFaceEdges extent).map fun faceId =>
        slabFaceStrandSelectionCount selection.closed.selected faceId) := by
  unfold PresentedSlabSupportedPartnerClosedFaceSelection.peelFaces
    slabFaceDropList
  exact flatMap_replicate_length_eq_natListSum
    (slabFaceStrandSelectionCount selection.closed.selected)
    (slabPhysicalFaceEdges extent)

theorem presentedSelectionAdaptiveAuxiliaryMass_eq_four_mul_peelFaces
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : PresentedSlabFusionWitnessAssignment K extent physical
      (boundaryCompleteSlabLinks extent)}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection K extent
      physical (boundaryCompleteSlabLinks extent) assignment) :
    adaptiveAuxiliaryMass
        (presentedSelectionAdaptiveAuxiliarySpecifications selection) =
      4 * selection.peelFaces.length := by
  unfold presentedSelectionAdaptiveAuxiliarySpecifications
  rw [adaptiveAuxiliaryMass_map_eq_natListSum]
  unfold presentedSelectionLinkPhysicalMass
  rw [slabLinkIncidentWeightSum_eq_four_mul_physicalWeightSum extent]
  rw [← presentedSelection_peelFaces_length_eq_physicalDrop_l1 selection]

theorem presentedSelectionAdaptiveAuxiliarySpecifications_width_le_three
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : PresentedSlabFusionWitnessAssignment K extent physical
      (boundaryCompleteSlabLinks extent)}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection K extent
      physical (boundaryCompleteSlabLinks extent) assignment)
    (specification : Nat × Nat)
    (hspecification : specification ∈
      presentedSelectionAdaptiveAuxiliarySpecifications selection) :
    specification.2 <= 3 := by
  unfold presentedSelectionAdaptiveAuxiliarySpecifications at hspecification
  obtain ⟨link, _, rfl⟩ := List.mem_map.mp hspecification
  exact presentedSlabSupportedSelectionAuxiliaryDropWordAt_length_le_three
    selection link

/-- **Presented auxiliary entropy bound.**  The complete link-word table lies
in a carrier of size at most `4096^peelSize`, uniformly in cutoff and volume. -/
theorem presentedSelectionAdaptiveAuxiliaryCarrier_length_le
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : PresentedSlabFusionWitnessAssignment K extent physical
      (boundaryCompleteSlabLinks extent)}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection K extent
      physical (boundaryCompleteSlabLinks extent) assignment) :
    (presentedSelectionAdaptiveAuxiliaryCarrier selection).length <=
      4096 ^ selection.peelFaces.length := by
  unfold presentedSelectionAdaptiveAuxiliaryCarrier
  apply adaptiveAuxiliaryCarrier_length_le_4096_pow
  · exact presentedSelectionAdaptiveAuxiliarySpecifications_width_le_three
      selection
  · rw [presentedSelectionAdaptiveAuxiliaryMass_eq_four_mul_peelFaces
      selection]
    exact Nat.le_refl _

end YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction.orderedPresentedSelectionAuxiliaryDrop_le_orderedPhysicalDrop_l1
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction.presentedSlabSupportedSelectionAuxiliaryDropWordAt_entry_le_incidentFace_l1
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction.presentedSelectionAdaptiveAuxiliaryRows_fit
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction.presentedSelectionAdaptiveAuxiliaryMass_eq_four_mul_peelFaces
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction.presentedSelectionAdaptiveAuxiliaryCarrier_length_le
