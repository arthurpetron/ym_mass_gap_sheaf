/-
# Finite inverse codes for supported presented component peels

A presented assignment may use a different certified physical-face order at
every link.  Peeling preserves those orders exactly, so an inverse code need
not pay to encode them again: reconstruction reads each order from the lowered
target.  The only new data are the physical peel word and one word of internal
coordinate drops per displayed link.

This file proves exact physical reconstruction and exact local auxiliary
reconstruction from that finite code.  Global raw-assignment reconstruction
and sparse entropy bounds are downstream.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
import YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight

namespace YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Ordered local auxiliary reconstruction -/

/-- A compiled ordered component drop never exceeds the source canonical link
label. -/
theorem OrderedSlabLinkPartnerClosedFaceSelection.drop_le_canonical
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness K extent physical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness)
    (edge : Nat) :
    selection.drop edge <=
      canonicalLinkLabelling witness.order.faceIds.length
        (orderedSlabLinkExternalSpins physical witness.order)
        witness.auxiliary edge := by
  rw [OrderedSlabLinkPartnerClosedFaceSelection.drop_apply selection]
  exact boolCountFrom_le _ _ _

/-- On a used internal coordinate, the ordered component drop is bounded by
the source auxiliary label. -/
theorem OrderedSlabLinkPartnerClosedFaceSelection.drop_le_auxiliary
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness K extent physical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness)
    (edge : Nat)
    (hedge : edge ∈ canonicalUsedAuxiliaryCoordinates
      witness.order.faceIds.length) :
    selection.drop edge <= witness.auxiliary edge := by
  obtain ⟨offset, hedgeEq, _⟩ :=
    canonicalUsedAuxiliary_coordinate_shape
      witness.order.length_le_six hedge
  have hnotPhysical :
      edge ∉ List.range witness.order.faceIds.length := by
    intro hmemRange
    have hlt := List.mem_range.mp hmemRange
    omega
  have hbound :=
    OrderedSlabLinkPartnerClosedFaceSelection.drop_le_canonical
      selection edge
  unfold canonicalLinkLabelling overlayOn at hbound
  rw [if_neg hnotPhysical] at hbound
  exact hbound

/-- Re-adding the used internal part of an ordered component drop to its
lowered auxiliary recovers the source auxiliary exactly. -/
theorem OrderedSlabLinkPartnerClosedFaceSelection.reconstructAuxiliary_lower
    {K : Nat} {extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {witness : PresentedSlabLinkFusionWitness K extent physical link}
    (selection : OrderedSlabLinkPartnerClosedFaceSelection K witness) :
    raiseEdgeLabellingBy
        (lowerEdgeLabellingBy witness.auxiliary selection.drop)
        (edgeLabellingSupportedOn
          (canonicalUsedAuxiliaryCoordinates witness.order.faceIds.length)
          selection.drop) =
      witness.auxiliary := by
  apply raiseEdgeLabellingBy_lowerEdgeLabellingBy_supported
  · have hbounded : witness.auxiliary ∈
        boundedEdgeLabellings (linkAuxiliaryCutoff K)
          (canonicalUsedAuxiliaryCoordinates witness.order.faceIds.length) := by
      simpa only [List.length_map] using
        (List.mem_filter.mp witness.auxiliary_mem).1
    exact (boundedEdgeLabellings_sound
      (linkAuxiliaryCutoff K)
      (canonicalUsedAuxiliaryCoordinates witness.order.faceIds.length)
      witness.auxiliary hbounded).2
  · exact OrderedSlabLinkPartnerClosedFaceSelection.drop_le_auxiliary
      selection

/-! ## 2. Encode and decode the presented internal drops -/

/-- Read one ordered internal-drop word, totalized by the empty word away
from the displayed link carrier. -/
def presentedSlabSupportedSelectionAuxiliaryDropWordAt
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (link : SlabLink) : List Nat :=
  if hlink : link ∈ links then
    (canonicalUsedAuxiliaryCoordinates
      (assignment ⟨link, hlink⟩).order.faceIds.length).map
        (selection.closed.atLink ⟨link, hlink⟩).drop
  else []

@[simp] theorem presentedSlabSupportedSelectionAuxiliaryDropWordAt_of_mem
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (link : SlabLink) (hlink : link ∈ links) :
    presentedSlabSupportedSelectionAuxiliaryDropWordAt selection link =
      (canonicalUsedAuxiliaryCoordinates
        (assignment ⟨link, hlink⟩).order.faceIds.length).map
          (selection.closed.atLink ⟨link, hlink⟩).drop := by
  simp [presentedSlabSupportedSelectionAuxiliaryDropWordAt, hlink]

/-- Every displayed presented-link word has width at most three, regardless
of the spin cutoff and of the retained physical-face order. -/
theorem presentedSlabSupportedSelectionAuxiliaryDropWordAt_length_le_three
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (link : SlabLink) :
    (presentedSlabSupportedSelectionAuxiliaryDropWordAt
      selection link).length <= 3 := by
  by_cases hlink : link ∈ links
  · rw [presentedSlabSupportedSelectionAuxiliaryDropWordAt_of_mem
      selection link hlink, List.length_map]
    exact canonicalUsedAuxiliaryCoordinates_length_le_three
      (assignment ⟨link, hlink⟩).order.length_le_six
  · simp [presentedSlabSupportedSelectionAuxiliaryDropWordAt, hlink]

/-- The finite code contains no face-order payload: those orders are retained
unchanged in the lowered presented target. -/
def presentedSlabSupportedSelectionDropCode
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment) :
    SlabFaceStrandComponentDropCode where
  physicalFaces := selection.peelFaces
  auxiliaryWords := slabAuxiliaryDropWordsFrom links
    (presentedSlabSupportedSelectionAuxiliaryDropWordAt selection)

/-- The full presented auxiliary table has exactly one row per displayed
link. -/
theorem presentedSlabSupportedSelectionDropCode_auxiliaryWords_length
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment) :
    (presentedSlabSupportedSelectionDropCode
      selection).auxiliaryWords.length = links.length := by
  unfold presentedSlabSupportedSelectionDropCode slabAuxiliaryDropWordsFrom
  exact List.length_map _

/-- Decode a link word using the certified order retained by its target
presentation. -/
def decodePresentedAuxiliaryDrop
    (code : SlabFaceStrandComponentDropCode)
    {extent : Nat} {link : SlabLink}
    (order : SlabLinkFaceOrder extent link) : SlabLabelling :=
  wordToEdgeLabelling
    (canonicalUsedAuxiliaryCoordinates order.faceIds.length)
    (slabAuxiliaryDropWordAt link code.auxiliaryWords)

/-- At every displayed link, the encoded word decodes to the exact supported
internal component drop. -/
theorem presentedSlabSupportedSelection_decodePresentedAuxiliaryDrop_dropCode
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (linked : {link // link ∈ links}) :
    decodePresentedAuxiliaryDrop
        (presentedSlabSupportedSelectionDropCode selection)
        (assignment linked).order =
      edgeLabellingSupportedOn
        (canonicalUsedAuxiliaryCoordinates
          (assignment linked).order.faceIds.length)
        (selection.closed.atLink linked).drop := by
  have hlookup :
      slabAuxiliaryDropWordAt linked.1
          (presentedSlabSupportedSelectionDropCode selection).auxiliaryWords =
        presentedSlabSupportedSelectionAuxiliaryDropWordAt
          selection linked.1 := by
    unfold presentedSlabSupportedSelectionDropCode
    exact slabAuxiliaryDropWordAt_from
      (presentedSlabSupportedSelectionAuxiliaryDropWordAt selection)
      links linked.1 linked.2
  unfold decodePresentedAuxiliaryDrop
  rw [hlookup,
    presentedSlabSupportedSelectionAuxiliaryDropWordAt_of_mem
      selection linked.1 linked.2]
  exact wordToEdgeLabelling_map_eq_supportedOn
    (selection.closed.atLink linked).drop
    (canonicalUsedAuxiliaryCoordinates
      (assignment linked).order.faceIds.length)
    (canonicalUsedAuxiliaryCoordinates_nodup
      (assignment linked).order.length_le_six)

/-! ## 3. Exact local and physical decoding -/

/-- Reconstruct a source auxiliary from one lowered presented witness and the
word keyed by its link. -/
def reconstructPresentedAuxiliaryAt
    (code : SlabFaceStrandComponentDropCode)
    {K extent : Nat} {targetPhysical : SlabLabelling} {link : SlabLink}
    (target : PresentedSlabLinkFusionWitness K extent targetPhysical link) :
    SlabLabelling :=
  raiseEdgeLabellingBy target.auxiliary
    (decodePresentedAuxiliaryDrop code target.order)

/-- Reconstruct the raw presented source payload in the literal displayed
link order.  Each target witness supplies its already-retained face order. -/
def reconstructPresentedAssignmentRaw
    (code : SlabFaceStrandComponentDropCode)
    {K extent : Nat} {targetPhysical : SlabLabelling}
    (links : List SlabLink)
    (target : PresentedSlabFusionWitnessAssignment
      K extent targetPhysical links) : SlabFusionWitnessAssignment :=
  links.attach.map fun linked =>
    (linked.1, reconstructPresentedAuxiliaryAt code (target linked))

/-- Reconstruct both source fields consumed by the expanded-fiber weight. -/
def reconstructPresentedEntry
    (code : SlabFaceStrandComponentDropCode)
    {K extent : Nat} {targetPhysical : SlabLabelling}
    (links : List SlabLink)
    (target : PresentedSlabFusionWitnessAssignment
      K extent targetPhysical links) :
    SlabLabelling × SlabFusionWitnessAssignment :=
  (code.reconstructPhysical targetPhysical,
    reconstructPresentedAssignmentRaw code links target)

/-- Decoding the physical word against the lowered target recovers the source
physical field. -/
theorem presentedSlabSupportedSelectionDropCode_reconstructPhysical
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment) :
    (presentedSlabSupportedSelectionDropCode selection).reconstructPhysical
        selection.closed.lowerPhysical =
      physical := by
  unfold SlabFaceStrandComponentDropCode.reconstructPhysical
    SlabFaceStrandComponentDropCode.decodePhysicalDrop
    presentedSlabSupportedSelectionDropCode
  exact selection.reconstructPhysical

/-- At each displayed link, code decoding against the accepted lowered
presented witness recovers the literal source auxiliary. -/
theorem presentedSlabSupportedSelectionDropCode_reconstructPresentedAuxiliaryAt
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (linked : {link // link ∈ links}) :
    reconstructPresentedAuxiliaryAt
        (presentedSlabSupportedSelectionDropCode selection)
        (selection.closed.loweredAssignment linked) =
      (assignment linked).auxiliary := by
  unfold reconstructPresentedAuxiliaryAt
    PresentedSlabPartnerClosedFaceSelection.loweredAssignment
    PresentedSlabPartnerClosedFaceSelection.loweredWitnessAt
  rw [presentedSlabSupportedSelection_decodePresentedAuxiliaryDrop_dropCode
    selection linked]
  exact
    OrderedSlabLinkPartnerClosedFaceSelection.reconstructAuxiliary_lower
      (selection.closed.atLink linked)

/-- **Global raw left inverse.**  The finite code and lowered presented target
reconstruct the literal source payload at every displayed link.  No separate
face-order code is consumed. -/
theorem presentedSlabSupportedSelectionDropCode_reconstructPresentedAssignmentRaw
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment) :
    reconstructPresentedAssignmentRaw
        (presentedSlabSupportedSelectionDropCode selection) links
        selection.closed.loweredAssignment =
      presentedSlabFusionWitnessAssignmentRaw links assignment := by
  unfold reconstructPresentedAssignmentRaw
    presentedSlabFusionWitnessAssignmentRaw
  apply List.map_congr_left
  intro linked hlinked
  congr 1
  exact
    presentedSlabSupportedSelectionDropCode_reconstructPresentedAuxiliaryAt
      selection linked

/-- The encoded supported peel is a left inverse on the complete source entry
used by the expanded-fiber formula. -/
theorem presentedSlabSupportedSelectionDropCode_reconstructPresentedEntry
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment) :
    reconstructPresentedEntry
        (presentedSlabSupportedSelectionDropCode selection) links
        selection.closed.loweredAssignment =
      (physical, presentedSlabFusionWitnessAssignmentRaw links assignment) := by
  apply Prod.ext
  · exact presentedSlabSupportedSelectionDropCode_reconstructPhysical
      selection
  · exact
      presentedSlabSupportedSelectionDropCode_reconstructPresentedAssignmentRaw
        selection

end YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode.OrderedSlabLinkPartnerClosedFaceSelection.drop_le_auxiliary
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode.OrderedSlabLinkPartnerClosedFaceSelection.reconstructAuxiliary_lower
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode.presentedSlabSupportedSelectionDropCode
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode.presentedSlabSupportedSelectionAuxiliaryDropWordAt_length_le_three
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode.presentedSlabSupportedSelection_decodePresentedAuxiliaryDrop_dropCode
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode.presentedSlabSupportedSelectionDropCode_reconstructPhysical
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode.presentedSlabSupportedSelectionDropCode_reconstructPresentedAuxiliaryAt
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode.presentedSlabSupportedSelectionDropCode_reconstructPresentedAssignmentRaw
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode.presentedSlabSupportedSelectionDropCode_reconstructPresentedEntry
