/-
# Sparse inverse codes for supported presented component peels

The full presented inverse code stores one internal-drop word at every slab
link.  This file erases every identically zero word and proves that the sparse
code still reconstructs the complete source physical and raw auxiliary entry.
Every retained row is nonzero and the sparse table never has more rows than
the displayed link list.

The remaining entropy step is geometric: charge retained rows and their
values to selected physical peel mass rather than to volume.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentSparseDropCode
import YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode

namespace YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentSparseDropCode

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
open YMGap.Continuum.CompactDualSlabFaceStrandComponentSparseDropCode
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Sparse encoding and exact local decoding -/

/-- Remove all zero auxiliary rows while leaving the physical peel word
unchanged. -/
def presentedSlabSupportedSelectionSparseDropCode
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment) :
    SlabFaceStrandComponentDropCode where
  physicalFaces := selection.peelFaces
  auxiliaryWords := slabSparseAuxiliaryDropWordsFrom links
    (presentedSlabSupportedSelectionAuxiliaryDropWordAt selection)

/-- Sparse decoding retains the exact supported internal component drop at
every displayed link. -/
theorem presentedSlabSupportedSelection_decodePresentedAuxiliaryDrop_sparseDropCode
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (hnodup : links.Nodup)
    (linked : {link // link ∈ links}) :
    decodePresentedAuxiliaryDrop
        (presentedSlabSupportedSelectionSparseDropCode selection)
        (assignment linked).order =
      edgeLabellingSupportedOn
        (canonicalUsedAuxiliaryCoordinates
          (assignment linked).order.faceIds.length)
        (selection.closed.atLink linked).drop := by
  let coordinates := canonicalUsedAuxiliaryCoordinates
    (assignment linked).order.faceIds.length
  have hsparse := wordToEdgeLabelling_sparseAuxiliaryDropWordsFrom
    (fun _ => coordinates)
    (presentedSlabSupportedSelectionAuxiliaryDropWordAt selection)
    links linked.1 hnodup linked.2
  unfold decodePresentedAuxiliaryDrop
    presentedSlabSupportedSelectionSparseDropCode
  change wordToEdgeLabelling coordinates
      (slabAuxiliaryDropWordAt linked.1
        (slabSparseAuxiliaryDropWordsFrom links
          (presentedSlabSupportedSelectionAuxiliaryDropWordAt selection))) = _
  rw [hsparse,
    presentedSlabSupportedSelectionAuxiliaryDropWordAt_of_mem
      selection linked.1 linked.2]
  exact wordToEdgeLabelling_map_eq_supportedOn
    (selection.closed.atLink linked).drop coordinates
    (canonicalUsedAuxiliaryCoordinates_nodup
      (assignment linked).order.length_le_six)

/-! ## 2. Sparse source reconstruction -/

/-- The sparse physical word reconstructs the exact source field. -/
theorem presentedSlabSupportedSelectionSparseDropCode_reconstructPhysical
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment) :
    (presentedSlabSupportedSelectionSparseDropCode selection).reconstructPhysical
        selection.closed.lowerPhysical = physical := by
  unfold SlabFaceStrandComponentDropCode.reconstructPhysical
    SlabFaceStrandComponentDropCode.decodePhysicalDrop
    presentedSlabSupportedSelectionSparseDropCode
  exact selection.reconstructPhysical

/-- Sparse decoding at a displayed link recovers the literal source
auxiliary. -/
theorem presentedSlabSupportedSelectionSparseDropCode_reconstructPresentedAuxiliaryAt
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (hnodup : links.Nodup)
    (linked : {link // link ∈ links}) :
    reconstructPresentedAuxiliaryAt
        (presentedSlabSupportedSelectionSparseDropCode selection)
        (selection.closed.loweredAssignment linked) =
      (assignment linked).auxiliary := by
  unfold reconstructPresentedAuxiliaryAt
    PresentedSlabPartnerClosedFaceSelection.loweredAssignment
    PresentedSlabPartnerClosedFaceSelection.loweredWitnessAt
  rw [presentedSlabSupportedSelection_decodePresentedAuxiliaryDrop_sparseDropCode
    selection hnodup linked]
  exact
    OrderedSlabLinkPartnerClosedFaceSelection.reconstructAuxiliary_lower
      (selection.closed.atLink linked)

/-- **Sparse global left inverse.**  The sparse code and lowered target still
recover the complete source entry consumed by the expanded-fiber weight. -/
theorem presentedSlabSupportedSelectionSparseDropCode_reconstructPresentedEntry
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (hnodup : links.Nodup) :
    reconstructPresentedEntry
        (presentedSlabSupportedSelectionSparseDropCode selection) links
        selection.closed.loweredAssignment =
      (physical, presentedSlabFusionWitnessAssignmentRaw links assignment) := by
  apply Prod.ext
  · exact presentedSlabSupportedSelectionSparseDropCode_reconstructPhysical
      selection
  · unfold reconstructPresentedEntry reconstructPresentedAssignmentRaw
      presentedSlabFusionWitnessAssignmentRaw
    apply List.map_congr_left
    intro linked hlinked
    congr 1
    exact
      presentedSlabSupportedSelectionSparseDropCode_reconstructPresentedAuxiliaryAt
        selection hnodup linked

/-! ## 3. Sparse table shape -/

/-- Zero-row erasure never increases the number of stored rows. -/
theorem presentedSlabSupportedSelectionSparseDropCode_auxiliaryWords_length_le
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment) :
    (presentedSlabSupportedSelectionSparseDropCode
      selection).auxiliaryWords.length <= links.length := by
  unfold presentedSlabSupportedSelectionSparseDropCode
  exact slabSparseAuxiliaryDropWordsFrom_length_le
    (presentedSlabSupportedSelectionAuxiliaryDropWordAt selection) links

/-- Every retained sparse row is genuinely nonzero. -/
theorem presentedSlabSupportedSelectionSparseDropCode_row_nonzero
    {K extent : Nat} {physical : SlabLabelling} {links : List SlabLink}
    {assignment : PresentedSlabFusionWitnessAssignment
      K extent physical links}
    (selection : PresentedSlabSupportedPartnerClosedFaceSelection
      K extent physical links assignment)
    (entry : SlabLink × List Nat)
    (hentry : entry ∈
      (presentedSlabSupportedSelectionSparseDropCode
        selection).auxiliaryWords) :
    finiteWordAllZeroB entry.2 = false := by
  unfold presentedSlabSupportedSelectionSparseDropCode at hentry
  exact finiteWordAllZeroB_eq_false_of_mem_sparse
    (presentedSlabSupportedSelectionAuxiliaryDropWordAt selection)
    links entry hentry

end YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentSparseDropCode

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentSparseDropCode.presentedSlabSupportedSelectionSparseDropCode
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentSparseDropCode.presentedSlabSupportedSelection_decodePresentedAuxiliaryDrop_sparseDropCode
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentSparseDropCode.presentedSlabSupportedSelectionSparseDropCode_reconstructPresentedEntry
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentSparseDropCode.presentedSlabSupportedSelectionSparseDropCode_auxiliaryWords_length_le
#print axioms
  YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentSparseDropCode.presentedSlabSupportedSelectionSparseDropCode_row_nonzero
