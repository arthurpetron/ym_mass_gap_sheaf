/-
# The cross-replica local switch is the identity on an inactive link

When the face selection is false on every physical face incident on one
link, its selected subnetwork has zero physical and auxiliary labels, while
its unselected subnetwork is the complete original auxiliary witness.
Consequently the two-replica crossed sum returns the original left and right
auxiliary fields exactly.

This is the local identity law needed to combine a finite active-row code
with the final switched target: only active links need explicit source-row
provenance.

Constructive contract: exact finite Boolean counts, the accepted auxiliary
l1 bound, and natural zero arithmetic only; no `Classical`, choice,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingAuxiliaryLocality
import YMGap.Continuum.CompactDualSlabCrossReplicaLocalSwitch

namespace YMGap.Continuum.CompactDualSlabCrossReplicaLocalSwitchInactive

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabAcceptedAuxiliaryValueBound
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingAuxiliaryLocality
open YMGap.Continuum.CompactDualSlabCrossReplicaLocalSwitch
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.CompactDualSlabSelectionComplement
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FusionSupportAddition
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

private theorem natListSum_map_eq_zero_of_local
    {A : Type} (weight : A -> Nat) : forall items : List A,
    (forall item, item ∈ items -> weight item = 0) ->
      natListSum (items.map weight) = 0
  | [], _ => rfl
  | head :: tail, hzero => by
      simp only [List.map_cons, natListSum]
      rw [hzero head List.mem_cons_self,
        natListSum_map_eq_zero_of_local weight tail
          (fun item hitem =>
            hzero item (List.mem_cons_of_mem head hitem))]

/-- An incident face contributes no selected copies when every incident
face-copy selection is false. -/
theorem slabLinkPartnerClosedFaceSelection_count_eq_zero_of_incident_false
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem)
    (hfalse : forall copy, copy.faceId ∈
      slabIncidentPlaqIds extent link -> selection.selected copy = false)
    (faceId : Nat) (hface : faceId ∈ slabIncidentPlaqIds extent link) :
    slabFaceStrandSelectionCount selection.selected faceId = 0 := by
  unfold slabFaceStrandSelectionCount
  have hselection :
      slabFaceStrandSelectionAt selection.selected faceId =
        fun _ => false := by
    funext slot
    unfold slabFaceStrandSelectionAt
    split
    · exact hfalse _ hface
    · rfl
  rw [hselection, boolCountFrom_false]

/-- With no selected incident physical strand, the unselected auxiliary
subnetwork is the complete source auxiliary field. -/
theorem slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary_eq_of_incident_false
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem)
    (hfalse : forall copy, copy.faceId ∈
      slabIncidentPlaqIds extent link -> selection.selected copy = false) :
    slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary selection =
      auxiliary := by
  unfold slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary
  rw [selection.toMateClosedSelection_drop]
  apply
    YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingAuxiliaryLocality.SlabLinkPartnerClosedFaceSelection.lowerAuxiliary_eq_of_physicalDrop_l1_eq_zero
  rw [YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1.SlabLinkPartnerClosedFaceSelection.physicalDrop_l1_eq_incidentFace_l1]
  exact natListSum_map_eq_zero_of_local
    (slabFaceStrandSelectionCount selection.selected)
    (slabIncidentPlaqIds extent link)
    (fun faceId hface =>
      slabLinkPartnerClosedFaceSelection_count_eq_zero_of_incident_false
        selection hfalse faceId hface)

/-- With no selected incident physical strand, the selected auxiliary
subnetwork is literally the zero labelling. -/
theorem slabLinkPartnerClosedFaceSelectionSelectedAuxiliary_eq_zero_of_incident_false
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem)
    (hfalse : forall copy, copy.faceId ∈
      slabIncidentPlaqIds extent link -> selection.selected copy = false) :
    slabLinkPartnerClosedFaceSelectionSelectedAuxiliary selection =
      zeroEdgeLabelling := by
  have hselectedMem :=
    slabLinkPartnerClosedFaceSelectionSelectedAuxiliary_mem selection
  have hphysicalZero : forall faceId,
      faceId ∈ slabIncidentPlaqIds extent link ->
        slabLinkPartnerClosedFaceSelectionSelectedPhysical selection
          faceId = 0 := by
    intro faceId hface
    rw [slabLinkPartnerClosedFaceSelectionSelectedPhysical_eq_count]
    exact
      slabLinkPartnerClosedFaceSelection_count_eq_zero_of_incident_false
        selection hfalse faceId hface
  have hmassZero :
      natListSum
          ((slabIncidentPlaqIds extent link).map
            (slabLinkPartnerClosedFaceSelectionSelectedPhysical selection)) =
        0 :=
    natListSum_map_eq_zero_of_local
      (slabLinkPartnerClosedFaceSelectionSelectedPhysical selection)
      (slabIncidentPlaqIds extent link) hphysicalZero
  funext edge
  by_cases hedge : edge ∈ canonicalUsedAuxiliaryCoordinates
      (slabIncidentPlaqIds extent link).length
  · have hbound :=
      slabLinkFusionWitness_auxiliary_le_incidentPhysical_l1
        hselectedMem edge hedge
    rw [hmassZero] at hbound
    unfold zeroEdgeLabelling
    omega
  · have hbounded := (List.mem_filter.mp hselectedMem).1
    have hzero :=
      (boundedEdgeLabellings_sound
        (linkAuxiliaryCutoff cutoff)
        (canonicalUsedAuxiliaryCoordinates
          (slabIncidentPlaqIds extent link).length)
        (slabLinkPartnerClosedFaceSelectionSelectedAuxiliary selection)
        hbounded).2 edge hedge
    unfold zeroEdgeLabelling
    exact hzero

/-- The first crossed auxiliary output is the original left source whenever
both local selections are inactive. -/
theorem slabCrossReplicaLeftAuxiliary_eq_left_of_incident_false
    {K extent : Nat} {leftPhysical rightPhysical : SlabLabelling}
    {link : SlabLink}
    {leftAuxiliary rightAuxiliary : SlabLabelling}
    {hleftMem : leftAuxiliary ∈
      slabLinkFusionWitnesses K extent leftPhysical link}
    {hrightMem : rightAuxiliary ∈
      slabLinkFusionWitnesses K extent rightPhysical link}
    (leftSelection : SlabLinkPartnerClosedFaceSelection
      K extent leftPhysical link leftAuxiliary hleftMem)
    (rightSelection : SlabLinkPartnerClosedFaceSelection
      K extent rightPhysical link rightAuxiliary hrightMem)
    (hleftFalse : forall copy, copy.faceId ∈
      slabIncidentPlaqIds extent link ->
        leftSelection.selected copy = false)
    (hrightFalse : forall copy, copy.faceId ∈
      slabIncidentPlaqIds extent link ->
        rightSelection.selected copy = false) :
    slabCrossReplicaLeftAuxiliary leftSelection rightSelection =
      leftAuxiliary := by
  unfold slabCrossReplicaLeftAuxiliary
  rw [slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary_eq_of_incident_false
      leftSelection hleftFalse,
    slabLinkPartnerClosedFaceSelectionSelectedAuxiliary_eq_zero_of_incident_false
      rightSelection hrightFalse]
  funext edge
  rfl

/-- The second crossed auxiliary output is the original right source under
the same inactive-link condition. -/
theorem slabCrossReplicaRightAuxiliary_eq_right_of_incident_false
    {K extent : Nat} {leftPhysical rightPhysical : SlabLabelling}
    {link : SlabLink}
    {leftAuxiliary rightAuxiliary : SlabLabelling}
    {hleftMem : leftAuxiliary ∈
      slabLinkFusionWitnesses K extent leftPhysical link}
    {hrightMem : rightAuxiliary ∈
      slabLinkFusionWitnesses K extent rightPhysical link}
    (leftSelection : SlabLinkPartnerClosedFaceSelection
      K extent leftPhysical link leftAuxiliary hleftMem)
    (rightSelection : SlabLinkPartnerClosedFaceSelection
      K extent rightPhysical link rightAuxiliary hrightMem)
    (hleftFalse : forall copy, copy.faceId ∈
      slabIncidentPlaqIds extent link ->
        leftSelection.selected copy = false)
    (hrightFalse : forall copy, copy.faceId ∈
      slabIncidentPlaqIds extent link ->
        rightSelection.selected copy = false) :
    slabCrossReplicaRightAuxiliary leftSelection rightSelection =
      rightAuxiliary := by
  unfold slabCrossReplicaRightAuxiliary
  rw [slabLinkPartnerClosedFaceSelectionSelectedAuxiliary_eq_zero_of_incident_false
      leftSelection hleftFalse,
    slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary_eq_of_incident_false
      rightSelection hrightFalse]
  funext edge
  unfold addEdgeLabelling zeroEdgeLabelling
  exact Nat.zero_add _

#print axioms slabLinkPartnerClosedFaceSelection_count_eq_zero_of_incident_false
#print axioms slabLinkPartnerClosedFaceSelectionUnselectedAuxiliary_eq_of_incident_false
#print axioms slabLinkPartnerClosedFaceSelectionSelectedAuxiliary_eq_zero_of_incident_false
#print axioms slabCrossReplicaLeftAuxiliary_eq_left_of_incident_false
#print axioms slabCrossReplicaRightAuxiliary_eq_right_of_incident_false

end YMGap.Continuum.CompactDualSlabCrossReplicaLocalSwitchInactive
