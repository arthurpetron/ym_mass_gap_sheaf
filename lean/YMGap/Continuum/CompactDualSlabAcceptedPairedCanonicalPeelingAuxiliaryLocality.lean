/-
# Canonical paired peeling is auxiliary-local to its active link carrier

The physical locality theorem shows that every selected strand component in
the canonical iteration stays inside the initial target-rooted support
component.  A link outside the corresponding active carrier therefore sees
zero selected physical mass at every peel.

The sharp pointwise conservation theorem then forces every used internal
auxiliary drop at that link to be zero.  Off the used internal coordinates,
an enumerated auxiliary witness is itself zero.  Hence one peel leaves the
complete auxiliary labelling unchanged at every inactive link, and the same
literal equality propagates through the terminating canonical iteration.

Constructive contract: pointwise natural subtraction, the proved component
locality witness, and the existing well-founded recursion only.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveAuxiliaryCarrier
import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingLocality

namespace YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingAuxiliaryLocality

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingLocality
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryPointwiseBound
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1
open YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveLinks
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Zero incident physical drop means zero auxiliary change -/

/-- If the selected physical l1 mass at one link is zero, lowering by the
component selection leaves its complete auxiliary witness unchanged. -/
theorem SlabLinkPartnerClosedFaceSelection.lowerAuxiliary_eq_of_physicalDrop_l1_eq_zero
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem)
    (hzero : natListSum
      ((List.finRange (slabIncidentPlaqIds extent link).length).map
        fun position => selection.drop position.val) = 0) :
    lowerEdgeLabellingBy auxiliary selection.drop = auxiliary := by
  funext edge
  by_cases hedge : edge ∈ canonicalUsedAuxiliaryCoordinates
      (slabIncidentPlaqIds extent link).length
  · have hbound :=
      SlabLinkPartnerClosedFaceSelection.auxiliaryDrop_le_physicalDrop_l1
        selection edge hedge
    rw [hzero] at hbound
    have hedgeZero : selection.drop edge = 0 := by omega
    simp [lowerEdgeLabellingBy, hedgeZero]
  · have hbounded : auxiliary ∈
        boundedEdgeLabellings (linkAuxiliaryCutoff cutoff)
          (canonicalUsedAuxiliaryCoordinates
            (slabIncidentPlaqIds extent link).length) :=
      (List.mem_filter.mp hmem).1
    have hauxiliaryZero :=
      (boundedEdgeLabellings_sound
        (linkAuxiliaryCutoff cutoff)
        (canonicalUsedAuxiliaryCoordinates
          (slabIncidentPlaqIds extent link).length)
        auxiliary hbounded).2 edge hedge
    simp [lowerEdgeLabellingBy, hauxiliaryZero]

private theorem natListSum_map_eq_zero_of
    {A : Type} (weight : A → Nat) : ∀ items : List A,
    (∀ item, item ∈ items → weight item = 0) →
      natListSum (items.map weight) = 0
  | [], _ => rfl
  | head :: tail, hzero => by
      simp only [List.map_cons, natListSum]
      rw [hzero head List.mem_cons_self,
        natListSum_map_eq_zero_of weight tail
          (fun item hitem =>
            hzero item (List.mem_cons_of_mem head hitem))]

/-- Linkwise form for a global component peel. -/
theorem SlabFusionWitnessFaceStrandSeed.lowerAssignment_atLink_eq_of_incident_selection_zero
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (link : SlabLink) (hlink : link ∈ links)
    (hzero : ∀ faceId, faceId ∈ slabIncidentPlaqIds extent link →
      slabFaceStrandSelectionCount seed.selected faceId = 0) :
    slabFusionWitnessAssignmentAt link
        (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed) =
      slabFusionWitnessAssignmentAt link assignment := by
  rw [SlabFusionWitnessFaceStrandSeed.lowerAssignment_atLink
    seed link hlink]
  apply
    SlabLinkPartnerClosedFaceSelection.lowerAuxiliary_eq_of_physicalDrop_l1_eq_zero
  rw [SlabLinkPartnerClosedFaceSelection.physicalDrop_l1_eq_incidentFace_l1]
  exact natListSum_map_eq_zero_of
    (fun faceId => slabFaceStrandSelectionCount seed.selected faceId)
    (slabIncidentPlaqIds extent link) hzero

/-! ## 2. One paired peel is unchanged off the initial active links -/

theorem SlabAcceptedPairedPeelChoice.lowerState_assignment_eq_of_not_mem_initialActiveLinks
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (initialPair : SlabObservableTwoReplicaPair D rootFaceId)
    {state : SlabAcceptedTwoReplicaState D}
    (htargetVertex : targetFaceId ∈
      slabTwoReplicaSupportFaceVertices D.extent
        initialPair.1.1.1 initialPair.2.1.1)
    (hstate : SlabAcceptedPairPhysicalLE state
      (slabObservableTwoReplicaPairToAcceptedState initialPair))
    (choice : SlabAcceptedPairedPeelChoice D state)
    (hroot : choice.faceId ∈
      slabTwoReplicaTargetSupportComponent D.extent
        initialPair.1.1.1 initialPair.2.1.1 targetFaceId)
    (link : SlabLink)
    (hlink : link ∈ boundaryCompleteSlabLinks D.extent)
    (hinactive : link ∉
      slabObservableTwoReplicaPairTargetSupportActiveLinks
        D initialPair targetFaceId) :
    slabFusionWitnessAssignmentAt link choice.lowerState.1.1.2 =
        slabFusionWitnessAssignmentAt link state.1.1.2 ∧
      slabFusionWitnessAssignmentAt link choice.lowerState.2.1.2 =
        slabFusionWitnessAssignmentAt link state.2.1.2 := by
  cases choice with
  | left faceId hface hpositive =>
      let seed := acceptedExpandedSourceRootSeed
        D faceId hface state.1 hpositive
      have hlocal : slabFusionWitnessAssignmentAt link
            (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed) =
          slabFusionWitnessAssignmentAt link state.1.1.2 := by
        apply
          SlabFusionWitnessFaceStrandSeed.lowerAssignment_atLink_eq_of_incident_selection_zero
            seed link hlink
        intro incidentFace hincident
        apply
          SlabFusionWitnessFaceStrandSeed.selectionCount_eq_zero_of_not_mem_initialTargetComponent
            seed htargetVertex
        · intro query hpositiveCurrent
          exact Or.inl (by
            have hle := (hstate query).1
            change state.1.1.1 query ≤ initialPair.1.1.1 query at hle
            omega)
        · exact hroot
        · intro hcomponent
          apply hinactive
          exact
            slabObservableTwoReplicaPairTargetSupportComponent_incident_mem_activeLinks
              D initialPair hlink hincident hcomponent
      constructor
      · simpa [SlabAcceptedPairedPeelChoice.lowerState,
          slabAcceptedTwoReplicaStateLowerLeftAt,
          acceptedExpandedSourceLowerAt, seed] using hlocal
      · rfl
  | right faceId hface hleftZero hpositive =>
      let seed := acceptedExpandedSourceRootSeed
        D faceId hface state.2 hpositive
      have hlocal : slabFusionWitnessAssignmentAt link
            (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed) =
          slabFusionWitnessAssignmentAt link state.2.1.2 := by
        apply
          SlabFusionWitnessFaceStrandSeed.lowerAssignment_atLink_eq_of_incident_selection_zero
            seed link hlink
        intro incidentFace hincident
        apply
          SlabFusionWitnessFaceStrandSeed.selectionCount_eq_zero_of_not_mem_initialTargetComponent
            seed htargetVertex
        · intro query hpositiveCurrent
          exact Or.inr (by
            have hle := (hstate query).2
            change state.2.1.1 query ≤ initialPair.2.1.1 query at hle
            omega)
        · exact hroot
        · intro hcomponent
          apply hinactive
          exact
            slabObservableTwoReplicaPairTargetSupportComponent_incident_mem_activeLinks
              D initialPair hlink hincident hcomponent
      constructor
      · rfl
      · simpa [SlabAcceptedPairedPeelChoice.lowerState,
          slabAcceptedTwoReplicaStateLowerRightAt,
          acceptedExpandedSourceLowerAt, seed] using hlocal

/-! ## 3. Auxiliary locality through the complete canonical iteration -/

/-- For any current state physically dominated by the fixed initial pair,
canonical peeling of its initial component leaves both auxiliary lookups
unchanged at every initially inactive link. -/
theorem slabAcceptedPairCanonicalPeeling_final_assignment_eq_of_not_mem_initialActiveLinks
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (initialPair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : initialPair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (state : SlabAcceptedTwoReplicaState D)
    (hstate : SlabAcceptedPairPhysicalLE state
      (slabObservableTwoReplicaPairToAcceptedState initialPair)) :
    ∀ link,
      link ∈ boundaryCompleteSlabLinks D.extent →
      link ∉ slabObservableTwoReplicaPairTargetSupportActiveLinks
        D initialPair targetFaceId →
      let finalState :=
        (slabAcceptedPairCanonicalPeeling D
          (slabTwoReplicaTargetSupportComponent D.extent
            initialPair.1.1.1 initialPair.2.1.1 targetFaceId)
          (fun faceId hface =>
            slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
              D rootFaceId targetFaceId htarget initialPair hpair
                faceId hface)
          state).1
      slabFusionWitnessAssignmentAt link finalState.1.1.2 =
          slabFusionWitnessAssignmentAt link state.1.1.2 ∧
        slabFusionWitnessAssignmentAt link finalState.2.1.2 =
          slabFusionWitnessAssignmentAt link state.2.1.2 := by
  rw [slabAcceptedPairCanonicalPeeling]
  split
  · intro link _ _
    exact ⟨rfl, rfl⟩
  · rename_i choice hchoice
    intro link hlink hinactive
    have htargetVertex : targetFaceId ∈
        slabTwoReplicaSupportFaceVertices D.extent
          initialPair.1.1.1 initialPair.2.1.1 := by
      apply mem_slabTwoReplicaSupportFaceVertices htarget
      exact Or.inl
        (slabObservableTwoReplicaPairLeft_target_positive_of_mem_source
          D rootFaceId targetFaceId initialPair hpair)
    have hroot : choice.faceId ∈
        slabTwoReplicaTargetSupportComponent D.extent
          initialPair.1.1.1 initialPair.2.1.1 targetFaceId :=
      slabAcceptedPairCanonicalChoice?_some_face_mem
        D state
        (slabTwoReplicaTargetSupportComponent D.extent
          initialPair.1.1.1 initialPair.2.1.1 targetFaceId)
        (fun faceId hface =>
          slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
            D rootFaceId targetFaceId htarget initialPair hpair
              faceId hface)
        choice hchoice
    have hstep :=
      SlabAcceptedPairedPeelChoice.lowerState_assignment_eq_of_not_mem_initialActiveLinks
        initialPair htargetVertex hstate choice hroot link hlink hinactive
    have htail :=
      slabAcceptedPairCanonicalPeeling_final_assignment_eq_of_not_mem_initialActiveLinks
        D rootFaceId targetFaceId htarget initialPair hpair
        choice.lowerState
        (SlabAcceptedPairedPeelChoice.lowerState_physicalLE choice hstate)
        link hlink hinactive
    exact ⟨htail.1.trans hstep.1, htail.2.trans hstep.2⟩
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

/-- Observable specialization: the terminal canonical state and the source
pair have identical auxiliary rows at every initially inactive link. -/
theorem slabObservablePairTargetSupportCanonicalPeeling_final_assignment_eq_outside_activeLinks
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (link : SlabLink)
    (hlink : link ∈ boundaryCompleteSlabLinks D.extent)
    (hinactive : link ∉
      slabObservableTwoReplicaPairTargetSupportActiveLinks
        D pair targetFaceId) :
    let finalState :=
      (slabObservablePairTargetSupportCanonicalPeeling
        D rootFaceId targetFaceId htarget pair hpair).1
    slabFusionWitnessAssignmentAt link finalState.1.1.2 =
        slabFusionWitnessAssignmentAt link pair.1.1.2 ∧
      slabFusionWitnessAssignmentAt link finalState.2.1.2 =
        slabFusionWitnessAssignmentAt link pair.2.1.2 := by
  have hlocal :=
    slabAcceptedPairCanonicalPeeling_final_assignment_eq_of_not_mem_initialActiveLinks
      D rootFaceId targetFaceId htarget pair hpair
      (slabObservableTwoReplicaPairToAcceptedState pair)
      (fun _ => ⟨Nat.le_refl _, Nat.le_refl _⟩)
      link hlink hinactive
  simpa only [slabObservablePairTargetSupportCanonicalPeeling,
    slabObservableTwoReplicaPairToAcceptedState,
    slabObservablePositiveSourceEntryToAccepted] using hlocal

#print axioms SlabLinkPartnerClosedFaceSelection.lowerAuxiliary_eq_of_physicalDrop_l1_eq_zero
#print axioms SlabFusionWitnessFaceStrandSeed.lowerAssignment_atLink_eq_of_incident_selection_zero
#print axioms SlabAcceptedPairedPeelChoice.lowerState_assignment_eq_of_not_mem_initialActiveLinks
#print axioms slabAcceptedPairCanonicalPeeling_final_assignment_eq_of_not_mem_initialActiveLinks
#print axioms slabObservablePairTargetSupportCanonicalPeeling_final_assignment_eq_outside_activeLinks

end YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingAuxiliaryLocality
