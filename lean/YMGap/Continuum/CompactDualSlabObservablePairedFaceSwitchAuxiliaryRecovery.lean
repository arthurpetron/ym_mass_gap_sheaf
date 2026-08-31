/-
# Auxiliary recovery for the paired-face switch

The final crossed assignments split the source links into two exact cases.
On links touching the target-rooted physical support, the stored active-row
table recovers both source auxiliary labellings.  On every other complete
link, the paired strand mask is false on all incident faces, so the local
cross-replica switch is literally the identity.

Consequently, equality of the final switched target, equality of the two
source physical fields, and equality of the active-row tables recover both
complete source assignments and hence the source pair itself.  This is a
data-level decoder theorem; no counting or retained-weight estimate is made.

Constructive contract: finite list lookup, support refinement, accepted
zero-extension, and the proved inactive-switch identity only.  No
`Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabCrossReplicaLocalSwitchInactive
import YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchPhysicalRecovery
import YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalAuxiliaryReconstruction

namespace YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAuxiliaryRecovery

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabCrossReplicaLocalSwitchInactive
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAssignment
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchDecoder
open YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveAuxiliaryCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveLinks
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalAuxiliaryReconstruction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

private theorem listMap_eq_on_mem_local
    {A B : Type} (items : List A) (left right : A -> B)
    (hmap : items.map left = items.map right) :
    forall item, item ∈ items -> left item = right item := by
  induction items with
  | nil =>
      intro item hitem
      exact False.elim (List.not_mem_nil hitem)
  | cons head tail ih =>
      simp only [List.map_cons] at hmap
      have hhead : left head = right head := (List.cons.inj hmap).1
      have htail : tail.map left = tail.map right := (List.cons.inj hmap).2
      intro item hitem
      rcases List.mem_cons.mp hitem with rfl | htailMem
      · exact hhead
      · exact ih htail item htailMem

/-! ## 1. Physical equality makes the active-row order common -/

theorem slabObservablePairTargetSupportActiveLinks_eq_of_physical_eq
    (D : SlabPhysicalData) {rootFaceId targetFaceId : Nat}
    (first second : SlabObservableTwoReplicaPair D rootFaceId)
    (hleft : first.1.1.1 = second.1.1.1)
    (hright : first.2.1.1 = second.2.1.1) :
    slabObservableTwoReplicaPairTargetSupportActiveLinks
        D first targetFaceId =
      slabObservableTwoReplicaPairTargetSupportActiveLinks
        D second targetFaceId := by
  unfold slabObservableTwoReplicaPairTargetSupportActiveLinks
  rw [hleft, hright]

/-- On an active link, common physical fields and a common active-row table
recover both complete local source auxiliary labellings. -/
theorem slabObservablePair_sourceAssignmentAt_eq_of_physical_eq_of_activeRows_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (first second : SlabObservableTwoReplicaPair D rootFaceId)
    (_hfirst : first ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (_hsecond : second ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (hleft : first.1.1.1 = second.1.1.1)
    (hright : first.2.1.1 = second.2.1.1)
    (hrows :
      slabObservablePairTargetSupportActiveAuxiliaryRows
          D first targetFaceId =
        slabObservablePairTargetSupportActiveAuxiliaryRows
          D second targetFaceId)
    (link : SlabLink)
    (hlink : link ∈
      slabObservableTwoReplicaPairTargetSupportActiveLinks
        D first targetFaceId) :
    slabFusionWitnessAssignmentAt link first.1.1.2 =
        slabFusionWitnessAssignmentAt link second.1.1.2 ∧
      slabFusionWitnessAssignmentAt link first.2.1.2 =
        slabFusionWitnessAssignmentAt link second.2.1.2 := by
  have hactive :=
    slabObservablePairTargetSupportActiveLinks_eq_of_physical_eq
      D (targetFaceId := targetFaceId) first second hleft hright
  have hcoordinates :
      slabObservablePairTargetSupportActiveLinkCoordinates
          D first targetFaceId =
        slabObservablePairTargetSupportActiveLinkCoordinates
          D second targetFaceId := by
    unfold slabObservablePairTargetSupportActiveLinkCoordinates
    rw [hactive]
  have hrowsCommon := hrows
  unfold slabObservablePairTargetSupportActiveAuxiliaryRows at hrowsCommon
  rw [← hcoordinates] at hrowsCommon
  have hfalseMem : (link, false) ∈
      slabObservablePairTargetSupportActiveLinkCoordinates
        D first targetFaceId := by
    unfold slabObservablePairTargetSupportActiveLinkCoordinates
    apply List.mem_flatMap.mpr
    exact ⟨link, hlink, List.mem_cons_self⟩
  have htrueMem : (link, true) ∈
      slabObservablePairTargetSupportActiveLinkCoordinates
        D first targetFaceId := by
    unfold slabObservablePairTargetSupportActiveLinkCoordinates
    apply List.mem_flatMap.mpr
    exact ⟨link, hlink,
      List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)⟩
  have hleftWord := listMap_eq_on_mem_local
    (slabObservablePairTargetSupportActiveLinkCoordinates
      D first targetFaceId)
    (slabObservablePairActiveAuxiliaryRowAt D first)
    (slabObservablePairActiveAuxiliaryRowAt D second)
    hrowsCommon (link, false) hfalseMem
  have hrightWord := listMap_eq_on_mem_local
    (slabObservablePairTargetSupportActiveLinkCoordinates
      D first targetFaceId)
    (slabObservablePairActiveAuxiliaryRowAt D first)
    (slabObservablePairActiveAuxiliaryRowAt D second)
    hrowsCommon (link, true) htrueMem
  have hcomplete :=
    slabObservableTwoReplicaPairTargetSupportActiveLink_mem_complete
      D first hlink
  have hsecondActive : link ∈
      slabObservableTwoReplicaPairTargetSupportActiveLinks
        D second targetFaceId := by
    rw [← hactive]
    exact hlink
  have hsecondComplete :=
    slabObservableTwoReplicaPairTargetSupportActiveLink_mem_complete
      D second hsecondActive
  let edges := canonicalUsedAuxiliaryCoordinates
    (slabIncidentPlaqIds D.extent link).length
  constructor
  · have hfirstLocal := slabFusionWitnessAssignmentAt_mem_local
      D.cutoff D.extent first.1.1.1
      (boundaryCompleteSlabLinks D.extent) first.1.1.2
      first.1.assignment_mem link hcomplete
    have hsecondLocal := slabFusionWitnessAssignmentAt_mem_local
      D.cutoff D.extent second.1.1.1
      (boundaryCompleteSlabLinks D.extent) second.1.1.2
      second.1.assignment_mem link hsecondComplete
    have hfirstSupport := (boundedEdgeLabellings_sound
      (linkAuxiliaryCutoff D.cutoff) edges
      (slabFusionWitnessAssignmentAt link first.1.1.2)
      (List.mem_filter.mp hfirstLocal).1).2
    have hsecondSupport := (boundedEdgeLabellings_sound
      (linkAuxiliaryCutoff D.cutoff) edges
      (slabFusionWitnessAssignmentAt link second.1.1.2)
      (List.mem_filter.mp hsecondLocal).1).2
    apply edgeLabelling_eq_of_word_eq_of_supported edges
      (slabFusionWitnessAssignmentAt link first.1.1.2)
      (slabFusionWitnessAssignmentAt link second.1.1.2)
      hfirstSupport hsecondSupport
    simpa [finiteEdgeLabellingWord,
      slabObservablePairActiveAuxiliaryRowAt, edges] using hleftWord
  · have hfirstAssignment : first.2.1.2 ∈
        slabFusionWitnessAssignmentsOn D.cutoff D.extent first.2.1.1
          (boundaryCompleteSlabLinks D.extent) :=
      (mem_slabExpandedFineSources_iff.mp first.2.2).2
    have hsecondAssignment : second.2.1.2 ∈
        slabFusionWitnessAssignmentsOn D.cutoff D.extent second.2.1.1
          (boundaryCompleteSlabLinks D.extent) :=
      (mem_slabExpandedFineSources_iff.mp second.2.2).2
    have hfirstLocal := slabFusionWitnessAssignmentAt_mem_local
      D.cutoff D.extent first.2.1.1
      (boundaryCompleteSlabLinks D.extent) first.2.1.2
      hfirstAssignment link hcomplete
    have hsecondLocal := slabFusionWitnessAssignmentAt_mem_local
      D.cutoff D.extent second.2.1.1
      (boundaryCompleteSlabLinks D.extent) second.2.1.2
      hsecondAssignment link hsecondComplete
    have hfirstSupport := (boundedEdgeLabellings_sound
      (linkAuxiliaryCutoff D.cutoff) edges
      (slabFusionWitnessAssignmentAt link first.2.1.2)
      (List.mem_filter.mp hfirstLocal).1).2
    have hsecondSupport := (boundedEdgeLabellings_sound
      (linkAuxiliaryCutoff D.cutoff) edges
      (slabFusionWitnessAssignmentAt link second.2.1.2)
      (List.mem_filter.mp hsecondLocal).1).2
    apply edgeLabelling_eq_of_word_eq_of_supported edges
      (slabFusionWitnessAssignmentAt link first.2.1.2)
      (slabFusionWitnessAssignmentAt link second.2.1.2)
      hfirstSupport hsecondSupport
    simpa [finiteEdgeLabellingWord,
      slabObservablePairActiveAuxiliaryRowAt, edges] using hrightWord

/-! ## 2. Every inactive complete link is locally unchanged -/

theorem slabObservablePairPairedFaceSwapMask_eq_false_of_inactive
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (link : SlabLink)
    (hcomplete : link ∈ boundaryCompleteSlabLinks D.extent)
    (hinactive : link ∉
      slabObservableTwoReplicaPairTargetSupportActiveLinks
        D pair targetFaceId)
    (faceId : Nat)
    (hincident : faceId ∈ slabIncidentPlaqIds D.extent link) :
    slabObservableTwoReplicaPairPairedFaceSwapMask
      D pair targetFaceId faceId = false := by
  unfold slabObservableTwoReplicaPairPairedFaceSwapMask
  apply decide_eq_false
  intro hcomponent
  apply hinactive
  apply slabObservableTwoReplicaPairTargetSupportComponent_incident_mem_activeLinks
    D pair hcomplete hincident
  exact slabObservableTwoReplicaPairTargetFaceComponent_subset_support
    D rootFaceId targetFaceId htarget pair hpair hcomponent

theorem slabObservablePairSwitchedLeftAuxiliaryAt_eq_source_of_inactive
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (link : SlabLink)
    (hcomplete : link ∈ boundaryCompleteSlabLinks D.extent)
    (hinactive : link ∉
      slabObservableTwoReplicaPairTargetSupportActiveLinks
        D pair targetFaceId) :
    slabObservablePairSwitchedLeftAuxiliaryAt
        D rootFaceId targetFaceId htarget pair hpair link =
      slabFusionWitnessAssignmentAt link pair.1.1.2 := by
  unfold slabObservablePairSwitchedLeftAuxiliaryAt
  rw [dif_pos hcomplete]
  apply slabCrossReplicaLeftAuxiliary_eq_left_of_incident_false
  · intro copy hincident
    simpa [slabObservablePairLeftSelectionAtLink] using
      slabObservablePairPairedFaceSwapMask_eq_false_of_inactive
        D rootFaceId targetFaceId htarget pair hpair link hcomplete
          hinactive copy.faceId hincident
  · intro copy hincident
    simpa [slabObservablePairRightSelectionAtLink] using
      slabObservablePairPairedFaceSwapMask_eq_false_of_inactive
        D rootFaceId targetFaceId htarget pair hpair link hcomplete
          hinactive copy.faceId hincident

theorem slabObservablePairSwitchedRightAuxiliaryAt_eq_source_of_inactive
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (link : SlabLink)
    (hcomplete : link ∈ boundaryCompleteSlabLinks D.extent)
    (hinactive : link ∉
      slabObservableTwoReplicaPairTargetSupportActiveLinks
        D pair targetFaceId) :
    slabObservablePairSwitchedRightAuxiliaryAt
        D rootFaceId targetFaceId htarget pair hpair link =
      slabFusionWitnessAssignmentAt link pair.2.1.2 := by
  unfold slabObservablePairSwitchedRightAuxiliaryAt
  rw [dif_pos hcomplete]
  apply slabCrossReplicaRightAuxiliary_eq_right_of_incident_false
  · intro copy hincident
    simpa [slabObservablePairLeftSelectionAtLink] using
      slabObservablePairPairedFaceSwapMask_eq_false_of_inactive
        D rootFaceId targetFaceId htarget pair hpair link hcomplete
          hinactive copy.faceId hincident
  · intro copy hincident
    simpa [slabObservablePairRightSelectionAtLink] using
      slabObservablePairPairedFaceSwapMask_eq_false_of_inactive
        D rootFaceId targetFaceId htarget pair hpair link hcomplete
          hinactive copy.faceId hincident

/-! ## 3. Final target plus active provenance recovers the whole pair -/

theorem slabObservablePairedFaceSwitchable_sourceAssignments_eq_of_targetPair_eq_of_physical_eq_of_activeRows_eq
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    (first second : SlabObservablePairedFaceSwitchablePair
      D rootFaceId targetFaceId)
    (htargetPair : slabObservablePairedFaceSwitchableTargetPair
        D rootFaceId targetFaceId htarget first =
      slabObservablePairedFaceSwitchableTargetPair
        D rootFaceId targetFaceId htarget second)
    (hphysical : first.pair.1.1.1 = second.pair.1.1.1 ∧
      first.pair.2.1.1 = second.pair.2.1.1)
    (hrows :
      slabObservablePairTargetSupportActiveAuxiliaryRows
          D first.pair targetFaceId =
        slabObservablePairTargetSupportActiveAuxiliaryRows
          D second.pair targetFaceId) :
    first.pair.1.1.2 = second.pair.1.1.2 ∧
      first.pair.2.1.2 = second.pair.2.1.2 := by
  have hactive :=
    slabObservablePairTargetSupportActiveLinks_eq_of_physical_eq
      D (targetFaceId := targetFaceId)
        first.pair second.pair hphysical.1 hphysical.2
  have hlookup : forall link,
      link ∈ boundaryCompleteSlabLinks D.extent ->
      slabFusionWitnessAssignmentAt link first.pair.1.1.2 =
          slabFusionWitnessAssignmentAt link second.pair.1.1.2 ∧
        slabFusionWitnessAssignmentAt link first.pair.2.1.2 =
          slabFusionWitnessAssignmentAt link second.pair.2.1.2 := by
    intro link hcomplete
    by_cases hlinkActive : link ∈
        slabObservableTwoReplicaPairTargetSupportActiveLinks
          D first.pair targetFaceId
    · exact
        slabObservablePair_sourceAssignmentAt_eq_of_physical_eq_of_activeRows_eq
          D rootFaceId targetFaceId first.pair second.pair
            first.pair_mem second.pair_mem hphysical.1 hphysical.2 hrows
            link hlinkActive
    · have hsecondInactive : link ∉
          slabObservableTwoReplicaPairTargetSupportActiveLinks
            D second.pair targetFaceId := by
        intro hsecondActive
        apply hlinkActive
        rw [hactive]
        exact hsecondActive
      have hfirstLeftLocal :=
        slabObservablePairSwitchedLeftAuxiliaryAt_eq_source_of_inactive
          D rootFaceId targetFaceId htarget first.pair first.pair_mem
            link hcomplete hlinkActive
      have hsecondLeftLocal :=
        slabObservablePairSwitchedLeftAuxiliaryAt_eq_source_of_inactive
          D rootFaceId targetFaceId htarget second.pair second.pair_mem
            link hcomplete hsecondInactive
      have hfirstRightLocal :=
        slabObservablePairSwitchedRightAuxiliaryAt_eq_source_of_inactive
          D rootFaceId targetFaceId htarget first.pair first.pair_mem
            link hcomplete hlinkActive
      have hsecondRightLocal :=
        slabObservablePairSwitchedRightAuxiliaryAt_eq_source_of_inactive
          D rootFaceId targetFaceId htarget second.pair second.pair_mem
            link hcomplete hsecondInactive
      have hfirstLeftLookup := slabFusionWitnessAssignmentAt_from
        (slabObservablePairSwitchedLeftAuxiliaryAt
          D rootFaceId targetFaceId htarget first.pair first.pair_mem)
        (boundaryCompleteSlabLinks D.extent) link hcomplete
      have hsecondLeftLookup := slabFusionWitnessAssignmentAt_from
        (slabObservablePairSwitchedLeftAuxiliaryAt
          D rootFaceId targetFaceId htarget second.pair second.pair_mem)
        (boundaryCompleteSlabLinks D.extent) link hcomplete
      have hfirstRightLookup := slabFusionWitnessAssignmentAt_from
        (slabObservablePairSwitchedRightAuxiliaryAt
          D rootFaceId targetFaceId htarget first.pair first.pair_mem)
        (boundaryCompleteSlabLinks D.extent) link hcomplete
      have hsecondRightLookup := slabFusionWitnessAssignmentAt_from
        (slabObservablePairSwitchedRightAuxiliaryAt
          D rootFaceId targetFaceId htarget second.pair second.pair_mem)
        (boundaryCompleteSlabLinks D.extent) link hcomplete
      change slabFusionWitnessAssignmentAt link
          (slabObservablePairSwitchedLeftAssignment
            D rootFaceId targetFaceId htarget first.pair first.pair_mem) =
        slabObservablePairSwitchedLeftAuxiliaryAt
          D rootFaceId targetFaceId htarget first.pair first.pair_mem link
        at hfirstLeftLookup
      change slabFusionWitnessAssignmentAt link
          (slabObservablePairSwitchedLeftAssignment
            D rootFaceId targetFaceId htarget second.pair second.pair_mem) =
        slabObservablePairSwitchedLeftAuxiliaryAt
          D rootFaceId targetFaceId htarget second.pair second.pair_mem link
        at hsecondLeftLookup
      change slabFusionWitnessAssignmentAt link
          (slabObservablePairSwitchedRightAssignment
            D rootFaceId targetFaceId htarget first.pair first.pair_mem) =
        slabObservablePairSwitchedRightAuxiliaryAt
          D rootFaceId targetFaceId htarget first.pair first.pair_mem link
        at hfirstRightLookup
      change slabFusionWitnessAssignmentAt link
          (slabObservablePairSwitchedRightAssignment
            D rootFaceId targetFaceId htarget second.pair second.pair_mem) =
        slabObservablePairSwitchedRightAuxiliaryAt
          D rootFaceId targetFaceId htarget second.pair second.pair_mem link
        at hsecondRightLookup
      have htargetLeft := congrArg
        (fun pair => slabFusionWitnessAssignmentAt link pair.1.1.2)
        htargetPair
      have htargetRight := congrArg
        (fun pair => slabFusionWitnessAssignmentAt link pair.2.1.2)
        htargetPair
      change slabFusionWitnessAssignmentAt link
          (slabObservablePairSwitchedLeftAssignment
            D rootFaceId targetFaceId htarget first.pair first.pair_mem) =
        slabFusionWitnessAssignmentAt link
          (slabObservablePairSwitchedLeftAssignment
            D rootFaceId targetFaceId htarget second.pair second.pair_mem)
        at htargetLeft
      change slabFusionWitnessAssignmentAt link
          (slabObservablePairSwitchedRightAssignment
            D rootFaceId targetFaceId htarget first.pair first.pair_mem) =
        slabFusionWitnessAssignmentAt link
          (slabObservablePairSwitchedRightAssignment
            D rootFaceId targetFaceId htarget second.pair second.pair_mem)
        at htargetRight
      exact ⟨hfirstLeftLocal.symm.trans
          (hfirstLeftLookup.symm.trans
            (htargetLeft.trans
              (hsecondLeftLookup.trans hsecondLeftLocal))),
        hfirstRightLocal.symm.trans
          (hfirstRightLookup.symm.trans
            (htargetRight.trans
              (hsecondRightLookup.trans hsecondRightLocal)))⟩
  have hfirstSecond : first.pair.2.1.2 ∈
      slabFusionWitnessAssignmentsOn D.cutoff D.extent first.pair.2.1.1
        (boundaryCompleteSlabLinks D.extent) :=
    (mem_slabExpandedFineSources_iff.mp first.pair.2.2).2
  have hsecondSecond : second.pair.2.1.2 ∈
      slabFusionWitnessAssignmentsOn D.cutoff D.extent second.pair.2.1.1
        (boundaryCompleteSlabLinks D.extent) :=
    (mem_slabExpandedFineSources_iff.mp second.pair.2.2).2
  constructor
  · apply slabFusionWitnessAssignment_eq_of_at_eq
      D.cutoff D.extent first.pair.1.1.1 second.pair.1.1.1
      first.pair.1.1.2 second.pair.1.1.2
      first.pair.1.assignment_mem second.pair.1.assignment_mem
    intro link hlink
    exact (hlookup link hlink).1
  · apply slabFusionWitnessAssignment_eq_of_at_eq
      D.cutoff D.extent first.pair.2.1.1 second.pair.2.1.1
      first.pair.2.1.2 second.pair.2.1.2
      hfirstSecond hsecondSecond
    intro link hlink
    exact (hlookup link hlink).2

/-- The final switched target, the two source physical fields, and the stored
active rows determine the literal source pair. -/
theorem slabObservablePairedFaceSwitchable_sourcePair_eq_of_targetPair_eq_of_physical_eq_of_activeRows_eq
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    (first second : SlabObservablePairedFaceSwitchablePair
      D rootFaceId targetFaceId)
    (htargetPair : slabObservablePairedFaceSwitchableTargetPair
        D rootFaceId targetFaceId htarget first =
      slabObservablePairedFaceSwitchableTargetPair
        D rootFaceId targetFaceId htarget second)
    (hphysical : first.pair.1.1.1 = second.pair.1.1.1 ∧
      first.pair.2.1.1 = second.pair.2.1.1)
    (hrows :
      slabObservablePairTargetSupportActiveAuxiliaryRows
          D first.pair targetFaceId =
        slabObservablePairTargetSupportActiveAuxiliaryRows
          D second.pair targetFaceId) :
    first.pair = second.pair := by
  have hassignments :=
    slabObservablePairedFaceSwitchable_sourceAssignments_eq_of_targetPair_eq_of_physical_eq_of_activeRows_eq
      first second htargetPair hphysical hrows
  apply Prod.ext
  · apply Subtype.ext
    exact Prod.ext hphysical.1 hassignments.1
  · apply Subtype.ext
    exact Prod.ext hphysical.2 hassignments.2

#print axioms slabObservablePairTargetSupportActiveLinks_eq_of_physical_eq
#print axioms slabObservablePair_sourceAssignmentAt_eq_of_physical_eq_of_activeRows_eq
#print axioms slabObservablePairPairedFaceSwapMask_eq_false_of_inactive
#print axioms slabObservablePairSwitchedLeftAuxiliaryAt_eq_source_of_inactive
#print axioms slabObservablePairSwitchedRightAuxiliaryAt_eq_source_of_inactive
#print axioms slabObservablePairedFaceSwitchable_sourceAssignments_eq_of_targetPair_eq_of_physical_eq_of_activeRows_eq
#print axioms slabObservablePairedFaceSwitchable_sourcePair_eq_of_targetPair_eq_of_physical_eq_of_activeRows_eq

end YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchAuxiliaryRecovery
