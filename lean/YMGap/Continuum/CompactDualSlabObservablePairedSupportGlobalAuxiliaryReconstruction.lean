/-
# Global auxiliary reconstruction from active rows and a common terminal

The global shape word identifies the complete target-rooted face component,
so it also identifies the filtered list of links incident to that component.
On those active links, equality of the paired auxiliary-row table determines
both source auxiliary labellings on every used canonical coordinate; accepted
support then extends this to literal equality of the local labellings.

On every remaining complete-slab link, canonical peeling is exactly auxiliary
local.  Equality of the terminal states therefore identifies the two source
lookups there.  The duplicate-free complete link list finally reconstructs
both source assignments.

Constructive contract: finite list recursion, accepted-support zero extension,
and the proved canonical locality theorem only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingAuxiliaryLocality
import YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalReconstruction
import YMGap.Continuum.CompactDualSlabExpandedTargetKey

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalAuxiliaryReconstruction

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingAuxiliaryLocality
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveAuxiliaryCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveLinks
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalCode
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalReconstruction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalShapeCode
open YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Shape equality identifies the active link order -/

private theorem listMap_eq_on_mem
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

/-- Equal global shape words give the same literal active-link list, not just
the same cardinality. -/
theorem slabObservablePairTargetSupportActiveLinks_eq_of_globalShapeCode_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (left right : SlabObservableTwoReplicaPair D rootFaceId)
    (hleft : left ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (hright : right ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat)
    (hshape :
      slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget left hleft massBudget =
        slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget right hright massBudget) :
    slabObservableTwoReplicaPairTargetSupportActiveLinks
        D left targetFaceId =
      slabObservableTwoReplicaPairTargetSupportActiveLinks
        D right targetFaceId := by
  have hcomponent :=
    slabObservableTwoReplicaPairTargetSupportGlobalShapeCode_eq_component_mem
      D rootFaceId targetFaceId htarget left right hleft hright
        massBudget hshape
  have hmask : slabTwoReplicaSupportSwapMask D.extent
        left.1.1.1 left.2.1.1 targetFaceId =
      slabTwoReplicaSupportSwapMask D.extent
        right.1.1.1 right.2.1.1 targetFaceId := by
    funext faceId
    unfold slabTwoReplicaSupportSwapMask
    by_cases hface : faceId ∈
        slabTwoReplicaTargetSupportComponent D.extent
          left.1.1.1 left.2.1.1 targetFaceId
    · have hrightFace := (hcomponent faceId).1 hface
      rw [decide_eq_true hface, decide_eq_true hrightFace]
    · have hrightFace : faceId ∉
          slabTwoReplicaTargetSupportComponent D.extent
            right.1.1.1 right.2.1.1 targetFaceId := by
        intro hrightMem
        exact hface ((hcomponent faceId).2 hrightMem)
      rw [decide_eq_false hface, decide_eq_false hrightFace]
  unfold slabObservableTwoReplicaPairTargetSupportActiveLinks
    slabTwoReplicaSupportLinkSwapB
  rw [hmask]

/-! ## 2. Active rows determine both local source assignments -/

/-- On an active link, equality of the aggregate paired row table determines
both complete local source auxiliary labellings. -/
theorem slabObservablePair_sourceAssignmentAt_eq_of_globalShapeCode_eq_of_activeRows_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (left right : SlabObservableTwoReplicaPair D rootFaceId)
    (hleft : left ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (hright : right ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat)
    (hshape :
      slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget left hleft massBudget =
        slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget right hright massBudget)
    (hrows :
      slabObservablePairTargetSupportActiveAuxiliaryRows
          D left targetFaceId =
        slabObservablePairTargetSupportActiveAuxiliaryRows
          D right targetFaceId)
    (link : SlabLink)
    (hlink : link ∈
      slabObservableTwoReplicaPairTargetSupportActiveLinks
        D left targetFaceId) :
    slabFusionWitnessAssignmentAt link left.1.1.2 =
        slabFusionWitnessAssignmentAt link right.1.1.2 ∧
      slabFusionWitnessAssignmentAt link left.2.1.2 =
        slabFusionWitnessAssignmentAt link right.2.1.2 := by
  have hactive :=
    slabObservablePairTargetSupportActiveLinks_eq_of_globalShapeCode_eq
      D rootFaceId targetFaceId htarget left right hleft hright
        massBudget hshape
  have hcoordinates :
      slabObservablePairTargetSupportActiveLinkCoordinates
          D left targetFaceId =
        slabObservablePairTargetSupportActiveLinkCoordinates
          D right targetFaceId := by
    unfold slabObservablePairTargetSupportActiveLinkCoordinates
    rw [hactive]
  have hrowsCommon := hrows
  unfold slabObservablePairTargetSupportActiveAuxiliaryRows at hrowsCommon
  rw [← hcoordinates] at hrowsCommon
  have hfalseMem : (link, false) ∈
      slabObservablePairTargetSupportActiveLinkCoordinates
        D left targetFaceId := by
    unfold slabObservablePairTargetSupportActiveLinkCoordinates
    apply List.mem_flatMap.mpr
    exact ⟨link, hlink, List.mem_cons_self⟩
  have htrueMem : (link, true) ∈
      slabObservablePairTargetSupportActiveLinkCoordinates
        D left targetFaceId := by
    unfold slabObservablePairTargetSupportActiveLinkCoordinates
    apply List.mem_flatMap.mpr
    exact ⟨link, hlink,
      List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)⟩
  have hleftWord := listMap_eq_on_mem
    (slabObservablePairTargetSupportActiveLinkCoordinates
      D left targetFaceId)
    (slabObservablePairActiveAuxiliaryRowAt D left)
    (slabObservablePairActiveAuxiliaryRowAt D right)
    hrowsCommon (link, false) hfalseMem
  have hrightWord := listMap_eq_on_mem
    (slabObservablePairTargetSupportActiveLinkCoordinates
      D left targetFaceId)
    (slabObservablePairActiveAuxiliaryRowAt D left)
    (slabObservablePairActiveAuxiliaryRowAt D right)
    hrowsCommon (link, true) htrueMem
  have hcomplete :=
    slabObservableTwoReplicaPairTargetSupportActiveLink_mem_complete
      D left hlink
  have hrightActive : link ∈
      slabObservableTwoReplicaPairTargetSupportActiveLinks
        D right targetFaceId := by
    rw [← hactive]
    exact hlink
  have hrightComplete :=
    slabObservableTwoReplicaPairTargetSupportActiveLink_mem_complete
      D right hrightActive
  let edges := canonicalUsedAuxiliaryCoordinates
    (slabIncidentPlaqIds D.extent link).length
  constructor
  · have hleftLocal := slabFusionWitnessAssignmentAt_mem_local
      D.cutoff D.extent left.1.1.1
      (boundaryCompleteSlabLinks D.extent) left.1.1.2
      left.1.assignment_mem link hcomplete
    have hrightLocal := slabFusionWitnessAssignmentAt_mem_local
      D.cutoff D.extent right.1.1.1
      (boundaryCompleteSlabLinks D.extent) right.1.1.2
      right.1.assignment_mem link hrightComplete
    have hleftSupport := (boundedEdgeLabellings_sound
      (linkAuxiliaryCutoff D.cutoff) edges
      (slabFusionWitnessAssignmentAt link left.1.1.2)
      (List.mem_filter.mp hleftLocal).1).2
    have hrightSupport := (boundedEdgeLabellings_sound
      (linkAuxiliaryCutoff D.cutoff) edges
      (slabFusionWitnessAssignmentAt link right.1.1.2)
      (List.mem_filter.mp hrightLocal).1).2
    apply edgeLabelling_eq_of_word_eq_of_supported edges
      (slabFusionWitnessAssignmentAt link left.1.1.2)
      (slabFusionWitnessAssignmentAt link right.1.1.2)
      hleftSupport hrightSupport
    simpa [finiteEdgeLabellingWord,
      slabObservablePairActiveAuxiliaryRowAt, edges] using hleftWord
  · have hleftAssignment : left.2.1.2 ∈
        slabFusionWitnessAssignmentsOn D.cutoff D.extent left.2.1.1
          (boundaryCompleteSlabLinks D.extent) :=
      (mem_slabExpandedFineSources_iff.mp left.2.2).2
    have hrightAssignment : right.2.1.2 ∈
        slabFusionWitnessAssignmentsOn D.cutoff D.extent right.2.1.1
          (boundaryCompleteSlabLinks D.extent) :=
      (mem_slabExpandedFineSources_iff.mp right.2.2).2
    have hleftLocal := slabFusionWitnessAssignmentAt_mem_local
      D.cutoff D.extent left.2.1.1
      (boundaryCompleteSlabLinks D.extent) left.2.1.2
      hleftAssignment link hcomplete
    have hrightLocal := slabFusionWitnessAssignmentAt_mem_local
      D.cutoff D.extent right.2.1.1
      (boundaryCompleteSlabLinks D.extent) right.2.1.2
      hrightAssignment link hrightComplete
    have hleftSupport := (boundedEdgeLabellings_sound
      (linkAuxiliaryCutoff D.cutoff) edges
      (slabFusionWitnessAssignmentAt link left.2.1.2)
      (List.mem_filter.mp hleftLocal).1).2
    have hrightSupport := (boundedEdgeLabellings_sound
      (linkAuxiliaryCutoff D.cutoff) edges
      (slabFusionWitnessAssignmentAt link right.2.1.2)
      (List.mem_filter.mp hrightLocal).1).2
    apply edgeLabelling_eq_of_word_eq_of_supported edges
      (slabFusionWitnessAssignmentAt link left.2.1.2)
      (slabFusionWitnessAssignmentAt link right.2.1.2)
      hleftSupport hrightSupport
    simpa [finiteEdgeLabellingWord,
      slabObservablePairActiveAuxiliaryRowAt, edges] using hrightWord

/-! ## 3. Common terminal plus active rows reconstruct all assignments -/

/-- Pointwise equality of all displayed local lookups reconstructs equality of
two accepted Cartesian assignments, even when their physical labels differ. -/
theorem slabFusionWitnessAssignment_eq_of_at_eq
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (left right : SlabFusionWitnessAssignment)
    (hleft : left ∈ slabFusionWitnessAssignmentsOn K extent leftPhysical
      (boundaryCompleteSlabLinks extent))
    (hright : right ∈ slabFusionWitnessAssignmentsOn K extent rightPhysical
      (boundaryCompleteSlabLinks extent))
    (hlookup : ∀ link, link ∈ boundaryCompleteSlabLinks extent →
      slabFusionWitnessAssignmentAt link left =
        slabFusionWitnessAssignmentAt link right) :
    left = right := by
  calc
    left = slabFusionWitnessAssignmentFrom
        (boundaryCompleteSlabLinks extent)
        (fun link => slabFusionWitnessAssignmentAt link left) :=
      (slabFusionWitnessAssignmentFrom_at_eq
        K extent leftPhysical (boundaryCompleteSlabLinks extent) left
        (boundaryCompleteSlabLinks_nodup extent) hleft).symm
    _ = slabFusionWitnessAssignmentFrom
        (boundaryCompleteSlabLinks extent)
        (fun link => slabFusionWitnessAssignmentAt link right) := by
      unfold slabFusionWitnessAssignmentFrom
      apply List.map_congr_left
      intro link hlink
      congr 1
      exact hlookup link hlink
    _ = right := slabFusionWitnessAssignmentFrom_at_eq
      K extent rightPhysical (boundaryCompleteSlabLinks extent) right
      (boundaryCompleteSlabLinks_nodup extent) hright

/-- Equal terminal state, shape word, and active auxiliary rows reconstruct
both complete source fusion assignments. -/
theorem slabObservablePair_sourceAssignments_eq_of_terminal_eq_of_globalShapeCode_eq_of_activeRows_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (left right : SlabObservableTwoReplicaPair D rootFaceId)
    (hleft : left ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (hright : right ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat)
    (hterminal :
      (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget left hleft).1 =
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget right hright).1)
    (hshape :
      slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget left hleft massBudget =
        slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget right hright massBudget)
    (hrows :
      slabObservablePairTargetSupportActiveAuxiliaryRows
          D left targetFaceId =
        slabObservablePairTargetSupportActiveAuxiliaryRows
          D right targetFaceId) :
    left.1.1.2 = right.1.1.2 ∧ left.2.1.2 = right.2.1.2 := by
  have hactive :=
    slabObservablePairTargetSupportActiveLinks_eq_of_globalShapeCode_eq
      D rootFaceId targetFaceId htarget left right hleft hright
        massBudget hshape
  have hlookup : ∀ link,
      link ∈ boundaryCompleteSlabLinks D.extent →
      slabFusionWitnessAssignmentAt link left.1.1.2 =
          slabFusionWitnessAssignmentAt link right.1.1.2 ∧
        slabFusionWitnessAssignmentAt link left.2.1.2 =
          slabFusionWitnessAssignmentAt link right.2.1.2 := by
    intro link hlink
    by_cases hlinkActive : link ∈
        slabObservableTwoReplicaPairTargetSupportActiveLinks
          D left targetFaceId
    · exact
        slabObservablePair_sourceAssignmentAt_eq_of_globalShapeCode_eq_of_activeRows_eq
          D rootFaceId targetFaceId htarget left right hleft hright
            massBudget hshape hrows link hlinkActive
    · have hrightInactive : link ∉
          slabObservableTwoReplicaPairTargetSupportActiveLinks
            D right targetFaceId := by
        intro hrightActive
        apply hlinkActive
        rw [hactive]
        exact hrightActive
      have hleftLocal :=
        slabObservablePairTargetSupportCanonicalPeeling_final_assignment_eq_outside_activeLinks
          D rootFaceId targetFaceId htarget left hleft
            link hlink hlinkActive
      have hrightLocal :=
        slabObservablePairTargetSupportCanonicalPeeling_final_assignment_eq_outside_activeLinks
          D rootFaceId targetFaceId htarget right hright
            link hlink hrightInactive
      have hterminalLeft := congrArg
        (fun state => slabFusionWitnessAssignmentAt link state.1.1.2)
          hterminal
      have hterminalRight := congrArg
        (fun state => slabFusionWitnessAssignmentAt link state.2.1.2)
          hterminal
      exact ⟨hleftLocal.1.symm.trans
          (hterminalLeft.trans hrightLocal.1),
        hleftLocal.2.symm.trans
          (hterminalRight.trans hrightLocal.2)⟩
  have hleftFirst := left.1.assignment_mem
  have hrightFirst := right.1.assignment_mem
  have hleftSecond : left.2.1.2 ∈
      slabFusionWitnessAssignmentsOn D.cutoff D.extent left.2.1.1
        (boundaryCompleteSlabLinks D.extent) :=
    (mem_slabExpandedFineSources_iff.mp left.2.2).2
  have hrightSecond : right.2.1.2 ∈
      slabFusionWitnessAssignmentsOn D.cutoff D.extent right.2.1.1
        (boundaryCompleteSlabLinks D.extent) :=
    (mem_slabExpandedFineSources_iff.mp right.2.2).2
  constructor
  · apply slabFusionWitnessAssignment_eq_of_at_eq
      D.cutoff D.extent left.1.1.1 right.1.1.1
      left.1.1.2 right.1.1.2 hleftFirst hrightFirst
    intro link hlink
    exact (hlookup link hlink).1
  · apply slabFusionWitnessAssignment_eq_of_at_eq
      D.cutoff D.extent left.2.1.1 right.2.1.1
      left.2.1.2 right.2.1.2 hleftSecond hrightSecond
    intro link hlink
    exact (hlookup link hlink).2

/-! ## 4. Complete source-pair reconstruction -/

/-- The terminal state and the three global information channels—shape,
physical values, and active auxiliary rows—determine the literal observable
source pair. -/
theorem slabObservablePair_eq_of_terminal_eq_of_globalShapeCode_eq_of_physicalValues_eq_of_activeRows_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (left right : SlabObservableTwoReplicaPair D rootFaceId)
    (hleft : left ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (hright : right ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat)
    (hterminal :
      (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget left hleft).1 =
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget right hright).1)
    (hshape :
      slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget left hleft massBudget =
        slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget right hright massBudget)
    (hvalues :
      slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues
          D rootFaceId targetFaceId htarget left hleft massBudget =
        slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues
          D rootFaceId targetFaceId htarget right hright massBudget)
    (hrows :
      slabObservablePairTargetSupportActiveAuxiliaryRows
          D left targetFaceId =
        slabObservablePairTargetSupportActiveAuxiliaryRows
          D right targetFaceId) :
    left = right := by
  have hphysical :=
    slabObservablePair_sourcePhysical_eq_of_terminal_eq_of_globalWords_eq
      D rootFaceId targetFaceId htarget left right hleft hright
        massBudget hterminal hshape hvalues
  have hassignments :=
    slabObservablePair_sourceAssignments_eq_of_terminal_eq_of_globalShapeCode_eq_of_activeRows_eq
      D rootFaceId targetFaceId htarget left right hleft hright
        massBudget hterminal hshape hrows
  apply Prod.ext
  · apply Subtype.ext
    exact Prod.ext hphysical.1 hassignments.1
  · apply Subtype.ext
    exact Prod.ext hphysical.2 hassignments.2

#print axioms slabObservablePairTargetSupportActiveLinks_eq_of_globalShapeCode_eq
#print axioms slabObservablePair_sourceAssignmentAt_eq_of_globalShapeCode_eq_of_activeRows_eq
#print axioms slabFusionWitnessAssignment_eq_of_at_eq
#print axioms slabObservablePair_sourceAssignments_eq_of_terminal_eq_of_globalShapeCode_eq_of_activeRows_eq
#print axioms slabObservablePair_eq_of_terminal_eq_of_globalShapeCode_eq_of_physicalValues_eq_of_activeRows_eq

end YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalAuxiliaryReconstruction
