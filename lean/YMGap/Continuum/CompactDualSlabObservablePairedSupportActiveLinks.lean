/-
# The active link carrier of the paired physical-support component

The aggregate auxiliary compiler should store source rows only at links
touching the initial target-rooted union-support component.  This module makes
that carrier literal by filtering the duplicate-free complete slab link list
with the already established component link bit.

Its load-bearing property is exact: at an active link, every incident face
which is positive in either source replica belongs to the same target
component.  Conversely, every boundary link of a component face is active.
Thus physical mass outside the component contributes zero at every active
link, which is the locality input for the global auxiliary budget.

Constructive contract: finite list filtering, Boolean component membership,
and the proved whole-link component law only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch
import YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveLinks

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-- Duplicate-free complete-slab links touching the target-rooted union
physical-support component. -/
def slabObservableTwoReplicaPairTargetSupportActiveLinks
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) : List SlabLink :=
  (boundaryCompleteSlabLinks D.extent).filter
    (slabTwoReplicaSupportLinkSwapB D.extent
      pair.1.1.1 pair.2.1.1 targetFaceId)

theorem slabObservableTwoReplicaPairTargetSupportActiveLinks_nodup
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) :
    (slabObservableTwoReplicaPairTargetSupportActiveLinks
      D pair targetFaceId).Nodup := by
  unfold slabObservableTwoReplicaPairTargetSupportActiveLinks
  exact List.filter_sublist.nodup
    (boundaryCompleteSlabLinks_nodup D.extent)

theorem slabObservableTwoReplicaPairTargetSupportActiveLink_mem_complete
    (D : SlabPhysicalData) {rootFaceId targetFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    {link : SlabLink}
    (hlink : link ∈
      slabObservableTwoReplicaPairTargetSupportActiveLinks
        D pair targetFaceId) :
    link ∈ boundaryCompleteSlabLinks D.extent := by
  exact (List.mem_filter.mp hlink).1

/-- Every positive incident face at an active link lies in the initial
target-rooted support component. -/
theorem slabObservableTwoReplicaPairTargetSupportActiveLink_positiveIncident_mem_component
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    {link : SlabLink}
    (hlink : link ∈
      slabObservableTwoReplicaPairTargetSupportActiveLinks
        D pair targetFaceId)
    {faceId : Nat}
    (hface : faceId ∈ slabIncidentPlaqIds D.extent link)
    (hpositive : 0 < pair.1.1.1 faceId ∨ 0 < pair.2.1.1 faceId) :
    faceId ∈ slabTwoReplicaTargetSupportComponent D.extent
      pair.1.1.1 pair.2.1.1 targetFaceId := by
  have hparts := List.mem_filter.mp hlink
  have heq := slabTwoReplicaSupportLinkSwapB_eq_face
    htarget
    (Or.inl
      (slabObservableTwoReplicaPairLeft_target_positive_of_mem_source
        D rootFaceId targetFaceId pair hpair))
    hparts.1 hface hpositive
  have hmask : slabTwoReplicaSupportSwapMask D.extent
      pair.1.1.1 pair.2.1.1 targetFaceId faceId = true := by
    rw [← heq]
    exact hparts.2
  exact of_decide_eq_true hmask

/-- Conversely, an incident complete-slab link of any component face belongs
to the active carrier. -/
theorem slabObservableTwoReplicaPairTargetSupportComponent_incident_mem_activeLinks
    (D : SlabPhysicalData) {rootFaceId targetFaceId faceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    {link : SlabLink}
    (hlink : link ∈ boundaryCompleteSlabLinks D.extent)
    (hface : faceId ∈ slabIncidentPlaqIds D.extent link)
    (hcomponent : faceId ∈
      slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId) :
    link ∈ slabObservableTwoReplicaPairTargetSupportActiveLinks
      D pair targetFaceId := by
  apply List.mem_filter.mpr
  refine ⟨hlink, ?_⟩
  unfold slabTwoReplicaSupportLinkSwapB
  apply List.any_eq_true.mpr
  exact ⟨faceId, hface, decide_eq_true hcomponent⟩

#print axioms slabObservableTwoReplicaPairTargetSupportActiveLinks
#print axioms slabObservableTwoReplicaPairTargetSupportActiveLinks_nodup
#print axioms slabObservableTwoReplicaPairTargetSupportActiveLink_mem_complete
#print axioms slabObservableTwoReplicaPairTargetSupportActiveLink_positiveIncident_mem_component
#print axioms slabObservableTwoReplicaPairTargetSupportComponent_incident_mem_activeLinks

end YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveLinks
