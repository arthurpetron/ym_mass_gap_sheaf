/-
# The physical eight-layer schedule is a permutation of slab Haar blocks

Every physical link occurs exactly once in the colored schedule. Its original
`idxOf` coordinate therefore occurs exactly once, and every block coordinate
is reached. No reordered action or replacement carrier is introduced here.
-/

import YMGap.Continuum.BF4ExactSlabEightLayerCone
import YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
import YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
import YMGap.Continuum.Z4CanonicalPolymerUniverse
import YMGap.Continuum.CayleyParentInj

namespace YMGap.Continuum.BF4ExactSlabPhysicalScheduleIndex

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabTemporalGaugeLedger
open YMGap.Continuum.Z4CanonicalPolymerUniverse

/-- The original block indices of the literal colored physical schedule. -/
def physicalScheduleIndex (extent : Nat) : List Nat :=
  (schedule extent).map
    (fun i => (boundaryCompleteSlabLinks extent).idxOf i.val)

theorem physical_schedule_index_nodup (extent : Nat) :
    (physicalScheduleIndex extent).Nodup := by
  unfold physicalScheduleIndex
  apply nodup_map_of_injOn _ _ (schedule_nodup extent)
  intro i _ j _ heq
  exact Subtype.ext (idxOf_injective_on_members i.property j.property heq)

theorem physical_schedule_index_covers (extent block : Nat)
    (hblock : block ∈ List.range (boundaryCompleteSlabLinks extent).length) :
    block ∈ physicalScheduleIndex extent := by
  let link := correctedSlabLinkAt extent block
  have hp : block ∈ correctedSlabLinkBlocks extent := hblock
  have hl : link ∈ boundaryCompleteSlabLinks extent := correctedSlabLinkAt_mem hp
  let i : PhysicalLink extent := ⟨link, hl⟩
  have hidx : block = (boundaryCompleteSlabLinks extent).idxOf link := by
    apply correctedSlabLinkAt_injective_on_physical hp
      (List.mem_range.mpr (List.idxOf_lt_length_of_mem hl))
    exact (correctedSlabLinkAt_idxOf hl).symm
  unfold physicalScheduleIndex
  apply List.mem_map.mpr
  exact ⟨i, schedule_covers extent i, hidx.symm⟩

/-- The eight-layer schedule lists precisely the original slab Haar blocks,
once each, though in color order rather than carrier order. -/
theorem physical_schedule_index_perm (extent : Nat) :
    ((schedule extent).map
      (fun i => (boundaryCompleteSlabLinks extent).idxOf i.val)).Perm
      (List.range (boundaryCompleteSlabLinks extent).length) := by
  change (physicalScheduleIndex extent).Perm
    (List.range (boundaryCompleteSlabLinks extent).length)
  apply perm_of_nodup_mem_iff _ _
    (physical_schedule_index_nodup extent)
    (CayleyParentInj.range_nodup _)
  intro block
  constructor
  · intro hb
    unfold physicalScheduleIndex at hb
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
    exact List.mem_range.mpr (List.idxOf_lt_length_of_mem i.property)
  · exact physical_schedule_index_covers extent block

#print axioms physicalScheduleIndex
#print axioms physical_schedule_index_nodup
#print axioms physical_schedule_index_covers
#print axioms physical_schedule_index_perm

end YMGap.Continuum.BF4ExactSlabPhysicalScheduleIndex
