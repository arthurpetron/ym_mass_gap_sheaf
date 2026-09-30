/-
# Exact one-face joint incidence for original physical links

The literal physical face list supplies the four-link patches. Distinct
links occur together in either zero or one such patch, according to the
existing Ward-star adjacency. A diagonal link can occur in up to six.
This is geometry only; no signed patch-energy inequality is assumed.
-/

import YMGap.Continuum.BF4ExactSlabSharedFaceUniqueness
import YMGap.Continuum.BF4ExactSlabWardStarGeometry
import YMGap.Continuum.BF4ExactSlabConditionalSweep
import YMGap.Continuum.BF4ExactSlabEightLayerCone

namespace YMGap.Continuum.BF4ExactSlabFacePatchIncidence

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabSharedFaceGeometry
open YMGap.Continuum.BF4ExactSlabSharedFaceUniqueness
open YMGap.Continuum.BF4ExactSlabWardStarGeometry
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- Boolean incidence of a witnessed physical link in an original physical
face identifier. The identifier list, not this Boolean, enforces physicality. -/
def keep (extent id : Nat) (link : PhysicalLink extent) : Bool :=
  decide (link.val ∈ edgesOf (slabPlaquetteAt extent id))

/-- Literal number of original physical face patches containing both links. -/
def jointCount (extent : Nat) (i j : PhysicalLink extent) : Nat :=
  ((slabPhysicalFaceEdges extent).filter
    (fun id => keep extent id i && keep extent id j)).length

theorem jointFilter_eq_sharedIds (extent : Nat) (i j : PhysicalLink extent) :
    (slabPhysicalFaceEdges extent).filter
        (fun id => keep extent id i && keep extent id j) =
      sharedIds extent i.val j.val := by
  unfold sharedIds
  apply congrArg (fun f => (slabPhysicalFaceEdges extent).filter f)
  funext id
  by_cases hi : i.val ∈ edgesOf (slabPlaquetteAt extent id) <;>
    by_cases hj : j.val ∈ edgesOf (slabPlaquetteAt extent id) <;>
    simp [keep, hi, hj]

theorem jointCount_eq_sharedIds_length (extent : Nat) (i j : PhysicalLink extent) :
    jointCount extent i j = (sharedIds extent i.val j.val).length := by
  unfold jointCount
  rw [jointFilter_eq_sharedIds]

theorem jointCount_self (extent : Nat) (i : PhysicalLink extent) :
    jointCount extent i i = (incidentIds extent i.val).length := by
  rw [jointCount_eq_sharedIds_length]
  congr 1
  unfold sharedIds incidentIds
  apply congrArg (fun f => (slabPhysicalFaceEdges extent).filter f)
  funext id
  by_cases hi : i.val ∈ edgesOf (slabPlaquetteAt extent id) <;> simp [hi]

/-- Diagonal incidence varies near the slab boundary but is at most six. -/
theorem jointCount_self_le_six (extent : Nat) (i : PhysicalLink extent) :
    jointCount extent i i ≤ 6 := by
  rw [jointCount_self]
  exact incidentIds_length_le_six extent i.val

/-- Distinct physical links appear together in at most one actual face. -/
theorem jointCount_distinct_le_one (extent : Nat) (i j : PhysicalLink extent)
    (hne : i.val ≠ j.val) : jointCount extent i j ≤ 1 := by
  rw [jointCount_eq_sharedIds_length]
  exact sharedIds_length_le_one extent i.val j.val hne

/-- A distinct Ward-neighbor pair has exactly one original physical patch. -/
theorem jointCount_distinct_near_eq_one (extent : Nat) (i j : PhysicalLink extent)
    (hne : i.val ≠ j.val) (hnear : Near extent i.val j.val) :
    jointCount extent i j = 1 := by
  have hw := (near_iff extent i.val j.val).mp hnear
  rcases hw with heq | ⟨id, hid, hi, hj⟩
  · exact False.elim (hne heq.symm)
  · have hmem : id ∈ sharedIds extent i.val j.val :=
      (mem_sharedIds_iff extent i.val j.val id).mpr ⟨hid, hi, hj⟩
    have hpos : 0 < jointCount extent i j := by
      rw [jointCount_eq_sharedIds_length]
      exact List.length_pos_of_mem hmem
    have hle := jointCount_distinct_le_one extent i j hne
    omega

/-- A non-neighbor pair occurs in no original physical face patch. -/
theorem jointCount_nonNear_eq_zero (extent : Nat) (i j : PhysicalLink extent)
    (hnot : ¬ Near extent i.val j.val) : jointCount extent i j = 0 := by
  rw [jointCount_eq_sharedIds_length]
  cases he : sharedIds extent i.val j.val with
  | nil => rfl
  | cons id rest =>
      have hmem : id ∈ sharedIds extent i.val j.val :=
        he ▸ List.mem_cons_self
      have hi := (mem_sharedIds_iff extent i.val j.val id).mp hmem
      exact False.elim (hnot ((near_iff extent i.val j.val).mpr
        (Or.inr ⟨id, hi.1, hi.2.1, hi.2.2⟩)))

/-- The original eight-layer link schedule remains duplicate-free. -/
theorem physical_schedule_nodup (extent : Nat) : (schedule extent).Nodup :=
  schedule_nodup extent

#print axioms keep
#print axioms jointCount
#print axioms jointFilter_eq_sharedIds
#print axioms jointCount_eq_sharedIds_length
#print axioms jointCount_self
#print axioms jointCount_self_le_six
#print axioms jointCount_distinct_le_one
#print axioms jointCount_distinct_near_eq_one
#print axioms jointCount_nonNear_eq_zero
#print axioms physical_schedule_nodup

end YMGap.Continuum.BF4ExactSlabFacePatchIncidence
