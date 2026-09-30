/-
# A lower bound on the physical face count of the boundary-complete slab

A literal row of distinct spatial plaquettes at time zero provides one face
for every index below the slab extent. This is only a finite geometric count;
it does not bound observables or correlations.
-/

import YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
import YMGap.Continuum.CayleyPruferInjection
import YMGap.Continuum.CayleyParentInj

namespace YMGap.Continuum.BF4ExactSlabPhysicalFaceCount

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- The full boundary-complete slab has at least `extent` physical faces. -/
theorem extent_le_physicalFaces_length (extent : Nat) :
    extent ≤ (slabPhysicalFaceEdges extent).length := by
  let f : Nat → Z4Plaq := fun i => ((i, 0, 0, 0), Z4Plane.p01)
  have hn : ((List.range extent).map f).Nodup :=
    CayleyPruferInjection.nodup_map_of_injOn f _
      (CayleyParentInj.range_nodup extent)
      (fun a _ b _ h => congrArg (fun p : Z4Plaq => p.1.1) h)
  have hs : ∀ p, p ∈ (List.range extent).map f →
      p ∈ boundaryCompleteSlabPlaquettes extent := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have hi_extent : i < extent := List.mem_range.mp hi
    apply (mem_boundaryCompleteSlabPlaquettes extent (f i)).mpr
    constructor
    · rw [mem_boxPlaquettes]
      change i < extent + 1 ∧ 0 < extent + 1 ∧ 0 < extent + 1 ∧ 0 < extent + 1
      exact ⟨by omega, by omega, by omega, by omega⟩
    · change 0 ≤ extent
      omega
  have hlen := CayleyPruferInjection.nodup_subset_length_le
    ((List.range extent).map f) (boundaryCompleteSlabPlaquettes extent) hn hs
  simpa [slabPhysicalFaceEdges] using hlen

end YMGap.Continuum.BF4ExactSlabPhysicalFaceCount

#print axioms YMGap.Continuum.BF4ExactSlabPhysicalFaceCount.extent_le_physicalFaces_length
