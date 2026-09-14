/-
# Exact cut comparison with projected plaquette boundaries

For a distinct finite face list, the cut indicator is its occurrence count.
When that indicator is the mod-two sum of two projected plaquette boundary
indicators, the actual cut list is a permutation of their symmetric
difference. This preserves the cardinality used by the saturated budget.
-/

import YMGap.Continuum.Z4TwoSpatialFaceContinuation

namespace YMGap.Continuum.Z4ProjectedBoundaryCutComparison

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4PlaquetteBoundaryRigidity
open YMGap.Continuum.Z4SpatialPlaquetteProjection
open YMGap.Continuum.Z4TwoSpatialFaceContinuation

theorem cut_link_guards (time : Nat) (faces : List Z4Plaq) (link : Z4Link)
    (hm : link ∈ cut time faces) : link.1.2.2.2=time ∧ link.2 ≠ Dir4.x3 := by
  obtain ⟨face,hf,he⟩ := List.mem_map.mp hm
  have hx := of_decide_eq_true (List.mem_filter.mp hf).2
  rw [← he]
  constructor
  · exact hx.2
  · rcases face with ⟨v,p⟩
    cases p <;> dsimp only [cutEdge,dirsOf] <;> decide

theorem cutCount_one_iff (time : Nat) (faces : List Z4Plaq) (hn : faces.Nodup) (link : Z4Link) :
    atTime time link ∈ cut time faces ↔ cutCount time link faces=1 := by
  constructor
  · exact occurrenceCount_eq_one_of_mem_nodup _ _ (cut_nodup time faces hn)
  · intro h
    by_cases hm : atTime time link ∈ cut time faces
    · exact hm
    · rw [cutCount,occurrenceCount_eq_zero_of_not_mem _ _ hm] at h
      contradiction

theorem symmetricBoundary_projected_bit (time : Nat) (left right : Z4Plaq)
    (hl : (dirsOf left.2).2 ≠ Dir4.x3) (hr : (dirsOf right.2).2 ≠ Dir4.x3) (link : Z4Link) :
    atTime time link ∈ symmetricBoundary (faceAt time left) (faceAt time right) ↔
      (projectedBit left link+projectedBit right link)%2=1 := by
  have hleft := retimed_spatial_boundary_mem time left hl link
  have hright := retimed_spatial_boundary_mem time right hr link
  simp only [symmetricBoundary,List.mem_append,List.mem_filter,decide_eq_true_eq,hleft,hright]
  by_cases ha : atTime left.1.2.2.2 link ∈ edgesOf left <;>
    by_cases hb : atTime right.1.2.2.2 link ∈ edgesOf right
  all_goals simp only [projectedBit,ha,hb,↓reduceIte,not_true_eq_false,not_false_eq_true,
    and_true,and_false,true_or,false_or]
  all_goals decide

theorem symmetricBoundary_link_guards (time : Nat) (left right : Z4Plaq)
    (hl : (dirsOf left.2).2 ≠ Dir4.x3) (hr : (dirsOf right.2).2 ≠ Dir4.x3)
    (link : Z4Link) (hm : link ∈ symmetricBoundary (faceAt time left) (faceAt time right)) :
    link.1.2.2.2=time ∧ link.2 ≠ Dir4.x3 := by
  rcases List.mem_append.mp hm with h | h
  · have hf := (List.mem_filter.mp h).1
    exact ⟨Z4FiniteTemporalSpatialSources.spatial_boundary_time (faceAt time left) hl link hf,
      spatial_boundary_dir (faceAt time left) hl link hf⟩
  · have hf := (List.mem_filter.mp h).1
    exact ⟨Z4FiniteTemporalSpatialSources.spatial_boundary_time (faceAt time right) hr link hf,
      spatial_boundary_dir (faceAt time right) hr link hf⟩

theorem cut_symmetricBoundary_perm (time : Nat) (faces : List Z4Plaq) (hn : faces.Nodup)
    (left right : Z4Plaq) (hl : (dirsOf left.2).2 ≠ Dir4.x3) (hr : (dirsOf right.2).2 ≠ Dir4.x3)
    (hc : ∀ link : Z4Link, link.2 ≠ Dir4.x3 →
      cutCount time link faces=(projectedBit left link+projectedBit right link)%2) :
    (cut time faces).Perm (symmetricBoundary (faceAt time left) (faceAt time right)) := by
  apply Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff _ _ (cut_nodup time faces hn)
    (symmetricBoundary_nodup _ _)
  intro link
  constructor
  · intro hm
    have hg := cut_link_guards time faces link hm
    have he : atTime time link=link := by rw [← hg.1]; rfl
    have hone := (cutCount_one_iff time faces hn link).mp (he ▸ hm)
    rw [hc link hg.2] at hone
    exact he ▸ (symmetricBoundary_projected_bit time left right hl hr link).mpr hone
  · intro hm
    have hg := symmetricBoundary_link_guards time left right hl hr link hm
    have he : atTime time link=link := by rw [← hg.1]; rfl
    have hone := (symmetricBoundary_projected_bit time left right hl hr link).mp (he ▸ hm)
    rw [← hc link hg.2] at hone
    exact he ▸ (cutCount_one_iff time faces hn link).mpr hone

end YMGap.Continuum.Z4ProjectedBoundaryCutComparison

#print axioms YMGap.Continuum.Z4ProjectedBoundaryCutComparison.cut_link_guards
#print axioms YMGap.Continuum.Z4ProjectedBoundaryCutComparison.cutCount_one_iff
#print axioms YMGap.Continuum.Z4ProjectedBoundaryCutComparison.symmetricBoundary_projected_bit
#print axioms YMGap.Continuum.Z4ProjectedBoundaryCutComparison.symmetricBoundary_link_guards
#print axioms YMGap.Continuum.Z4ProjectedBoundaryCutComparison.cut_symmetricBoundary_perm
