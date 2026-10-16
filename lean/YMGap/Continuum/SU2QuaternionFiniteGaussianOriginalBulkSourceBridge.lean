/-
# Original spatial-face geometry for the rational bulk source

The explicit rational bulk face list is a literal subfamily of the canonical
original spatial-face carrier at width `s^2`.  This leaf proves that support
identity without importing the generated vacuum-reflection compiler cone.

This identifies finite source geometry only.  The original Wilson-expression
compiler, source-polynomial pin, FREE/ORIGINAL law comparison, continuum
theory and physical/Clay mass gap remain separate.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
import YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkSourceBridge

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource

/-- Every formula-level bulk face is literally one of the canonical original
spatial faces at width `s^2`. -/
theorem bulkSourceFace_mem_spatialFaces_square
    {s : Nat} {face : Z4Plaq}
    (hface : face ∈ bulkSourceFaces s) :
    face ∈ spatialFaces (s * s) := by
  have hraw := hface
  unfold bulkSourceFaces at hraw
  obtain ⟨rx, hrx, hraw⟩ := List.mem_flatMap.mp hraw
  obtain ⟨ry, hry, hraw⟩ := List.mem_flatMap.mp hraw
  obtain ⟨rz, hrz, hraw⟩ := List.mem_flatMap.mp hraw
  obtain ⟨plane, hplane, rfl⟩ := List.mem_map.mp hraw
  have hrxlt := List.mem_range.mp hrx
  have hrylt := List.mem_range.mp hry
  have hrzlt := List.mem_range.mp hrz
  have hs : 0 < s := Nat.zero_lt_of_lt hrxlt
  have hlimit := bulkSourceOffset_add_side_le_square s hs
  apply (spatialFaces_mem_iff (s * s) _).mpr
  change
    bulkSourceOffset s + rx < s * s ∧
      bulkSourceOffset s + ry < s * s ∧
      bulkSourceOffset s + rz < s * s ∧
      0 = 0 ∧
      (dirsOf plane).2 ≠ Dir4.x3
  refine ⟨
    Nat.lt_of_lt_of_le
      (Nat.add_lt_add_left hrxlt (bulkSourceOffset s)) hlimit,
    Nat.lt_of_lt_of_le
      (Nat.add_lt_add_left hrylt (bulkSourceOffset s)) hlimit,
    Nat.lt_of_lt_of_le
      (Nat.add_lt_add_left hrzlt (bulkSourceOffset s)) hlimit,
    rfl, ?_⟩
  simp only [bulkSourcePlanes, List.mem_cons, List.not_mem_nil,
    or_false] at hplane
  rcases hplane with rfl | rfl | rfl <;> decide

theorem bulkSourceFaces_spatial
    (s : Nat) :
    ∀ face, face ∈ bulkSourceFaces s →
      face ∈ spatialFaces (s * s) := by
  intro face hface
  exact bulkSourceFace_mem_spatialFaces_square hface

#print axioms bulkSourceFace_mem_spatialFaces_square
#print axioms bulkSourceFaces_spatial

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkSourceBridge
