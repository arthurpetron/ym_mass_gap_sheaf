/-
# Literal tube membership is the temporal window and endpoint boundary

The existing twelve tube sides are exactly the temporal faces based in
the three intervening layers whose lower spatial edge, retimed to the
actual lower probe, belongs to its boundary. This characterizes the SAME
literal tube list without assuming a path or evaluating a Haar moment.
-/

import YMGap.Continuum.BF4ExactSlabMinimalMomentParity

namespace YMGap.Continuum.BF4ExactSlabTubeSupportGeometry

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4ThreeCutSaturation
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry
open YMGap.Continuum.Z4UnitCubeIncidenceParity

theorem layer_mem_iff (margin time : Nat) (face : Z4Plaq) :
    face ∈ (baseLayer time).map (shiftFace margin margin) ↔
      crosses (margin+time) face = true ∧
        atTime margin (cutEdge face) ∈ edgesOf (sliceFace margin 0) := by
  rcases face with ⟨⟨a,b,c,t⟩,p⟩
  cases p <;> simp [baseLayer, shiftFace, shiftVertex, sliceFace, edgesOf,
    atTime, cutEdge, crosses, dirsOf, addE, Nat.add_comm, Nat.add_left_comm]
  all_goals simp only [and_or_left, and_assoc, and_comm, and_left_comm, or_comm]

theorem tube_mem_iff (margin : Nat) (face : Z4Plaq) :
    face ∈ tubeSides margin ↔ window margin face = true ∧
      atTime margin (cutEdge face) ∈ edgesOf (sliceFace margin 0) := by
  simp only [tubeSides, baseSides, List.map_append, List.mem_append,
    layer_mem_iff, Nat.add_zero, window, Bool.or_eq_true_iff, or_and_right]

theorem tube_window (margin : Nat) (face : Z4Plaq) (hf : face ∈ tubeSides margin) :
    window margin face = true := (tube_mem_iff margin face).mp hf |>.1

theorem tube_boundary (margin : Nat) (face : Z4Plaq) (hf : face ∈ tubeSides margin) :
    atTime margin (cutEdge face) ∈ edgesOf (sliceFace margin 0) :=
  (tube_mem_iff margin face).mp hf |>.2

theorem temporal_face_mem_iff_count (faces : List Z4Plaq) (hn : faces.Nodup)
    (face : Z4Plaq) (ht : (dirsOf face.2).2 = Dir4.x3) :
    face ∈ faces ↔ cutCount face.1.2.2.2 (cutEdge face) faces = 1 := by
  have hx : crosses face.1.2.2.2 face = true := decide_eq_true ⟨ht,rfl⟩
  have he : atTime face.1.2.2.2 (cutEdge face) = cutEdge face := rfl
  rw [cutCount,he]
  constructor
  · intro hf
    exact occurrenceCount_eq_one_of_mem_nodup _ _ (cut_nodup _ _ hn)
      (List.mem_map.mpr ⟨face,List.mem_filter.mpr ⟨hf,hx⟩,rfl⟩)
  · intro hc
    by_cases hf : face ∈ faces
    · exact hf
    · have hm : cutEdge face ∉ cut face.1.2.2.2 faces := by
        intro h
        obtain ⟨g,hg,heq⟩ := List.mem_map.mp h
        have hg' := List.mem_filter.mp hg
        have hgf := cutEdge_injective hg'.2 hx heq
        exact hf (hgf ▸ hg'.1)
      rw [occurrenceCount_eq_zero_of_not_mem _ _ hm] at hc
      cases hc

end YMGap.Continuum.BF4ExactSlabTubeSupportGeometry

#print axioms YMGap.Continuum.BF4ExactSlabTubeSupportGeometry.layer_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabTubeSupportGeometry.tube_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabTubeSupportGeometry.tube_window
#print axioms YMGap.Continuum.BF4ExactSlabTubeSupportGeometry.tube_boundary
#print axioms YMGap.Continuum.BF4ExactSlabTubeSupportGeometry.temporal_face_mem_iff_count
