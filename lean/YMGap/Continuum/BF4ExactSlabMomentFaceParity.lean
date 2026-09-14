/-
# Original moment charges fix total and spatial odd-face parity

Append the actual endpoint probe faces to the original odd-face list.
The existing all-spin moment checker makes its link incidences even.
The explicit finite coordinate cochains then prove that both its total
face count and spatial face count are even. Equivalently, both original
counts have the parity of the number of inserted endpoint probes.
No spin, time-window, connectedness or positivity assumption is added.
-/

import YMGap.Continuum.Z4WeightedIncidenceParity
import YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction

namespace YMGap.Continuum.BF4ExactSlabMomentFaceParity

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4SpatialDefectTemporalDecoder
open YMGap.Continuum.Z4WeightedIncidenceParity
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabMinimalMomentParity
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction

def chargedFaces (margin : Nat) (lo hi : Bool) (state : EdgeLabelling) : List Z4Plaq :=
  (if lo then [sliceFace margin 0] else []) ++
    (if hi then [sliceFace margin 3] else []) ++ oddFaces (responseExtent margin) state

theorem chargedFaces_physical (margin : Nat) (lo hi : Bool) (state : EdgeLabelling)
    (face : Z4Plaq) (hf : face ∈ chargedFaces margin lo hi state) :
    face ∈ boundaryCompleteSlabPlaquettes (responseExtent margin) := by
  have h0 := slice_physical margin ⟨0,by decide⟩
  have h3 := slice_physical margin ⟨3,by decide⟩
  cases lo <;> cases hi <;>
    simp only [chargedFaces, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.cons_append, List.mem_cons] at hf
  · exact oddFaces_physical hf
  · rcases hf with rfl | hf
    · exact h3
    · exact oddFaces_physical hf
  · rcases hf with rfl | hf
    · exact h0
    · exact oddFaces_physical hf
  · rcases hf with rfl | rfl | hf
    · exact h0
    · exact h3
    · exact oddFaces_physical hf

theorem chargedFaces_incidence (margin : Nat) (lo hi : Bool) (state : EdgeLabelling) (link : Z4Link) :
    faceIncidenceCount link (chargedFaces margin lo hi state) = endpointCharge margin lo hi link +
      faceIncidenceCount link (oddFaces (responseExtent margin) state) := by
  cases lo <;> cases hi <;>
    simp only [chargedFaces, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.cons_append,
      faceIncidenceCount, endpointCharge, Nat.zero_add, Nat.add_zero, Nat.add_assoc]

theorem chargedFaces_length (margin : Nat) (lo hi : Bool) (state : EdgeLabelling) :
    (chargedFaces margin lo hi state).length = (if lo then 1 else 0)+(if hi then 1 else 0)+
      (oddFaces (responseExtent margin) state).length := by
  cases lo <;> cases hi <;>
    simp only [chargedFaces, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_cons, List.length_nil] <;> omega

theorem chargedFaces_spatial (margin : Nat) (lo hi : Bool) (state : EdgeLabelling) :
    spatialFaces (chargedFaces margin lo hi state) =
      (if lo then [sliceFace margin 0] else []) ++
        (if hi then [sliceFace margin 3] else []) ++ spatialOddFaces margin state := by
  cases lo <;> cases hi <;> rfl

theorem chargedFaces_spatial_length (margin : Nat) (lo hi : Bool) (state : EdgeLabelling) :
    (spatialFaces (chargedFaces margin lo hi state)).length = (if lo then 1 else 0)+(if hi then 1 else 0)+
      (spatialOddFaces margin state).length := by
  rw [chargedFaces_spatial]
  cases lo <;> cases hi <;>
    simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_cons, List.length_nil] <;> omega

/-- Both counts are pinned to the ORIGINAL endpoint flags, at every spin. -/
theorem moment_face_parities (margin : Nat) (lo hi : Bool) (state : EdgeLabelling)
    (hc : momentCheck margin lo hi state = true) :
    (oddFaces (responseExtent margin) state).length%2 = ((if lo then 1 else 0)+(if hi then 1 else 0))%2 ∧
      (spatialOddFaces margin state).length%2 = ((if lo then 1 else 0)+(if hi then 1 else 0))%2 := by
  have h := closed_face_counts_even (boundaryCompleteSlabLinks (responseExtent margin))
    (boundaryCompleteSlabLinks_nodup _) (chargedFaces margin lo hi state)
    (fun face hf link hl => (mem_boundaryCompleteSlabLinks_iff _ _).mpr
      ⟨face,chargedFaces_physical margin lo hi state face hf,hl⟩)
    (fun link _ => by rw [chargedFaces_incidence]; exact moment_odd_geometry_parity margin lo hi state hc link)
  rw [chargedFaces_length, chargedFaces_spatial_length] at h
  constructor <;> omega

end YMGap.Continuum.BF4ExactSlabMomentFaceParity

#print axioms YMGap.Continuum.BF4ExactSlabMomentFaceParity.chargedFaces
#print axioms YMGap.Continuum.BF4ExactSlabMomentFaceParity.chargedFaces_physical
#print axioms YMGap.Continuum.BF4ExactSlabMomentFaceParity.chargedFaces_incidence
#print axioms YMGap.Continuum.BF4ExactSlabMomentFaceParity.chargedFaces_length
#print axioms YMGap.Continuum.BF4ExactSlabMomentFaceParity.chargedFaces_spatial
#print axioms YMGap.Continuum.BF4ExactSlabMomentFaceParity.chargedFaces_spatial_length
#print axioms YMGap.Continuum.BF4ExactSlabMomentFaceParity.moment_face_parities
