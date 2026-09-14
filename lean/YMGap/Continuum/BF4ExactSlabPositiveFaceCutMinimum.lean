/-
# Leaf rejection controls the ORIGINAL full positive-spin face support

The singleton check is pinned to geometric face incidence. Each nonempty
temporal cut of a retained original replica has at least four faces,
regardless of spin parity. The three-cut pair bound explicitly requires
coverage at each cut; this module does not assume it from connectedness.
-/

import YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
import YMGap.Continuum.Z4LeaflessTemporalCutMinimum

namespace YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4TemporalCutParityMinimum (cut)
open YMGap.Continuum.BF4ExactSlabSingletonOccupiedLink
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter

def positiveFaces (extent : Nat) (state : EdgeLabelling) : List Z4Plaq :=
  (boundaryCompleteSlabPlaquettes extent).filter
    (fun f => decide (0 < state ((boundaryCompleteSlabPlaquettes extent).idxOf f)))

theorem positiveFaces_nodup (extent : Nat) (state : EdgeLabelling) : (positiveFaces extent state).Nodup :=
  (boundaryCompleteSlabPlaquettes_nodup extent).filter _

theorem positiveFaces_physical {extent : Nat} {state : EdgeLabelling} {face : Z4Plaq}
    (hf : face ∈ positiveFaces extent state) : face ∈ boundaryCompleteSlabPlaquettes extent :=
  (List.mem_filter.mp hf).1

private theorem filtered_incidence (extent : Nat) (state : EdgeLabelling) (link : Z4Link) :
    ∀ faces : List Z4Plaq,
    (faces.filter (fun f => decide (link ∈ edgesOf f ∧
      0 < state ((boundaryCompleteSlabPlaquettes extent).idxOf f)))).length =
    faceIncidenceCount link (faces.filter
      (fun f => decide (0 < state ((boundaryCompleteSlabPlaquettes extent).idxOf f))))
  | [] => rfl
  | f::fs => by
    have ih := filtered_incidence extent state link fs
    by_cases hs : 0 < state ((boundaryCompleteSlabPlaquettes extent).idxOf f)
    all_goals by_cases he : link ∈ edgesOf f
    all_goals simp only [List.filter_cons, hs, he, and_self, and_false, and_true,
      decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
      faceIncidenceCount, List.length_cons, Nat.zero_add, ih]
    all_goals omega

theorem incidentOccupied_length (extent : Nat) (state : EdgeLabelling) (link : Z4Link) :
    (incidentOccupied extent state link).length = faceIncidenceCount link (positiveFaces extent state) :=
  filtered_incidence extent state link _

theorem retained_vertical_no_leaf {margin : Nat} {state : EdgeLabelling}
    (h : leafKeep margin state = true) (v : Z4Vertex) :
    faceIncidenceCount (v,Dir4.x3) (positiveFaces (responseExtent margin) state) ≠ 1 := by
  by_cases hl : (v,Dir4.x3) ∈ boundaryCompleteSlabLinks (responseExtent margin)
  · rw [← incidentOccupied_length]
    exact retained_link_not_singleton h v hl
  · rw [incidence_outside _ _ hl _ (fun _ hf => positiveFaces_physical hf)]
    exact Nat.zero_ne_one

theorem retained_cut_minimum_four {margin : Nat} {state : EdgeLabelling}
    (h : leafKeep margin state = true) (time : Nat)
    (hne : cut time (positiveFaces (responseExtent margin) state) ≠ []) :
    4 ≤ (cut time (positiveFaces (responseExtent margin) state)).length :=
  Z4LeaflessTemporalCutMinimum.cut_minimum_four time _ (positiveFaces_nodup _ _)
    (retained_vertical_no_leaf h) hne

theorem retained_pair_three_cut_minimum_twelve {margin : Nat} {left right : EdgeLabelling}
    (h : pairLeafKeep margin (left,right) = true) (time : Nat)
    (h0 : cut time (positiveFaces (responseExtent margin) left) ≠ [] ∨
      cut time (positiveFaces (responseExtent margin) right) ≠ [])
    (h1 : cut (time+1) (positiveFaces (responseExtent margin) left) ≠ [] ∨
      cut (time+1) (positiveFaces (responseExtent margin) right) ≠ [])
    (h2 : cut (time+2) (positiveFaces (responseExtent margin) left) ≠ [] ∨
      cut (time+2) (positiveFaces (responseExtent margin) right) ≠ []) :
    12 ≤ (positiveFaces (responseExtent margin) left).length +
      (positiveFaces (responseExtent margin) right).length :=
  Z4LeaflessTemporalCutMinimum.pair_three_cut_minimum_twelve time _ _
    (positiveFaces_nodup _ _) (positiveFaces_nodup _ _)
    (retained_vertical_no_leaf (Bool.and_eq_true_iff.mp h).1)
    (retained_vertical_no_leaf (Bool.and_eq_true_iff.mp h).2) h0 h1 h2

end YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum

#print axioms YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum.positiveFaces
#print axioms YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum.positiveFaces_nodup
#print axioms YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum.positiveFaces_physical
#print axioms YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum.incidentOccupied_length
#print axioms YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum.retained_vertical_no_leaf
#print axioms YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum.retained_cut_minimum_four
#print axioms YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum.retained_pair_three_cut_minimum_twelve
