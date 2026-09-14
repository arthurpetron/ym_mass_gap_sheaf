/-
# Accepted original minimal mixed moments have exactly the literal tube

Original physical labels at most one, temporal-window support, and the
original mixed-moment center checker force positive support to be exactly
the existing twelve tube sides. The list permutation and physical-label
pin retain the carrier needed for the subsequent Haar evaluation.
No value, sign, or enumeration multiplicity is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabTubeSupportGeometry
import YMGap.Continuum.BF4ExactSlabMinimalMomentContinuation

namespace YMGap.Continuum.BF4ExactSlabMinimalMixedTube

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4ThreeCutSaturation
open YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabMinimalMomentContinuation
open YMGap.Continuum.BF4ExactSlabTubeSupportGeometry
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization

theorem accepted_face_count (margin : Nat) (lo hi : Bool) (state : EdgeLabelling)
    (hs : ∀ id, id ∈ slabPhysicalFaceEdges (responseExtent margin) → state id ≤ 1)
    (hw : ∀ f, f ∈ positiveFaces (responseExtent margin) state → window margin f = true)
    (hc : momentCheck margin lo hi state = true) (face : Z4Plaq)
    (hf : window margin face = true) :
    cutCount face.1.2.2.2 (cutEdge face) (positiveFaces (responseExtent margin) state) =
      endpointBit margin lo (cutEdge face) := by
  have hd : (cutEdge face).2 ≠ Dir4.x3 := by
    rcases face with ⟨v,p⟩
    cases p <;> simp [cutEdge,dirsOf]
  have hh := moment_cut_pin margin lo hi state hs hw hc (cutEdge face) hd
  rcases window_times hf with h | h | h
  · rw [h]; exact hh.1
  · rw [h]; exact hh.2.1
  · rw [h]; exact hh.2.2.1

theorem accepted_mixed_mem (margin : Nat) (state : EdgeLabelling)
    (hs : ∀ id, id ∈ slabPhysicalFaceEdges (responseExtent margin) → state id ≤ 1)
    (hw : ∀ f, f ∈ positiveFaces (responseExtent margin) state → window margin f = true)
    (hc : momentCheck margin true true state = true) (face : Z4Plaq) :
    face ∈ positiveFaces (responseExtent margin) state ↔ face ∈ tubeSides margin := by
  constructor
  · intro hf
    have ht := hw face hf
    have hone := (temporal_face_mem_iff_count _ (positiveFaces_nodup _ _) face
      (window_temporal ht)).mp hf
    rw [accepted_face_count margin true true state hs hw hc face ht] at hone
    have hb : atTime margin (cutEdge face) ∈ edgesOf (sliceFace margin 0) := by
      by_cases h : atTime margin (cutEdge face) ∈ edgesOf (sliceFace margin 0)
      · exact h
      · simp [endpointBit,h] at hone
    exact (tube_mem_iff margin face).mpr ⟨ht,hb⟩
  · intro hf
    have ht := tube_window margin face hf
    apply (temporal_face_mem_iff_count _ (positiveFaces_nodup _ _) face (window_temporal ht)).mpr
    rw [accepted_face_count margin true true state hs hw hc face ht]
    simp [endpointBit,tube_boundary margin face hf]

theorem accepted_mixed_support_perm (margin : Nat) (state : EdgeLabelling)
    (hs : ∀ id, id ∈ slabPhysicalFaceEdges (responseExtent margin) → state id ≤ 1)
    (hw : ∀ f, f ∈ positiveFaces (responseExtent margin) state → window margin f = true)
    (hc : momentCheck margin true true state = true) :
    (positiveFaces (responseExtent margin) state).Perm (tubeSides margin) :=
  Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff _ _
    (positiveFaces_nodup _ _) (tubeSides_nodup margin) (accepted_mixed_mem margin state hs hw hc)

theorem accepted_mixed_face_label (margin : Nat) (state : EdgeLabelling)
    (hs : ∀ id, id ∈ slabPhysicalFaceEdges (responseExtent margin) → state id ≤ 1)
    (hw : ∀ f, f ∈ positiveFaces (responseExtent margin) state → window margin f = true)
    (hc : momentCheck margin true true state = true) (face : Z4Plaq)
    (hf : face ∈ boundaryCompleteSlabPlaquettes (responseExtent margin)) :
    state ((boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf face) =
      if face ∈ tubeSides margin then 1 else 0 := by
  have hb := hs _ (List.mem_range.mpr (List.idxOf_lt_length_of_mem hf))
  have hm := accepted_mixed_mem margin state hs hw hc face
  by_cases ht : face ∈ tubeSides margin
  · have hp := of_decide_eq_true (List.mem_filter.mp (hm.mpr ht)).2
    rw [if_pos ht]
    omega
  · have hz : state ((boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf face) = 0 := by
      by_cases hzero : state ((boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf face) = 0
      · exact hzero
      · exact False.elim (ht (hm.mp (List.mem_filter.mpr ⟨hf,decide_eq_true (by omega)⟩)))
    rw [if_neg ht,hz]

/-- A concrete original index labelling; all nonphysical indices are zero. -/
def tubeLabelling (margin : Nat) : EdgeLabelling := fun id =>
  if id ∈ slabPhysicalFaceEdges (responseExtent margin) ∧
      slabPlaquetteAt (responseExtent margin) id ∈ tubeSides margin then 1 else 0

theorem accepted_mixed_label_pin (margin : Nat) (state : EdgeLabelling)
    (hs : ∀ id, id ∈ slabPhysicalFaceEdges (responseExtent margin) → state id ≤ 1)
    (hw : ∀ f, f ∈ positiveFaces (responseExtent margin) state → window margin f = true)
    (hc : momentCheck margin true true state = true) (id : Nat)
    (hi : id ∈ slabPhysicalFaceEdges (responseExtent margin)) : state id = tubeLabelling margin id := by
  have h := accepted_mixed_face_label margin state hs hw hc _ (slabPlaquetteAt_mem hi)
  rw [idxOf_slabPlaquetteAt hi] at h
  simpa only [tubeLabelling, hi, true_and] using h

end YMGap.Continuum.BF4ExactSlabMinimalMixedTube

#print axioms YMGap.Continuum.BF4ExactSlabMinimalMixedTube.accepted_face_count
#print axioms YMGap.Continuum.BF4ExactSlabMinimalMixedTube.accepted_mixed_mem
#print axioms YMGap.Continuum.BF4ExactSlabMinimalMixedTube.accepted_mixed_support_perm
#print axioms YMGap.Continuum.BF4ExactSlabMinimalMixedTube.accepted_mixed_face_label
#print axioms YMGap.Continuum.BF4ExactSlabMinimalMixedTube.tubeLabelling
#print axioms YMGap.Continuum.BF4ExactSlabMinimalMixedTube.accepted_mixed_label_pin
