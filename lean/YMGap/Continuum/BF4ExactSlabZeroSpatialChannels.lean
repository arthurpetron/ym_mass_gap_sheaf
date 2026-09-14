/-
# Original all-spin channels with no spatial odd faces

Finite temporal charge conservation rejects either one-endpoint channel.
An accepted mixed channel has exactly the canonical tube's physical
parities; an accepted partition channel has even physical labels. These
are statements about the original momentCheck and original Haar moments,
without a fundamental-spin or three-layer-window hypothesis. Even labels
are not declared absent, and no sign or aggregate remainder bound is inferred.
-/

import YMGap.Continuum.Z4FiniteTemporalEndpointParity
import YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
import YMGap.Continuum.BF4ExactSlabCanonicalTubeMoments

namespace YMGap.Continuum.BF4ExactSlabZeroSpatialChannels

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4ThreeCutSaturation
open YMGap.Continuum.Z4SpatialDefectTemporalDecoder
open YMGap.Continuum.Z4FiniteTemporalEndpointParity
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabConnectedTemporalCrossing
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabMinimalMomentParity
open YMGap.Continuum.BF4ExactSlabMinimalPowerWindow
open YMGap.Continuum.BF4ExactSlabMinimalMixedTube
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport
open YMGap.Continuum.BF4ExactSlabCanonicalTubeMoments

local infix:50 " ≈ " => Q'.eqv

theorem retimed_endpoint_mem_any (margin time target : Nat) (link : Z4Link) :
    atTime time link ∈ edgesOf (sliceFace margin target) ↔
      time = margin+target ∧ atTime margin link ∈ edgesOf (sliceFace margin 0) := by
  constructor
  · intro h
    have ht := endpoint_link_time margin target (atTime time link) h
    have hm := List.mem_map.mpr ⟨atTime time link,h,atTime_twice margin time link⟩
    have hr := retime_slice_edges margin target 0
    rw [Nat.add_zero] at hr
    exact ⟨ht,hr ▸ hm⟩
  · rintro ⟨he,h⟩
    subst time
    rw [← retime_slice_edges margin 0 target]
    exact List.mem_map.mpr ⟨atTime margin link,h,atTime_twice (margin+target) margin link⟩

theorem accepted_flags_equal (margin : Nat) (lo hi : Bool) (state : EdgeLabelling)
    (hs : spatialOddFaces margin state = [])
    (hc : momentCheck margin lo hi state = true) : lo = hi := by
  let link : Z4Link := ((1+margin,1+margin,1+margin,0),.x0)
  have hm : atTime margin link ∈ edgesOf (sliceFace margin 0) := by
    simp [atTime,link,sliceFace,edgesOf,dirsOf]
  have hcharge (time : Nat) : endpointCharge margin lo hi (atTime time link) =
      twoImpulses margin (margin+3) (if lo then 1 else 0) (if hi then 1 else 0) time := by
    cases lo <;> cases hi <;>
      simp [endpointCharge, retimed_endpoint_mem_any, hm, twoImpulses]
  have he := endpoint_sum_even margin (margin+3) (if lo then 1 else 0) (if hi then 1 else 0)
    link (by change Dir4.x0 ≠ Dir4.x3; decide)
    (oddFaces (responseExtent margin) state) (oddFaces_nodup _ _) hs
    (fun time => by rw [← hcharge]; exact moment_odd_geometry_parity margin lo hi state hc _)
  cases lo <;> cases hi <;> simp_all

theorem one_endpoint_check_false (margin : Nat) (lo hi : Bool) (state : EdgeLabelling)
    (hne : lo ≠ hi) (hs : spatialOddFaces margin state = []) :
    momentCheck margin lo hi state = false := by
  cases hc : momentCheck margin lo hi state with
  | false => rfl
  | true => exact False.elim (hne (accepted_flags_equal margin lo hi state hs hc))

theorem one_endpoint_zero (margin : Nat) (lo hi : Bool) (state : EdgeLabelling)
    (hne : lo ≠ hi) (hs : spatialOddFaces margin state = []) :
    moment margin lo hi state ≈ 0 :=
  moment_rejected margin lo hi state (one_endpoint_check_false margin lo hi state hne hs)

theorem spatial_empty_of_temporal (faces : List Z4Plaq)
    (ht : ∀ face, face ∈ faces → (dirsOf face.2).2 = Dir4.x3) : spatialFaces faces = [] := by
  have hnone (face : Z4Plaq) (hf : face ∈ spatialFaces faces) : False :=
    (of_decide_eq_true (List.mem_filter.mp hf).2) (ht face (List.mem_filter.mp hf).1)
  cases he : spatialFaces faces with
  | nil => rfl
  | cons face rest =>
    exact False.elim (hnone face (he ▸ List.mem_cons_self))

theorem tube_spatial_empty (margin : Nat) : spatialOddFaces margin (tubeLabelling margin) = [] := by
  unfold spatialOddFaces
  rw [← positive_eq_odd _ _ (fun id _ => tube_small margin id)]
  exact spatial_empty_of_temporal _ (fun face hf => window_temporal (tube_positive_window margin face hf))

theorem zero_spatial_empty (margin : Nat) : spatialOddFaces margin zeroEdgeLabelling = [] := by
  unfold spatialOddFaces
  rw [← positive_eq_odd (responseExtent margin) zeroEdgeLabelling (fun _ _ => Nat.zero_le 1), zero_positive]
  rfl

theorem mixed_parity_pin (margin : Nat) (state : EdgeLabelling)
    (hs : spatialOddFaces margin state = []) (hc : momentCheck margin true true state = true)
    (id : Nat) (hi : id ∈ slabPhysicalFaceEdges (responseExtent margin)) :
    state id % 2 = tubeLabelling margin id := by
  have hp := spatial_odd_determine_face_parity margin true true state (tubeLabelling margin)
    hc (tube_momentCheck margin) (hs.trans (tube_spatial_empty margin).symm)
    (slabPlaquetteAt (responseExtent margin) id) (slabPlaquetteAt_mem hi)
  rw [idxOf_slabPlaquetteAt hi,
    Nat.mod_eq_of_lt (show tubeLabelling margin id < 2 from by have h := tube_small margin id; omega)] at hp
  exact hp

theorem partition_parity_zero (margin : Nat) (state : EdgeLabelling)
    (hs : spatialOddFaces margin state = []) (hc : momentCheck margin false false state = true)
    (id : Nat) (hi : id ∈ slabPhysicalFaceEdges (responseExtent margin)) : state id % 2 = 0 := by
  have hp := spatial_odd_determine_face_parity margin false false state zeroEdgeLabelling
    hc (zero_momentCheck margin) (hs.trans (zero_spatial_empty margin).symm)
    (slabPlaquetteAt (responseExtent margin) id) (slabPlaquetteAt_mem hi)
  rw [idxOf_slabPlaquetteAt hi] at hp
  exact hp

/-- One zero-spatial replica suffices to remove the original product of means. -/
theorem pairTerm_pin_no_means (margin : Nat) (left right : EdgeLabelling)
    (hs : spatialOddFaces margin left = []) :
    pairTerm margin left right ≈ moment margin true true left * moment margin false false right := by
  have hz := one_endpoint_zero margin true false left (by decide) hs
  have hp : moment margin true false left * moment margin false true right ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hz) (Q'.zero_mul_eqv _)
  have hn := Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hp) (by decide : -(0 : Q') ≈ 0)
  exact Q'.eqv_trans _ _ _ (pairTerm_pin margin left right)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) hn) (Q'.eqv_of_eq (Q'.add_zero' _)))

theorem nonzero_pair_checks (margin : Nat) (left right : EdgeLabelling)
    (hs : spatialOddFaces margin left = []) (hne : ¬pairTerm margin left right ≈ 0) :
    momentCheck margin true true left = true ∧ momentCheck margin false false right = true := by
  have hp := pairTerm_pin_no_means margin left right hs
  constructor
  · cases hc : momentCheck margin true true left with
    | true => rfl
    | false => exact False.elim (hne (Q'.eqv_trans _ _ _ hp
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (moment_rejected margin true true left hc))
          (Q'.zero_mul_eqv _))))
  · cases hc : momentCheck margin false false right with
    | true => rfl
    | false => exact False.elim (hne (Q'.eqv_trans _ _ _ hp
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (moment_rejected margin false false right hc))
          (Q'.mul_zero_eqv _))))

end YMGap.Continuum.BF4ExactSlabZeroSpatialChannels

#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialChannels.retimed_endpoint_mem_any
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialChannels.accepted_flags_equal
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialChannels.one_endpoint_check_false
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialChannels.one_endpoint_zero
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialChannels.spatial_empty_of_temporal
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialChannels.tube_spatial_empty
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialChannels.zero_spatial_empty
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialChannels.mixed_parity_pin
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialChannels.partition_parity_zero
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialChannels.pairTerm_pin_no_means
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialChannels.nonzero_pair_checks
