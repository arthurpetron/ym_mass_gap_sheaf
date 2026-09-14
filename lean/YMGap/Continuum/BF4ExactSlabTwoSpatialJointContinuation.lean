/-
# The original joint channel's two spatial faces are parallel caps

Equal endpoint flags give equal endpoint impulses on each spatial link.
The finite four-impulse decoder forces the two spatial odd faces to have
the same projection. Their original duplicate-free list forces different
times. The exact cut formula retains the original checker and both caps;
no temporal-window assumption, Haar sign or weight estimate is introduced.
-/

import YMGap.Continuum.Z4TwoSpatialFaceContinuation
import YMGap.Continuum.BF4ExactSlabSingleCapDecoder

namespace YMGap.Continuum.BF4ExactSlabTwoSpatialJointContinuation

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4SpatialDefectTemporalDecoder
open YMGap.Continuum.Z4FiniteTemporalEndpointParity
open YMGap.Continuum.Z4SpatialPlaquetteProjection
open YMGap.Continuum.Z4TwoSpatialFaceContinuation
open YMGap.Continuum.BF4ExactSlabSingleSpatialCap
open YMGap.Continuum.BF4ExactSlabSingleCapDecoder
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabMinimalMomentParity
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction

theorem joint_endpoint_source (margin : Nat) (lo : Bool) (link : Z4Link) (time : Nat) :
    endpointCharge margin lo lo (atTime time link) =
      twoImpulses margin (margin+3) (if lo then boundaryBit margin link else 0)
        (if lo then boundaryBit margin link else 0) time := by
  cases lo
  · simp only [endpointCharge, twoImpulses, Bool.false_eq_true, ↓reduceIte, ite_self]
  · change ((if atTime time link ∈ edgesOf (capFace margin margin) then 1 else 0)+
      (if atTime time link ∈ edgesOf (capFace margin (margin+3)) then 1 else 0)) = _
    rw [cap_indicator,cap_indicator]
    rfl

theorem joint_two_spatial_flags (margin : Nat) (state : EdgeLabelling) (left right : Z4Plaq)
    (hs : spatialOddFaces margin state=[left,right]) :
    (dirsOf left.2).2 ≠ Dir4.x3 ∧ (dirsOf right.2).2 ≠ Dir4.x3 :=
  ⟨of_decide_eq_true (List.mem_filter.mp (show left ∈ spatialOddFaces margin state from
      hs ▸ List.mem_cons_self)).2,
    of_decide_eq_true (List.mem_filter.mp (show right ∈ spatialOddFaces margin state from
      hs ▸ List.mem_cons_of_mem _ List.mem_cons_self)).2⟩

theorem joint_two_spatial_boundary (margin : Nat) (lo : Bool) (state : EdgeLabelling)
    (left right : Z4Plaq) (hs : spatialOddFaces margin state=[left,right])
    (hc : momentCheck margin lo lo state=true) (link : Z4Link) (hd : link.2 ≠ Dir4.x3) :
    atTime left.1.2.2.2 link ∈ edgesOf left ↔ atTime right.1.2.2.2 link ∈ edgesOf right :=
  two_spatial_projected_boundary margin (margin+3) (if lo then boundaryBit margin link else 0)
    (fun t => endpointCharge margin lo lo (atTime t link)) link hd
    (oddFaces (responseExtent margin) state) (oddFaces_nodup _ _) left right hs
    (joint_endpoint_source margin lo link)
    (fun t => moment_odd_geometry_parity margin lo lo state hc (atTime t link))

theorem joint_two_spatial_projection (margin : Nat) (lo : Bool) (state : EdgeLabelling)
    (left right : Z4Plaq) (hs : spatialOddFaces margin state=[left,right])
    (hc : momentCheck margin lo lo state=true) : faceAt 0 left=faceAt 0 right := by
  have hf := joint_two_spatial_flags margin state left right hs
  exact projected_boundary_eq left right hf.1 hf.2
    (joint_two_spatial_boundary margin lo state left right hs hc)

theorem joint_two_spatial_times_ne (margin : Nat) (lo : Bool) (state : EdgeLabelling)
    (left right : Z4Plaq) (hs : spatialOddFaces margin state=[left,right])
    (hc : momentCheck margin lo lo state=true) : left.1.2.2.2 ≠ right.1.2.2.2 := by
  intro ht
  have he := projection_and_time_injective left right
    (joint_two_spatial_projection margin lo state left right hs hc) ht
  have hn : (spatialOddFaces margin state).Nodup := (oddFaces_nodup _ _).filter _
  rw [hs] at hn
  exact (List.nodup_cons.mp hn).1 (List.mem_cons.mpr (Or.inl he))

theorem joint_two_spatial_bit_eq (margin : Nat) (lo : Bool) (state : EdgeLabelling)
    (left right : Z4Plaq) (hs : spatialOddFaces margin state=[left,right])
    (hc : momentCheck margin lo lo state=true) (link : Z4Link) (hd : link.2 ≠ Dir4.x3) :
    projectedBit left link=projectedBit right link := by
  have hp := joint_two_spatial_boundary margin lo state left right hs hc link hd
  by_cases hl : atTime left.1.2.2.2 link ∈ edgesOf left
  · have hr := hp.mp hl
    simp only [projectedBit,if_pos hl,if_pos hr]
  · have hr : atTime right.1.2.2.2 link ∉ edgesOf right := fun h => hl (hp.mpr h)
    simp only [projectedBit,if_neg hl,if_neg hr]

theorem joint_two_spatial_cut_decode (margin : Nat) (lo : Bool) (state : EdgeLabelling)
    (left right : Z4Plaq) (hs : spatialOddFaces margin state=[left,right])
    (hc : momentCheck margin lo lo state=true) (link : Z4Link) (hd : link.2 ≠ Dir4.x3)
    (time : Nat) :
    cutCount time link (oddFaces (responseExtent margin) state) =
      ((if margin ≤ time then (if lo then boundaryBit margin link else 0) else 0)+
        (if margin+3 ≤ time then (if lo then boundaryBit margin link else 0) else 0)+
        (if left.1.2.2.2 ≤ time then projectedBit left link else 0)+
        (if right.1.2.2.2 ≤ time then projectedBit left link else 0))%2 := by
  have h := two_spatial_cut_decode margin (margin+3) (if lo then boundaryBit margin link else 0)
    (fun t => endpointCharge margin lo lo (atTime t link)) link hd
    (oddFaces (responseExtent margin) state) (oddFaces_nodup _ _) left right hs
    (joint_endpoint_source margin lo link)
    (fun t => moment_odd_geometry_parity margin lo lo state hc (atTime t link)) time
  rw [← joint_two_spatial_bit_eq margin lo state left right hs hc link hd] at h
  exact h

theorem joint_cut_between_caps (margin : Nat) (lo : Bool) (state : EdgeLabelling)
    (left right : Z4Plaq) (hs : spatialOddFaces margin state=[left,right])
    (hc : momentCheck margin lo lo state=true) (link : Z4Link) (hd : link.2 ≠ Dir4.x3)
    (time : Nat) (hlo : margin ≤ time) (hhi : time < margin+3)
    (hb : between left.1.2.2.2 right.1.2.2.2 time) :
    cutCount time link (oddFaces (responseExtent margin) state) =
      ((if lo then boundaryBit margin link else 0)+projectedBit left link)%2 := by
  rw [joint_two_spatial_cut_decode margin lo state left right hs hc link hd time,
    if_pos hlo,if_neg (Nat.not_le_of_lt hhi),Nat.add_zero]
  rcases hb with hb | hb
  · rw [if_pos hb.1,if_neg (Nat.not_le_of_lt hb.2),Nat.add_zero]
  · rw [if_neg (Nat.not_le_of_lt hb.2),if_pos hb.1,Nat.add_zero]

end YMGap.Continuum.BF4ExactSlabTwoSpatialJointContinuation

#print axioms YMGap.Continuum.BF4ExactSlabTwoSpatialJointContinuation.joint_endpoint_source
#print axioms YMGap.Continuum.BF4ExactSlabTwoSpatialJointContinuation.joint_two_spatial_flags
#print axioms YMGap.Continuum.BF4ExactSlabTwoSpatialJointContinuation.joint_two_spatial_boundary
#print axioms YMGap.Continuum.BF4ExactSlabTwoSpatialJointContinuation.joint_two_spatial_projection
#print axioms YMGap.Continuum.BF4ExactSlabTwoSpatialJointContinuation.joint_two_spatial_times_ne
#print axioms YMGap.Continuum.BF4ExactSlabTwoSpatialJointContinuation.joint_two_spatial_bit_eq
#print axioms YMGap.Continuum.BF4ExactSlabTwoSpatialJointContinuation.joint_two_spatial_cut_decode
#print axioms YMGap.Continuum.BF4ExactSlabTwoSpatialJointContinuation.joint_cut_between_caps
