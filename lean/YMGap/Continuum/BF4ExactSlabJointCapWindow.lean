/-
# A cut between the two original joint caps lies inside the saturated window

Outside the endpoint interval, the two equal endpoint charges cancel.
The cap boundary then forces a nonempty cut between the caps. A temporal
window assumption on the original odd-face list therefore puts every
between-cap cut in that window. Different cap times give the explicit
test cut at their minimum. The mixed and partition channels remain distinct.
-/

import YMGap.Continuum.BF4ExactSlabTwoSpatialJointContinuation
import YMGap.Continuum.BF4ExactSlabPower42MeansCaps

namespace YMGap.Continuum.BF4ExactSlabJointCapWindow

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4ThreeCutSaturation
open YMGap.Continuum.Z4FiniteTemporalEndpointParity
open YMGap.Continuum.Z4SpatialDefectTemporalDecoder
open YMGap.Continuum.Z4TwoSpatialFaceContinuation
open YMGap.Continuum.BF4ExactSlabSingleCapDecoder
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabMinimalMomentParity
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabTwoSpatialJointContinuation
open YMGap.Continuum.BF4ExactSlabPower42MeansCaps (nonempty_window_cut_time)

theorem cap_base_bit (face : Z4Plaq) : projectedBit face (cutEdge face)=1 :=
  if_pos List.mem_cons_self

theorem between_min (a b : Nat) (hne : a ≠ b) : between a b (min a b) := by
  by_cases h : a ≤ b
  · rw [Nat.min_eq_left h]
    exact Or.inl ⟨Nat.le_refl _,by omega⟩
  · rw [Nat.min_eq_right (by omega)]
    exact Or.inr ⟨Nat.le_refl _,by omega⟩

theorem joint_between_outside_nonempty (margin : Nat) (lo : Bool) (state : EdgeLabelling)
    (left right : Z4Plaq) (hs : spatialOddFaces margin state=[left,right])
    (hc : momentCheck margin lo lo state=true) (time : Nat)
    (hb : between left.1.2.2.2 right.1.2.2.2 time)
    (hout : time < margin ∨ margin+3 ≤ time) :
    cut time (oddFaces (responseExtent margin) state) ≠ [] := by
  have h := joint_two_spatial_cut_decode margin lo state left right hs hc (cutEdge left)
    (cutEdge_spatial left) time
  rw [cap_base_bit] at h
  have hcap : ((if left.1.2.2.2 ≤ time then 1 else 0)+(if right.1.2.2.2 ≤ time then 1 else 0))=1 := by
    rcases hb with hb | hb
    · rw [if_pos hb.1,if_neg (Nat.not_le_of_lt hb.2)]
    · rw [if_neg (Nat.not_le_of_lt hb.2),if_pos hb.1]
  rw [Nat.add_assoc,hcap] at h
  have hone : cutCount time (cutEdge left) (oddFaces (responseExtent margin) state)=1 := by
    rcases hout with hout | hout
    · rw [if_neg (Nat.not_le_of_lt hout),if_neg (by omega : ¬margin+3 ≤ time)] at h
      exact h
    · rw [if_pos (by omega : margin ≤ time),if_pos hout] at h
      omega
  intro he
  rw [cutCount,he] at hone
  contradiction

theorem joint_cap_interval_window (margin : Nat) (lo : Bool) (state : EdgeLabelling)
    (left right : Z4Plaq) (hs : spatialOddFaces margin state=[left,right])
    (hc : momentCheck margin lo lo state=true)
    (hw : ∀ face, face ∈ oddFaces (responseExtent margin) state →
      (dirsOf face.2).2=Dir4.x3 → window margin face=true)
    (time : Nat) (hb : between left.1.2.2.2 right.1.2.2.2 time) :
    margin ≤ time ∧ time < margin+3 := by
  constructor
  · by_cases h : margin ≤ time
    · exact h
    · have ht := nonempty_window_cut_time margin _ hw time
        (joint_between_outside_nonempty margin lo state left right hs hc time hb (Or.inl (by omega)))
      omega
  · by_cases h : time < margin+3
    · exact h
    · have ht := nonempty_window_cut_time margin _ hw time
        (joint_between_outside_nonempty margin lo state left right hs hc time hb (Or.inr (by omega)))
      omega

theorem joint_caps_test_cut (margin : Nat) (lo : Bool) (state : EdgeLabelling)
    (left right : Z4Plaq) (hs : spatialOddFaces margin state=[left,right])
    (hc : momentCheck margin lo lo state=true)
    (hw : ∀ face, face ∈ oddFaces (responseExtent margin) state →
      (dirsOf face.2).2=Dir4.x3 → window margin face=true) :
    between left.1.2.2.2 right.1.2.2.2 (min left.1.2.2.2 right.1.2.2.2) ∧
      margin ≤ min left.1.2.2.2 right.1.2.2.2 ∧ min left.1.2.2.2 right.1.2.2.2 < margin+3 := by
  have hb := between_min _ _ (joint_two_spatial_times_ne margin lo state left right hs hc)
  exact ⟨hb,joint_cap_interval_window margin lo state left right hs hc hw _ hb⟩

theorem partition_between_caps_nonempty (margin : Nat) (state : EdgeLabelling)
    (left right : Z4Plaq) (hs : spatialOddFaces margin state=[left,right])
    (hc : momentCheck margin false false state=true) (time : Nat)
    (hlo : margin ≤ time) (hhi : time < margin+3) (hb : between left.1.2.2.2 right.1.2.2.2 time) :
    cut time (oddFaces (responseExtent margin) state) ≠ [] := by
  have h := joint_cut_between_caps margin false state left right hs hc (cutEdge left)
    (cutEdge_spatial left) time hlo hhi hb
  rw [cap_base_bit] at h
  intro he
  rw [cutCount,he] at h
  contradiction

theorem mixed_zero_spatial_cut_nonempty (margin : Nat) (state : EdgeLabelling)
    (hs : spatialOddFaces margin state=[]) (hc : momentCheck margin true true state=true)
    (time : Nat) (hlo : margin ≤ time) (hhi : time < margin+3) :
    cut time (oddFaces (responseExtent margin) state) ≠ [] := by
  let link : Z4Link := ((1+margin,1+margin,1+margin,0),.x0)
  have hbit : boundaryBit margin link=1 := if_pos List.mem_cons_self
  have h := moment_temporal_bit margin true true state hc link (by change Dir4.x0 ≠ Dir4.x3; decide) time
  rw [hs] at h
  change cutCount time link (oddFaces (responseExtent margin) state)=
    temporalBit (fun t => endpointCharge margin true true (atTime t link)) (fun _ => 0) time at h
  have he : (fun t => endpointCharge margin true true (atTime t link))=twoImpulses margin (margin+3) 1 1 := by
    funext t
    rw [joint_endpoint_source,hbit]
    rfl
  rw [he,two_impulses_decode,if_pos hlo,if_neg (Nat.not_le_of_lt hhi)] at h
  intro he
  rw [cutCount,he] at h
  contradiction

end YMGap.Continuum.BF4ExactSlabJointCapWindow

#print axioms YMGap.Continuum.BF4ExactSlabJointCapWindow.cap_base_bit
#print axioms YMGap.Continuum.BF4ExactSlabJointCapWindow.between_min
#print axioms YMGap.Continuum.BF4ExactSlabJointCapWindow.joint_between_outside_nonempty
#print axioms YMGap.Continuum.BF4ExactSlabJointCapWindow.joint_cap_interval_window
#print axioms YMGap.Continuum.BF4ExactSlabJointCapWindow.joint_caps_test_cut
#print axioms YMGap.Continuum.BF4ExactSlabJointCapWindow.partition_between_caps_nonempty
#print axioms YMGap.Continuum.BF4ExactSlabJointCapWindow.mixed_zero_spatial_cut_nonempty
