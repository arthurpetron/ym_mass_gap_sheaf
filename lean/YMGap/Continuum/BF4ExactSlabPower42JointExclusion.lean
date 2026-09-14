/-
# The original power-42 spatial sector cannot be in the joint channel

The two spatial caps must lie in one replica. If they lie in the mixed
replica, a cut between them is the symmetric difference of two plaquette
boundaries, whose length cannot be four. The partition replica has no odd
faces, contradicting the saturated four-link cut. If the caps lie in the
partition replica, both replicas occupy that cut, again contradicting
saturation. This excludes only power 42, not higher joint contributions.
-/

import YMGap.Continuum.BF4ExactSlabJointCapWindow
import YMGap.Continuum.Z4ProjectedBoundaryCutComparison

namespace YMGap.Continuum.BF4ExactSlabPower42JointExclusion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator (zeroEdgeLabelling)
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4PlaquetteBoundaryRigidity
open YMGap.Continuum.Z4SpatialPlaquetteProjection
open YMGap.Continuum.Z4ProjectedBoundaryCutComparison
open YMGap.Continuum.BF4ExactSlabJointCapWindow
open YMGap.Continuum.BF4ExactSlabTwoSpatialJointContinuation
open YMGap.Continuum.BF4ExactSlabSingleCapDecoder
open YMGap.Continuum.BF4ExactSlabPower42TemporalSaturation
open YMGap.Continuum.BF4ExactSlabPower42SpatialBudget
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabMinimalPowerWindow (positive_eq_odd)
open YMGap.Continuum.BF4ExactSlabCanonicalTubeMoments (zero_positive zero_momentCheck)
open YMGap.Continuum.BF4ExactSlabZeroSpatialChannels (zero_spatial_empty)
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem partition_zero_spatial_odd_empty (margin : Nat) (state : EdgeLabelling)
    (hs : spatialOddFaces margin state=[]) (hc : momentCheck margin false false state=true) :
    oddFaces (responseExtent margin) state=[] := by
  have hz : oddFaces (responseExtent margin) zeroEdgeLabelling=[] :=
    (positive_eq_odd _ _ (fun _ _ => Nat.zero_le 1)).symm.trans (zero_positive _)
  cases he : oddFaces (responseExtent margin) state with
  | nil => rfl
  | cons face rest =>
    have hm := (spatial_odd_determine_membership margin false false state zeroEdgeLabelling
      hc (zero_momentCheck margin) (hs.trans (zero_spatial_empty margin).symm) face).mp
      (show face ∈ oddFaces (responseExtent margin) state from he ▸ List.mem_cons_self)
    rw [hz] at hm
    cases hm

theorem mixed_between_caps_cut_ne_four (margin : Nat) (state : EdgeLabelling)
    (left right : Z4Plaq) (hs : spatialOddFaces margin state=[left,right])
    (hc : momentCheck margin true true state=true) (time : Nat)
    (hlo : margin ≤ time) (hhi : time < margin+3)
    (hb : between left.1.2.2.2 right.1.2.2.2 time) :
    (cut time (oddFaces (responseExtent margin) state)).length ≠ 4 := by
  have hf := joint_two_spatial_flags margin state left right hs
  have hp := cut_symmetricBoundary_perm time (oddFaces (responseExtent margin) state)
    (oddFaces_nodup _ _) (sliceFace margin 0) left
    (by change Dir4.x1 ≠ Dir4.x3; decide) hf.1
    (fun link hd => joint_cut_between_caps margin true state left right hs hc link hd time hlo hhi hb)
  intro he
  exact symmetricBoundary_ne_four _ _ (hp.length_eq.symm.trans he)

theorem power42_spatial_joint_false {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (he : pairPower margin pair=42) (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0)
    (hd : spatialDefectKeep margin pair=true) : jointCheck margin pair=false := by
  cases hj : jointCheck margin pair with
  | false => rfl
  | true =>
    have hc := Bool.and_eq_true_iff.mp hj
    have hw := power42_temporal_window hs hp he hne hd
    have hsp := power42_spatial_distribution hs hp he hne hd
    simp only [hj,↓reduceIte] at hsp
    rcases hsp with hsp | hsp
    · have hr : spatialOddFaces margin pair.2=[] := List.eq_nil_of_length_eq_zero hsp.2
      have hz := partition_zero_spatial_odd_empty margin pair.2 hr hc.2
      cases hl : spatialOddFaces margin pair.1 with
      | nil => simp only [hl,List.length_nil] at hsp; omega
      | cons left rest =>
        cases rest with
        | nil => simp only [hl,List.length_cons,List.length_nil] at hsp; omega
        | cons right tail =>
          have ht : tail=[] := List.eq_nil_of_length_eq_zero (by
            simp only [hl,List.length_cons] at hsp
            omega)
          subst tail
          have hwc := joint_caps_test_cut margin true pair.1 left right hl hc.1 hw.1
          have hfour := (power42_cut_saturation hs hp he hne hd).2.2 _ hwc.2.1 hwc.2.2
          rw [hz] at hfour
          exact False.elim (mixed_between_caps_cut_ne_four margin pair.1 left right hl hc.1
            _ hwc.2.1 hwc.2.2 hwc.1 hfour)
    · have hl : spatialOddFaces margin pair.1=[] := List.eq_nil_of_length_eq_zero hsp.1
      cases hr : spatialOddFaces margin pair.2 with
      | nil => simp only [hr,List.length_nil] at hsp; omega
      | cons left rest =>
        cases rest with
        | nil => simp only [hr,List.length_cons,List.length_nil] at hsp; omega
        | cons right tail =>
          have ht : tail=[] := List.eq_nil_of_length_eq_zero (by
            simp only [hr,List.length_cons] at hsp
            omega)
          subst tail
          have hwc := joint_caps_test_cut margin false pair.2 left right hr hc.2 hw.2
          exact False.elim (power42_cuts_exclusive hs hp he hne hd _ hwc.2.1 hwc.2.2
            ⟨mixed_zero_spatial_cut_nonempty margin pair.1 hl hc.1 _ hwc.2.1 hwc.2.2,
              partition_between_caps_nonempty margin pair.2 left right hr hc.2
                _ hwc.2.1 hwc.2.2 hwc.1⟩)

end YMGap.Continuum.BF4ExactSlabPower42JointExclusion

#print axioms YMGap.Continuum.BF4ExactSlabPower42JointExclusion.partition_zero_spatial_odd_empty
#print axioms YMGap.Continuum.BF4ExactSlabPower42JointExclusion.mixed_between_caps_cut_ne_four
#print axioms YMGap.Continuum.BF4ExactSlabPower42JointExclusion.power42_spatial_joint_false
