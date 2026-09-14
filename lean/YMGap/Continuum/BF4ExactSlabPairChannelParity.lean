/-
# The two ORIGINAL connected-pair channels are mutually exclusive

The mixed-moment/partition channel has even odd-face count in each
replica. The two one-endpoint means have odd counts instead. Thus their
original checkers cannot both accept the same pair. The joint checker is
a computable channel bit; a nonzero original pair supplies the two actual
accepted moment checks for that bit.

Both total and spatial odd-face counts across the replicas are even.
A surviving spatial defect therefore contains at least two spatial odd
faces, counting replica occurrences. The mean channel has at least one
in EACH replica. These constraints do not count their configurations or
assert a sign of the surviving Haar products.
-/

import YMGap.Continuum.BF4ExactSlabMomentFaceParity
import YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut

namespace YMGap.Continuum.BF4ExactSlabPairChannelParity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.BF4ExactSlabMomentFaceParity
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction

local infix:50 " ≈ " => Q'.eqv

def jointCheck (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  momentCheck margin true true pair.1 && momentCheck margin false false pair.2

def meansCheck (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  momentCheck margin true false pair.1 && momentCheck margin false true pair.2

private theorem product_rejected (margin : Nat) (a b c d : Bool) (pair : EdgeLabelling × EdgeLabelling)
    (h : (momentCheck margin a b pair.1 && momentCheck margin c d pair.2) = false) :
    moment margin a b pair.1 * moment margin c d pair.2 ≈ 0 := by
  cases hl : momentCheck margin a b pair.1 with
  | false =>
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (moment_rejected margin a b pair.1 hl)) (Q'.zero_mul_eqv _)
  | true =>
    have hr : momentCheck margin c d pair.2 = false := by simpa only [hl, Bool.true_and] using h
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (moment_rejected margin c d pair.2 hr)) (Q'.mul_zero_eqv _)

theorem joint_means_exclusive (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hj : jointCheck margin pair = true) : meansCheck margin pair = false := by
  cases hm : meansCheck margin pair with
  | false => rfl
  | true =>
    have hjl := (Bool.and_eq_true_iff.mp hj).1
    have hml := (Bool.and_eq_true_iff.mp hm).1
    have hjp := (moment_face_parities margin true true pair.1 hjl).1
    have hmp := (moment_face_parities margin true false pair.1 hml).1
    change (oddFaces (responseExtent margin) pair.1).length%2=0 at hjp
    change (oddFaces (responseExtent margin) pair.1).length%2=1 at hmp
    omega

theorem pairTerm_joint_pin (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hj : jointCheck margin pair = true) :
    pairTerm margin pair.1 pair.2 ≈ moment margin true true pair.1*moment margin false false pair.2 := by
  have hz := product_rejected margin true false false true pair (joint_means_exclusive margin pair hj)
  exact Q'.eqv_trans _ _ _ (pairTerm_pin margin pair.1 pair.2)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ hz) (by decide : -(0 : Q') ≈ 0))) (Q'.eqv_of_eq (Q'.add_zero' _)))

theorem pairTerm_means_pin (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hj : jointCheck margin pair = false) :
    pairTerm margin pair.1 pair.2 ≈ -(moment margin true false pair.1*moment margin false true pair.2) := by
  have hz := product_rejected margin true true false false pair hj
  exact Q'.eqv_trans _ _ _ (pairTerm_pin margin pair.1 pair.2)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hz) (Q'.eqv_of_eq (Q'.zero_add' _)))

/-- Nonzero original amplitude determines actual accepted checks in one channel. -/
theorem nonzero_pair_channel_checks (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0) :
    momentCheck margin true (jointCheck margin pair) pair.1 = true ∧
      momentCheck margin false (!(jointCheck margin pair)) pair.2 = true := by
  cases hj : jointCheck margin pair with
  | true => exact Bool.and_eq_true_iff.mp hj
  | false =>
    cases hm : meansCheck margin pair with
    | true => exact Bool.and_eq_true_iff.mp hm
    | false =>
      exact False.elim (hne (Q'.eqv_trans _ _ _ (pairTerm_means_pin margin pair hj)
        (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (product_rejected margin true false false true pair hm))
          (by decide : -(0 : Q') ≈ 0))))

def pairSpatial (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Nat :=
  (spatialOddFaces margin pair.1).length+(spatialOddFaces margin pair.2).length

theorem nonzero_pair_face_counts_even (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0) :
    ((oddFaces (responseExtent margin) pair.1).length+(oddFaces (responseExtent margin) pair.2).length)%2=0 ∧
      pairSpatial margin pair%2=0 := by
  have hc := nonzero_pair_channel_checks margin pair hne
  have hl := moment_face_parities margin true (jointCheck margin pair) pair.1 hc.1
  have hr := moment_face_parities margin false (!(jointCheck margin pair)) pair.2 hc.2
  unfold pairSpatial
  cases hj : jointCheck margin pair <;>
    simp only [hj, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hl hr
  all_goals constructor <;> omega

theorem nonzero_spatial_minimum_two (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0)
    (hs : ¬(spatialOddFaces margin pair.1 = [] ∧ spatialOddFaces margin pair.2 = [])) :
    2 ≤ pairSpatial margin pair := by
  have he := (nonzero_pair_face_counts_even margin pair hne).2
  by_cases hp : 2 ≤ pairSpatial margin pair
  · exact hp
  · have hz : pairSpatial margin pair=0 := by omega
    have hl : (spatialOddFaces margin pair.1).length=0 := by unfold pairSpatial at hz; omega
    have hr : (spatialOddFaces margin pair.2).length=0 := by unfold pairSpatial at hz; omega
    exact False.elim (hs ⟨List.length_eq_zero_iff.mp hl,List.length_eq_zero_iff.mp hr⟩)

theorem means_each_spatial_positive (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hm : meansCheck margin pair = true) :
    1 ≤ (spatialOddFaces margin pair.1).length ∧ 1 ≤ (spatialOddFaces margin pair.2).length := by
  have hl := (moment_face_parities margin true false pair.1 (Bool.and_eq_true_iff.mp hm).1).2
  have hr := (moment_face_parities margin false true pair.2 (Bool.and_eq_true_iff.mp hm).2).2
  change (spatialOddFaces margin pair.1).length%2=1 at hl
  change (spatialOddFaces margin pair.2).length%2=1 at hr
  constructor <;> omega

end YMGap.Continuum.BF4ExactSlabPairChannelParity

#print axioms YMGap.Continuum.BF4ExactSlabPairChannelParity.jointCheck
#print axioms YMGap.Continuum.BF4ExactSlabPairChannelParity.meansCheck
#print axioms YMGap.Continuum.BF4ExactSlabPairChannelParity.joint_means_exclusive
#print axioms YMGap.Continuum.BF4ExactSlabPairChannelParity.pairTerm_joint_pin
#print axioms YMGap.Continuum.BF4ExactSlabPairChannelParity.pairTerm_means_pin
#print axioms YMGap.Continuum.BF4ExactSlabPairChannelParity.nonzero_pair_channel_checks
#print axioms YMGap.Continuum.BF4ExactSlabPairChannelParity.pairSpatial
#print axioms YMGap.Continuum.BF4ExactSlabPairChannelParity.nonzero_pair_face_counts_even
#print axioms YMGap.Continuum.BF4ExactSlabPairChannelParity.nonzero_spatial_minimum_two
#print axioms YMGap.Continuum.BF4ExactSlabPairChannelParity.means_each_spatial_positive
