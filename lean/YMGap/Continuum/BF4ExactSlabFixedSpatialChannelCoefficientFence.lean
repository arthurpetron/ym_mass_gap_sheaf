/-
# The footprint band alone cannot supply a small physical energy ratio

For every nonempty family the constructed first-order coefficient satisfies
(1-w)*C>=96. This is a bound on the explicit band coefficient, NOT a lower
bound on actual energy, variance, channel cost or Yang--Mills mass.

Thus dropping the signed remainder or replacing it by a nonnegative payment
cannot turn this particular ceiling into the c<1/2 input of the existing
survival consumer. A sharper actual-source estimate or retained cancellation
is necessary. No physical source, action, cutoff or frontier field is changed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelVarianceBound
import YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
import YMGap.Continuum.ThetaProductStrictFloor

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialChannelCoefficientFence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.GaussQBinomEulerNormalization (euler)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap)
open YMGap.Continuum.BF4ExactSlabStarRateObstruction (prefixCap_ge_one)
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound (headFloor_le_oneThirtySecond)
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformLocalBand
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelVarianceBound

local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] channelFirstOrderVarianceConstant

private theorem one_le_pow (r : Q') (hr : (1 : Q') ≤ r) :
    ∀ k : Nat, (1 : Q') ≤ r^k
  | 0 => Q'.le_refl' _
  | k+1 => by
      rw [Q'.pow_succ]
      have hr0 : (0 : Q') ≤ r := Q'.le_trans' _ _ _ Q'.zero_le_one hr
      have hm := Q'.mul_le_mul_of_nonneg_right _ _ _ hr (Q'.pow_nonneg r hr0 k)
      exact Q'.le_trans' _ _ _ (one_le_pow r hr k)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _).symm) hm)

/-- The actual constructed head floor is at most one eighth of the step.
The sharper intermediate estimate is headFloor<=(1-w)^2/8. -/
theorem headFloor_le_stepEighth {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    headFloor w ≤ ((1 : Q')-w)*Q'.mkPos 1 8 (by decide) := by
  let E := EulerProductStrictFloor.floor w
  let h := (1 : Q')-w
  let eighth : Q' := Q'.mkPos 1 8 (by decide)
  have hE0 : (0 : Q') ≤ E := Q'.le_of_lt (EulerProductStrictFloor.floor_pos hw0 hw1)
  have hh0 : (0 : Q') ≤ h := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have hh1 : h ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (Q'.le_of_lt hw0)))
    (Q'.le_of_eqv (by decide : (1 : Q') + -0 ≈ 1))
  have heuler : euler w 1 ≈ h :=
    Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv w)))
  have hE : E ≤ h := Q'.le_trans' _ _ _
    (EulerProductStrictFloor.floor_le_euler hw0 hw1 1) (Q'.le_of_eqv heuler)
  have hs : E*E ≤ h*h := HKConv.mul_le_mul' hE0 hh0 hE hE
  have hh : h*h ≤ h := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ h hh1 hh0) (Q'.le_of_eqv (Q'.mul_one_eqv h))
  have hpin : headFloor w ≈ (E*E)*eighth := by
    unfold headFloor SU2PointwiseHeatStrictFloor.floor ThetaProductStrictFloor.floor
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.var 1) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.mul (.var 1) (.var 1))))
        (by decide) (fun | 0 => E | _ => HalfPow.half))
      (Q'.mul_eqv_congr_left (E*E) _ _
        (by decide : HalfPow.half*(HalfPow.half*HalfPow.half) ≈ Q'.mkPos 1 8 (by decide)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
    (Q'.mul_le_mul_of_nonneg_right _ _ eighth (Q'.le_trans' _ _ _ hs hh) (by decide))

/-- Cleared coefficient limitation; only the explicit positive band is used.
It makes no assertion about the true original energy/variance ratio. -/
theorem channelLeadingCoefficient_ge_ninetySix {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size : Nat) (hsize : 0 < size) :
    (96 : Q') ≤ ((1 : Q')-w)*channelFirstOrderVarianceConstant hw0 hw1 size := by
  let h := (1 : Q')-w
  let l := localLower w (4*size)
  let u := localUpper w (4*size)
  let L := l*l
  let U := u*u
  let C := channelFirstOrderVarianceConstant hw0 hw1 size
  have hl0 : (0 : Q') < l := localLower_positive hw0 hw1 _
  have hL0 : (0 : Q') < L := Q'.mul_pos hl0 hl0
  have hf0 : (0 : Q') ≤ headFloor w := Q'.le_of_lt (headFloor_positive hw0 hw1)
  have hf1 : headFloor w ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (headFloor_le_oneThirtySecond hw0 hw1) (by decide)
  have hl : l ≤ headFloor w := Q'.le_trans' _ _ _
    (HKConvGen.pow_base_antitone hf0 hf1 (by omega : 1 ≤ 7*(4*size)))
    (Q'.le_of_eqv (Q'.mul_one_eqv _))
  have hl1 : l ≤ (1 : Q') := Q'.le_trans' _ _ _ hl hf1
  have hL : L ≤ h*Q'.mkPos 1 8 (by decide) := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ l hl1 (Q'.le_of_lt hl0))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv l))
      (Q'.le_trans' _ _ _ hl (headFloor_le_stepEighth hw0 hw1)))
  have hu : (1 : Q') ≤ u := one_le_pow _ (prefixCap_ge_one hw0 hw1) _
  have hu0 : (0 : Q') ≤ u := Q'.le_trans' _ _ _ Q'.zero_le_one hu
  have hU : (1 : Q') ≤ U := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (by decide : (1 : Q')*1 ≈ 1))
    (HKConv.mul_le_mul' Q'.zero_le_one hu0 hu hu)
  have hfirst : (96 : Q')*L ≤ 12*h := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ 96 hL (by decide))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.const 96) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.const 96) (.var 1)) (.var 0)) (by decide)
        (fun | 0 => h | _ => Q'.mkPos 1 8 (by decide)))
      (Q'.mul_eqv_congr_right _ _ h
        (by decide : (96 : Q')*Q'.mkPos 1 8 (by decide) ≈ 12))))
  have hnext : 12*h ≤ h*(12*U) := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.const 12) (.var 0)) (.mul (.mul (.var 0) (.const 12)) (.const 1))
      (by decide) (fun _ => h)))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (h*12) hU
        (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)) (by decide)))
      (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _)))
  have hcancel : C*L ≈ 12*U := by
    unfold C channelFirstOrderVarianceConstant
    exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (12*U) _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv L hL0)))
        (Q'.mul_one_eqv _))
  have hright : L*(h*C) ≈ h*(12*U) := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 2) (.var 0))) (by decide)
      (fun | 0 => L | 1 => h | _ => C))
    (Q'.mul_eqv_congr_left h _ _ hcancel)
  apply HKConvGen.mul_le_mul_left_cancel hL0
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv L 96))
    (Q'.le_trans' _ _ _ hfirst
      (Q'.le_trans' _ _ _ hnext (Q'.ge_of_eqv hright)))

#print axioms headFloor_le_stepEighth
#print axioms channelLeadingCoefficient_ge_ninetySix

end YMGap.Continuum.BF4ExactSlabFixedSpatialChannelCoefficientFence
