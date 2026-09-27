/-
# Midpoint and width constants for the two-link perturbation estimate

The calibrated lower and upper collar multipliers straddle one. Their
midpoint and width are explicit rational data used in the final scalar
rearrangement; this module makes no covariance or gap claim.
-/

import YMGap.Continuum.BF4ExactSlabSmallNomePairCalibration

namespace YMGap.Continuum.BF4ExactSlabTwoLinkPerturbationConstants

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.HKPos
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.BF4ExactSlabSmallNomePairCalibration
open YMGap.Continuum.QuaternionHaarCharacterInterval

local infix:50 " ≈ " => Q'.eqv

def width (w : Q') : Q' := twoLinkUpper w + -twoLinkLower w

def midpoint (w : Q') : Q' :=
  HalfPow.half * (twoLinkLower w + twoLinkUpper w)

private theorem one_le_pow_base (a : Q') (ha : (1 : Q') ≤ a) :
    ∀ n : Nat, (1 : Q') ≤ a ^ n
  | 0 => by simpa using (Q'.le_refl' (1 : Q'))
  | n + 1 => by
      have ih := one_le_pow_base a ha n
      exact Q'.le_trans' _ _ _ ih
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
          (Q'.mul_le_mul_of_nonneg_right _ _ _ ha
            (Q'.pow_nonneg a (Q'.le_trans' _ _ _ Q'.zero_le_one ha) n)))

theorem lower_le_one {w : Q'} (hw : (0 : Q') < w)
    (hd : heatRemainderBound w < (1 : Q')) :
    twoLinkLower w ≤ (1 : Q') := by
  have hδ : (0 : Q') ≤ heatRemainderBound w :=
    remainder_nonnegative (Q'.le_of_lt hw)
  have hrpos : (0 : Q') < 1 + -heatRemainderBound w := HKPos.one_sub_pos hd
  have hr0 : (0 : Q') ≤ 1 + -heatRemainderBound w := Q'.le_of_lt hrpos
  have hr1 : 1 + -heatRemainderBound w ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_left 1 (-heatRemainderBound w) 0
        (Q'.neg_le_neg hδ))
      (by decide)
  have hp := HKConvGen.pow_base_antitone hr0 hr1
    (m := 0) (n := 12) (Nat.zero_le 12)
  simpa [twoLinkLower] using hp

theorem one_le_upper {w : Q'} (hw : (0 : Q') < w) :
    (1 : Q') ≤ twoLinkUpper w := by
  have hδ : (0 : Q') ≤ heatRemainderBound w :=
    remainder_nonnegative (Q'.le_of_lt hw)
  have hbase : (1 : Q') ≤ 1 + heatRemainderBound w :=
    Q'.add_le_self_of_nonneg _ _ hδ
  simpa [twoLinkUpper] using one_le_pow_base (1 + heatRemainderBound w) hbase 12

theorem width_nonnegative {w : Q'} (hw : (0 : Q') < w)
    (hd : heatRemainderBound w < (1 : Q')) :
    (0 : Q') ≤ width w := by
  unfold width
  exact Q'.sub_nonneg_of_le
    (Q'.le_trans' _ _ _ (lower_le_one hw hd) (one_le_upper hw))

theorem midpoint_positive {w : Q'} (hw : (0 : Q') < w)
    (hd : heatRemainderBound w < (1 : Q')) :
    (0 : Q') < midpoint w := by
  unfold midpoint
  exact Q'.mul_pos (by decide : (0 : Q') < HalfPow.half)
    (Q'.add_pos (twoLinkLower_positive hd) (twoLinkUpper_positive (Q'.le_of_lt hw)))

theorem midpoint_nonnegative {w : Q'} (hw : (0 : Q') < w)
    (hd : heatRemainderBound w < (1 : Q')) :
    (0 : Q') ≤ midpoint w :=
  Q'.le_of_lt (midpoint_positive hw hd)

theorem four_midpoint_eqv_twice_sum (w : Q') :
    (4 : Q') * midpoint w ≈
      2 * (twoLinkLower w + twoLinkUpper w) := by
  unfold midpoint
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 4 HalfPow.half
      (twoLinkLower w + twoLinkUpper w)))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (4 * HalfPow.half) 2
        (twoLinkLower w + twoLinkUpper w) (by decide))
      (Q'.eqv_refl _))

end YMGap.Continuum.BF4ExactSlabTwoLinkPerturbationConstants

#print axioms YMGap.Continuum.BF4ExactSlabTwoLinkPerturbationConstants.lower_le_one
#print axioms YMGap.Continuum.BF4ExactSlabTwoLinkPerturbationConstants.one_le_upper
#print axioms YMGap.Continuum.BF4ExactSlabTwoLinkPerturbationConstants.width_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabTwoLinkPerturbationConstants.midpoint_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabTwoLinkPerturbationConstants.midpoint_positive
#print axioms YMGap.Continuum.BF4ExactSlabTwoLinkPerturbationConstants.four_midpoint_eqv_twice_sum
