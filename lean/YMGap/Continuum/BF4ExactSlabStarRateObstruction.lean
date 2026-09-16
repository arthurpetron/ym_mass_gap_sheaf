/-
# The current coarse directional rate is not a small per-edge weight

The explicit squared directional rate q = 1 - L/U is at least 63/64:
the heat majorant includes its constant term 1, so U >= 2^6 = 64,
whereas the capped local floor gives L <= 1. Consequently 2*q < 1
cannot hold for these constants at any rational nome 0 < w < 1.

This rules out using THIS coarse bound as a small per-edge weight.
It is not a bound on an actual cross-link influence coefficient and
does not assert physical non-mixing or failure of a Yang--Mills gap.
-/

import YMGap.Continuum.BF4ExactSlabStarInverseApproximation

namespace YMGap.Continuum.BF4ExactSlabStarRateObstruction

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation

private theorem pow_mono {x y : Q'} (hx : (0 : Q') ≤ x) (hxy : x ≤ y) :
    ∀ n : Nat, x ^ n ≤ y ^ n
  | 0 => Q'.le_refl' 1
  | n + 1 => Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hxy (Q'.pow_nonneg x hx n))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (pow_mono hx hxy n)
        (Q'.le_trans' _ _ _ hx hxy))

/-- The absolute heat-prefix cap includes the exact constant Haar mode. -/
theorem prefixCap_ge_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (1 : Q') ≤ prefixCap w := by
  have h := majorant_prefix_bound hw0 hw1 1
  change (1 : Q') ≤ prefixCap w at h
  exact h

/-- The present explicit comparison ratio never exceeds 1/64. -/
theorem starRatio_le_oneSixtyFourth {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    starRatio w ≤ Q'.mkPos 1 64 (by decide) := by
  have hL : lowerFactor w ≤ (1 : Q') :=
    HKConvGen.pow_base_antitone (Q'.le_of_lt (localFloor_positive hw0 hw1))
      Q'.min_le_right (m := 0) (n := 6) (by decide)
  have hcap : (2 : Q') ≤ localCap w :=
    Q'.add_le_add (Q'.le_refl' 1) (prefixCap_ge_one hw0 hw1)
  have hU : (64 : Q') ≤ upperFactor w :=
    pow_mono (by decide : (0 : Q') ≤ 2) hcap 6
  apply HKConv.divPos_le_of_le (CReal.num_pos_of_pos (upperFactor_positive hw0))
  exact Q'.le_trans' _ _ _ hL (Q'.le_trans' _ _ _
    (by decide : (1 : Q') ≤ Q'.mkPos 1 64 (by decide) * 64)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hU (by decide)))

/-- This is the already-defined SQUARED directional rate, not a cross-link
influence coefficient. Its lower bound is uniform over the indicated nomes. -/
theorem inverseRate_ge_sixtyThreeSixtyFour {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    Q'.mkPos 63 64 (by decide) ≤ inverseRate w := by
  change Q'.mkPos 63 64 (by decide) ≤ 1 + -starRatio w
  exact Q'.le_trans' _ _ _
    (by decide : Q'.mkPos 63 64 (by decide) ≤ 1 + -(Q'.mkPos 1 64 (by decide)))
    (Q'.add_le_add (Q'.le_refl' 1) (Q'.neg_le_neg (starRatio_le_oneSixtyFourth hw0 hw1)))

/-- Even the arithmetic criterion with two copies of this coarse rate fails. -/
theorem not_two_mul_inverseRate_lt_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    ¬ ((2 : Q') * inverseRate w < (1 : Q')) := by
  have h : (1 : Q') ≤ (2 : Q') * inverseRate w :=
    Q'.le_trans' _ _ _
      (by decide : (1 : Q') ≤ (2 : Q') * Q'.mkPos 63 64 (by decide))
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (inverseRate_ge_sixtyThreeSixtyFour hw0 hw1) (by decide))
  exact Int.not_lt.mpr h

end YMGap.Continuum.BF4ExactSlabStarRateObstruction

#print axioms YMGap.Continuum.BF4ExactSlabStarRateObstruction.prefixCap_ge_one
#print axioms YMGap.Continuum.BF4ExactSlabStarRateObstruction.starRatio_le_oneSixtyFourth
#print axioms YMGap.Continuum.BF4ExactSlabStarRateObstruction.inverseRate_ge_sixtyThreeSixtyFour
#print axioms YMGap.Continuum.BF4ExactSlabStarRateObstruction.not_two_mul_inverseRate_lt_one
