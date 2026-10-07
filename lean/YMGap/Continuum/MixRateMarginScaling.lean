/-
# How the proved mixRate margin depends on the nome and the width

ADDITIVE.  Mixed status: the theorems below are PROVED, and they show a gap between what is
proved and what is needed (OBSTRUCTION-TO-USE, not an obstruction to a mass gap).

The margin of `wilsonVacuumSqContraction_mixRate` is
`mixFraction w width = kineticFloor/kineticCap = (headFloor w / prefixCap w)^{n(width)}`,
with `n(width) = (temporalFaces width).length`.

* `mixFraction_le_pow`: `mixFraction ≤ (1/32)^{n(width)}` for EVERY `0 < w < 1`.
  This uses the existing `headFloor_le_oneThirtySecond` and `prefixCap_ge_one`.
* `mixFraction_le_width1`: at width 1, `mixFraction ≤ (1/32)^3 = 2^{-15}`, with
  `n(1) = 3` checked by the kernel (`temporalFaces_one`).
* `n(width) = 3·width³` for width 1..4 (3, 24, 81, 192): that is a compiled `#eval`
  measurement, NOT a Lean theorem beyond width 1.

Axioms: `propext`, `Quot.sound`.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
import YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
import YMGap.Continuum.BF4ExactSlabStarRateObstruction
import YMGap.Continuum.SpectralGap

namespace YMGap.Continuum.MixRateMarginScaling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (kineticFloor kineticCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (temporalFaces)

theorem one_le_pow' {q : Q'} (hq : (1 : Q') ≤ q) : ∀ d : Nat, (1 : Q') ≤ q ^ d
  | 0 => Q'.le_refl' 1
  | d + 1 => by
    have h0 : (0 : Q') ≤ q := Q'.le_trans' _ _ _ (by decide) hq
    have ih := one_le_pow' hq d
    exact Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ 1 * 1)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hq (by decide))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ ih h0))

def thirtySecond : Q' := Q'.mkPos 1 32 (by decide)

/-- The margin decays at least like `32^{-n(width)}`, uniformly in the nome. -/
theorem mixFraction_le_pow {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat) :
    mixFraction hw0 hw1 width ≤ thirtySecond ^ (temporalFaces width).length := by
  have hcap : (1 : Q') ≤ kineticCap w width :=
    one_le_pow' (BF4ExactSlabStarRateObstruction.prefixCap_ge_one hw0 hw1) _
  have hfl : kineticFloor w width ≤ thirtySecond ^ (temporalFaces width).length :=
    SpectralGap.pow_le_pow_left
      (Q'.le_of_lt (BF4ExactSlabRetainedHeatHeadComparison.headFloor_positive hw0 hw1))
      (BF4ExactSlabSharedWindowFloorBound.headFloor_le_oneThirtySecond hw0 hw1) _
  have hm0 := Q'.le_of_lt (mixFraction_positive hw0 hw1 width)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _))) ?_
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hcap hm0) ?_
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (mixFraction_mul_cap hw0 hw1 width)) hfl

set_option maxRecDepth 100000 in
theorem temporalFaces_one : (temporalFaces 1).length = 3 := by decide

theorem mixFraction_le_width1 {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    mixFraction hw0 hw1 1 ≤ Q'.mkPos 1 32768 (by decide) := by
  have h := mixFraction_le_pow hw0 hw1 1
  rw [temporalFaces_one] at h
  exact Q'.le_trans' _ _ _ h (by decide)

/-- Rate form: `1 − 32^{-n} ≤ mixRate`. -/
theorem mixRate_ge {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat) :
    1 + -(thirtySecond ^ (temporalFaces width).length) ≤ mixRate hw0 hw1 width :=
  Q'.add_le_add (Q'.le_refl' 1) (Q'.neg_le_neg (mixFraction_le_pow hw0 hw1 width))

end YMGap.Continuum.MixRateMarginScaling

#print axioms YMGap.Continuum.MixRateMarginScaling.mixFraction_le_pow
#print axioms YMGap.Continuum.MixRateMarginScaling.temporalFaces_one
#print axioms YMGap.Continuum.MixRateMarginScaling.mixFraction_le_width1
#print axioms YMGap.Continuum.MixRateMarginScaling.mixRate_ge
