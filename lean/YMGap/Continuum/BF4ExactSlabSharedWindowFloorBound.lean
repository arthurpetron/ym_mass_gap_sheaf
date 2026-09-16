/-
# Size of the existing one-face absolute heat window

The already constructed retained-head floor is at most 1/32 at every
rational nome 0<w<1. The existing prefix cap is at least one, so even a
single face's absolute window has cap at least 32 times its floor.

These statements concern the constants already used in the original
shared-face comparison. They neither estimate the actual conditional
influence nor claim a counterexample to Yang--Mills mixing or a mass gap.
No floor, cutoff, action, or operator is changed.
-/

import YMGap.Continuum.SU2RoundedHeatLower
import YMGap.Continuum.BF4ExactSlabStarRateObstruction

namespace YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison

local infix:50 " ≈ " => Q'.eqv

local instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

private theorem headFloor_twice_lower (w : Q') :
    headFloor w ≈ (2 : Q') * SU2PointwiseHeatPositiveWindow.lower w := by
  unfold headFloor SU2PointwiseHeatPositiveWindow.lower SU2PointwiseHeatStrictFloor.finiteFloor
  let F := SU2PointwiseHeatStrictFloor.floor w
  let h := HalfPow.half
  change h * F ≈ (2 : Q') * ((F * h) * h)
  calc
    h * F ≈ F * h := Q'.mul_comm_eqv _ _
    _ ≈ F * (((2 : Q') * h) * h) := Q'.mul_eqv_congr_left _ _ _ (by decide)
    _ ≈ (2 : Q') * ((F * h) * h) := by
      show _ * (_ : Int) = _ * (_ : Int)
      simp only [Cheb.mul_num, Q'.mul_den_cast]
      ac_rfl

/-- The actual retained-head floor has this uniform upper ceiling;
its strictly positive lower value still depends on the named nome. -/
theorem headFloor_le_oneThirtySecond {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    headFloor w ≤ Q'.mkPos 1 32 (by decide) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (headFloor_twice_lower w))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q')
        (SU2RoundedHeatLower.lower_le_oneSixtyFourth hw0 hw1) (by decide))
      (by decide))

/-- Even without any six-face inflation, the existing absolute cap/floor
window has spread at least 32. This is not a conditional influence bound. -/
theorem thirtyTwo_mul_headFloor_le_prefixCap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (32 : Q') * headFloor w ≤ prefixCap w :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ (32 : Q')
      (headFloor_le_oneThirtySecond hw0 hw1) (by decide))
    (Q'.le_trans' _ _ _ (by decide)
      (BF4ExactSlabStarRateObstruction.prefixCap_ge_one hw0 hw1))

end YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound

#print axioms YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound.headFloor_le_oneThirtySecond
#print axioms YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound.thirtyTwo_mul_headFloor_le_prefixCap
