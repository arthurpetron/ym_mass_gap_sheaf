/-
# Reciprocal parameters for the actual shared-link star window

The constants below are exactly the lower and upper star bounds used by the
actual two-exterior comparison. The retained face floor and prefix cap imply
an explicit positive finite window, hence the existing finite-polynomial
reciprocal construction applies. This is a finite normalizer approximation
parameter, not an influence or physical-gap estimate.
-/

import YMGap.Continuum.BF4ExactSlabCrossExteriorStar
import YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
import YMGap.Continuum.BF4ExactSlabStarRateObstruction
import YMGap.Continuum.QuaternionHaarPositiveWindowInverse

namespace YMGap.Continuum.BF4ExactSlabStarReciprocalParameters

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabCrossExteriorStar
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
open YMGap.Continuum.BF4ExactSlabStarRateObstruction
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity

private theorem pow_mono {x y : Q'} (hx : (0 : Q') ≤ x) (hxy : x ≤ y) :
    ∀ n : Nat, x ^ n ≤ y ^ n
  | 0 => Q'.le_refl' 1
  | n + 1 => Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hxy (Q'.pow_nonneg x hx n))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (pow_mono hx hxy n)
        (Q'.le_trans' _ _ _ hx hxy))

/-- The upper constant in the actual shared-link star comparison is strictly
positive at every rational nome `0<w<1`. -/
theorem starUpper_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (extent : Nat) (link : Z4Link) :
    (0 : Q') < starUpper w extent link := by
  unfold starUpper
  apply HKPos.pow_pos
  exact Q'.pos_of_lt_of_le (by decide : (0 : Q') < (1 : Q'))
    (prefixCap_ge_one hw0 hw1)

/-- The actual lower and upper constants are ordered for the full incident
face count, not merely for a one-face window. -/
theorem starLower_le_starUpper {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (extent : Nat) (link : Z4Link) :
    starLower w extent link ≤ starUpper w extent link := by
  unfold starLower starUpper
  apply pow_mono (Q'.le_of_lt (headFloor_positive hw0 hw1))
  exact Q'.le_trans' _ _ _ (headFloor_le_oneThirtySecond hw0 hw1)
    (Q'.le_trans' _ _ _ (by decide : Q'.mkPos 1 32 (by decide) ≤ (1 : Q'))
      (prefixCap_ge_one hw0 hw1))

/-- The geometric error ratio supplied to the existing polynomial reciprocal
is computed from this same actual star lower/upper pair. -/
def starRadius {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (link : Z4Link) : Q' :=
  QuaternionHaarPositiveWindowInverse.radius (starLower w extent link)
    (starUpper w extent link) (starUpper_positive hw0 hw1 extent link)

theorem starRadius_nonnegative {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (extent : Nat) (link : Z4Link) :
    (0 : Q') ≤ starRadius hw0 hw1 extent link :=
  QuaternionHaarPositiveWindowInverse.radius_nonnegative
    (starUpper_positive hw0 hw1 extent link)
    (starLower_le_starUpper hw0 hw1 extent link)

theorem starRadius_lt_one {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (extent : Nat) (link : Z4Link) :
    starRadius hw0 hw1 extent link < (1 : Q') :=
  QuaternionHaarPositiveWindowInverse.radius_lt_one
    (starLower_positive hw0 hw1 extent link)
    (starUpper_positive hw0 hw1 extent link)

/-- Explicit finite reciprocal cutoff for the actual shared-link star window. -/
def starApproximationCutoff {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (extent : Nat) (link : Z4Link) (epsilon : Q') : Nat :=
  QuaternionHaarPositiveWindowInverse.approximationCutoff
    (starLower w extent link) (starUpper w extent link)
    (starUpper_positive hw0 hw1 extent link) epsilon

end YMGap.Continuum.BF4ExactSlabStarReciprocalParameters

#print axioms YMGap.Continuum.BF4ExactSlabStarReciprocalParameters.starUpper_positive
#print axioms YMGap.Continuum.BF4ExactSlabStarReciprocalParameters.starLower_le_starUpper
#print axioms YMGap.Continuum.BF4ExactSlabStarReciprocalParameters.starRadius
#print axioms YMGap.Continuum.BF4ExactSlabStarReciprocalParameters.starRadius_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabStarReciprocalParameters.starRadius_lt_one
#print axioms YMGap.Continuum.BF4ExactSlabStarReciprocalParameters.starApproximationCutoff
