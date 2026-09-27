/-
# Two-link small-nome collar calibration

These scalar factors record the worst-case insertion bounds for at most
twelve faces. They are finite Haar weight comparisons, not a gap or decay
statement.
-/

import YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison

namespace YMGap.Continuum.BF4ExactSlabSmallNomePairCalibration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.HKPos
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate

/-- The lower twelve-face multiplier from one-face insertion. -/
def twoLinkLower (w : Q') : Q' :=
  (1 + -(heatRemainderBound w))^12

/-- The upper twelve-face multiplier from one-face insertion. -/
def twoLinkUpper (w : Q') : Q' :=
  (1 + heatRemainderBound w)^12

/-- The original face remainder is nonnegative for nonnegative nome. -/
theorem remainder_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) :
    (0 : Q') ≤ heatRemainderBound w :=
  heatRemainderBound_nonnegative hw

/-- Strict positivity of the lower collar multiplier when each insertion
factor is positive. -/
theorem twoLinkLower_positive {w : Q'}
    (hdelta : heatRemainderBound w < (1 : Q')) :
    (0 : Q') < twoLinkLower w := by
  unfold twoLinkLower
  exact HKPos.pow_pos (HKPos.one_sub_pos hdelta) 12

/-- Positivity of the upper collar multiplier for nonnegative nome. -/
theorem twoLinkUpper_positive {w : Q'} (hw : (0 : Q') ≤ w) :
    (0 : Q') < twoLinkUpper w := by
  unfold twoLinkUpper
  exact HKPos.pow_pos
    (Q'.pos_add_nonneg (by decide) (remainder_nonnegative hw)) 12

/-- Exact rational pilot calibration separating the twelve-face upper and
lower multipliers. -/
theorem existingNome_pair_calibration :
    (25 : Q') * twoLinkUpper nome < 26 * twoLinkLower nome := by
  decide

#print axioms twoLinkLower
#print axioms twoLinkUpper
#print axioms remainder_nonnegative
#print axioms twoLinkLower_positive
#print axioms twoLinkUpper_positive
#print axioms existingNome_pair_calibration

end YMGap.Continuum.BF4ExactSlabSmallNomePairCalibration
