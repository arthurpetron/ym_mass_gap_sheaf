/-
Core-B low-mode prefix.

The full `CrossRatioMonotone` family is uniform in the mode `s`.  This file closes its
`s = 0` member for every `0 ≤ w ≤ wH`, by reducing it to the mixed-power inequality
`w^8 wH^6 ≤ w^6 wH^8`.  It is a genuine all-coupling prefix theorem, not a finite
enumeration and not an inhabitant of the full frontier structure.
-/

import YMGap.Continuum.CoreBBridgeEndpoints
import YMGap.Continuum.DiscreteLaplaceMargin
import YMGap.Continuum.CrossRatioMonotone

namespace YMGap.Continuum.CoreBModePrefix

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.AutoconvGershgorin

private theorem mul_eqv_congr₂ {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') :
    (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem coeffW_one_square (w : Q') :
    (coeffW w 1 * coeffW w 1).eqv ((4 : Q') * qpow w 6) := by
  change (((2 : Q') * qpow w 3) * ((2 : Q') * qpow w 3)).eqv
    ((4 : Q') * qpow w 6)
  refine Q'.eqv_trans _ _ _ (mul_swap4 (2 : Q') (qpow w 3) 2 (qpow w 3)) ?_
  exact mul_eqv_congr₂ (by decide) (Q'.eqv_symm (qpow_add w 3 3))

private theorem acN_one_zero (w : Q') : (acN w 1 0).eqv 1 := by
  have h := DiscreteLaplaceMargin.acN_one w 0
  rw [coeffW_zero] at h
  exact Q'.eqv_trans _ _ _ h (Q'.one_mul_eqv 1)

private theorem acN_one_two (w : Q') :
    (acN w 1 2).eqv ((3 : Q') * qpow w 8) := by
  have h := DiscreteLaplaceMargin.acN_one w 2
  rw [coeffW_zero] at h
  refine Q'.eqv_trans _ _ _ h (Q'.one_mul_eqv (coeffW w 2))

private theorem acN_one_one_square (w : Q') :
    (acN w 1 1 * acN w 1 1).eqv ((4 : Q') * qpow w 6) := by
  have h1 := DiscreteLaplaceMargin.acN_one w 1
  rw [coeffW_zero] at h1
  have h1' : (acN w 1 1).eqv (coeffW w 1) :=
    Q'.eqv_trans _ _ _ h1 (Q'.one_mul_eqv (coeffW w 1))
  exact Q'.eqv_trans _ _ _ (mul_eqv_congr₂ h1' h1') (coeffW_one_square w)

/-- The `s = 0` member of `CrossRatioMonotone.cross`, uniformly on `[0,wH]`. -/
theorem cross_mode_zero {w : Q'} (hw0 : (0 : Q') ≤ w) (hwH : w ≤ wH) :
    (acN w 1 0 * acN w 1 2) * (acN wH 1 1 * acN wH 1 1)
      ≤ (acN wH 1 0 * acN wH 1 2) * (acN w 1 1 * acN w 1 1) := by
  have hpow : qpow w 8 * qpow wH 6 ≤ qpow w 6 * qpow wH 8 :=
    CrossRatioMonotone.qpow_cross_le hw0 hwH (show 6 ≤ 8 by decide)
  have hscaled : (12 : Q') * (qpow w 8 * qpow wH 6)
      ≤ (12 : Q') * (qpow w 6 * qpow wH 8) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpow (by decide)
  have hL0 : (acN w 1 0 * acN w 1 2).eqv ((3 : Q') * qpow w 8) := by
    refine Q'.eqv_trans _ _ _ (mul_eqv_congr₂ (acN_one_zero w) (acN_one_two w)) ?_
    exact Q'.one_mul_eqv ((3 : Q') * qpow w 8)
  have hR0 : (acN wH 1 0 * acN wH 1 2).eqv ((3 : Q') * qpow wH 8) := by
    refine Q'.eqv_trans _ _ _ (mul_eqv_congr₂ (acN_one_zero wH) (acN_one_two wH)) ?_
    exact Q'.one_mul_eqv ((3 : Q') * qpow wH 8)
  have hL :
      ((acN w 1 0 * acN w 1 2) * (acN wH 1 1 * acN wH 1 1)).eqv
        ((12 : Q') * (qpow w 8 * qpow wH 6)) := by
    refine Q'.eqv_trans _ _ _
      (mul_eqv_congr₂ hL0 (acN_one_one_square wH)) ?_
    refine Q'.eqv_trans _ _ _
      (mul_swap4 (3 : Q') (qpow w 8) 4 (qpow wH 6)) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (by decide)
  have hR :
      ((acN wH 1 0 * acN wH 1 2) * (acN w 1 1 * acN w 1 1)).eqv
        ((12 : Q') * (qpow w 6 * qpow wH 8)) := by
    refine Q'.eqv_trans _ _ _
      (mul_eqv_congr₂ hR0 (acN_one_one_square w)) ?_
    refine Q'.eqv_trans _ _ _
      (mul_swap4 (3 : Q') (qpow wH 8) 4 (qpow w 6)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right ((3 : Q') * 4) 12
        (qpow wH 8 * qpow w 6) (by decide)) ?_
    exact Q'.mul_eqv_congr_left (12 : Q') _ _
      (Q'.mul_comm_eqv (qpow wH 8) (qpow w 6))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
    (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hR))

end YMGap.Continuum.CoreBModePrefix

#print axioms YMGap.Continuum.CoreBModePrefix.cross_mode_zero
