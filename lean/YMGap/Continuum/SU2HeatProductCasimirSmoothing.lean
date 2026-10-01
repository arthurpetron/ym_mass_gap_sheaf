/-
# Extent-free squared smoothing of the original product attenuation

Every retained degree path is the single power with its TOTAL Casimir.
An omitted coordinate makes the actual path attenuation zero.  Applying the
division-free one-power estimate therefore costs no number-of-links factor.
This is scalar arithmetic; the concrete product-operator join is separate.
-/

import YMGap.Continuum.SU2HeatSquaredCasimirSmoothing
import YMGap.Continuum.SU2HeatProductCutoffDebt

namespace YMGap.Continuum.SU2HeatProductCasimirSmoothing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport (qpow qpow_nonneg)
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.SU2HeatProductCutoffDebt
open YMGap.Continuum.SU2HeatSquaredCasimirSmoothing

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a b c d : Q'} (ha : a ≈ b) (hb : c ≈ d) :
    a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem productAttenuation_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K : Nat) (ds : List Nat) : (0 : Q') ≤ productAttenuation w K ds := by
  have hp := productAttenuation_retained w K ds
  by_cases hr : retained K ds = true
  · simp only [hr, if_true] at hp
    exact Q'.le_trans' _ _ _ (qpow_nonneg w hw0 _) (Q'.le_of_eqv hp.symm)
  · simp only [hr] at hp
    exact Q'.le_of_eqv hp.symm

/-- Actual squared product attenuation pays the total Casimir at EVERY
cutoff, including omitted paths and both nome endpoints. No extent cost. -/
theorem product_squared_casimir_smoothing {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (ds : List Nat) :
    (((1 : Q') - w) * totalCasimir ds) *
        (productAttenuation w K ds * productAttenuation w K ds) ≤
      productAttenuation w K ds := by
  have hp := productAttenuation_retained w K ds
  have hc := totalCasimirNat_pin ds
  by_cases hr : retained K ds = true
  · simp only [hr, if_true] at hp
    have hleft : (((1 : Q')-w)*totalCasimir ds) *
        (productAttenuation w K ds*productAttenuation w K ds) ≈
        (((1 : Q')-w)*Q'.ofNat (totalCasimirNat ds)) *
          (qpow w (totalCasimirNat ds)*qpow w (totalCasimirNat ds)) :=
      mul_congr
        (Q'.mul_eqv_congr_left _ _ _ hc.symm) (mul_congr hp hp)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ (qpow_squared_casimir_smoothing hw0 hw1 _)
        (Q'.le_of_eqv hp.symm))
  · simp only [hr] at hp
    have hz : (((1 : Q')-w)*totalCasimir ds) *
        (productAttenuation w K ds*productAttenuation w K ds) ≈ 0 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (mul_congr hp hp))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv 0))
          (Q'.mul_zero_eqv _))
    exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ hz hp.symm)

#print axioms productAttenuation_nonnegative
#print axioms product_squared_casimir_smoothing

end YMGap.Continuum.SU2HeatProductCasimirSmoothing
