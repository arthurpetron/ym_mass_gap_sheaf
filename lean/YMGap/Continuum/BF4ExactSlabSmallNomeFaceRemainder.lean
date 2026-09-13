/-
# Original face heat factors as a quantitatively small perturbation of one

The computed guard `(2*w^3)*R(p) <= 1/2`, with the existing coefficient
radius R(p), makes the original character majorant geometric from label one.
Consequently EVERY finite positive-label remainder is bounded by twice its
first majorant. This bound retains w and the actual face polynomial and does
not depend on the representation cutoff. No numerical nome is selected.

The actual face polynomial is one plus this computed remainder, at the
coefficient level. This is a small-nome estimate, not beta-, volume- or
spacing-uniform spectral control, nor positivity of a reflected minor.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail

namespace YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.SU2HeatCharacterPolynomialMajorant
open YMGap.Continuum.SU2HeatCharacterPolynomialTail
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local infix:50 " ≈ " => Q'.eqv

def firstRatio (w : Q') (p : RatPoly) : Q' := (2 * qpow w 3) * characterRadius p

def firstTailBound (w : Q') (p : RatPoly) : Q' := heatCharacterMajorant w p 1 * 2

theorem firstTailBound_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (p : RatPoly) :
    (0 : Q') ≤ firstTailBound w p :=
  Q'.mul_nonneg _ _ (heatCharacterMajorant_nonnegative hw p 1) (by decide)

theorem firstMajorant_geometric {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (p : RatPoly) (hsmall : firstRatio w p ≤ HalfPow.half) (k : Nat) :
    heatCharacterMajorant w p (1 + k) ≤ heatCharacterMajorant w p 1 * HalfPow.half ^ k := by
  apply CharacterTail.geom_dom (fun i => heatCharacterMajorant w p (1 + i))
    _ _ HalfPow.half_nonneg (Q'.le_refl' _)
  intro i
  rw [← Nat.add_assoc]
  exact Q'.le_trans' _ _ _ (heatCharacterMajorant_ratio hw0 hw1 p 0 _ (Nat.zero_le _))
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hsmall (heatCharacterMajorant_nonnegative hw0 p _))

private theorem geometricHead_eq (C : Q') : geoTailBase C HalfPow.half 0 ≈ C * 2 :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv C))
    (Q'.mul_eqv_congr_left C _ _ (by decide))

theorem positiveLabels_coefficientL1 {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (p : RatPoly) (hsmall : firstRatio w p ≤ HalfPow.half) (count : Nat) :
    finSum (fun i => polynomialCoefficientL1
      (polySmul (coeffW w (1 + i)) (characterPolynomial p (1 + i)))) count ≤ firstTailBound w p := by
  have hterm := ExpNeg.finSum_le_finSum_of_termwise
    (fun i => polynomialCoefficientL1 (polySmul (coeffW w (1 + i)) (characterPolynomial p (1 + i))))
    (fun i => heatCharacterMajorant w p 1 * HalfPow.half ^ i)
    (fun i => Q'.le_trans' _ _ _ (heatCharacter_coefficientL1 hw0 p (1 + i))
      (firstMajorant_geometric hw0 hw1 p hsmall i)) count
  have hgeo : finSum (fun i => heatCharacterMajorant w p 1 * HalfPow.half ^ i) count ≤
      geoTailBase (heatCharacterMajorant w p 1) HalfPow.half 0 := by
    simpa only [geoIncrBase, Nat.zero_add] using
      (geoTailBase_series_le (heatCharacterMajorant_nonnegative hw0 p 1)
        (by decide : (0 : Q') < HalfPow.half) (by decide : HalfPow.half < (1 : Q')) 0 count)
  exact Q'.le_trans' _ _ _ hterm (Q'.le_trans' _ _ _ hgeo (Q'.le_of_eqv (geometricHead_eq _)))

theorem faceTail_coefficientL1 {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (extent id K : Nat) (hsmall : firstRatio w (faceScalar extent id) ≤ HalfPow.half) :
    polynomialCoefficientL1 (faceHeatTail w extent id 1 K) ≤ firstTailBound w (faceScalar extent id) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (coefficientL1_sum_range _ K))
    (positiveLabels_coefficientL1 hw0 hw1 _ hsmall K)

theorem faceHeat_zero (w : Q') (extent id : Nat) :
    RatPolyCoeffEqv (faceHeatPolynomial w 0 extent id) polyOne := by
  rw [faceHeatPolynomial_eq_sum]
  change RatPolyCoeffEqv (polySmul 1 polyOne) polyOne
  exact RatPolyCoeffEqv.one_smul _

theorem faceHeat_zero_coefficientL1 (w : Q') (extent id : Nat) :
    polynomialCoefficientL1 (faceHeatPolynomial w 0 extent id) ≤ (1 : Q') := by
  rw [faceHeatPolynomial_eq_sum]
  change polynomialCoefficientL1 (polySmul 1 polyOne) ≤ (1 : Q')
  decide

/-- Actual original prefix equals one plus its positive-label remainder. -/
theorem faceHeat_eq_one_add (w : Q') (extent id K : Nat) :
    RatPolyCoeffEqv (faceHeatPolynomial w K extent id)
      (polyAdd polyOne (faceHeatTail w extent id 1 K)) := by
  have h := faceHeatPolynomial_cutoff_append w 0 K extent id
  rw [Nat.zero_add] at h
  rw [h]
  exact (faceHeat_zero w extent id).add (RatPolyCoeffEqv.refl _)

theorem faceHeat_coefficientL1_small {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (extent id K : Nat) (hsmall : firstRatio w (faceScalar extent id) ≤ HalfPow.half) :
    polynomialCoefficientL1 (faceHeatPolynomial w K extent id) ≤ 1 + firstTailBound w (faceScalar extent id) := by
  have h := faceHeatPolynomial_cutoff_append w 0 K extent id
  rw [Nat.zero_add] at h
  rw [h]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (coefficientL1_add _ _))
    (ExpNeg.add_le_add2 (faceHeat_zero_coefficientL1 w extent id) (faceTail_coefficientL1 hw0 hw1 extent id K hsmall))

end YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder

#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder.firstRatio
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder.firstTailBound
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder.firstTailBound_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder.firstMajorant_geometric
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder.positiveLabels_coefficientL1
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder.faceTail_coefficientL1
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder.faceHeat_zero
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder.faceHeat_zero_coefficientL1
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder.faceHeat_eq_one_add
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder.faceHeat_coefficientL1_small
