/-
# Quantified perturbation of the actual ORIGINAL whole-forest amplitudes

Each interacting amplitude is its full-spectator reference plus an explicit
signed collar error. For an upper observable of interval cap c, the unit
error is bounded by c*eta(w)*Zsp and the scalar error by
lambda(w)*c*eta(w)*Zsp/256, eta(w)=(1+128*w^3)^24-1.
The actual fundamental probe has c=2 and the unit has c=1. The cutoff and
volume do not occur in these relative coefficients; the nome guards remain.
No interacting determinant sign or normalized thermodynamic floor is assumed.
-/

import YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin

namespace YMGap.Continuum.BF4ExactSlabBulkProbeAmplitudePerturbation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests
open YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference
open YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground
open YMGap.Continuum.BF4ExactSlabBulkProbeScalarBackground
open YMGap.Continuum.BF4ExactSlabBulkProbeLocalIntervals
open YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval
open YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin
open YMGap.Continuum.BF4ExactSlabPartialInterfaceTests
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels (channelWeightPower)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

def upperCollarError (w : Q') (K half : Nat) : RatPoly :=
  productPerturbation w (centralExtent half) K (reflectedCollarIds half)

theorem collar_moment_split (w : Q') (K half : Nat) (B p : RatPoly) :
    quaternionHaar (blocks half) (polyMul B (polyMul p (upperCollarHeat w K half))) ≈
      quaternionHaar (blocks half) (polyMul B p) +
        quaternionHaar (blocks half) (polyMul B (polyMul p (upperCollarError w K half))) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc B p (upperCollarHeat w K half)).symm)
    (Q'.eqv_trans _ _ _ (moment_eq_reference_add_error w (centralExtent half) K (reflectedCollarIds half) (blocks half) (polyMul B p))
      (Q'.add_eqv_congr_left _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc B p (upperCollarError w K half)))))

def unitError (w : Q') (K : Nat) {half : Nat} (e : PlaquetteExpression half) : Q' :=
  quaternionHaar (blocks half) (polyMul (positiveBackground w K half) (polyMul (upper e) (upperCollarError w K half)))

def scalarError (w : Q') (K : Nat) {half : Nat} (e : PlaquetteExpression half) : Q' :=
  channelWeightPower w 4 * quaternionHaar (blocks half)
    (polyMul (scalarBackground w K half) (polyMul (polyMul (upper e) (upperScalar half)) (upperCollarError w K half)))

variable {w : Q'} (hw : (0 : Q') ≤ w)
include hw

theorem unitAmplitude_split (K : Nat) (hK : 1 ≤ K) {half : Nat} (e : PlaquetteExpression half) :
    testAmplitude hw K hK half (localChoice half none) (spectatorHeat w K half) e ≈
      unitAmplitudeReference w K half (lower e) + unitError w K e :=
  Q'.eqv_trans _ _ _ (unitAmplitude_collar_pin hw K hK e)
    (Q'.eqv_trans _ _ _ (collar_moment_split w K half _ _)
      (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (unitReference_presentation hw K half _ _
        (lower_reflection e) (upper_supported e)))))

theorem scalarAmplitude_split (K : Nat) (hK : 1 ≤ K) {half : Nat} (e : PlaquetteExpression half) :
    testAmplitude hw K hK half (localChoice half (some (false,false))) (scalarTest w K half) e ≈
      scalarAmplitudeReference w K half (lower e) + scalarError w K e :=
  Q'.eqv_trans _ _ _ (scalarAmplitude_collar_pin hw K hK e)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (collar_moment_split w K half _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
        (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (scalarReference_presentation hw K half _ _
          (lower_reflection e) (upper_supported e))))))

theorem weight_nonnegative : ∀ n, (0 : Q') ≤ channelWeightPower w n
  | 0 => Q'.zero_le_one
  | n+1 => Q'.mul_nonneg _ _ (coeffW_nonneg hw 1) (weight_nonnegative n)

variable (hw1 : w ≤ (1 : Q')) (hsmall : heatRatio w ≤ HalfPow.half) (hdelta : heatRemainderBound w ≤ 1)
include hw1 hsmall hdelta

/-- Relative unit-test error with a supplied, constructive local interval. -/
theorem unitError_bound (K : Nat) {half : Nat} (e : PlaquetteExpression half) {c : Q'}
    (P : Interval (blocks half) (upper e) c) :
    Q'.abs (unitError w K e) ≤ (c * productErrorCap w 24) * backgroundMass w K half :=
  Q'.le_trans' _ _ _
    ((P.mul (reflectedCollarInterval hw hw1 hsmall K half)).weighted_haar_bound (backgroundCertificate hw hw1 hsmall hdelta K half))
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (background_integral_pin hw K half)))

/-- The scalar square remains inside the certified background, keeping its exact mass. -/
theorem scalarError_bound (K : Nat) {half : Nat} (e : PlaquetteExpression half) {c : Q'}
    (P : Interval (blocks half) (upper e) c) :
    Q'.abs (scalarError w K e) ≤
      channelWeightPower w 4 * ((c * productErrorCap w 24) * (Q'.invSucc 255 * backgroundMass w K half)) := by
  have hlocal := ((P.mul (upperScalarInterval half)).changeCap (Q'.mul_one_eqv c)).mul
    (reflectedCollarInterval hw hw1 hsmall K half)
  have h := scalar_weighted_bound hw hw1 hsmall hdelta K half hlocal
  have hs := ExpNeg.abs_mul_le (channelWeightPower w 4)
    (quaternionHaar (blocks half) (polyMul (scalarBackground w K half)
      (polyMul (polyMul (upper e) (upperScalar half)) (upperCollarError w K half))))
  rw [ExpNeg.abs_of_nonneg (weight_nonnegative hw 4)] at hs
  exact Q'.le_trans' _ _ _ hs (Q'.mul_le_mul_of_nonneg_left _ _ _ h (weight_nonnegative hw 4))

theorem unitProbe_error_bound (K half : Nat) :
    Q'.abs (unitError w K (bulkProbe half)) ≤ (2 * productErrorCap w 24) * backgroundMass w K half :=
  unitError_bound hw hw1 hsmall hdelta K _ (upperProbeInterval half)

theorem unitUnit_error_bound (K half : Nat) :
    Q'.abs (unitError w K (.unit : PlaquetteExpression half)) ≤ productErrorCap w 24 * backgroundMass w K half :=
  Q'.le_trans' _ _ _ (unitError_bound hw hw1 hsmall hdelta K (.unit : PlaquetteExpression half) (Interval.one _))
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv _)))

theorem scalarProbe_error_bound (K half : Nat) :
    Q'.abs (scalarError w K (bulkProbe half)) ≤
      channelWeightPower w 4 * ((2 * productErrorCap w 24) * (Q'.invSucc 255 * backgroundMass w K half)) :=
  scalarError_bound hw hw1 hsmall hdelta K _ (upperProbeInterval half)

theorem scalarUnit_error_bound (K half : Nat) :
    Q'.abs (scalarError w K (.unit : PlaquetteExpression half)) ≤
      channelWeightPower w 4 * (productErrorCap w 24 * (Q'.invSucc 255 * backgroundMass w K half)) :=
  Q'.le_trans' _ _ _ (scalarError_bound hw hw1 hsmall hdelta K (.unit : PlaquetteExpression half) (Interval.one _))
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv _))))

end YMGap.Continuum.BF4ExactSlabBulkProbeAmplitudePerturbation

#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeAmplitudePerturbation.upperCollarError
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeAmplitudePerturbation.collar_moment_split
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeAmplitudePerturbation.unitError
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeAmplitudePerturbation.scalarError
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeAmplitudePerturbation.unitAmplitude_split
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeAmplitudePerturbation.scalarAmplitude_split
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeAmplitudePerturbation.weight_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeAmplitudePerturbation.unitError_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeAmplitudePerturbation.scalarError_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeAmplitudePerturbation.unitProbe_error_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeAmplitudePerturbation.unitUnit_error_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeAmplitudePerturbation.scalarProbe_error_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeAmplitudePerturbation.scalarUnit_error_bound
