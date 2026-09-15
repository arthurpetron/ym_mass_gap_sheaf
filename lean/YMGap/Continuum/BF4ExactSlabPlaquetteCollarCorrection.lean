/-
# A source-computed collar-correction order for original all-spin observables

The original reflected polynomial has a certified interval cap bound(e)+1,
computed from its spins and expression syntax. This cap supplies the finite
geometric correction order at any requested relative accuracy. The exact
order is unchanged by actual bulk/time embedding.

The corrected integral approximates the EXISTING collar-removed unit-test
reference, with error epsilon times the SAME spectator partition, for every
cutoff and translated volume at nome 1/1024. No new interval assumption or
partition reciprocal is supplied. The correction changes the insertion:
admissible corrected observable/test construction and separation for a fixed
thermodynamic state remain open; this is not a transfer inverse or mass gap.
-/

import YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection
import YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCollarCorrection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection
open YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground
open YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference
open YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

variable {half : Nat}

def observableInterval (e : PlaquetteExpression half) : Interval (blocks half) (upper e) (bound e+1) :=
  Interval.ofSquare (upperBound e)

def observableOrder (e : PlaquetteExpression half) (epsilon : Q') : Nat :=
  correctionOrder (bound e+1) (Q'.zero_le_add _ _ (bound_nonnegative e) Q'.zero_le_one) epsilon

/-- The original face recoding changes neither the cap nor the chosen degree. -/
theorem observableOrder_bulkAtTime (padding : Nat) (lag : Fin (padding+1)) (e : PlaquetteExpression half) (epsilon : Q') :
    observableOrder (bulkAtTime padding lag e) epsilon = observableOrder e epsilon := by
  simp only [observableOrder, bound_bulkAtTime]

theorem unit_squareBackground (K half : Nat) : RatPolyCoeffEqv (squareBackground K half polyOne) (positiveBackground nome K half) :=
  ((RatPolyCoeffEqv.refl _).mul (RatPolyCoeffEqv.one_mul _)).trans (RatPolyCoeffEqv.mul_one _)

theorem unit_squareBackground_mass (K half : Nat) :
    quaternionHaar (blocks half) (squareBackground K half polyOne) ≈ backgroundMass nome K half :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (unit_squareBackground K half)) (background_integral_pin (Q'.le_of_lt nome_pos) K half)

theorem reference_pin (K : Nat) (e : PlaquetteExpression half) :
    referenceMoment K half polyOne (upper e) ≈ unitAmplitudeReference nome K half (lower e) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff ((unit_squareBackground K half).mul_right (upper e)))
    (Q'.eqv_symm (unitReference_presentation (Q'.le_of_lt nome_pos) K half _ _ (lower_reflection e) (upper_supported e)))

def correctedIntegral (K n : Nat) (e : PlaquetteExpression half) : Q' := correctedMoment K half n polyOne (upper e)

theorem correctedIntegral_error (K n : Nat) (e : PlaquetteExpression half) :
    Q'.abs (correctedIntegral K n e + -(unitAmplitudeReference nome K half (lower e))) ≤
      ((bound e+1)*HalfPow.half^n)*backgroundMass nome K half := by
  have hp := Q'.add_eqv_congr_left (correctedIntegral K n e) _ _ (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (reference_pin K e)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hp))
    (Q'.le_trans' _ _ _ (correctedMoment_error K half n (supported_one _) (observableInterval e))
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (unit_squareBackground_mass K half))))

/-- Only the original observable and epsilon determine the correction order. -/
theorem correctedIntegral_atOrder (K : Nat) (e : PlaquetteExpression half) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Q'.abs (correctedIntegral K (observableOrder e epsilon) e + -(unitAmplitudeReference nome K half (lower e))) ≤
      epsilon*backgroundMass nome K half := by
  have hp := Q'.add_eqv_congr_left (correctedIntegral K (observableOrder e epsilon) e) _ _
    (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (reference_pin K e)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hp))
    (Q'.le_trans' _ _ _ (correctedMoment_atOrder K half (supported_one _) (observableInterval e) epsilon he)
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (unit_squareBackground_mass K half))))

/-- One source-derived degree, EVERY original action cutoff, padding and admissible lag. -/
theorem bulk_correctedIntegral_atOrder (K padding : Nat) (lag : Fin (padding+1)) (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Q'.abs (correctedIntegral K (observableOrder e epsilon) (bulkAtTime padding lag e) +
      -(unitAmplitudeReference nome K (half+padding) (lower (bulkAtTime padding lag e)))) ≤
      epsilon*backgroundMass nome K (half+padding) := by
  have h := correctedIntegral_atOrder K (bulkAtTime padding lag e) epsilon he
  rw [observableOrder_bulkAtTime] at h
  exact h

end YMGap.Continuum.BF4ExactSlabPlaquetteCollarCorrection

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCollarCorrection.observableInterval
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCollarCorrection.observableOrder
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCollarCorrection.observableOrder_bulkAtTime
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCollarCorrection.unit_squareBackground
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCollarCorrection.unit_squareBackground_mass
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCollarCorrection.reference_pin
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCollarCorrection.correctedIntegral
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCollarCorrection.correctedIntegral_error
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCollarCorrection.correctedIntegral_atOrder
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCollarCorrection.bulk_correctedIntegral_atOrder
