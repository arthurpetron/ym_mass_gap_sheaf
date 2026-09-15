/-
# Arbitrarily accurate collar cancellation relative to ORIGINAL spectators

At the existing nome 1/1024, the actual translated upper collar has
H=1+R with a certified cap |R|<=1/262144<=1/2, every K and half.
Finite geometric corrections have cap 2 and residual cap 2^(-n).
They remain original shared-variable polynomials, not pointwise inverses.

An arbitrary supported square S^2 may stay INSIDE the original positive
spectator background. Every corrected signed insertion has a geometric
error relative to that SAME mass; for S on the probe links, this mass is
exactly Haar(S^2)*Zsp. Correction order depends on the insertion cap and
requested relative tolerance, not K, half or a partition reciprocal.
The corrected square norm loses at most a factor 4, independently of n.

These are actual integral estimates. The correction changes the insertion;
this does not yet construct a fixed-observable OS test, surviving general
packet floor, thermodynamic separating family or transfer inverse. The
nome is fixed: no beta/spacing-uniform continuum result is claimed.
-/

import YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
import YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin

namespace YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes
open YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground
open YMGap.Continuum.BF4ExactSlabBulkProbeScalarBackground
open YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval
open YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin
open YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))
local notation "hw" => Q'.le_of_lt nome_pos
local notation "hw1" => Q'.le_of_lt nome_lt_one

def collarRemainder (K half : Nat) : RatPoly :=
  productPerturbation nome (centralExtent half) K (reflectedCollarIds half)

theorem collar_heat_pin (K half : Nat) : RatPolyCoeffEqv (upperCollarHeat nome K half)
    (polyAdd polyOne (collarRemainder K half)) := product_eq_one_add nome (centralExtent half) K _

/-- The existing exact-rational collar estimate, with a deliberately coarser geometric rate. -/
theorem collar_cap_half : productErrorCap nome 24 ≤ HalfPow.half :=
  Q'.le_trans' _ _ _ existingNome_collar_cap (by decide : Q'.invSucc 262143 ≤ HalfPow.half)

def collarRemainderInterval (K half : Nat) : Interval (blocks half) (collarRemainder K half) (productErrorCap nome 24) :=
  reflectedCollarInterval hw hw1 existingNome_guards.1 K half

def collarCorrector (K half n : Nat) : RatPoly := corrector (collarRemainder K half) n
def collarResidual (K half n : Nat) : RatPoly := residual (collarRemainder K half) n

theorem collar_cancellation (K half n : Nat) : RatPolyCoeffEqv
    (polyAdd (polyMul (upperCollarHeat nome K half) (collarCorrector K half n)) (collarResidual K half n)) polyOne :=
  (((collar_heat_pin K half).mul_right _).add (RatPolyCoeffEqv.refl _)).trans (cancellation _ n)

def collarCorrectorInterval (K half n : Nat) : Interval (blocks half) (collarCorrector K half n) 2 :=
  correctorInterval (collarRemainderInterval K half) collar_cap_half n

def collarResidualInterval (K half n : Nat) : Interval (blocks half) (collarResidual K half n) (HalfPow.half^n) :=
  residualInterval ((collarRemainderInterval K half).weaken collar_cap_half) n

/-- The actual selected polynomial square remains inside the positive measure. -/
def squareBackground (K half : Nat) (S : RatPoly) : RatPoly :=
  polyMul (positiveBackground nome K half) (polyMul S S)

def squareBackgroundCertificate (K half : Nat) {S : RatPoly} (hS : SupportedQuaternionBlocks (blocks half) S) :
    Certificate (blocks half) (squareBackground K half S) :=
  (backgroundCertificate hw hw1 existingNome_guards.1 (Q'.le_of_lt existingNome_guards.2) K half).mul (.square S hS)

theorem squareBackground_mass (K half : Nat) {S : RatPoly} (hS : SupportedQuaternionBlocks (blocks half) S)
    (hlS : LinkLocal (centralExtent half) (probeLinks half) S) :
    quaternionHaar (blocks half) (squareBackground K half S) ≈
      quaternionHaar (blocks half) (polyMul S S) * backgroundMass nome K half :=
  background_local_moment hw K half (supported_polyMul hS hS) (hlS.mul hlS)

def referenceMoment (K half : Nat) (S p : RatPoly) : Q' :=
  quaternionHaar (blocks half) (polyMul (squareBackground K half S) p)

def correctedMoment (K half n : Nat) (S p : RatPoly) : Q' :=
  quaternionHaar (blocks half) (polyMul (squareBackground K half S)
    (polyMul p (polyMul (upperCollarHeat nome K half) (collarCorrector K half n))))

/-- The coefficient c*2^(-n) has no heat-cutoff or volume argument. -/
theorem correctedMoment_error (K half n : Nat) {S p : RatPoly} {c : Q'}
    (hS : SupportedQuaternionBlocks (blocks half) S) (P : Interval (blocks half) p c) :
    Q'.abs (correctedMoment K half n S p + -(referenceMoment K half S p)) ≤
      (c*HalfPow.half^n)*quaternionHaar (blocks half) (squareBackground K half S) :=
  relative_error (squareBackgroundCertificate K half hS) P (collar_heat_pin K half)
    (upperCollarHeat_supported nome K half) (collarRemainderInterval K half) collar_cap_half n

theorem correctedMoment_local_error (K half n : Nat) {S p : RatPoly} {c : Q'}
    (hS : SupportedQuaternionBlocks (blocks half) S) (hlS : LinkLocal (centralExtent half) (probeLinks half) S)
    (P : Interval (blocks half) p c) :
    Q'.abs (correctedMoment K half n S p + -(referenceMoment K half S p)) ≤
      (c*HalfPow.half^n)*(quaternionHaar (blocks half) (polyMul S S)*backgroundMass nome K half) :=
  Q'.le_trans' _ _ _ (correctedMoment_error K half n hS P)
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (squareBackground_mass K half hS hlS)))

/-- Chosen relative accuracy with no reciprocal floor and no volume-dependent degree. -/
theorem correctedMoment_atOrder (K half : Nat) {S p : RatPoly} {c : Q'}
    (hS : SupportedQuaternionBlocks (blocks half) S) (P : Interval (blocks half) p c)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Q'.abs (correctedMoment K half (correctionOrder c P.nonnegative epsilon) S p + -(referenceMoment K half S p)) ≤
      epsilon*quaternionHaar (blocks half) (squareBackground K half S) :=
  relative_error_atOrder (squareBackgroundCertificate K half hS) P (collar_heat_pin K half)
    (upperCollarHeat_supported nome K half) (collarRemainderInterval K half) collar_cap_half epsilon he

theorem correctedMoment_local_atOrder (K half : Nat) {S p : RatPoly} {c : Q'}
    (hS : SupportedQuaternionBlocks (blocks half) S) (hlS : LinkLocal (centralExtent half) (probeLinks half) S)
    (P : Interval (blocks half) p c) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Q'.abs (correctedMoment K half (correctionOrder c P.nonnegative epsilon) S p + -(referenceMoment K half S p)) ≤
      epsilon*(quaternionHaar (blocks half) (polyMul S S)*backgroundMass nome K half) :=
  Q'.le_trans' _ _ _ (correctedMoment_atOrder K half hS P epsilon he)
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (squareBackground_mass K half hS hlS)))

/-- Uniform in correction degree, retaining the same selected square and spectators. -/
theorem correctedTest_square_bound (K half n : Nat) {S p : RatPoly}
    (hS : SupportedQuaternionBlocks (blocks half) S) (hp : SupportedQuaternionBlocks (blocks half) p) :
    quaternionHaar (blocks half) (polyMul (squareBackground K half S)
      (polyMul (polyMul p (collarCorrector K half n)) (polyMul p (collarCorrector K half n)))) ≤
      4 * quaternionHaar (blocks half) (polyMul (squareBackground K half S) (polyMul p p)) :=
  corrected_square_bound (squareBackgroundCertificate K half hS) hp (collarRemainderInterval K half) collar_cap_half n

end YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection

#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.collarRemainder
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.collar_heat_pin
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.collar_cap_half
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.collarRemainderInterval
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.collarCorrector
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.collarResidual
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.collar_cancellation
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.collarCorrectorInterval
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.collarResidualInterval
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.squareBackground
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.squareBackgroundCertificate
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.squareBackground_mass
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.referenceMoment
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.correctedMoment
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.correctedMoment_error
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.correctedMoment_local_error
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.correctedMoment_atOrder
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.correctedMoment_local_atOrder
#print axioms YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection.correctedTest_square_bound
