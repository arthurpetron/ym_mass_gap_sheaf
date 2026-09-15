/-
# The geometric collar correction is an ORIGINAL admissible observable

The actual finite heat collar and geometric recursion are expressions in
the existing lower plaquette algebra. Both lower and upper evaluations
are pinned to the actual correction polynomials, with interval cap 2.
Multiplying an original observable by this expression gives a genuine
original test amplitude equal to the previously estimated corrected Haar
integral. Its relative error is therefore inherited without a new pin.

The input observable is CHANGED by the correction. Neither invariance of
the OS null quotient under multiplication nor detection of an unchanged
state is asserted. The expression depends on the heat cutoff; its cutoff
and degree limits, thermodynamic separation and transfer inverse remain
open. The fixed nome is 1/1024, not a continuum scaling trajectory.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression
import YMGap.Continuum.BF4ExactSlabPlaquetteCollarCorrection

namespace YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteHeatExpression
open YMGap.Continuum.BF4ExactSlabPlaquetteCollarCorrection
open YMGap.Continuum.BF4ExactSlabSpectatorCollarCorrection
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests
open YMGap.Continuum.BF4ExactSlabBulkProbeInteractingAmplitudes
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorReference
open YMGap.Continuum.BF4ExactSlabBulkProbePositiveBackground
open YMGap.Continuum.BF4ExactSlabBulkProbeCollarInterval
open YMGap.Continuum.BF4ExactSlabBulkProbeCollarAmplitudePin
open YMGap.Continuum.BF4ExactSlabPartialInterfaceTests (testAmplitude)
open YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))
local notation "hw" => Q'.le_of_lt nome_pos

private theorem smul_neg (p : RatPoly) : RatPolyCoeffEqv (polySmul (-1) p) (polyNeg p) :=
  (cap_mul_left (-1) p).symm.trans (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
    (by decide) (fun _ => p))

def geometricExpression {half : Nat} (R : PlaquetteExpression half) : Nat → PlaquetteExpression half
  | 0 => .smul 0 .unit
  | n+1 => .add .unit (.mul (.smul (-1) R) (geometricExpression R n))

theorem evaluate_geometric {half : Nat} (F : Nat → Nat → RatPoly) (R : PlaquetteExpression half) : ∀ n,
    RatPolyCoeffEqv (evaluate F (geometricExpression R n)) (corrector (evaluate F R) n)
  | 0 => RatPolyCoeffEqv.zero_smul _
  | n+1 => (RatPolyCoeffEqv.refl _).add ((smul_neg _).mul (evaluate_geometric F R n))

private theorem corrector_congr {R S : RatPoly} (h : RatPolyCoeffEqv R S) : ∀ n,
    RatPolyCoeffEqv (corrector R n) (corrector S n)
  | 0 => RatPolyCoeffEqv.refl _
  | n+1 => (RatPolyCoeffEqv.refl _).add ((RatPolyCoeffEqv.neg h).mul (corrector_congr h n))

def collarRExpression (K half : Nat) : PlaquetteExpression half :=
  .add (collarExpression nome K half) (.smul (-1) .unit)

private theorem subtract_one {H R : RatPoly} (h : RatPolyCoeffEqv H (polyAdd polyOne R)) :
    RatPolyCoeffEqv (polyAdd H (polyNeg polyOne)) R :=
  (h.add (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq (.add (.add (.const 1) (.var 0)) (.neg (.const 1))) (.var 0)
      (by decide) (fun _ => R))

theorem collarRExpression_lower (K half : Nat) : RatPolyCoeffEqv (lower (collarRExpression K half))
    (productPerturbation nome (centralExtent half) K (lowerCollar half)) :=
  ((collarExpression_lower nome K half).add (smul_neg _)).trans (subtract_one (product_eq_one_add nome (centralExtent half) K _))

theorem collarRExpression_upper (K half : Nat) : RatPolyCoeffEqv (upper (collarRExpression K half)) (collarRemainder K half) :=
  ((collarExpression_upper nome K half).add (smul_neg _)).trans (subtract_one (collar_heat_pin K half))

def correctionExpression (K half n : Nat) : PlaquetteExpression half := geometricExpression (collarRExpression K half) n

theorem correctionExpression_lower (K half n : Nat) : RatPolyCoeffEqv (lower (correctionExpression K half n))
    (corrector (productPerturbation nome (centralExtent half) K (lowerCollar half)) n) :=
  (evaluate_geometric _ _ n).trans (corrector_congr (collarRExpression_lower K half) n)

theorem correctionExpression_upper (K half n : Nat) :
    RatPolyCoeffEqv (upper (correctionExpression K half n)) (collarCorrector K half n) :=
  (evaluate_geometric _ _ n).trans (corrector_congr (collarRExpression_upper K half) n)

def correctionLowerInterval (K half n : Nat) : Interval (blocks half) (lower (correctionExpression K half n)) 2 :=
  .ofCoeff (lower_supported _) (correctionExpression_lower K half n)
    (correctorInterval (collarInterval hw (Q'.le_of_lt nome_lt_one) existingNome_guards.1 K half) collar_cap_half n)

def correctionUpperInterval (K half n : Nat) : Interval (blocks half) (upper (correctionExpression K half n)) 2 :=
  .ofCoeff (upper_supported _) (correctionExpression_upper K half n) (collarCorrectorInterval K half n)

def correctedExpression (K n : Nat) {half : Nat} (e : PlaquetteExpression half) : PlaquetteExpression half :=
  .mul e (correctionExpression K half n)

theorem correctedExpression_upper (K n : Nat) {half : Nat} (e : PlaquetteExpression half) :
    RatPolyCoeffEqv (upper (correctedExpression K n e)) (polyMul (upper e) (collarCorrector K half n)) :=
  (RatPolyCoeffEqv.refl _).mul (correctionExpression_upper K half n)

private theorem commute_collar (p G H : RatPoly) : RatPolyCoeffEqv (polyMul (polyMul p G) H) (polyMul p (polyMul H G)) :=
  (RatPolyCoeffEqv.mul_assoc p G H).trans ((RatPolyCoeffEqv.refl p).mul (RatPolyCoeffEqv.mul_comm G H))

/-- The existing OS test consumes the actual CHANGED original expression. -/
theorem correctedAmplitude_pin (K : Nat) (hK : 1 ≤ K) (n : Nat) {half : Nat} (e : PlaquetteExpression half) :
    testAmplitude hw K hK half (localChoice half none) (spectatorHeat nome K half) (correctedExpression K n e) ≈
      correctedIntegral K n e := by
  have hp := ((correctedExpression_upper K n e).mul_right (upperCollarHeat nome K half)).trans (commute_collar _ _ _)
  exact Q'.eqv_trans _ _ _ (unitAmplitude_collar_pin hw K hK (correctedExpression K n e))
    (haar_of_coeff ((RatPolyCoeffEqv.refl _).mul hp |>.trans
      ((unit_squareBackground K half).symm.mul (RatPolyCoeffEqv.refl _))))

/-- No supplied interval or integral pin remains for the original observable. -/
theorem correctedAmplitude_atOrder (K : Nat) (hK : 1 ≤ K) {half : Nat} (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Q'.abs (testAmplitude hw K hK half (localChoice half none) (spectatorHeat nome K half)
      (correctedExpression K (observableOrder e epsilon) e) + -(unitAmplitudeReference nome K half (lower e))) ≤
      epsilon*backgroundMass nome K half :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr
    (Q'.add_eqv_congr_right _ _ _ (correctedAmplitude_pin K hK (observableOrder e epsilon) e))))
    (correctedIntegral_atOrder K e epsilon he)

end YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector

#print axioms YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector.geometricExpression
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector.evaluate_geometric
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector.collarRExpression
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector.collarRExpression_lower
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector.collarRExpression_upper
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector.correctionExpression
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector.correctionExpression_lower
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector.correctionExpression_upper
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector.correctionLowerInterval
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector.correctionUpperInterval
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector.correctedExpression
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector.correctedExpression_upper
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector.correctedAmplitude_pin
#print axioms YMGap.Continuum.BF4ExactSlabOriginalCollarCorrector.correctedAmplitude_atOrder
