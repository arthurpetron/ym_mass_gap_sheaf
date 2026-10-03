/-
# Original weighted heat-energy order

The scalar numerator is the literal Haar-weighted coefficient fold of the
ORIGINAL conditional Laurent rows. Its actual Euler derivative sign is
constructed from the Bochner margin, positive saturated conditional heat,
and an already-certified arbitrary original output weight. One computed
margin row cutoff works for the fixed source at every nome. No derivative
sign, variance inequality, endpoint order, or independent-output premise
is supplied. The finite energy order includes the nome-one boundary by
scalar polynomial Taylor closure, not a generic carrier diagonal pullback.

This is ordinary finite conditional heat energy; it does not prove an
interacting Yang-Mills estimate, OS gap, or physical/continuum conclusion.
-/

import YMGap.Continuum.QuaternionHaarNomeRows
import YMGap.Continuum.SU2QuaternionBochnerNomeRows
import YMGap.Continuum.SU2QuaternionHeadHeatCurveSupport
import YMGap.Continuum.SU2QuaternionHeatLaurentInterpolation
import YMGap.Continuum.RationalLaurentQuadraticOrder

namespace YMGap.Continuum.SU2QuaternionWeightedHeatInterpolation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission (relativeHeat)
open YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction (conditionalHeat)
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian (partialHaarHead_congr)
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (angularSquare)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionHeadHeatGenerator (nomeHeatPolynomial finiteNomeFlow)
open YMGap.Continuum.SU2QuaternionHeadHeatCurves (angularNomeRows)
open YMGap.Continuum.SU2QuaternionHeadHeatCurveSupport (nomeHeatPolynomial_supported)
open YMGap.Continuum.SU2QuaternionAngularBochner (gamma2)
open YMGap.Continuum.SU2QuaternionBochnerNomeRows
open YMGap.Continuum.RatPolyNomeRows
open YMGap.Continuum.RatPolyNomeRowCutoff
open YMGap.Continuum.QuaternionHaarNomeRows
open YMGap.Continuum.SU2QuaternionInverseNomeKernel (inverseNomeExponent)
open YMGap.Continuum.SU2QuaternionConditionalLaurentRows
open YMGap.Continuum.SU2QuaternionHeatLaurentInterpolation
open YMGap.Continuum.RationalLaurentIntervalOrder (laurent)
open YMGap.Continuum.RationalLaurentQuadraticOrder

local infix:50 " ≈ " => Q'.eqv

/-- Literal scalar numerator of the original weighted angular interpolation. -/
def angularNumerator (tail : Nat) (w : Q') (K : Nat) (p W : RatPoly) : Poly :=
  weightedNumerator tail W (conditionalLaurentRows w K (angularNomeRows tail p))

/-- A computed cutoff of the fixed ORIGINAL Bochner row skeleton. -/
def marginCutoff (tail : Nat) (p : RatPoly) : Nat :=
  rowCutoff (tail+1) (bochnerMarginRows (nomeHeatPolynomial tail p))

private theorem scale_neg (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul c (polyNeg p)) (polyNeg (polySmul c p)) :=
  ((neg_smul p).smul c).trans
    ((RatPolyCoeffEqv.smul_assoc c (-1) p).trans
      ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv c (-1)) p).trans
        ((RatPolyCoeffEqv.smul_assoc (-1) c p).symm.trans (neg_smul _).symm)))

private theorem scale_comm (a b : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul a (polySmul b p)) (polySmul b (polySmul a p)) :=
  (RatPolyCoeffEqv.smul_assoc a b p).trans
    ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv a b) p).trans
      (RatPolyCoeffEqv.smul_assoc b a p).symm)

private theorem euler_shift (E : Nat) (A : Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (eulerRows (E+2) A) r)
      (polyAdd (evalRows (eulerRows E A) r) (polyNeg (polySmul 2 (evalRows A r)))) := by
  have hc : RatPolyCoeffEqv (polySmul (Q'.ofNat (E+2)) (evalRows A r))
      (polyAdd (polySmul (Q'.ofNat E) (evalRows A r)) (polySmul 2 (evalRows A r))) :=
    (RatPolyCoeffEqv.smul_coefficient (Q'.ofNat_add_eqv E 2) _).trans
      (RatPolyCoeffEqv.add_smul_same _ _ _).symm
  exact (evalRows_euler_pin (E+2) A r).trans
    (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg hc)).trans
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.add (.var 0) (.neg (.add (.var 1) (.var 2))))
        (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2)))
        (by decide) (fun
          | 0 => polySmul r (evalRows (derivativeRows A) r)
          | 1 => polySmul (Q'.ofNat E) (evalRows A r)
          | _ => polySmul 2 (evalRows A r))).trans
          ((evalRows_euler_pin E A r).symm.add (RatPolyCoeffEqv.refl _))))

private theorem weighted_shift_pin (blocks : Nat) (W : RatPoly) (A : Rows)
    (E : Nat) (r : Q') :
    Q'.recip (RGTransport.qpow r E) *
        (r*QPoly.eval (pderiv (weightedNumerator blocks W A)) r +
          -(Q'.ofNat (E+2)*QPoly.eval (weightedNumerator blocks W A) r)) ≈
      quaternionHaar blocks (polyMul W
        (polyAdd
          (polySmul (Q'.recip (RGTransport.qpow r E)) (evalRows (eulerRows E A) r))
          (polyNeg (polySmul 2
            (polySmul (Q'.recip (RGTransport.qpow r E)) (evalRows A r)))))) := by
  let s := Q'.recip (RGTransport.qpow r E)
  have hc : RatPolyCoeffEqv (polySmul s (evalRows (eulerRows (E+2) A) r))
      (polyAdd (polySmul s (evalRows (eulerRows E A) r))
        (polyNeg (polySmul 2 (polySmul s (evalRows A r))))) :=
    ((euler_shift E A r).smul s).trans
      ((RatPolyCoeffEqv.smul_add s _ _).trans
        ((RatPolyCoeffEqv.refl _).add
          ((scale_neg s _).trans (RatPolyCoeffEqv.neg (scale_comm s 2 _)))))
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left s _ _ (weightedNumerator_euler_eval blocks W A (E+2) r))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polyMul_smul_right blocks s W _))
      (haar_of_coeff (hc.mul_left W)))

private theorem conditional_coeff (u : Q') (K : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) : RatPolyCoeffEqv (conditionalHeat u K p) (conditionalHeat u K q) :=
  partialHaarHead_congr (h.mul_left (relativeHeat u K))

private theorem conditional_add (u : Q') (K : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (conditionalHeat u K (polyAdd p q))
      (polyAdd (conditionalHeat u K p) (conditionalHeat u K q)) := by
  unfold conditionalHeat
  have h := partialHaarHead_congr (RatPolyCoeffEqv.mul_add_right (relativeHeat u K) p q)
  rw [partialHaarHead_add] at h
  exact h

private theorem conditional_smul (u c : Q') (K : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (conditionalHeat u K (polySmul c p)) (polySmul c (conditionalHeat u K p)) :=
  (partialHaarHead_congr (RatPolyCoeffEqv.polyMul_smul_right c (relativeHeat u K) p)).trans
    (partialHaarHead_smul c _)

private theorem conditional_neg (u : Q') (K : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (conditionalHeat u K (polyNeg p)) (polyNeg (conditionalHeat u K p)) :=
  (conditional_coeff u K (neg_smul p)).trans
    ((conditional_smul u (-1) K p).trans (neg_smul _).symm)

/-- The actual scalar Laurent function is the same original weighted energy. -/
theorem angularNumerator_original_pin (tail : Nat) (w : Q') (K : Nat)
    (p W : RatPoly) (r : Q') :
    laurent (angularNumerator tail w K p W) (inverseNomeExponent K) r ≈
      quaternionHaar tail (polyMul W (angularInterpolation tail w K p r)) :=
  weightedNumerator_laurent_pin tail W
    (conditionalLaurentRows w K (angularNomeRows tail p)) (inverseNomeExponent K) r

/-- Exact cleared derivative of the ORIGINAL weighted energy divided by r^2. -/
theorem angularNumerator_euler_pin (tail : Nat) (w : Q') (K : Nat)
    (p W : RatPoly) (r : Q') :
    Q'.recip (RGTransport.qpow r (inverseNomeExponent K)) *
      (r*QPoly.eval (pderiv (angularNumerator tail w K p W)) r +
        -(Q'.ofNat (inverseNomeExponent K+2)*QPoly.eval (angularNumerator tail w K p W) r)) ≈
      quaternionHaar tail (polyMul W
        (polyAdd (angularInterpolationEuler tail w K p r)
          (polyNeg (polySmul 2 (angularInterpolation tail w K p r))))) :=
  weighted_shift_pin tail W (conditionalLaurentRows w K (angularNomeRows tail p))
    (inverseNomeExponent K) r

/-- Constructed positive Euler-minus-two-energy certificate at strict nomes.
There is no positivity assumption on the fixed finite kernel itself. -/
def angularInterpolation_margin_certificate (tail : Nat) (ht : 0 < tail)
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (hK : marginCutoff tail p ≤ K)
    (r : Q') (hwr : w < r) :
    Certificate tail (polyAdd (angularInterpolationEuler tail w K p r)
      (polyNeg (polySmul 2 (angularInterpolation tail w K p r)))) := by
  have hr : (0 : Q') < r := HeatKernelRGStep.lt_of_lt_of_le hw (Q'.le_of_lt hwr)
  let u := w*Q'.recip r
  have hu0 : (0 : Q') < u := Q'.mul_pos hw (Q'.recip_pos r)
  have hu1 : u < (1 : Q') :=
    Q'.lt_of_le_of_lt (Q'.le_of_eqv (Q'.mul_comm_eqv w (Q'.recip r)))
      (HeatKernelRGStep.lt_of_lt_of_le
        (Q'.mul_lt_mul_of_pos_left (Q'.recip_pos r) hwr)
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recip_eqv r hr))))
  let V := finiteNomeFlow tail p r
  let A := nomeHeatPolynomial tail p
  have hmargin : RatPolyCoeffEqv (conditionalHeat u K (evalRows (bochnerMarginRows A) r))
      (polyAdd (conditionalHeat u K (gamma2 V)) (polyNeg (conditionalHeat u K (angularSquare V)))) :=
    (conditional_coeff u K (evalRows_bochnerMarginRows A r)).trans
      ((conditional_add u K _ _).trans
        ((RatPolyCoeffEqv.refl _).add (conditional_neg u K _)))
  have hscale : RatPolyCoeffEqv
      (polySmul 2 (conditionalHeat u K (evalRows (bochnerMarginRows A) r)))
      (polyAdd (polySmul 2 (conditionalHeat u K (gamma2 V)))
        (polyNeg (polySmul 2 (conditionalHeat u K (angularSquare V))))) :=
    (hmargin.smul 2).trans ((RatPolyCoeffEqv.smul_add 2 _ _).trans
      ((RatPolyCoeffEqv.refl _).add (scale_neg 2 _)))
  have hid : HaarCarrierEqv tail
      (polyAdd (angularInterpolationEuler tail w K p r)
        (polyNeg (polySmul 2 (angularInterpolation tail w K p r))))
      (polySmul 2 (conditionalHeat u K (evalRows (bochnerMarginRows A) r))) :=
    (HaarCarrierEqv.add (angularInterpolation_euler tail ht w K p r hr hp)
      (HaarCarrierEqv.neg (HaarCarrierEqv.smul 2
        (RatPolyCoeffEqv.haarCarrier (angularInterpolation_original_pin tail w K p r hr))))).trans
          (RatPolyCoeffEqv.haarCarrier hscale.symm)
  exact .transport hid (.smul 2 (by decide)
    (conditional_bochnerMarginRows_certificate tail ht u hu0 hu1 K A
      (nomeHeatPolynomial_supported tail p) r hK))

/-- Actual signed scalar Euler numerator is nonnegative under EVERY already
certified same-output weight; shared spectators remain shared. -/
theorem angularNumerator_euler_nonnegative (tail : Nat) (ht : 0 < tail)
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (p W : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (hK : marginCutoff tail p ≤ K)
    (P : Certificate tail W) (r : Q') (hwr : w < r) :
    (0 : Q') ≤ r*QPoly.eval (pderiv (angularNumerator tail w K p W)) r +
      -(Q'.ofNat (inverseNomeExponent K+2)*QPoly.eval (angularNumerator tail w K p W) r) := by
  have hs := (P.mul (angularInterpolation_margin_certificate tail ht w hw K p hp hK r hwr)).haar_nonnegative
  exact Q'.nonneg_of_mul_pos (Q'.recip_pos _)
    (Q'.le_trans' _ _ _ hs (Q'.ge_of_eqv (angularNumerator_euler_pin tail w K p W r)))

/-- Derived finite original conditional energy order, including r=w and r=1.
The cutoff is source-computed, not uniform over changing sources/volumes. -/
theorem angularInterpolation_weighted_quadratic (tail : Nat) (ht : 0 < tail)
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (p W : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p)
    (hK : marginCutoff tail p ≤ K) (P : Certificate tail W)
    (r : Q') (hr : w ≤ r) (hr1 : r ≤ (1 : Q')) :
    quaternionHaar tail (polyMul W (angularInterpolation tail w K p r)) ≤
      (r*r)*quaternionHaar tail (polyMul W (angularInterpolation tail w K p 1)) := by
  have horder := laurent_quadratic_upper (angularNumerator tail w K p W) (inverseNomeExponent K)
    w hw0 hw1 (fun x hx _ => angularNumerator_euler_nonnegative tail ht w hw0 K p W hp hK P x hx)
    r hr hr1
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (angularNumerator_original_pin tail w K p W r))
    (Q'.le_trans' _ _ _ horder (Q'.le_of_eqv (Q'.mul_eqv_congr_left (r*r) _ _
      (angularNumerator_original_pin tail w K p W 1))))

end YMGap.Continuum.SU2QuaternionWeightedHeatInterpolation

#print axioms YMGap.Continuum.SU2QuaternionWeightedHeatInterpolation.angularNumerator
#print axioms YMGap.Continuum.SU2QuaternionWeightedHeatInterpolation.marginCutoff
#print axioms YMGap.Continuum.SU2QuaternionWeightedHeatInterpolation.angularNumerator_original_pin
#print axioms YMGap.Continuum.SU2QuaternionWeightedHeatInterpolation.angularNumerator_euler_pin
#print axioms YMGap.Continuum.SU2QuaternionWeightedHeatInterpolation.angularInterpolation_margin_certificate
#print axioms YMGap.Continuum.SU2QuaternionWeightedHeatInterpolation.angularNumerator_euler_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionWeightedHeatInterpolation.angularInterpolation_weighted_quadratic
