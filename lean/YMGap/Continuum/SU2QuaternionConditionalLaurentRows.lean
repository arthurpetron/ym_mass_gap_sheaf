/-
# Actual conditional heat from finite Laurent rows

The common denominator is the actual finite packet exponent. Literal row
Euler differentiation gives the inverse-nome chain rule and the input Casimir
generator, retaining the already-existing output and all shared spectators.
Only the Laurent coordinate r is required positive. No positivity, saturation,
source support, output independence or conditional variance bound is assumed.
-/

import YMGap.Continuum.RatPolyNomeRows
import YMGap.Continuum.SU2QuaternionInverseNomeKernel

namespace YMGap.Continuum.SU2QuaternionConditionalLaurentRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyPositivePrimitive (coordinate)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian (partialHaarHead_congr)
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission (relativeHeat)
open YMGap.Continuum.SU2QuaternionRelativeHeatConditionalContraction (conditionalHeat)
open YMGap.Continuum.SU2QuaternionConditionalHeatGenerator
open YMGap.Continuum.SU2QuaternionInverseNomeKernel
open YMGap.Continuum.RatPolyNomeRows
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy (angularLaplacian)
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)

local infix:50 " ≈ " => Q'.eqv

def conditionalLaurentRows (w : Q') (K : Nat) (A : Rows) : Rows :=
  mapRows partialHaarHead (mulRows (inverseNomeRows w K) A)

def conditionalLaurentValue (w : Q') (K : Nat) (A : Rows) (r : Q') : RatPoly :=
  polySmul (Q'.recip (RGTransport.qpow r (inverseNomeExponent K)))
    (evalRows (conditionalLaurentRows w K A) r)

def conditionalLaurentEuler (w : Q') (K : Nat) (A : Rows) (r : Q') : RatPoly :=
  polySmul (Q'.recip (RGTransport.qpow r (inverseNomeExponent K)))
    (evalRows (eulerRows (inverseNomeExponent K) (conditionalLaurentRows w K A)) r)

private theorem conditional_add (u : Q') (K : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (conditionalHeat u K (polyAdd p q))
      (polyAdd (conditionalHeat u K p) (conditionalHeat u K q)) := by
  unfold conditionalHeat
  have h := partialHaarHead_congr (RatPolyCoeffEqv.mul_add_right (relativeHeat u K) p q)
  rw [partialHaarHead_add] at h
  exact h

private theorem conditional_smul (u c : Q') (K : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (conditionalHeat u K (polySmul c p))
      (polySmul c (conditionalHeat u K p)) :=
  (partialHaarHead_congr (RatPolyCoeffEqv.polyMul_smul_right c (relativeHeat u K) p)).trans
    (partialHaarHead_smul c _)

private theorem conditional_coeff (u : Q') (K : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) : RatPolyCoeffEqv (conditionalHeat u K p) (conditionalHeat u K q) :=
  partialHaarHead_congr (h.mul_left (relativeHeat u K))

private theorem euler_coeff_eval (E : Nat) (a : Poly) (r : Q') :
    QPoly.eval (psub (pmul coordinate (pderiv a)) (pscale (Q'.ofNat E) a)) r ≈
      r * QPoly.eval (pderiv a) r + -(Q'.ofNat E * QPoly.eval a r) := by
  have hc : QPoly.eval coordinate r ≈ r := poly_identity_of_normal_eq
    (.add (.const 0) (.mul (.var 0) (.add (.const 1) (.mul (.var 0) (.const 0)))))
    (.var 0) (by decide) (fun _ => r)
  exact Q'.eqv_trans _ _ _ (eval_psub _ _ r)
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (eval_pmul coordinate (pderiv a) r)
        (Q'.mul_eqv_congr_right _ _ _ hc))
      (Q'.neg_eqv_congr _ _ (eval_pscale (Q'.ofNat E) a r)))

private theorem row_euler_expansion (E : Nat) (A : Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (eulerRows E A) r)
      (polySum (A.map fun a => polySmul
        (r*QPoly.eval (pderiv a.1) r + -(Q'.ofNat E*QPoly.eval a.1 r)) a.2)) := by
  induction A with
  | nil => exact .refl _
  | cons a A ih =>
      exact (RatPolyCoeffEqv.smul_coefficient (euler_coeff_eval E a.1 r) a.2).add ih

private theorem euler_zero_pin (A : Rows) (r : Q') :
    RatPolyCoeffEqv (evalRows (eulerRows 0 A) r) (polySmul r (evalRows (derivativeRows A) r)) :=
  (evalRows_euler_pin 0 A r).trans
    (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.zero_smul _))).trans
      (RatPolyCoeffEqv.add_zero _))

/-- The literal finite Laurent rows equal the ORIGINAL conditional kernel
applied to the same row source, with the existing output still retained. -/
theorem conditionalLaurentValue_original_pin (w : Q') (K : Nat) (A : Rows) (r : Q')
    (hr : (0 : Q') < r) :
    RatPolyCoeffEqv (conditionalLaurentValue w K A r)
      (conditionalHeat (w*Q'.recip r) K (evalRows A r)) := by
  let s := Q'.recip (RGTransport.qpow r (inverseNomeExponent K))
  have hp : RatPolyCoeffEqv (evalRows (conditionalLaurentRows w K A) r)
      (partialHaarHead (polyMul (evalRows (inverseNomeRows w K) r) (evalRows A r))) :=
    (evalRows_partialHaarHead (mulRows (inverseNomeRows w K) A) r).trans
      (partialHaarHead_congr (evalRows_mul (inverseNomeRows w K) A r))
  have hk : RatPolyCoeffEqv (polySmul s (evalRows (inverseNomeRows w K) r))
      (relativeHeat (w*Q'.recip r) K) := inverseNomeKernel_original_pin w r K hr
  exact (hp.smul s).trans
    ((partialHaarHead_smul s _).symm.trans
      ((partialHaarHead_congr (RatPolyCoeffEqv.polyMul_smul_left s _ _).symm).trans
        (partialHaarHead_congr (hk.mul_right (evalRows A r)))))

/-- The actual Laurent Euler derivative splits into the inverse-nome kernel
chain and the literal derivative of the ORIGINAL numerator source. -/
theorem conditionalLaurentEuler_chain_split (w : Q') (K : Nat) (A : Rows) (r : Q')
    (hr : (0 : Q') < r) :
    RatPolyCoeffEqv (conditionalLaurentEuler w K A r)
      (polyAdd
        (polySmul (-(w*Q'.recip r))
          (formalConditionalNomeDerivative (w*Q'.recip r) K (evalRows A r)))
        (conditionalHeat (w*Q'.recip r) K (polySmul r (evalRows (derivativeRows A) r)))) := by
  let s := Q'.recip (RGTransport.qpow r (inverseNomeExponent K))
  let u := w*Q'.recip r
  let N := inverseNomeRows w K
  let p := evalRows A r
  let d := polySmul r (evalRows (derivativeRows A) r)
  have hp : RatPolyCoeffEqv
      (evalRows (eulerRows (inverseNomeExponent K) (conditionalLaurentRows w K A)) r)
      (partialHaarHead (polyAdd
        (polyMul (evalRows (eulerRows (inverseNomeExponent K) N) r) p)
        (polyMul (evalRows N r) d))) :=
    (evalRows_euler_partialHaarHead (inverseNomeExponent K) (mulRows N A) r).trans
      (partialHaarHead_congr ((evalRows_euler_mul (inverseNomeExponent K) N A r).trans
        ((RatPolyCoeffEqv.refl _).add
          ((euler_zero_pin A r).mul_left (evalRows N r)))))
  have hNe : RatPolyCoeffEqv (polySmul s (evalRows (eulerRows (inverseNomeExponent K) N) r))
      (polySmul (-u) (formalConditionalKernelDerivative u K)) :=
    ((row_euler_expansion (inverseNomeExponent K) N r).smul s).trans
      (inverseNomeEuler_chain_pin w r K hr)
  have hN : RatPolyCoeffEqv (polySmul s (evalRows N r)) (relativeHeat u K) :=
    inverseNomeKernel_original_pin w r K hr
  have hscale : RatPolyCoeffEqv
      (polySmul s (polyAdd
        (polyMul (evalRows (eulerRows (inverseNomeExponent K) N) r) p)
        (polyMul (evalRows N r) d)))
      (polyAdd
        (polyMul (polySmul (-u) (formalConditionalKernelDerivative u K)) p)
        (polyMul (relativeHeat u K) d)) :=
    (RatPolyCoeffEqv.smul_add s _ _).trans
      ((((RatPolyCoeffEqv.polyMul_smul_left s _ _).symm).trans (hNe.mul_right p)).add
        (((RatPolyCoeffEqv.polyMul_smul_left s _ _).symm).trans (hN.mul_right d)))
  have hsplit : RatPolyCoeffEqv
      (partialHaarHead (polyAdd
        (polyMul (polySmul (-u) (formalConditionalKernelDerivative u K)) p)
        (polyMul (relativeHeat u K) d)))
      (polyAdd (polySmul (-u) (formalConditionalNomeDerivative u K p)) (conditionalHeat u K d)) := by
    rw [partialHaarHead_add]
    exact ((partialHaarHead_congr (RatPolyCoeffEqv.polyMul_smul_left (-u) _ _)).trans
      (partialHaarHead_smul (-u) _)).add (RatPolyCoeffEqv.refl _)
  exact (hp.smul s).trans ((partialHaarHead_smul s _).symm.trans
    ((partialHaarHead_congr hscale).trans hsplit))

private theorem negative_generator (tail : Nat) (ht : 0 < tail) (u : Q') (K : Nat) (p : RatPoly) :
    HaarCarrierEqv tail (polySmul (-u) (formalConditionalNomeDerivative u K p))
      (conditionalHeat u K (angularLaplacian p)) := by
  have hl : RatPolyCoeffEqv (polySmul (-u) (formalConditionalNomeDerivative u K p))
      (polySmul (-1) (polySmul u (formalConditionalNomeDerivative u K p))) :=
    (RatPolyCoeffEqv.smul_coefficient
      (poly_identity_of_normal_eq (.neg (.var 0)) (.mul (.const (-1)) (.var 0))
        (by decide) (fun _ => u)) _).trans ((RatPolyCoeffEqv.smul_assoc (-1) u _).symm)
  have hc : RatPolyCoeffEqv (polySmul (-1) (polyNeg (angularLaplacian p))) (angularLaplacian p) :=
    ((neg_smul _).smul (-1)).trans
      ((RatPolyCoeffEqv.smul_assoc (-1) (-1) _).trans
        ((RatPolyCoeffEqv.smul_coefficient (by decide : ((-1:Q')*(-1)) ≈ 1) _).trans
          (RatPolyCoeffEqv.one_smul _)))
  have hg := HaarCarrierEqv.smul (-1) (conditionalHeat_formal_nome_generator tail ht u K p)
  have hr : RatPolyCoeffEqv (polySmul (-1) (conditionalHeat u K (polyNeg (angularLaplacian p))))
      (conditionalHeat u K (angularLaplacian p)) :=
    (conditional_smul u (-1) K _).symm.trans (conditional_coeff u K hc)
  exact (RatPolyCoeffEqv.haarCarrier hl).trans (hg.trans (RatPolyCoeffEqv.haarCarrier hr))

/-- Genuine input-generator chain rule for the actual finite conditional
packet. No source support/saturation or output independence is needed. -/
theorem conditionalLaurentEuler_input_generator (tail : Nat) (ht : 0 < tail)
    (w : Q') (K : Nat) (A : Rows) (r : Q') (hr : (0 : Q') < r) :
    HaarCarrierEqv tail (conditionalLaurentEuler w K A r)
      (conditionalHeat (w*Q'.recip r) K
        (polyAdd (angularLaplacian (evalRows A r))
          (polySmul r (evalRows (derivativeRows A) r)))) :=
  (RatPolyCoeffEqv.haarCarrier (conditionalLaurentEuler_chain_split w K A r hr)).trans
    ((HaarCarrierEqv.add (negative_generator tail ht (w*Q'.recip r) K (evalRows A r))
      (HaarCarrierEqv.refl tail _)).trans
        (RatPolyCoeffEqv.haarCarrier (conditional_add (w*Q'.recip r) K _ _).symm))

end YMGap.Continuum.SU2QuaternionConditionalLaurentRows

#print axioms YMGap.Continuum.SU2QuaternionConditionalLaurentRows.conditionalLaurentRows
#print axioms YMGap.Continuum.SU2QuaternionConditionalLaurentRows.conditionalLaurentValue
#print axioms YMGap.Continuum.SU2QuaternionConditionalLaurentRows.conditionalLaurentEuler
#print axioms YMGap.Continuum.SU2QuaternionConditionalLaurentRows.conditionalLaurentValue_original_pin
#print axioms YMGap.Continuum.SU2QuaternionConditionalLaurentRows.conditionalLaurentEuler_chain_split
#print axioms YMGap.Continuum.SU2QuaternionConditionalLaurentRows.conditionalLaurentEuler_input_generator
