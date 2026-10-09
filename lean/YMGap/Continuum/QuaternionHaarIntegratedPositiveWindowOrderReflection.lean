/-
Integrated positive-window order reflection at arbitrary certified multipliers.
The premise orders the actual Haar integral of R*(p*q) for every certified R;
it does not assert that p*q has a polynomial certificate.
-/

import YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection

namespace YMGap.Continuum.QuaternionHaarIntegratedPositiveWindowOrderReflection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarPositiveWindowOrderReflection
  (reciprocalCertificate reflectionCutoff costTolerance costTolerance_pos costTolerance_pays)

local infix:50 " ≈ " => Q'.eqv

/-- Finite error from a genuinely integrated order on every certified
multiplier. The corrector insertion is certified by B and the reciprocal. -/
theorem reflection_with_error_of_positive_multiplier_order
    {blocks : Nat} {background p q : RatPoly} {ell u c : Q'}
    (hp : SU2QuaternionArbitraryHaarRadialPositivity.SupportedQuaternionBlocks blocks p)
    (hell : (0 : Q') < ell) (hu : (0 : Q') < u) (hle : ell ≤ u)
    (L : Certificate blocks (polyAdd p (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg p)))
    (B : Certificate blocks background) (Q : Interval blocks q c)
    (P : ∀ {R : RatPoly}, Certificate blocks R →
      (0 : Q') ≤ quaternionHaar blocks (polyMul R (polyMul p q)))
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (k : Nat)
    (hk : reflectionCutoff ell u hu epsilon ≤ k) :
    (0 : Q') ≤ quaternionHaar blocks (polyMul background q) +
      (epsilon*c)*quaternionHaar blocks background := by
  let g := reciprocal p u hu k
  let e := polyAdd (polyMul p g) (polyNeg polyOne)
  have hR : Certificate blocks (polyMul background g) :=
    B.mul (reciprocalCertificate hu U k)
  have hpos : (0 : Q') ≤ quaternionHaar blocks
      (polyMul background (polyMul g (polyMul p q))) :=
    Q'.le_trans' _ _ _ (P hR)
      (Q'.le_of_eqv (haar_of_coeff
        (RatPolyCoeffEqv.mul_assoc background g (polyMul p q))))
  have herr := ((approximationInterval hp hell hu hle L U epsilon hepsilon k hk).mul Q).weighted_haar_bound B
  have he : quaternionHaar blocks (polyMul background (polyMul g (polyMul p q))) ≈
      quaternionHaar blocks (polyMul background q) +
        quaternionHaar blocks (polyMul background (polyMul e q)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
      (.add (.mul (.var 0) (.var 3))
        (.mul (.var 0) (.mul (.add (.mul (.var 2) (.var 1)) (.neg (.const 1))) (.var 3))))
      (by decide) (fun | 0 => background | 1 => g | 2 => p | _ => q)))
      (quaternionHaar_append blocks _ _)
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv he))
    (Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _ (Q'.le_abs_self _) herr))

/-- Exact removal of a positive certified window multiplier from an
integrated order. No certificate for p*q is constructed or consumed. -/
theorem haar_nonnegative_of_positive_multiplier_order
    {blocks : Nat} {background p q : RatPoly} {ell u : Q'}
    (hp : SU2QuaternionArbitraryHaarRadialPositivity.SupportedQuaternionBlocks blocks p)
    (hq : SU2QuaternionArbitraryHaarRadialPositivity.SupportedQuaternionBlocks blocks q)
    (hell : (0 : Q') < ell) (hu : (0 : Q') < u) (hle : ell ≤ u)
    (L : Certificate blocks (polyAdd p (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg p)))
    (B : Certificate blocks background)
    (P : ∀ {R : RatPoly}, Certificate blocks R →
      (0 : Q') ≤ quaternionHaar blocks (polyMul R (polyMul p q))) :
    (0 : Q') ≤ quaternionHaar blocks (polyMul background q) := by
  let Q := polynomialInterval blocks q hq
  let cost := polynomialCap q * quaternionHaar blocks background
  have hc : (0 : Q') ≤ cost := Q'.mul_nonneg _ _ Q.nonnegative B.haar_nonnegative
  apply Q'.le_of_le_add_mul_invSucc 0 _ 1
  intro N
  let epsilon := Q'.invSucc N
  let inner := costTolerance cost hc epsilon
  have hi : (0 : Q') < inner := costTolerance_pos cost hc epsilon (Q'.invSucc_pos N)
  let k := reflectionCutoff ell u hu inner
  have h := reflection_with_error_of_positive_multiplier_order
    hp hell hu hle L U B Q P inner hi k (Nat.le_refl _)
  have hpay : (inner * polynomialCap q) * quaternionHaar blocks background ≤ epsilon :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (costTolerance_pays cost hc epsilon (Q'.le_of_lt (Q'.invSucc_pos N)))
  exact Q'.le_trans' _ _ _ h (Q'.add_le_add_left _ _ _
    (Q'.le_trans' _ _ _ hpay (Q'.ge_of_eqv (Q'.one_mul_eqv epsilon))))

end YMGap.Continuum.QuaternionHaarIntegratedPositiveWindowOrderReflection

#print axioms YMGap.Continuum.QuaternionHaarIntegratedPositiveWindowOrderReflection.reflection_with_error_of_positive_multiplier_order
#print axioms YMGap.Continuum.QuaternionHaarIntegratedPositiveWindowOrderReflection.haar_nonnegative_of_positive_multiplier_order
