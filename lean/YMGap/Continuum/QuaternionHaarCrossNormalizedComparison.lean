/-
# Denominator-cleared comparison from four actual finite certificates

The original positive polynomials `p,q,D,E` may share arbitrary quaternion
coordinates. Floors for `p,E` and caps for `q,D` imply the directed
comparison `ell²*(q*D) ≤ U²*(p*E)` by a constructive telescoping certificate.
This is finite Haar-order algebra, not a conditional-kernel identity.
-/

import YMGap.Continuum.QuaternionHaarChangedProductComparison

namespace YMGap.Continuum.QuaternionHaarCrossNormalizedComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarChangedProductComparison

private theorem cross_factor_coeff (ell U : Q') (p q : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polySmul U p) (polyNeg (polySmul ell q)))
      (polyAdd
        (polyMul (cap U) (polyAdd p (polyNeg (cap ell))))
        (polyMul (cap ell) (polyAdd (cap U) (polyNeg q)))) := by
  have hscale : RatPolyCoeffEqv
      (polyAdd (polySmul U p) (polyNeg (polySmul ell q)))
      (polyAdd (polyMul (cap U) p)
        (polyNeg (polyMul (cap ell) q))) :=
    RatPolyCoeffEqv.add (cap_mul_left U p).symm
      (RatPolyCoeffEqv.neg (cap_mul_left ell q).symm)
  have hring : RatPolyCoeffEqv
      (polyAdd (polyMul (cap U) p)
        (polyNeg (polyMul (cap ell) q)))
      (polyAdd
        (polyMul (cap U) (polyAdd p (polyNeg (cap ell))))
        (polyMul (cap ell) (polyAdd (cap U) (polyNeg q)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 2) (.var 0)) (.neg (.mul (.var 3) (.var 1))))
      (.add (.mul (.var 2) (.add (.var 0) (.neg (.var 3))))
        (.mul (.var 3) (.add (.var 2) (.neg (.var 1)))))
      (by decide)
      (fun | 0 => p | 1 => q | 2 => cap U | _ => cap ell)
  exact hscale.trans hring

/-- A floor on `p` and a cap on `q` give the directed, scaled one-factor
comparison. Both terms in the construction are products of certificates. -/
def crossFactorComparison {n : Nat} (p q : RatPoly) (ell U : Q')
    (hEll : (0 : Q') ≤ ell) (hU : (0 : Q') ≤ U)
    (pFloor : Certificate n (polyAdd p (polyNeg (cap ell))))
    (qCap : Certificate n (polyAdd (cap U) (polyNeg q))) :
    Certificate n (polyAdd (polySmul U p) (polyNeg (polySmul ell q))) :=
  .ofCoeff (cross_factor_coeff ell U p q)
    (((Certificate.constant n U hU).mul pFloor).add
      ((Certificate.constant n ell hEll).mul qCap))

private theorem scaled_product_coeff (a b : Q') (p q : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polySmul a p) (polySmul b q))
      (polySmul (a*b) (polyMul p q)) :=
  (RatPolyCoeffEqv.polyMul_smul_left a p (polySmul b q)).trans
    (((RatPolyCoeffEqv.polyMul_smul_right b p q).smul a).trans
      (RatPolyCoeffEqv.smul_assoc a b (polyMul p q)))

/-- Denominator-cleared cross comparison in polynomial-scalar notation.
The four positive factors need not be independent or replica-specific. -/
def crossProductComparison_smul {n : Nat} (p q D E : RatPoly) (ell U : Q')
    (hEll : (0 : Q') ≤ ell) (hU : (0 : Q') ≤ U)
    (P : Certificate n p) (Q : Certificate n q)
    (DD : Certificate n D) (EE : Certificate n E)
    (pFloor : Certificate n (polyAdd p (polyNeg (cap ell))))
    (EFloor : Certificate n (polyAdd E (polyNeg (cap ell))))
    (qCap : Certificate n (polyAdd (cap U) (polyNeg q)))
    (DCap : Certificate n (polyAdd (cap U) (polyNeg D))) :
    Certificate n
      (polyAdd (polySmul (U*U) (polyMul p E))
        (polyNeg (polySmul (ell*ell) (polyMul q D)))) := by
  have hraw : Certificate n
      (polyAdd
        (polyMul (polySmul U p) (polySmul U E))
        (polyNeg (polyMul (polySmul ell q) (polySmul ell D)))) :=
    two_factor_gap
      (crossFactorComparison p q ell U hEll hU pFloor qCap)
      (Certificate.smul U hU EE)
      (Certificate.smul ell hEll Q)
      (crossFactorComparison E D ell U hEll hU EFloor DCap)
  exact .ofCoeff
    (RatPolyCoeffEqv.add
      (scaled_product_coeff U U p E).symm
      (RatPolyCoeffEqv.neg (scaled_product_coeff ell ell q D).symm)) hraw

/-- Original cap-polynomial form: `ell²*(q*D) ≤ U²*(p*E)` under every
supported square Haar insertion. The normalizers `D,E` remain actual
polynomials, rather than being replaced by scalar constants. -/
def crossProductComparison {n : Nat} (p q D E : RatPoly) (ell U : Q')
    (hEll : (0 : Q') ≤ ell) (hU : (0 : Q') ≤ U)
    (P : Certificate n p) (Q : Certificate n q)
    (DD : Certificate n D) (EE : Certificate n E)
    (pFloor : Certificate n (polyAdd p (polyNeg (cap ell))))
    (EFloor : Certificate n (polyAdd E (polyNeg (cap ell))))
    (qCap : Certificate n (polyAdd (cap U) (polyNeg q)))
    (DCap : Certificate n (polyAdd (cap U) (polyNeg D))) :
    Certificate n
      (polyAdd (polyMul (cap (U*U)) (polyMul p E))
        (polyNeg (polyMul (cap (ell*ell)) (polyMul q D)))) :=
  .ofCoeff
    (RatPolyCoeffEqv.add
      (cap_mul_left (U*U) (polyMul p E))
      (RatPolyCoeffEqv.neg (cap_mul_left (ell*ell) (polyMul q D))))
    (crossProductComparison_smul p q D E ell U hEll hU P Q DD EE
      pFloor EFloor qCap DCap)

#print axioms crossFactorComparison
#print axioms crossProductComparison_smul
#print axioms crossProductComparison

end YMGap.Continuum.QuaternionHaarCrossNormalizedComparison
