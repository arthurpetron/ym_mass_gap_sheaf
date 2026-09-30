/-
# Uniform finite reciprocal-dual square bound from relative score certificates

The positive lower window controls the explicit reciprocal approximation rate,
but does not enter this polynomial square cap. The relative numerator bound
is an input certificate; this file does not produce it for a physical action.
-/

import YMGap.Continuum.QuaternionHaarPositiveWindowInverse
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.QuaternionHaarRelativeReciprocalDualNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse

/-- A ring identity for the squared-score plus multiplier-square decomposition. -/
private theorem score_square_identity (C A B G : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyMul C C)
        (polyNeg (polyMul (polyMul G B) (polyMul G B))))
      (polyAdd
        (polyMul (polyMul G G)
          (polyMul (polyAdd (polyMul C A) B)
            (polyAdd (polyMul C A) (polyNeg B))))
        (polyMul (polyMul C C)
          (polyAdd polyOne
            (polyNeg (polyMul (polyMul A G) (polyMul A G)))))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 0))
      (.neg (.mul (.mul (.var 3) (.var 2)) (.mul (.var 3) (.var 2)))))
    (.add
      (.mul (.mul (.var 3) (.var 3))
        (.mul (.add (.mul (.var 0) (.var 1)) (.var 2))
          (.add (.mul (.var 0) (.var 1)) (.neg (.var 2)))))
      (.mul (.mul (.var 0) (.var 0))
        (.add (.const 1)
          (.neg (.mul (.mul (.var 1) (.var 3))
            (.mul (.var 1) (.var 3)))))))
    (by decide) (fun | 0 => C | 1 => A | 2 => B | _ => G)

/-- The reciprocal dual has a cap independent of the polynomial's positive
window. Both signed score bounds are genuine cone certificates. -/
def reciprocal_dual_square_certificate {blocks : Nat} {A B : RatPoly}
    {ell u C : Q'} (hA : SupportedQuaternionBlocks blocks A)
    (_hB : SupportedQuaternionBlocks blocks B)
    (hell : (0 : Q') < ell) (hu : (0 : Q') < u)
    (hle : ell ≤ u) (hC : (0 : Q') ≤ C)
    (L : Certificate blocks (polyAdd A (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg A)))
    (Splus : Certificate blocks (polyAdd (polyMul (cap C) A) B))
    (Sminus : Certificate blocks (polyAdd (polyMul (cap C) A) (polyNeg B)))
    (k : Nat) :
    Certificate blocks
      (polyAdd (cap (C*C))
        (polyNeg (polyMul
          (polyMul (reciprocal A u hu k) B)
          (polyMul (reciprocal A u hu k) B)))) := by
  let G := reciprocal A u hu k
  have hG : SupportedQuaternionBlocks blocks G :=
    reciprocal_supported hA u hu k
  have hCC : (0 : Q') ≤ C*C := Q'.mul_nonneg _ _ hC hC
  have hcap : Certificate blocks (polyMul (cap C) (cap C)) :=
    Certificate.ofCoeff (cap_mul C C) (Certificate.constant blocks (C*C) hCC)
  have hscore : Certificate blocks
      (polyMul (polyAdd (polyMul (cap C) A) B)
        (polyAdd (polyMul (cap C) A) (polyNeg B))) :=
    Splus.mul Sminus
  have hfirst : Certificate blocks
      (polyMul (polyMul G G)
        (polyMul (polyAdd (polyMul (cap C) A) B)
          (polyAdd (polyMul (cap C) A) (polyNeg B)))) :=
    (Certificate.square G hG).mul hscore
  have hsecond : Certificate blocks
      (polyMul (polyMul (cap C) (cap C))
        (polyAdd polyOne
          (polyNeg (polyMul (polyMul A G) (polyMul A G))))) :=
    hcap.mul (multiplierSquareCertificate hA hell hu hle L U k)
  have hsum := hfirst.add hsecond
  apply Certificate.ofCoeff ?_ hsum
  exact ((cap_mul C C).symm.add (RatPolyCoeffEqv.refl _)).trans
    (score_square_identity (cap C) A B G)

/-- The SAME bound under every certified positive original background.
The lower window remains in the reciprocal's proof/modulus, not this cost. -/
theorem reciprocal_dual_weighted_norm_le {blocks : Nat} {A B W : RatPoly}
    {ell u C : Q'} (hA : SupportedQuaternionBlocks blocks A)
    (hB : SupportedQuaternionBlocks blocks B)
    (hell : (0 : Q') < ell) (hu : (0 : Q') < u)
    (hle : ell ≤ u) (hC : (0 : Q') ≤ C)
    (L : Certificate blocks (polyAdd A (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg A)))
    (Splus : Certificate blocks (polyAdd (polyMul (cap C) A) B))
    (Sminus : Certificate blocks (polyAdd (polyMul (cap C) A) (polyNeg B)))
    (Wpos : Certificate blocks W) (k : Nat) :
    quaternionHaar blocks (polyMul W
      (polyMul (polyMul (reciprocal A u hu k) B)
        (polyMul (reciprocal A u hu k) B))) ≤
      (C*C) * quaternionHaar blocks W := by
  let J := polyMul (reciprocal A u hu k) B
  let D := polyAdd (cap (C*C)) (polyNeg (polyMul J J))
  have hn := (Wpos.mul
    (reciprocal_dual_square_certificate hA hB hell hu hle hC L U Splus Sminus k)).haar_nonnegative
  have hid : RatPolyCoeffEqv
      (polyAdd (polyMul W (polyMul J J)) (polyMul W D))
      (polyMul (cap (C*C)) W) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
        (.mul (.var 0) (.add (.var 2) (.neg (.mul (.var 1) (.var 1))))))
      (.mul (.var 2) (.var 0)) (by decide)
      (fun | 0 => W | 1 => J | _ => cap (C*C))
  have he : Q'.eqv
      (quaternionHaar blocks (polyMul W (polyMul J J)) +
        quaternionHaar blocks (polyMul W D))
      ((C*C) * quaternionHaar blocks W) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append blocks _ _))
      (Q'.eqv_trans _ _ _ (haar_of_coeff (hid.trans (cap_mul_left (C*C) W)))
        (quaternionHaar_polySmul blocks (C*C) W))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn) (Q'.le_of_eqv he)

end YMGap.Continuum.QuaternionHaarRelativeReciprocalDualNorm

#print axioms YMGap.Continuum.QuaternionHaarRelativeReciprocalDualNorm.reciprocal_dual_square_certificate
#print axioms YMGap.Continuum.QuaternionHaarRelativeReciprocalDualNorm.reciprocal_dual_weighted_norm_le
