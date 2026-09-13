/-
# Nonnegative coefficient polynomials on a certified Haar-positive variable

Horner substitution produces an actual multivariate RatPoly. A polynomial
with nonnegative rational coefficients is compiled into a square certificate
when its substituted variable already has one. Its constant coefficient is
a lower bound for the ORIGINAL normalized Haar value, even when all powers
share the same link variables. No scalar independence is used.
-/

import YMGap.Continuum.QuaternionHaarSquareCertificate
import YMGap.Continuum.Favard

namespace YMGap.Continuum.QPolyHaarPositiveSubstitution

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Exact Horner substitution into the original polynomial algebra. -/
def subst (x : RatPoly) : Poly → RatPoly
  | [] => polyZero
  | c :: p => polyAdd (polySmul c polyOne) (polyMul x (subst x p))

theorem eval_subst (rho : Nat → Q') (x : RatPoly) : ∀ p : Poly,
    evalRatPoly rho (subst x p) ≈ QPoly.eval p (evalRatPoly rho x)
  | [] => Q'.eqv_refl 0
  | c :: p => Q'.eqv_trans _ _ _ (evalRatPoly_add rho _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (evalRatPoly_smul rho _ _)
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (evalRatPoly_one rho)) (Q'.mul_one_eqv c)))
        (Q'.eqv_trans _ _ _ (evalRatPoly_mul rho _ _)
          (Q'.mul_eqv_congr_left _ _ _ (eval_subst rho x p))))

/-- The nonnegative coefficient test feeds an explicit square constructor. -/
def certificate {blocks : Nat} {x : RatPoly} (X : Certificate blocks x) :
    (p : Poly) → nonnegCoeffs p → Certificate blocks (subst x p)
  | [], _ => .ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm (.constant blocks 0 (Q'.le_refl' 0))
  | c :: p, h => by
      unfold nonnegCoeffs at h
      rw [nonnegCoeffsB, Bool.and_eq_true] at h
      have hh := h
      exact .add (.constant blocks c (of_decide_eq_true hh.1)) (X.mul (certificate X p hh.2))

/-- Normalization of the same finite quaternion Haar functional. -/
theorem haar_one (blocks : Nat) : quaternionHaar blocks polyOne ≈ (1 : Q') := by
  change (1 : Q') * quaternionHaarMono blocks [] + 0 ≈ 1
  exact Q'.eqv_trans _ _ _ (QPoly.q_add_zero_eqv _)
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (quaternionHaarMono_one blocks))

/-- Its constant coefficient is retained as a genuine integrated lower
bound. The variable is certified by squares, not assumed pointwise positive. -/
theorem eval_zero_le_haar {blocks : Nat} {x : RatPoly} (X : Certificate blocks x) :
    ∀ p : Poly, nonnegCoeffs p → QPoly.eval p 0 ≤ quaternionHaar blocks (subst x p)
  | [], _ => Q'.le_refl' 0
  | c :: p, h => by
      unfold nonnegCoeffs at h
      rw [nonnegCoeffsB, Bool.and_eq_true] at h
      have hh := h
      have htail := (X.mul (certificate X p hh.2)).haar_nonnegative
      have hconst : quaternionHaar blocks (polySmul c polyOne) ≈ c :=
        Q'.eqv_trans _ _ _ (quaternionHaar_polySmul blocks c polyOne)
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (haar_one blocks)) (Q'.mul_one_eqv c))
      have he : QPoly.eval (c :: p) 0 ≈ c :=
        Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _)) (QPoly.q_add_zero_eqv c)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hconst)
          (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ htail)
            (Q'.ge_of_eqv (quaternionHaar_append blocks _ _))))

/-- Retain the constant coefficient with ANY certified positive insertion.
This is the product-floor mechanism; the insertion may share every variable. -/
theorem eval_zero_mul_haar_le {blocks : Nat} {x z : RatPoly}
    (X : Certificate blocks x) (Z : Certificate blocks z) :
    ∀ p : Poly, nonnegCoeffs p →
      QPoly.eval p 0 * quaternionHaar blocks z ≤ quaternionHaar blocks (polyMul z (subst x p))
  | [], _ => Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.zero_mul_eqv _))
      (Q'.ge_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_zero_right z)))
  | c :: p, h => by
      unfold nonnegCoeffs at h
      rw [nonnegCoeffsB, Bool.and_eq_true] at h
      have htail := (Z.mul (X.mul (certificate X p h.2))).haar_nonnegative
      have hconst : quaternionHaar blocks (polyMul z (polySmul c polyOne))
          ≈ c * quaternionHaar blocks z :=
        Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right blocks c z polyOne)
          (Q'.mul_eqv_congr_left _ _ _ (quaternionHaar_polyMul_one_right blocks z))
      have he : QPoly.eval (c :: p) 0 ≈ c :=
        Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _)) (QPoly.q_add_zero_eqv c)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ he))
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hconst)
          (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ htail)
            (Q'.ge_of_eqv (quaternionHaar_polyMul_add_right blocks z _ _))))

end YMGap.Continuum.QPolyHaarPositiveSubstitution

#print axioms YMGap.Continuum.QPolyHaarPositiveSubstitution.subst
#print axioms YMGap.Continuum.QPolyHaarPositiveSubstitution.eval_subst
#print axioms YMGap.Continuum.QPolyHaarPositiveSubstitution.certificate
#print axioms YMGap.Continuum.QPolyHaarPositiveSubstitution.haar_one
#print axioms YMGap.Continuum.QPolyHaarPositiveSubstitution.eval_zero_le_haar
#print axioms YMGap.Continuum.QPolyHaarPositiveSubstitution.eval_zero_mul_haar_le
