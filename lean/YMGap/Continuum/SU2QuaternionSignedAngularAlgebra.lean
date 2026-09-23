/-
# Algebra of finite signed angular directions

The finite signed direction already used by the original heat response is a
derivation.  These coefficient identities expose its linearity, Leibniz rule,
and iterated product rule without adding analytic assumptions.
-/

import YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound
import YMGap.Continuum.QuaternionHaarProductLogCurvature

namespace YMGap.Continuum.SU2QuaternionSignedAngularAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSquareCertificate

private theorem direction_congr {n : Nat} (terms : List (AngularTerm n))
    {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (signedAngularDirection terms p)
      (signedAngularDirection terms q) := by
  induction terms with
  | nil => exact .refl _
  | cons term rest ih =>
      exact ((angularDerivative_congr _ _ h).smul term.coefficient).add ih

/-- A finite signed angular direction is additive. -/
theorem signedAngularDirection_add {n : Nat} (terms : List (AngularTerm n))
    (p q : RatPoly) :
    RatPolyCoeffEqv (signedAngularDirection terms (polyAdd p q))
      (polyAdd (signedAngularDirection terms p) (signedAngularDirection terms q)) := by
  induction terms with
  | nil =>
      simp only [signedAngularDirection]
      exact (RatPolyCoeffEqv.add_zero polyZero).symm
  | cons term rest ih =>
      simp only [signedAngularDirection, applyAngularTerm]
      refine ((((angularDerivative_add _ _ p q).smul term.coefficient).trans
        (RatPolyCoeffEqv.smul_add term.coefficient _ _)).add ih).trans ?_
      exact RatPolyCoeffEqv.four_add_swap _ _ _ _

/-- A finite signed angular direction commutes with rational scaling. -/
theorem signedAngularDirection_smul {n : Nat} (terms : List (AngularTerm n))
    (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (signedAngularDirection terms (polySmul c p))
      (polySmul c (signedAngularDirection terms p)) := by
  induction terms with
  | nil =>
      simp only [signedAngularDirection]
      exact (RatPolyCoeffEqv.smul_zero c).symm
  | cons term rest ih =>
      simp only [signedAngularDirection, applyAngularTerm]
      have hhead : RatPolyCoeffEqv
          (polySmul term.coefficient
            (polySmul c (angularDerivative
              (4*term.block.val+term.first.val) (4*term.block.val+term.second.val) p)))
          (polySmul c
            (polySmul term.coefficient (angularDerivative
              (4*term.block.val+term.first.val) (4*term.block.val+term.second.val) p))) :=
        (RatPolyCoeffEqv.smul_assoc term.coefficient c _).trans
          ((RatPolyCoeffEqv.smul_coefficient
            (Q'.mul_comm_eqv term.coefficient c) _).trans
            (RatPolyCoeffEqv.smul_assoc c term.coefficient _).symm)
      refine ((((angularDerivative_smul _ _ c p).smul term.coefficient).trans hhead).add ih).trans ?_
      exact (RatPolyCoeffEqv.smul_add c _ _).symm

/-- Leibniz rule for the complete finite signed direction. -/
theorem signedAngularDirection_mul {n : Nat} (terms : List (AngularTerm n))
    (p q : RatPoly) :
    RatPolyCoeffEqv (signedAngularDirection terms (polyMul p q))
      (polyAdd
        (polyMul (signedAngularDirection terms p) q)
        (polyMul p (signedAngularDirection terms q))) := by
  induction terms with
  | nil =>
      simp only [signedAngularDirection]
      exact (RatPolyCoeffEqv.zero_add polyZero).symm.trans
        (RatPolyCoeffEqv.add
          (RatPolyCoeffEqv.mul_zero_left q)
          (RatPolyCoeffEqv.mul_zero_right p)).symm
  | cons term rest ih =>
      simp only [signedAngularDirection, applyAngularTerm]
      have hterm := ((angularDerivative_mul
        (4*term.block.val+term.first.val) (4*term.block.val+term.second.val) p q).smul term.coefficient).trans
        ((RatPolyCoeffEqv.smul_add term.coefficient _ _).trans
          ((RatPolyCoeffEqv.polyMul_smul_left term.coefficient _ _).symm.add
            (RatPolyCoeffEqv.polyMul_smul_right term.coefficient _ _).symm))
      refine (hterm.add ih).trans ?_
      exact coeffEvalExpr_eqv_of_normalize_eq
        (.add (.add (.mul (.var 0) (.var 5)) (.mul (.var 4) (.var 1)))
          (.add (.mul (.var 2) (.var 5)) (.mul (.var 4) (.var 3))))
        (.add (.mul (.add (.var 0) (.var 2)) (.var 5))
          (.mul (.var 4) (.add (.var 1) (.var 3)))) (by decide)
        (fun | 0 => applyAngularTerm term p | 1 => applyAngularTerm term q
             | 2 => signedAngularDirection rest p | 3 => signedAngularDirection rest q
             | 4 => p | _ => q)

/-- Iterated Leibniz rule.  The middle term is represented as multiplication
by the constant polynomial `cap 2`, matching the product-curvature producer. -/
theorem signedAngularDirection_second_mul {n : Nat}
    (terms : List (AngularTerm n)) (p q : RatPoly) :
    RatPolyCoeffEqv
      (signedAngularDirection terms
        (signedAngularDirection terms (polyMul p q)))
      (polyAdd
        (polyMul (signedAngularDirection terms (signedAngularDirection terms p)) q)
        (polyAdd
          (polyMul (cap 2)
            (polyMul (signedAngularDirection terms p)
              (signedAngularDirection terms q)))
          (polyMul p
            (signedAngularDirection terms (signedAngularDirection terms q))))) := by
  let D := signedAngularDirection terms
  refine (direction_congr terms (signedAngularDirection_mul terms p q)).trans ?_
  refine (signedAngularDirection_add terms (polyMul (D p) q) (polyMul p (D q))).trans ?_
  refine ((signedAngularDirection_mul terms (D p) q).add
    (signedAngularDirection_mul terms p (D q))).trans ?_
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add
      (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 3)))
      (.add (.mul (.var 1) (.var 3)) (.mul (.var 2) (.var 5))))
    (.add (.mul (.var 0) (.var 4))
      (.add (.mul (.const 2) (.mul (.var 1) (.var 3)))
        (.mul (.var 2) (.var 5))))
    (by decide)
    (fun | 0 => D (D p)
         | 1 => D p
         | 2 => p
         | 3 => D q
         | 4 => q
         | _ => D (D q))

/-- Product curvature for the ACTUAL signed derivative, rather than free
formal jet variables. Exact first/second product rules supply the join. -/
def signedAngular_productLogCurvatureLower
    {n : Nat} (terms : List (AngularTerm n)) (p q : RatPoly) (r s : Q')
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q)
    (P : Certificate n
      (polyAdd (polyMul (cap r) (polyMul p p))
        (polyAdd (polyMul p (signedAngularDirection terms (signedAngularDirection terms p)))
          (polyNeg (polyMul (signedAngularDirection terms p) (signedAngularDirection terms p))))))
    (Q : Certificate n
      (polyAdd (polyMul (cap s) (polyMul q q))
        (polyAdd (polyMul q (signedAngularDirection terms (signedAngularDirection terms q)))
          (polyNeg (polyMul (signedAngularDirection terms q) (signedAngularDirection terms q)))))) :
    let product := polyMul p q
    Certificate n
      (polyAdd (polyMul (cap (r+s)) (polyMul product product))
        (polyAdd (polyMul product (signedAngularDirection terms (signedAngularDirection terms product)))
          (polyNeg (polyMul (signedAngularDirection terms product) (signedAngularDirection terms product))))) := by
  let D := signedAngularDirection terms
  have first := signedAngularDirection_mul terms p q
  have second := signedAngularDirection_second_mul terms p q
  exact Certificate.ofCoeff
    ((RatPolyCoeffEqv.refl _).add
      ((second.mul_left (polyMul p q)).add (RatPolyCoeffEqv.neg (first.mul first))))
    (QuaternionHaarProductLogCurvature.productLogCurvatureLower
      p (D p) (D (D p)) q (D q) (D (D q)) r s hp hq P Q)

end YMGap.Continuum.SU2QuaternionSignedAngularAlgebra

#print axioms YMGap.Continuum.SU2QuaternionSignedAngularAlgebra.signedAngularDirection_add
#print axioms YMGap.Continuum.SU2QuaternionSignedAngularAlgebra.signedAngularDirection_smul
#print axioms YMGap.Continuum.SU2QuaternionSignedAngularAlgebra.signedAngularDirection_mul
#print axioms YMGap.Continuum.SU2QuaternionSignedAngularAlgebra.signedAngularDirection_second_mul
#print axioms YMGap.Continuum.SU2QuaternionSignedAngularAlgebra.signedAngular_productLogCurvatureLower
