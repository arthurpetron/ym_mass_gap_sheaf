/-
# Actual unit-interval coordinate on the original Haar square carrier

A constructed unit square bound for X supplies square certificates for
Y=(1+X)/2 and 1-Y. The inverse affine coordinate 2Y-1 is pinned to X by
COEFFICIENT equality, so polynomial reconstruction survives every original
Haar insertion. No pointwise positivity constructor or new carrier is used.
-/

import YMGap.Continuum.QuaternionHaarSharpCharacterInterval
import YMGap.Continuum.QPolyRatPolySubstitutionAlgebra

namespace YMGap.Continuum.QuaternionHaarUnitIntervalCoordinate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QPolyHaarPositiveSubstitution
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra
open YMGap.Continuum.SU2ClassPolynomialAlgebra (PolyEqv)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval

def unitCoordinate : Poly := [HalfPow.half, HalfPow.half]

def unitArgument (X : RatPoly) : RatPoly := subst X unitCoordinate

private theorem subst_var (X : RatPoly) :
    RatPolyCoeffEqv (subst X [0,1]) X :=
  (subst_zero_cons X [1]).trans
    ((((subst_singleton X 1).trans (RatPolyCoeffEqv.one_smul polyOne)).mul_left X).trans
      (RatPolyCoeffEqv.mul_one X))

private theorem subst_one_minus (X : RatPoly) :
    RatPolyCoeffEqv (subst X [1,-1]) (polyAdd (cap 1) (polyNeg X)) := by
  change RatPolyCoeffEqv
    (polyAdd (cap 1) (polyMul X (subst X [-1]))) _
  apply (RatPolyCoeffEqv.refl (cap 1)).add
  exact (((subst_singleton X (-1)).mul_left X).trans
    ((RatPolyCoeffEqv.polyMul_smul_right (-1) X polyOne).trans
      ((RatPolyCoeffEqv.mul_one X).smul (-1)))).trans
    ((cap_mul_left (-1) X).symm.trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.const (-1)) (.var 0)) (.neg (.var 0)) (by decide) (fun _ => X)))

/-- Constructed witness for the actual Y, not a pointwise premise. -/
def unitArgument_certificate {blocks : Nat} {X : RatPoly}
    (P : SquareBound blocks X 1) : Certificate blocks (unitArgument X) := by
  have hscale : PolyEqv unitCoordinate (pscale HalfPow.half [1,1]) :=
    fun x => poly_eqv _ _ x (by decide)
  have hbase : RatPolyCoeffEqv (subst X [1,1]) (polyAdd (cap 1) X) :=
    (subst_one_add X).trans
      ((RatPolyCoeffEqv.one_smul polyOne).symm.add (RatPolyCoeffEqv.refl X))
  exact .ofCoeff
    ((subst_polyEqv X hscale).trans
      ((subst_pscale X HalfPow.half [1,1]).trans (hbase.smul HalfPow.half)))
    (.smul HalfPow.half HalfPow.half_nonneg (unitSquareInterval P).lower)

/-- The second Bernstein coordinate also has an actual square witness. -/
def oneMinusUnitArgument_certificate {blocks : Nat} {X : RatPoly}
    (P : SquareBound blocks X 1) :
    Certificate blocks (subst (unitArgument X) [1,-1]) := by
  have hscale : PolyEqv (compose unitCoordinate [1,-1])
      (pscale HalfPow.half [1,-1]) :=
    fun x => poly_eqv _ _ x (by decide)
  exact .ofCoeff
    (((subst_compose X unitCoordinate [1,-1]).symm.trans
      (subst_polyEqv X hscale)).trans
      ((subst_pscale X HalfPow.half [1,-1]).trans
        ((subst_one_minus X).smul HalfPow.half)))
    (.smul HalfPow.half HalfPow.half_nonneg (unitSquareInterval P).upper)

/-- The actual inverse coordinate is X under every coefficient insertion. -/
theorem unitArgument_inverse (X : RatPoly) :
    RatPolyCoeffEqv (subst (unitArgument X) [-1,2]) X := by
  have hinverse : PolyEqv (compose unitCoordinate [-1,2]) [0,1] :=
    fun x => poly_eqv _ _ x (by decide)
  exact ((subst_compose X unitCoordinate [-1,2]).symm.trans
    (subst_polyEqv X hinverse)).trans (subst_var X)

/-- Full polynomial transport retains the original X, not just its values. -/
theorem unitArgument_unshift (X : RatPoly) (p : Poly) :
    RatPolyCoeffEqv (subst (unitArgument X) (compose [-1,2] p)) (subst X p) :=
  (subst_compose (unitArgument X) [-1,2] p).trans
    (subst_arg (unitArgument_inverse X) p)

#print axioms unitCoordinate
#print axioms unitArgument
#print axioms unitArgument_certificate
#print axioms oneMinusUnitArgument_certificate
#print axioms unitArgument_inverse
#print axioms unitArgument_unshift

end YMGap.Continuum.QuaternionHaarUnitIntervalCoordinate
