/-
# Cleared curvature stability by actual finite jet errors

The discrepancy is a signed polynomial identity on the SAME variables.
Shared-variable interval products bound it without discarding cross terms.
An original positive floor pays the error in p squared, so the curvature
cost increases by one, not by an inverse-floor multiplier.

This is an algebraic certificate compiler. Its inputs must be constructed
for the original value, first and second jets; it supplies no analytic
estimate, cutoff, conditional score, OS passage or physical gap itself.
-/

import YMGap.Continuum.QuaternionHaarPolynomialIntervalProduct
import YMGap.Continuum.QuaternionHaarSignedInterval

namespace YMGap.Continuum.QuaternionHaarCurvatureApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_add cap_mul)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSignedInterval

/-- Cleared log-curvature in the supplied literal jets. -/
def jetCurvature (C : Q') (p dp ddp : RatPoly) : RatPoly :=
  polyAdd (polyMul (cap C) (polyMul p p))
    (polyAdd (polyMul p ddp) (polyNeg (polyMul dp dp)))

/-- Exact discrepancy after p=f+e and the two corresponding jet pins. -/
def errorPolynomial (C : Q') (p dp ddp e de dde : RatPoly) : RatPoly :=
  polyAdd
    (polyAdd
      (polyMul (cap C)
        (polyAdd (polyMul (cap 2) (polyMul p e)) (polyNeg (polyMul e e))))
      (polyAdd (polyAdd (polyMul p dde) (polyMul e ddp))
        (polyNeg (polyMul e dde))))
    (polyAdd (polyNeg (polyMul (cap 2) (polyMul dp de))) (polyMul de de))

/-- Signed errors retain one or two explicit small factors. -/
def errorCap (C U0 U1 U2 a b c : Q') : Q' :=
  C*(2*(U0*a)+a*a) + ((U0*c+a*U2)+a*c) + (2*(U1*b)+b*b)

private def env7 (C p dp ddp e de dde : RatPoly) : Nat → RatPoly
  | 0 => C
  | 1 => p
  | 2 => dp
  | 3 => ddp
  | 4 => e
  | 5 => de
  | _ => dde

private def minus (p q : PolyExpr) : PolyExpr := .add p (.neg q)
private def curvatureExpr (C p dp ddp : PolyExpr) : PolyExpr :=
  .add (.mul C (.mul p p)) (.add (.mul p ddp) (.neg (.mul dp dp)))

private theorem cap_neg (a : Q') : RatPolyCoeffEqv (polyNeg (cap a)) (cap (-a)) := by
  intro weight
  change Q'.eqv ((-(a*1))*weight []+0) (((-a)*1)*weight []+0)
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv a 1))) (Q'.eqv_refl _)

/-- Coefficientwise discrepancy identity; no independently assigned jet. -/
theorem curvature_difference_pin (C : Q') {p dp ddp f df ddf e de dde : RatPoly}
    (h0 : RatPolyCoeffEqv p (polyAdd f e))
    (h1 : RatPolyCoeffEqv dp (polyAdd df de))
    (h2 : RatPolyCoeffEqv ddp (polyAdd ddf dde)) :
    RatPolyCoeffEqv
      (polyAdd (jetCurvature C p dp ddp) (polyNeg (jetCurvature C f df ddf)))
      (errorPolynomial C p dp ddp e de dde) := by
  have recover {x y z : RatPoly} (h : RatPolyCoeffEqv x (polyAdd y z)) :
      RatPolyCoeffEqv y (polyAdd x (polyNeg z)) :=
    (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
      (minus (.add (.var 0) (.var 1)) (.var 1)) (by decide)
      (fun | 0 => y | _ => z)).trans (h.symm.add (.refl _))
  have hf := recover h0
  have hdf := recover h1
  have hddf := recover h2
  have hcurv : RatPolyCoeffEqv (jetCurvature C f df ddf)
      (jetCurvature C (polyAdd p (polyNeg e)) (polyAdd dp (polyNeg de))
        (polyAdd ddp (polyNeg dde))) :=
    ((RatPolyCoeffEqv.refl _).mul (hf.mul hf)).add
      ((hf.mul hddf).add (RatPolyCoeffEqv.neg (hdf.mul hdf)))
  refine ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg hcurv)).trans ?_
  exact coeffEvalExpr_eqv_of_normalize_eq
    (minus (curvatureExpr (.var 0) (.var 1) (.var 2) (.var 3))
      (curvatureExpr (.var 0) (minus (.var 1) (.var 4))
        (minus (.var 2) (.var 5)) (minus (.var 3) (.var 6))))
    (.add
      (.add
        (.mul (.var 0)
          (minus (.mul (.const 2) (.mul (.var 1) (.var 4)))
            (.mul (.var 4) (.var 4))))
        (minus (.add (.mul (.var 1) (.var 6)) (.mul (.var 4) (.var 3)))
          (.mul (.var 4) (.var 6))))
      (.add (.neg (.mul (.const 2) (.mul (.var 2) (.var 5))))
        (.mul (.var 5) (.var 5))))
    (by decide) (env7 (cap C) p dp ddp e de dde)

/-- Produced two-sided discrepancy interval, with shared variables allowed. -/
def error_interval {blocks : Nat} {C U0 U1 U2 a b c : Q'}
    {p dp ddp e de dde : RatPoly} (hC : (0 : Q') ≤ C)
    (P : Interval blocks p U0) (DP : Interval blocks dp U1)
    (DDP : Interval blocks ddp U2) (E : Interval blocks e a)
    (DE : Interval blocks de b) (DDE : Interval blocks dde c) :
    Interval blocks (errorPolynomial C p dp ddp e de dde) (errorCap C U0 U1 U2 a b c) :=
  (((Interval.constant blocks C hC).mul
      (((Interval.constant blocks 2 (by decide)).mul (P.mul E)).add
        (Interval.neg (E.mul E)))).add
    (((P.mul DDE).add (E.mul DDP)).add (Interval.neg (E.mul DDE)))).add
    ((Interval.neg ((Interval.constant blocks 2 (by decide)).mul (DP.mul DE))).add (DE.mul DE))

/-- The actual original floor supplies the square payment, without division. -/
def floor_square_payment {blocks : Nat} {p : RatPoly} {m B : Q'}
    (hm : (0 : Q') ≤ m) (hB : B ≤ m*m)
    (F : Certificate blocks (polyAdd p (polyNeg (cap m)))) :
    Certificate blocks (polyAdd (polyMul p p) (polyNeg (cap B))) := by
  have hsum : RatPolyCoeffEqv (polyAdd p (cap m))
      (polyAdd (polyAdd p (polyNeg (cap m))) (cap (m+m))) :=
    (coeffEvalExpr_eqv_of_normalize_eq (.add (.var 0) (.var 1))
      (.add (minus (.var 0) (.var 1)) (.add (.var 1) (.var 1)))
      (by decide) (fun | 0 => p | _ => cap m)).trans
        ((RatPolyCoeffEqv.refl _).add (cap_add m m))
  let G := Certificate.ofCoeff hsum
    (F.add (Certificate.constant blocks (m+m) (Q'.zero_le_add _ _ hm hm)))
  let H := (F.mul G).add
    (Certificate.constant blocks (m*m + -B) (Q'.sub_nonneg_of_le hB))
  -- Replace the scalar payment before the difference-of-squares identity.
  have hpay : RatPolyCoeffEqv (cap (m*m + -B))
      (polyAdd (polyMul (cap m) (cap m)) (polyNeg (cap B))) :=
    (cap_add (m*m) (-B)).symm.trans
      (((cap_mul m m).symm).add (cap_neg B).symm)
  exact Certificate.ofCoeff
    ((coeffEvalExpr_eqv_of_normalize_eq
      (minus (.mul (.var 0) (.var 0)) (.var 2))
      (.add (.mul (minus (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
        (minus (.mul (.var 1) (.var 1)) (.var 2)))
      (by decide) (fun | 0 => p | 1 => cap m | _ => cap B)).trans
        ((RatPolyCoeffEqv.refl _).add hpay.symm)) H

/-- Transfer a constructed curvature certificate through actual jet pins.
The discrepancy and floor are explicit witnesses, not opaque analytic inputs. -/
def curvature_approximation_certificate {blocks : Nat} {C m U0 U1 U2 a b c : Q'}
    {p dp ddp f df ddf e de dde : RatPoly}
    (hC : (0 : Q') ≤ C) (hm : (0 : Q') ≤ m)
    (h0 : RatPolyCoeffEqv p (polyAdd f e))
    (h1 : RatPolyCoeffEqv dp (polyAdd df de))
    (h2 : RatPolyCoeffEqv ddp (polyAdd ddf dde))
    (P : Interval blocks p U0) (DP : Interval blocks dp U1)
    (DDP : Interval blocks ddp U2) (E : Interval blocks e a)
    (DE : Interval blocks de b) (DDE : Interval blocks dde c)
    (hbudget : errorCap C U0 U1 U2 a b c ≤ m*m)
    (floor : Certificate blocks (polyAdd p (polyNeg (cap m))))
    (weighted : Certificate blocks (jetCurvature C f df ddf)) :
    Certificate blocks (jetCurvature (C+1) p dp ddp) := by
  let B := errorCap C U0 U1 U2 a b c
  let discrepancy := error_interval hC P DP DDP E DE DDE
  let D := Certificate.ofCoeff
    ((RatPolyCoeffEqv.refl _).add (curvature_difference_pin C h0 h1 h2)) discrepancy.lower
  let paid := floor_square_payment hm hbudget floor
  have hC1 : RatPolyCoeffEqv (cap (C+1)) (polyAdd (cap C) polyOne) :=
    (cap_add C 1).symm.trans ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.one_smul polyOne))
  exact Certificate.ofCoeff
    (((hC1.mul (RatPolyCoeffEqv.refl _)).add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (curvatureExpr (.add (.var 0) (.const 1)) (.var 1) (.var 2) (.var 3))
        (.add
          (.add (.var 4)
            (.add (.var 5)
              (minus (curvatureExpr (.var 0) (.var 1) (.var 2) (.var 3)) (.var 4))))
          (minus (.mul (.var 1) (.var 1)) (.var 5)))
        (by decide) (fun
          | 0 => cap C
          | 1 => p
          | 2 => dp
          | 3 => ddp
          | 4 => jetCurvature C f df ddf
          | _ => cap B))) ((weighted.add D).add paid)

end YMGap.Continuum.QuaternionHaarCurvatureApproximation

#print axioms YMGap.Continuum.QuaternionHaarCurvatureApproximation.curvature_difference_pin
#print axioms YMGap.Continuum.QuaternionHaarCurvatureApproximation.error_interval
#print axioms YMGap.Continuum.QuaternionHaarCurvatureApproximation.floor_square_payment
#print axioms YMGap.Continuum.QuaternionHaarCurvatureApproximation.curvature_approximation_certificate
