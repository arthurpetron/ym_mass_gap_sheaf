/-
# Two-sided polynomial bounds relative to a fixed base

Unlike `Interval`, the base need not be positive.  Both endpoint statements
are explicit original-Haar certificates.  Signed scalar multiplication is
implemented by exchanging the endpoints when the scalar is negative.
-/

import YMGap.Constructive.CRealExp
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound
import YMGap.Continuum.QuaternionHaarAngularCarrier

namespace YMGap.Continuum.QuaternionHaarRelativePolynomialInterval

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarAngularCarrier

structure RelativeInterval (blocks : Nat) (base p : RatPoly) (c : Q') : Type where
  lower : Certificate blocks
    (polyAdd (polyMul (cap c) base) p)
  upper : Certificate blocks
    (polyAdd (polyMul (cap c) base) (polyNeg p))

namespace RelativeInterval

def ofCoeff {blocks : Nat} {base p q : RatPoly} {c : Q'}
    (h : RatPolyCoeffEqv p q) (Q : RelativeInterval blocks base q c) :
    RelativeInterval blocks base p c where
  lower := Certificate.ofCoeff ((RatPolyCoeffEqv.refl _).add h) Q.lower
  upper := Certificate.ofCoeff
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg h)) Q.upper

def changeCap {blocks : Nat} {base p : RatPoly} {c d : Q'}
    (h : Q'.eqv c d) (P : RelativeInterval blocks base p c) :
    RelativeInterval blocks base p d := by
  have hc : RatPolyCoeffEqv (cap d) (cap c) :=
    RatPolyCoeffEqv.smul_coefficient (Q'.eqv_symm h) polyOne
  exact ⟨Certificate.ofCoeff ((hc.mul_right base).add (RatPolyCoeffEqv.refl _)) P.lower,
    Certificate.ofCoeff ((hc.mul_right base).add (RatPolyCoeffEqv.refl _)) P.upper⟩

def add {blocks : Nat} {base p q : RatPoly} {c d : Q'}
    (P : RelativeInterval blocks base p c)
    (Q : RelativeInterval blocks base q d) :
    RelativeInterval blocks base (polyAdd p q) (c+d) := by
  have hc : RatPolyCoeffEqv (cap (c+d)) (polyAdd (cap c) (cap d)) :=
    (cap_add c d).symm
  constructor
  · exact Certificate.ofCoeff (((hc.mul_right base).add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.add (.var 0) (.var 1)) (.var 2)) (.add (.var 3) (.var 4)))
        (.add (.add (.mul (.var 0) (.var 2)) (.var 3))
          (.add (.mul (.var 1) (.var 2)) (.var 4)))
        (by decide) (fun | 0 => cap c | 1 => cap d | 2 => base | 3 => p | _ => q)))
      (P.lower.add Q.lower)
  · exact Certificate.ofCoeff (((hc.mul_right base).add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.add (.var 0) (.var 1)) (.var 2))
          (.neg (.add (.var 3) (.var 4))))
        (.add (.add (.mul (.var 0) (.var 2)) (.neg (.var 3)))
          (.add (.mul (.var 1) (.var 2)) (.neg (.var 4))))
        (by decide) (fun | 0 => cap c | 1 => cap d | 2 => base | 3 => p | _ => q)))
      (P.upper.add Q.upper)

private def scalePositive {blocks : Nat} {base p : RatPoly} {c : Q'}
    (a : Q') (ha : (0 : Q') ≤ a) (P : RelativeInterval blocks base p c) :
    RelativeInterval blocks base (polySmul a p) (a*c) := by
  have hcost : RatPolyCoeffEqv (cap (a*c)) (polyMul (cap a) (cap c)) :=
    (cap_mul a c).symm
  have hp : RatPolyCoeffEqv (polySmul a p) (polyMul (cap a) p) :=
    (cap_mul_left a p).symm
  have hn : RatPolyCoeffEqv (polyNeg (polySmul a p))
      (polyNeg (polyMul (cap a) p)) := RatPolyCoeffEqv.neg hp
  have L := Certificate.ofCoeff (cap_mul_left a _)
    (P.lower.smul a ha)
  have U := Certificate.ofCoeff (cap_mul_left a _)
    (P.upper.smul a ha)
  constructor
  · exact Certificate.ofCoeff (((hcost.mul_right base).add hp).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 0) (.var 3)))
        (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.var 3)))
        (by decide) (fun | 0 => cap a | 1 => cap c | 2 => base | _ => p))) L
  · exact Certificate.ofCoeff (((hcost.mul_right base).add hn).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.neg (.mul (.var 0) (.var 3))))
        (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.var 3))))
        (by decide) (fun | 0 => cap a | 1 => cap c | 2 => base | _ => p))) U

private def neg {blocks : Nat} {base p : RatPoly} {c : Q'}
    (P : RelativeInterval blocks base p c) :
    RelativeInterval blocks base (polyNeg p) c where
  lower := P.upper
  upper := Certificate.ofCoeff
    ((RatPolyCoeffEqv.refl _).add
      (coeffEvalExpr_eqv_of_normalize_eq (.neg (.neg (.var 0))) (.var 0)
        (by decide) (fun _ => p))) P.lower

def smulSigned {blocks : Nat} {base p : RatPoly} {c : Q'}
    (r : Q') (P : RelativeInterval blocks base p c) :
    RelativeInterval blocks base (polySmul r p) (Q'.abs r*c) := by
  by_cases hr : (0 : Q') ≤ r
  · exact (scalePositive r hr P).changeCap
      (Q'.mul_eqv_congr_right _ _ c (Q'.eqv_of_eq (show Q'.abs r = r from if_pos hr))).symm
  · have hnr : (0 : Q') ≤ -r := Q'.neg_nonneg_of_not_nonneg hr
    have A := scalePositive (-r) hnr (neg P)
    have habs : Q'.abs r = -r := by unfold Q'.abs; rw [if_neg hr]
    have hpoly : RatPolyCoeffEqv (polySmul r p) (polySmul (-r) (polyNeg p)) := by
      have hcoef : ((-r) * (-1 : Q')).eqv r :=
        poly_identity_of_normal_eq (.mul (.neg (.var 0)) (.const (-1)))
          (.var 0) (by decide) (fun _ => r)
      exact ((RatPolyCoeffEqv.smul_coefficient (Q'.eqv_symm hcoef) p).trans
        ((RatPolyCoeffEqv.smul_assoc (-r) (-1) p).symm.trans
          ((neg_smul p).symm.smul (-r))))
    exact ofCoeff hpoly (A.changeCap
      (Q'.mul_eqv_congr_right _ _ c (Q'.eqv_of_eq habs)).symm)

def zero (blocks : Nat) (base : RatPoly) :
    RelativeInterval blocks base polyZero 0 := by
  have hz : RatPolyCoeffEqv (polyMul (cap 0) base) polyZero :=
    ((RatPolyCoeffEqv.zero_smul polyOne).mul_right base).trans
      (RatPolyCoeffEqv.mul_zero_left base)
  have Z : Certificate blocks polyZero := Certificate.ofCoeff
    (RatPolyCoeffEqv.zero_smul polyOne).symm
    (Certificate.constant blocks 0 (Q'.le_refl' _))
  exact ⟨Certificate.ofCoeff ((hz.add (RatPolyCoeffEqv.refl _)).trans
      (RatPolyCoeffEqv.zero_add polyZero)) Z,
    Certificate.ofCoeff ((hz.add (RatPolyCoeffEqv.refl polyZero)).trans
      (RatPolyCoeffEqv.zero_add polyZero)) Z⟩

end RelativeInterval

end YMGap.Continuum.QuaternionHaarRelativePolynomialInterval

#print axioms YMGap.Continuum.QuaternionHaarRelativePolynomialInterval.RelativeInterval.ofCoeff
#print axioms YMGap.Continuum.QuaternionHaarRelativePolynomialInterval.RelativeInterval.changeCap
#print axioms YMGap.Continuum.QuaternionHaarRelativePolynomialInterval.RelativeInterval.add
#print axioms YMGap.Continuum.QuaternionHaarRelativePolynomialInterval.RelativeInterval.smulSigned
#print axioms YMGap.Continuum.QuaternionHaarRelativePolynomialInterval.RelativeInterval.zero
