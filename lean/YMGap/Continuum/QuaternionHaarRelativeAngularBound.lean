/-
# Constructed relative angular certificates for positive polynomials

Positive sums and products retain their original polynomial. Relative
derivative costs add under multiplication, rather than multiplying absolute
value caps. The intended consumer is the existing positive Jacobi heat
polynomial; no analytic field or continuum operator is postulated here.
-/

import YMGap.Continuum.QuaternionHaarHeatAngularDerivative
import YMGap.Continuum.QuaternionHaarAngularCarrier

namespace YMGap.Continuum.QuaternionHaarRelativeAngularBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarAngularCarrier

/-- Witnesses in the original polynomial positive cone, not a pointwise
positivity assumption or a replacement for a continuum frontier. -/
structure RelativeBound (blocks i j : Nat) (p : RatPoly) (c : Q') : Type where
  positive : Certificate blocks p
  nonnegative : (0 : Q') ≤ c
  upper : Certificate blocks (polyAdd (polyMul (cap c) p) (polyNeg (angularDerivative i j p)))
  lower : Certificate blocks (polyAdd (polyMul (cap c) p) (angularDerivative i j p))

private theorem cap_derivative (i j : Nat) (c : Q') :
    RatPolyCoeffEqv (angularDerivative i j (cap c)) polyZero :=
  (angularDerivative_smul i j c polyOne).trans
    (((angularDerivative_one i j).smul c).trans (RatPolyCoeffEqv.smul_zero c))

namespace RelativeBound

variable {blocks i j : Nat}

def ofCoeff {p q : RatPoly} {c : Q'} (h : RatPolyCoeffEqv p q)
    (Q : RelativeBound blocks i j q c) : RelativeBound blocks i j p c where
  positive := .ofCoeff h Q.positive
  nonnegative := Q.nonnegative
  upper := .ofCoeff ((h.mul_left _).add (RatPolyCoeffEqv.neg (angularDerivative_congr i j h))) Q.upper
  lower := .ofCoeff ((h.mul_left _).add (angularDerivative_congr i j h)) Q.lower

def changeCap {p : RatPoly} {c d : Q'} (h : Q'.eqv c d)
    (P : RelativeBound blocks i j p c) : RelativeBound blocks i j p d where
  positive := P.positive
  nonnegative := Q'.le_trans' _ _ _ P.nonnegative (Q'.le_of_eqv h)
  upper := .ofCoeff (((RatPolyCoeffEqv.smul_coefficient (Q'.eqv_symm h) polyOne).mul_right p).add
    (.refl _)) P.upper
  lower := .ofCoeff (((RatPolyCoeffEqv.smul_coefficient (Q'.eqv_symm h) polyOne).mul_right p).add
    (.refl _)) P.lower

def ofZeroDerivative {p : RatPoly} (P : Certificate blocks p)
    (h : RatPolyCoeffEqv (angularDerivative i j p) polyZero) :
    RelativeBound blocks i j p 0 where
  positive := P
  nonnegative := Q'.le_refl' _
  upper := .ofCoeff
    ((((cap_mul_left 0 p).trans (RatPolyCoeffEqv.zero_smul p)).add (RatPolyCoeffEqv.neg h)).trans
      (RatPolyCoeffEqv.refl _))
    (.ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm (.constant blocks 0 (Q'.le_refl' _)))
  lower := .ofCoeff
    ((((cap_mul_left 0 p).trans (RatPolyCoeffEqv.zero_smul p)).add h).trans (RatPolyCoeffEqv.refl _))
    (.ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm (.constant blocks 0 (Q'.le_refl' _)))

def constant (blocks i j : Nat) (c : Q') (hc : (0 : Q') ≤ c) :
    RelativeBound blocks i j (cap c) 0 :=
  ofZeroDerivative (.constant blocks c hc) (cap_derivative i j c)

def zero (blocks i j : Nat) : RelativeBound blocks i j polyZero 0 :=
  ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm (constant blocks i j 0 (Q'.le_refl' _))

def raise {p : RatPoly} {c : Q'} (P : RelativeBound blocks i j p c)
    (e : Q') (he : (0 : Q') ≤ e) : RelativeBound blocks i j p (c+e) where
  positive := P.positive
  nonnegative := Q'.zero_le_add _ _ P.nonnegative he
  upper := .ofCoeff
    ((((cap_add c e).symm.mul_right p).add (.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.add (.var 0) (.var 1)) (.var 2)) (.neg (.var 3)))
        (.add (.add (.mul (.var 0) (.var 2)) (.neg (.var 3))) (.mul (.var 1) (.var 2)))
        (by decide) (fun | 0 => cap c | 1 => cap e | 2 => p | _ => angularDerivative i j p)))
    (P.upper.add ((Certificate.constant blocks e he).mul P.positive))
  lower := .ofCoeff
    ((((cap_add c e).symm.mul_right p).add (.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.add (.var 0) (.var 1)) (.var 2)) (.var 3))
        (.add (.add (.mul (.var 0) (.var 2)) (.var 3)) (.mul (.var 1) (.var 2)))
        (by decide) (fun | 0 => cap c | 1 => cap e | 2 => p | _ => angularDerivative i j p)))
    (P.lower.add ((Certificate.constant blocks e he).mul P.positive))

def weaken {p : RatPoly} {c d : Q'} (P : RelativeBound blocks i j p c) (h : c ≤ d) :
    RelativeBound blocks i j p d :=
  (P.raise (d + -c) (Q'.sub_nonneg_of_le h)).changeCap
    (poly_identity_of_normal_eq (.add (.var 0) (.add (.var 1) (.neg (.var 0))))
      (.var 1) (by decide) (fun | 0 => c | _ => d))

def add {p q : RatPoly} {c : Q'} (P : RelativeBound blocks i j p c)
    (Q : RelativeBound blocks i j q c) : RelativeBound blocks i j (polyAdd p q) c where
  positive := P.positive.add Q.positive
  nonnegative := P.nonnegative
  upper := .ofCoeff
    (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (angularDerivative_add i j p q))).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.add (.var 1) (.var 2))) (.neg (.add (.var 3) (.var 4))))
        (.add (.add (.mul (.var 0) (.var 1)) (.neg (.var 3)))
          (.add (.mul (.var 0) (.var 2)) (.neg (.var 4))))
        (by decide) (fun
          | 0 => cap c | 1 => p | 2 => q | 3 => angularDerivative i j p
          | _ => angularDerivative i j q))) (P.upper.add Q.upper)
  lower := .ofCoeff
    (((RatPolyCoeffEqv.refl _).add (angularDerivative_add i j p q)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.add (.var 1) (.var 2))) (.add (.var 3) (.var 4)))
        (.add (.add (.mul (.var 0) (.var 1)) (.var 3))
          (.add (.mul (.var 0) (.var 2)) (.var 4)))
        (by decide) (fun
          | 0 => cap c | 1 => p | 2 => q | 3 => angularDerivative i j p
          | _ => angularDerivative i j q))) (P.lower.add Q.lower)

def mul {p q : RatPoly} {c d : Q'} (P : RelativeBound blocks i j p c)
    (Q : RelativeBound blocks i j q d) : RelativeBound blocks i j (polyMul p q) (c+d) where
  positive := P.positive.mul Q.positive
  nonnegative := Q'.zero_le_add _ _ P.nonnegative Q.nonnegative
  upper := .ofCoeff
    ((((cap_add c d).symm.mul_right _).add
      (RatPolyCoeffEqv.neg (angularDerivative_mul i j p q))).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.add (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
          (.neg (.add (.mul (.var 4) (.var 3)) (.mul (.var 2) (.var 5)))))
        (.add (.mul (.add (.mul (.var 0) (.var 2)) (.neg (.var 4))) (.var 3))
          (.mul (.var 2) (.add (.mul (.var 1) (.var 3)) (.neg (.var 5)))))
        (by decide) (fun
          | 0 => cap c | 1 => cap d | 2 => p | 3 => q
          | 4 => angularDerivative i j p | _ => angularDerivative i j q)))
    ((P.upper.mul Q.positive).add (P.positive.mul Q.upper))
  lower := .ofCoeff
    ((((cap_add c d).symm.mul_right _).add (angularDerivative_mul i j p q)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.add (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
          (.add (.mul (.var 4) (.var 3)) (.mul (.var 2) (.var 5))))
        (.add (.mul (.add (.mul (.var 0) (.var 2)) (.var 4)) (.var 3))
          (.mul (.var 2) (.add (.mul (.var 1) (.var 3)) (.var 5))))
        (by decide) (fun
          | 0 => cap c | 1 => cap d | 2 => p | 3 => q
          | 4 => angularDerivative i j p | _ => angularDerivative i j q)))
    ((P.lower.mul Q.positive).add (P.positive.mul Q.lower))

def smul {p : RatPoly} {c : Q'} (P : RelativeBound blocks i j p c)
    (a : Q') (ha : (0 : Q') ≤ a) : RelativeBound blocks i j (polySmul a p) c :=
  ofCoeff (cap_mul_left a p).symm
    (((constant blocks i j a ha).mul P).changeCap (QPoly.q_zero_add_eqv c))

/-- An affine positive factor costs `d*r` when its slope is at most `r`
times its constant coefficient. No inverse of the full polynomial is used. -/
def affine {x : RatPoly} {a b d r : Q'} (X : Certificate blocks x)
    (DX : Interval blocks (angularDerivative i j x) d)
    (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) (hr : (0 : Q') ≤ r)
    (hslope : b ≤ r*a) :
    RelativeBound blocks i j (polyAdd (cap a) (polyMul (cap b) x)) (d*r) := by
  let p := polyAdd (cap a) (polyMul (cap b) x)
  have capNeg : RatPolyCoeffEqv (polyNeg (cap b)) (cap (-b)) := by
    intro weight
    change Q'.eqv ((-(b*1))*weight []+0) (((-b)*1)*weight []+0)
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.neg_mul_eqv b 1))) (Q'.eqv_refl _)
  have clearance : Certificate blocks (polyAdd (polyMul (cap r) p) (polyNeg (cap b))) := by
    refine .ofCoeff
      ((coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.add (.var 1) (.mul (.var 2) (.var 3)))) (.neg (.var 2)))
        (.add (.add (.mul (.var 0) (.var 1)) (.neg (.var 2)))
          (.mul (.mul (.var 0) (.var 2)) (.var 3)))
        (by decide) (fun | 0 => cap r | 1 => cap a | 2 => cap b | _ => x)).trans
        ((((cap_mul r a).add capNeg).trans (cap_add (r*a) (-b))).add
          ((cap_mul r b).mul_right x))) ?_
    exact (Certificate.constant blocks (r*a + -b) (Q'.sub_nonneg_of_le hslope)).add
      ((Certificate.constant blocks (r*b) (Q'.mul_nonneg _ _ hr hb)).mul X)
  have dp : RatPolyCoeffEqv (angularDerivative i j p)
      (polyMul (cap b) (angularDerivative i j x)) :=
    (angularDerivative_add i j (cap a) (polyMul (cap b) x)).trans
      (((cap_derivative i j a).add
        ((angularDerivative_mul i j (cap b) x).trans
          ((((cap_derivative i j b).mul_right x).add (.refl _)).trans
            (((RatPolyCoeffEqv.mul_zero_left x).add (.refl _)).trans
              (RatPolyCoeffEqv.zero_add _))))).trans (RatPolyCoeffEqv.zero_add _))
  refine ⟨(Certificate.constant blocks a ha).add ((Certificate.constant blocks b hb).mul X),
    Q'.mul_nonneg _ _ DX.nonnegative hr, ?_, ?_⟩
  · exact .ofCoeff
      ((((cap_mul d r).symm.mul_right p).add (RatPolyCoeffEqv.neg dp)).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.neg (.mul (.var 3) (.var 4))))
          (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.var 3))))
            (.mul (.var 3) (.add (.var 0) (.neg (.var 4)))))
          (by decide) (fun
            | 0 => cap d | 1 => cap r | 2 => p | 3 => cap b | _ => angularDerivative i j x)))
      (((Certificate.constant blocks d DX.nonnegative).mul clearance).add
        ((Certificate.constant blocks b hb).mul DX.upper))
  · exact .ofCoeff
      ((((cap_mul d r).symm.mul_right p).add dp).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 3) (.var 4)))
          (.add (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.neg (.var 3))))
            (.mul (.var 3) (.add (.var 0) (.var 4))))
          (by decide) (fun
            | 0 => cap d | 1 => cap r | 2 => p | 3 => cap b | _ => angularDerivative i j x)))
      (((Certificate.constant blocks d DX.nonnegative).mul clearance).add
        ((Certificate.constant blocks b hb).mul DX.lower))

/-- Absorb a certified value/derivative approximation error at a sufficiently
late cutoff. The positive floor pays only the error; the relative constant
increases by one, not by the inverse of that floor. -/
def ofApproximation {p f e : RatPoly} {c a b : Q'}
    (P : Certificate blocks p) (h : RatPolyCoeffEqv p (polyAdd f e))
    (F : RelativeBound blocks i j f c) (E : Interval blocks e a)
    (DE : Interval blocks (angularDerivative i j e) b)
    (floor : Certificate blocks (polyAdd p (polyNeg (cap (c*a+b))))) :
    RelativeBound blocks i j p (c+1) := by
  let total := polyAdd f e
  let budget := cap (c*a+b)
  have hp : Certificate blocks total := .ofCoeff h.symm P
  have hf : Certificate blocks (polyAdd total (polyNeg budget)) :=
    .ofCoeff (h.symm.add (.refl _)) floor
  have hu : Certificate blocks (polyAdd budget
      (polyAdd (polyMul (cap c) e) (polyNeg (angularDerivative i j e)))) :=
    .ofCoeff ((RatPolyCoeffEqv.refl _).add ((cap_mul_left c e).add (.refl _)))
      (((E.smul c F.nonnegative).add (intervalNeg DE)).lower)
  have hl : Certificate blocks (polyAdd budget
      (polyAdd (polyMul (cap c) e) (angularDerivative i j e))) :=
    .ofCoeff ((RatPolyCoeffEqv.refl _).add ((cap_mul_left c e).add (.refl _)))
      (((E.smul c F.nonnegative).add DE).lower)
  have hc : RatPolyCoeffEqv (cap (c+1)) (polyAdd (cap c) polyOne) :=
    (cap_add c 1).symm.trans ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.one_smul polyOne))
  refine ofCoeff h ⟨hp, Q'.zero_le_add _ _ F.nonnegative Q'.zero_le_one, ?_, ?_⟩
  · exact .ofCoeff
      (((hc.mul_right total).add (RatPolyCoeffEqv.neg (angularDerivative_add i j f e))).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.add (.var 0) (.const 1)) (.add (.var 1) (.var 2)))
            (.neg (.add (.var 3) (.var 4))))
          (.add (.add (.add (.mul (.var 0) (.var 1)) (.neg (.var 3)))
              (.add (.var 5) (.add (.mul (.var 0) (.var 2)) (.neg (.var 4)))))
            (.add (.add (.var 1) (.var 2)) (.neg (.var 5))))
          (by decide) (fun
            | 0 => cap c | 1 => f | 2 => e | 3 => angularDerivative i j f
            | 4 => angularDerivative i j e | _ => budget)))
      ((F.upper.add hu).add hf)
  · exact .ofCoeff
      (((hc.mul_right total).add (angularDerivative_add i j f e)).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.add (.var 0) (.const 1)) (.add (.var 1) (.var 2)))
            (.add (.var 3) (.var 4)))
          (.add (.add (.add (.mul (.var 0) (.var 1)) (.var 3))
              (.add (.var 5) (.add (.mul (.var 0) (.var 2)) (.var 4))))
            (.add (.add (.var 1) (.var 2)) (.neg (.var 5))))
          (by decide) (fun
            | 0 => cap c | 1 => f | 2 => e | 3 => angularDerivative i j f
            | 4 => angularDerivative i j e | _ => budget)))
      ((F.lower.add hl).add hf)

end RelativeBound
end YMGap.Continuum.QuaternionHaarRelativeAngularBound

#print axioms YMGap.Continuum.QuaternionHaarRelativeAngularBound.RelativeBound.ofCoeff
#print axioms YMGap.Continuum.QuaternionHaarRelativeAngularBound.RelativeBound.changeCap
#print axioms YMGap.Continuum.QuaternionHaarRelativeAngularBound.RelativeBound.ofZeroDerivative
#print axioms YMGap.Continuum.QuaternionHaarRelativeAngularBound.RelativeBound.constant
#print axioms YMGap.Continuum.QuaternionHaarRelativeAngularBound.RelativeBound.zero
#print axioms YMGap.Continuum.QuaternionHaarRelativeAngularBound.RelativeBound.raise
#print axioms YMGap.Continuum.QuaternionHaarRelativeAngularBound.RelativeBound.weaken
#print axioms YMGap.Continuum.QuaternionHaarRelativeAngularBound.RelativeBound.add
#print axioms YMGap.Continuum.QuaternionHaarRelativeAngularBound.RelativeBound.mul
#print axioms YMGap.Continuum.QuaternionHaarRelativeAngularBound.RelativeBound.smul
#print axioms YMGap.Continuum.QuaternionHaarRelativeAngularBound.RelativeBound.affine
#print axioms YMGap.Continuum.QuaternionHaarRelativeAngularBound.RelativeBound.ofApproximation
