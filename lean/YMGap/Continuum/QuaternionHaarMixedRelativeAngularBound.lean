/-
# Constructed mixed relative angular bounds

First and mixed angular derivatives of a positive polynomial are controlled
by explicit two-sided polynomial certificates. Product costs follow the
ordinary two-variable Leibniz rule; no quotient of polynomials or analytic
positivity premise is introduced.
-/

import YMGap.Continuum.QuaternionHaarRelativeAngularBound
import YMGap.Continuum.QuaternionHaarRelativeIntervalProduct

namespace YMGap.Continuum.QuaternionHaarMixedRelativeAngularBound

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
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarRelativePolynomialInterval

/-- A positive polynomial with two first-order relative bounds and one
ordered mixed-derivative bound. The outer derivative acts after the inner. -/
structure MixedBound (blocks oi oj ii ij : Nat) (p : RatPoly)
    (a b c : Q') : Type where
  outer : RelativeBound blocks oi oj p a
  inner : RelativeBound blocks ii ij p b
  mixedNonnegative : (0 : Q') ≤ c
  mixed : RelativeInterval blocks p
    (angularDerivative oi oj (angularDerivative ii ij p)) c

namespace MixedBound

variable {blocks oi oj ii ij : Nat}

private def firstInterval {i j : Nat} {p : RatPoly} {a : Q'}
    (P : RelativeBound blocks i j p a) :
    RelativeInterval blocks p (angularDerivative i j p) a :=
  ⟨P.lower, P.upper⟩

/-- Transport all three certificates through one exact polynomial identity. -/
def ofCoeff {p q : RatPoly} {a b c : Q'} (h : RatPolyCoeffEqv p q)
    (Q : MixedBound blocks oi oj ii ij q a b c) :
    MixedBound blocks oi oj ii ij p a b c where
  outer := Q.outer.ofCoeff h
  inner := Q.inner.ofCoeff h
  mixedNonnegative := Q.mixedNonnegative
  mixed := RelativeInterval.baseOfCoeff h
    (RelativeInterval.ofCoeff
      (angularDerivative_congr oi oj (angularDerivative_congr ii ij h)) Q.mixed)

/-- Equivalent rational presentations of the three caps are interchangeable. -/
def changeCaps {p : RatPoly} {a b c a' b' c' : Q'}
    (P : MixedBound blocks oi oj ii ij p a b c)
    (ha : Q'.eqv a a') (hb : Q'.eqv b b') (hc : Q'.eqv c c') :
    MixedBound blocks oi oj ii ij p a' b' c' where
  outer := P.outer.changeCap ha
  inner := P.inner.changeCap hb
  mixedNonnegative := Q'.le_trans' _ _ _ P.mixedNonnegative (Q'.le_of_eqv hc)
  mixed := P.mixed.changeCap hc

/-- Enlarging each cap preserves all certificates. -/
def weaken {p : RatPoly} {a b c a' b' c' : Q'}
    (P : MixedBound blocks oi oj ii ij p a b c)
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    MixedBound blocks oi oj ii ij p a' b' c' where
  outer := P.outer.weaken ha
  inner := P.inner.weaken hb
  mixedNonnegative := Q'.le_trans' _ _ _ P.mixedNonnegative hc
  mixed := P.mixed.weaken P.outer.positive hc

private theorem derivative_zero (i j : Nat) :
    RatPolyCoeffEqv (angularDerivative i j polyZero) polyZero :=
  (angularDerivative_congr i j (RatPolyCoeffEqv.zero_smul polyOne).symm).trans
    ((angularDerivative_smul i j 0 polyOne).trans
      (((angularDerivative_one i j).smul 0).trans
        (RatPolyCoeffEqv.smul_zero 0)))

private theorem derivative_cap (i j : Nat) (r : Q') :
    RatPolyCoeffEqv (angularDerivative i j (cap r)) polyZero :=
  (angularDerivative_smul i j r polyOne).trans
    (((angularDerivative_one i j).smul r).trans
      (RatPolyCoeffEqv.smul_zero r))

/-- A nonnegative constant has zero first and mixed relative costs. -/
def constant (blocks oi oj ii ij : Nat) (r : Q') (hr : (0 : Q') ≤ r) :
    MixedBound blocks oi oj ii ij (cap r) 0 0 0 := by
  have hinner := derivative_cap ii ij r
  have hmixed : RatPolyCoeffEqv
      (angularDerivative oi oj (angularDerivative ii ij (cap r))) polyZero :=
    (angularDerivative_congr oi oj hinner).trans (derivative_zero oi oj)
  exact ⟨RelativeBound.constant blocks oi oj r hr,
    RelativeBound.constant blocks ii ij r hr, Q'.le_refl' _,
    RelativeInterval.ofCoeff hmixed (RelativeInterval.zero blocks (cap r))⟩

def zero (blocks oi oj ii ij : Nat) :
    MixedBound blocks oi oj ii ij polyZero 0 0 0 :=
  ofCoeff (RatPolyCoeffEqv.zero_smul polyOne).symm
    (constant blocks oi oj ii ij 0 (Q'.le_refl' _))

/-- Addition at equal three caps does not accumulate a new relative cost. -/
def add {p q : RatPoly} {a b c : Q'}
    (P : MixedBound blocks oi oj ii ij p a b c)
    (Q : MixedBound blocks oi oj ii ij q a b c) :
    MixedBound blocks oi oj ii ij (polyAdd p q) a b c := by
  have hder : RatPolyCoeffEqv
      (angularDerivative oi oj (angularDerivative ii ij (polyAdd p q)))
      (polyAdd
        (angularDerivative oi oj (angularDerivative ii ij p))
        (angularDerivative oi oj (angularDerivative ii ij q))) :=
    (angularDerivative_congr oi oj (angularDerivative_add ii ij p q)).trans
      (angularDerivative_add oi oj _ _)
  exact ⟨P.outer.add Q.outer, P.inner.add Q.inner, P.mixedNonnegative,
    RelativeInterval.ofCoeff hder (P.mixed.sumBases Q.mixed)⟩

/-- Positive rational scaling retains all relative costs. -/
def smul {p : RatPoly} {a b c : Q'}
    (P : MixedBound blocks oi oj ii ij p a b c)
    (r : Q') (hr : (0 : Q') ≤ r) :
    MixedBound blocks oi oj ii ij (polySmul r p) a b c := by
  have hder : RatPolyCoeffEqv
      (angularDerivative oi oj (angularDerivative ii ij (polySmul r p)))
      (polySmul r (angularDerivative oi oj (angularDerivative ii ij p))) :=
    (angularDerivative_congr oi oj (angularDerivative_smul ii ij r p)).trans
      (angularDerivative_smul oi oj r _)
  exact ⟨P.outer.smul r hr, P.inner.smul r hr, P.mixedNonnegative,
    RelativeInterval.ofCoeff hder (P.mixed.smulBoth r hr)⟩

/-- Leibniz cost for an ordered mixed derivative. The cross terms cost the
products of opposite first-derivative caps. -/
def mul {p q : RatPoly} {a b c d e f : Q'}
    (P : MixedBound blocks oi oj ii ij p a b c)
    (Q : MixedBound blocks oi oj ii ij q d e f) :
    MixedBound blocks oi oj ii ij (polyMul p q)
      (a+d) (b+e) ((c+f)+(a*e+b*d)) := by
  let xp := angularDerivative oi oj p
  let yp := angularDerivative ii ij p
  let xyp := angularDerivative oi oj yp
  let xq := angularDerivative oi oj q
  let yq := angularDerivative ii ij q
  let xyq := angularDerivative oi oj yq
  have hraw : RatPolyCoeffEqv
      (angularDerivative oi oj (angularDerivative ii ij (polyMul p q)))
      (polyAdd (polyAdd (polyMul xyp q) (polyMul yp xq))
        (polyAdd (polyMul xp yq) (polyMul p xyq))) :=
    (angularDerivative_congr oi oj (angularDerivative_mul ii ij p q)).trans
      ((angularDerivative_add oi oj _ _).trans
        ((angularDerivative_mul oi oj yp q).add
          (angularDerivative_mul oi oj p yq)))
  have hperm : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyMul xyp q) (polyMul yp xq))
        (polyAdd (polyMul xp yq) (polyMul p xyq)))
      (polyAdd (polyAdd (polyMul xyp q) (polyMul p xyq))
        (polyAdd (polyMul xp yq) (polyMul yp xq))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
      (.add (.add (.var 0) (.var 3)) (.add (.var 2) (.var 1)))
      (by decide)
      (fun | 0 => polyMul xyp q | 1 => polyMul yp xq
           | 2 => polyMul xp yq | _ => polyMul p xyq)
  let A := P.mixed.mul (RelativeInterval.self Q.outer.positive)
  let B := (RelativeInterval.self P.outer.positive).mul Q.mixed
  let C := (firstInterval P.outer).mul (firstInterval Q.inner)
  let D := (firstInterval P.inner).mul (firstInterval Q.outer)
  have hcap : Q'.eqv
      (((c*1)+(1*f))+((a*e)+(b*d)))
      ((c+f)+(a*e+b*d)) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.const 1)) (.mul (.const 1) (.var 1)))
        (.add (.mul (.var 2) (.var 3)) (.mul (.var 4) (.var 5))))
      (.add (.add (.var 0) (.var 1))
        (.add (.mul (.var 2) (.var 3)) (.mul (.var 4) (.var 5))))
      (by decide)
      (fun | 0 => c | 1 => f | 2 => a | 3 => e | 4 => b | _ => d)
  have hmixed := RelativeInterval.ofCoeff (hraw.trans hperm)
    (((A.add B).add (C.add D)).changeCap hcap)
  have hcross : (0 : Q') ≤ a*e+b*d :=
    Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ P.outer.nonnegative Q.inner.nonnegative)
      (Q'.mul_nonneg _ _ P.inner.nonnegative Q.outer.nonnegative)
  exact ⟨P.outer.mul Q.outer, P.inner.mul Q.inner,
    Q'.zero_le_add _ _
      (Q'.zero_le_add _ _ P.mixedNonnegative Q.mixedNonnegative) hcross,
    hmixed⟩

#print axioms MixedBound.ofCoeff
#print axioms MixedBound.changeCaps
#print axioms MixedBound.weaken
#print axioms MixedBound.constant
#print axioms MixedBound.zero
#print axioms MixedBound.add
#print axioms MixedBound.smul
#print axioms MixedBound.mul

end MixedBound
end YMGap.Continuum.QuaternionHaarMixedRelativeAngularBound
