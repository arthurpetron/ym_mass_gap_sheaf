/-
# Two angular integrations by parts with the original background retained

The background is not discarded or made into an independent probability
law. Its two explicitly zero derivatives permit transferring both angular
derivatives. The resulting annihilation statement is for derivative duals,
not for arbitrary distant local observables under an interacting measure.
-/

import YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
import YMGap.Continuum.SU2QuaternionAngularReindex

namespace YMGap.Continuum.QuaternionHaarRetainedDoubleIBP

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- Skew-adjointness retaining a background whose derivative is explicitly
zero. There is no positivity, support, or probability-factorization premise. -/
theorem retained_pair {n block i j : Nat} (hb : block < n)
    (hi : i < 4) (hj : j < 4) (V u f : RatPoly)
    (hV : RatPolyCoeffEqv (blockAngularDerivative block i j V) polyZero) :
    H n (polyMul V (polyMul (blockAngularDerivative block i j u) f)) ≈
      -(H n (polyMul V (polyMul u (blockAngularDerivative block i j f)))) := by
  have hd : RatPolyCoeffEqv
      (blockAngularDerivative block i j (polyMul V f))
      (polyMul V (blockAngularDerivative block i j f)) :=
    (angularDerivative_mul (4*block+i) (4*block+j) V f).trans
      ((((hV.mul_right f).trans (RatPolyCoeffEqv.mul_zero_left f)).add
        (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.zero_add _))
  have hleft := coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
    (fun | 0 => V | 1 => blockAngularDerivative block i j u | _ => f)
  have hright := (hd.mul_right u).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 0) (.mul (.var 2) (.var 1))) (by decide)
      (fun | 0 => V | 1 => blockAngularDerivative block i j f | _ => u))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hleft)
    (Q'.eqv_trans _ _ _ (angular_pair_at hb hi hj (polyMul V f) u)
      (Q'.neg_eqv_congr _ _ (haar_of_coeff hright)))

/-- Two adjoints reverse the derivative order and restore the positive sign.
The complete independent background stays inside both integrals. -/
theorem retained_double_pair {n a b i j k l : Nat}
    (ha : a < n) (hb : b < n) (hi : i < 4) (hj : j < 4)
    (hk : k < 4) (hl : l < 4) (V u f : RatPoly)
    (hVa : RatPolyCoeffEqv (blockAngularDerivative a i j V) polyZero)
    (hVb : RatPolyCoeffEqv (blockAngularDerivative b k l V) polyZero) :
    H n (polyMul V (polyMul
      (blockAngularDerivative b k l (blockAngularDerivative a i j u)) f)) ≈
      H n (polyMul V (polyMul u
        (blockAngularDerivative a i j (blockAngularDerivative b k l f)))) := by
  have hfirst := retained_pair hb hk hl V (blockAngularDerivative a i j u) f hVb
  have hsecond := retained_pair ha hi hj V u (blockAngularDerivative b k l f) hVa
  exact Q'.eqv_trans _ _ _ hfirst
    (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hsecond) (Q'.neg_neg_eqv _))

/-- A derivative dual annihilates a test whose corresponding mixed
derivative vanishes. This does not claim decorrelation of arbitrary tests. -/
theorem retained_double_annihilates {n a b i j k l : Nat}
    (ha : a < n) (hb : b < n) (hi : i < 4) (hj : j < 4)
    (hk : k < 4) (hl : l < 4) (V u f : RatPoly)
    (hVa : RatPolyCoeffEqv (blockAngularDerivative a i j V) polyZero)
    (hVb : RatPolyCoeffEqv (blockAngularDerivative b k l V) polyZero)
    (hf : RatPolyCoeffEqv
      (blockAngularDerivative a i j (blockAngularDerivative b k l f)) polyZero) :
    H n (polyMul V (polyMul
      (blockAngularDerivative b k l (blockAngularDerivative a i j u)) f)) ≈ 0 :=
  Q'.eqv_trans _ _ _ (retained_double_pair ha hb hi hj hk hl V u f hVa hVb)
    (haar_of_coeff (((hf.mul_left u).trans (RatPolyCoeffEqv.mul_zero_right u)).mul_left V |>.trans
      (RatPolyCoeffEqv.mul_zero_right V)))

#print axioms retained_pair
#print axioms retained_double_pair
#print axioms retained_double_annihilates

end YMGap.Continuum.QuaternionHaarRetainedDoubleIBP
