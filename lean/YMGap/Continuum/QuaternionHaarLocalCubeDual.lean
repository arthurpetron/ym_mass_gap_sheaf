/-
# Inverse-free local second-adjoint dual under the unchanged weight

Write the density as V*A, where V is independent of the two selected angular
directions. Differentiating A^3*g twice leaves an explicit polynomial factor
A. The remaining polynomial is a local dual; no reciprocal or deleted-action
probability law is introduced. Its pairing retains an extra A^2 factor.
-/

import YMGap.Continuum.QuaternionHaarLocalCubeAdjoint
import YMGap.Continuum.QuaternionHaarRetainedDoubleIBP

namespace YMGap.Continuum.QuaternionHaarLocalCubeDual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarLocalCubeAdjoint
open YMGap.Continuum.QuaternionHaarRetainedDoubleIBP

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- Exact weighted adjoint pairing. The full weight V*A appears on BOTH
sides, and the additional local A^2 is not discarded. -/
theorem local_cube_dual_pair {n a b i j k l : Nat}
    (ha : a < n) (hb : b < n) (hi : i < 4) (hj : j < 4)
    (hk : k < 4) (hl : l < 4) (V A g f : RatPoly)
    (hVa : RatPolyCoeffEqv (blockAngularDerivative a i j V) polyZero)
    (hVb : RatPolyCoeffEqv (blockAngularDerivative b k l V) polyZero) :
    H n (polyMul (polyMul V A)
      (polyMul (cubeAdjoint (4*a+i) (4*a+j) (4*b+k) (4*b+l) A g) f)) ≈
      H n (polyMul (polyMul V A)
        (polyMul (polyMul (polyMul A A) g)
          (blockAngularDerivative a i j (blockAngularDerivative b k l f)))) := by
  let J := cubeAdjoint (4*a+i) (4*a+j) (4*b+k) (4*b+l) A g
  let u := polyMul (polyMul (polyMul A A) A) g
  have hfactor := cubeAdjoint_factor (4*a+i) (4*a+j) (4*b+k) (4*b+l) A g
  have hleft : RatPolyCoeffEqv (polyMul (polyMul V A) (polyMul J f))
      (polyMul V (polyMul
        (blockAngularDerivative b k l (blockAngularDerivative a i j u)) f)) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3))) (by decide)
      (fun | 0 => V | 1 => A | 2 => J | _ => f)).trans
      ((hfactor.symm.mul_right f).mul_left V)
  have hright : RatPolyCoeffEqv
      (polyMul V (polyMul u
        (blockAngularDerivative a i j (blockAngularDerivative b k l f))))
      (polyMul (polyMul V A) (polyMul (polyMul (polyMul A A) g)
        (blockAngularDerivative a i j (blockAngularDerivative b k l f)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.mul (.mul (.var 1) (.var 1)) (.var 1)) (.var 2)) (.var 3)))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.mul (.mul (.var 1) (.var 1)) (.var 2)) (.var 3)))
      (by decide) (fun
        | 0 => V
        | 1 => A
        | 2 => g
        | _ => blockAngularDerivative a i j (blockAngularDerivative b k l f))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hleft)
    (Q'.eqv_trans _ _ _ (retained_double_pair ha hb hi hj hk hl V u f hVa hVb)
      (haar_of_coeff hright))

/-- Exact zero pairing for the derivative dual, despite the interacting
weight, when the test's selected mixed derivative vanishes. -/
theorem local_cube_dual_annihilates {n a b i j k l : Nat}
    (ha : a < n) (hb : b < n) (hi : i < 4) (hj : j < 4)
    (hk : k < 4) (hl : l < 4) (V A g f : RatPoly)
    (hVa : RatPolyCoeffEqv (blockAngularDerivative a i j V) polyZero)
    (hVb : RatPolyCoeffEqv (blockAngularDerivative b k l V) polyZero)
    (hf : RatPolyCoeffEqv
      (blockAngularDerivative a i j (blockAngularDerivative b k l f)) polyZero) :
    H n (polyMul (polyMul V A)
      (polyMul (cubeAdjoint (4*a+i) (4*a+j) (4*b+k) (4*b+l) A g) f)) ≈ 0 :=
  Q'.eqv_trans _ _ _ (local_cube_dual_pair ha hb hi hj hk hl V A g f hVa hVb)
    (haar_of_coeff
      ((((hf.mul_left (polyMul (polyMul A A) g)).trans
        (RatPolyCoeffEqv.mul_zero_right _)).mul_left (polyMul V A)).trans
        (RatPolyCoeffEqv.mul_zero_right _)))

#print axioms local_cube_dual_pair
#print axioms local_cube_dual_annihilates

end YMGap.Continuum.QuaternionHaarLocalCubeDual
