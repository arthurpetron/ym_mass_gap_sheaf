/-
# Two finite inverse corrections: one exact cancellation identity

For H_R=1+R and H_S=1+S, H_R*G_R+E_R=H_S*G_S+E_S=1.
Hence G_R-G_S = -G_R*(R-S)*G_S + G_R*E_S - E_R*G_S.
When both remainders have interval cap at most 1/2, this gives
4*d+2*(2^(-n)+2^(-m)) for the difference, where d bounds R-S.
Both the heat polynomial and correction order may change. No limiting
inverse, independent variables, or degree-dependent coefficient cap is used.
-/

import YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse

namespace YMGap.Continuum.QuaternionHaarPolynomialCorrectorStability

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse

def difference (R S : RatPoly) (n m : Nat) : RatPoly :=
  polyAdd (corrector R n) (polyNeg (corrector S m))

def expansion (R S : RatPoly) (n m : Nat) : RatPoly :=
  polyAdd (polyNeg (polyMul (polyMul (corrector R n) (polyAdd R (polyNeg S))) (corrector S m)))
    (polyAdd (polyMul (corrector R n) (residual S m)) (polyNeg (polyMul (residual R n) (corrector S m))))

theorem difference_pin (R S : RatPoly) (n m : Nat) :
    RatPolyCoeffEqv (difference R S n m) (expansion R S n m) := by
  let G := corrector R n
  let F := corrector S m
  have h := ((RatPolyCoeffEqv.refl G).mul (cancellation S m)).add
    (RatPolyCoeffEqv.neg ((cancellation R n).mul (RatPolyCoeffEqv.refl F)))
  have he : RatPolyCoeffEqv
      (polyAdd (polyMul G (polyAdd (polyMul (polyAdd polyOne S) F) (residual S m)))
        (polyNeg (polyMul (polyAdd (polyMul (polyAdd polyOne R) G) (residual R n)) F)))
      (expansion R S n m) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 2) (.add (.mul (.add (.const 1) (.var 1)) (.var 3)) (.var 5)))
        (.neg (.mul (.add (.mul (.add (.const 1) (.var 0)) (.var 2)) (.var 4)) (.var 3))))
      (.add (.neg (.mul (.mul (.var 2) (.add (.var 0) (.neg (.var 1)))) (.var 3)))
        (.add (.mul (.var 2) (.var 5)) (.neg (.mul (.var 4) (.var 3)))))
      (by decide) (fun | 0 => R | 1 => S | 2 => G | 3 => F | 4 => residual R n | _ => residual S m)
  have hz := coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.const 1)) (.neg (.mul (.const 1) (.var 1))))
    (.add (.var 0) (.neg (.var 1))) (by decide) (fun | 0 => G | _ => F)
  exact (hz.symm.trans h.symm).trans he

def differenceInterval {blocks : Nat} {R S : RatPoly} {r s d : Q'}
    (P : Interval blocks R r) (Q : Interval blocks S s)
    (hr : r ≤ HalfPow.half) (hs : s ≤ HalfPow.half)
    (D : Interval blocks (polyAdd R (polyNeg S)) d) (n m : Nat) :
    Interval blocks (difference R S n m) (4*d+2*(HalfPow.half^n+HalfPow.half^m)) := by
  let G := correctorInterval P hr n
  let F := correctorInterval Q hs m
  let E := residualInterval (P.weaken hr) n
  let J := residualInterval (Q.weaken hs) m
  have hcap : Q'.eqv ((2*d)*2+(2*HalfPow.half^m+HalfPow.half^n*2))
      (4*d+2*(HalfPow.half^n+HalfPow.half^m)) :=
    poly_identity_of_normal_eq
      (.add (.mul (.mul (.const 2) (.var 0)) (.const 2))
        (.add (.mul (.const 2) (.var 2)) (.mul (.var 1) (.const 2))))
      (.add (.mul (.const 4) (.var 0)) (.mul (.const 2) (.add (.var 1) (.var 2))))
      (by decide) (fun | 0 => d | 1 => HalfPow.half^n | _ => HalfPow.half^m)
  exact .ofCoeff (supported_add G.support (negInterval F).support) (difference_pin R S n m)
    (((negInterval ((G.mul D).mul F)).add ((G.mul J).add (negInterval (E.mul F)))).changeCap hcap)

end YMGap.Continuum.QuaternionHaarPolynomialCorrectorStability

#print axioms YMGap.Continuum.QuaternionHaarPolynomialCorrectorStability.difference
#print axioms YMGap.Continuum.QuaternionHaarPolynomialCorrectorStability.expansion
#print axioms YMGap.Continuum.QuaternionHaarPolynomialCorrectorStability.difference_pin
#print axioms YMGap.Continuum.QuaternionHaarPolynomialCorrectorStability.differenceInterval
