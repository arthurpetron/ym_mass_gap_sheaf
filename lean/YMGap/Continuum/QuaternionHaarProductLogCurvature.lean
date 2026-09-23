/-
# Product tensorization of denominator-cleared log curvature

This is the purely polynomial product rule.  Multiplying the two supplied
local certificates by the opposite literal square makes both mixed terms
cancel exactly.  No positivity of either polynomial is assumed.
-/

import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.QuaternionHaarProductLogCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound

/-- Denominator-cleared log curvature tensorizes across a product.  The
displayed first and second jets are the exact Leibniz jets of `p*q`; the
lemma itself only needs support of the two factors and the two local
certificates. -/
def productLogCurvatureLower
    {blocks : Nat} (p dp ddp q dq ddq : RatPoly) (r s : Q')
    (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q)
    (P : Certificate blocks
      (polyAdd (polyMul (cap r) (polyMul p p))
        (polyAdd (polyMul p ddp) (polyNeg (polyMul dp dp)))))
    (Q : Certificate blocks
      (polyAdd (polyMul (cap s) (polyMul q q))
        (polyAdd (polyMul q ddq) (polyNeg (polyMul dq dq))))) :
    Certificate blocks
      (polyAdd
        (polyMul (cap (r+s))
          (polyMul (polyMul p q) (polyMul p q)))
        (polyAdd
          (polyMul (polyMul p q)
            (polyAdd (polyMul ddp q)
              (polyAdd (polyMul (cap 2) (polyMul dp dq)) (polyMul p ddq))))
          (polyNeg
            (polyMul
              (polyAdd (polyMul dp q) (polyMul p dq))
              (polyAdd (polyMul dp q) (polyMul p dq)))))) := by
  have hsource := (Certificate.multiplySquare q hq P).add
    (Certificate.multiplySquare p hp Q)
  have hcap : RatPolyCoeffEqv
      (polyMul (cap (r+s)) (polyMul (polyMul p q) (polyMul p q)))
      (polyMul (polyAdd (cap r) (cap s))
        (polyMul (polyMul p q) (polyMul p q))) :=
    (cap_add r s).symm.mul_right _
  let env : Nat → RatPoly
    | 0 => p
    | 1 => dp
    | 2 => ddp
    | 3 => q
    | 4 => dq
    | 5 => ddq
    | 6 => cap r
    | _ => cap s
  exact Certificate.ofCoeff
    ((hcap.add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add
          (.mul (.add (.var 6) (.var 7))
            (.mul (.mul (.var 0) (.var 3)) (.mul (.var 0) (.var 3))))
          (.add
            (.mul (.mul (.var 0) (.var 3))
              (.add (.mul (.var 2) (.var 3))
                (.add (.mul (.const 2) (.mul (.var 1) (.var 4)))
                  (.mul (.var 0) (.var 5)))))
            (.neg
              (.mul
                (.add (.mul (.var 1) (.var 3)) (.mul (.var 0) (.var 4)))
                (.add (.mul (.var 1) (.var 3)) (.mul (.var 0) (.var 4)))))))
        (.add
          (.mul (.mul (.var 3) (.var 3))
            (.add (.mul (.var 6) (.mul (.var 0) (.var 0)))
              (.add (.mul (.var 0) (.var 2))
                (.neg (.mul (.var 1) (.var 1))))))
          (.mul (.mul (.var 0) (.var 0))
            (.add (.mul (.var 7) (.mul (.var 3) (.var 3)))
              (.add (.mul (.var 3) (.var 5))
                (.neg (.mul (.var 4) (.var 4)))))))
        (by decide) env)) hsource

end YMGap.Continuum.QuaternionHaarProductLogCurvature

#print axioms YMGap.Continuum.QuaternionHaarProductLogCurvature.productLogCurvatureLower
