/-
# Polynomial-cost tensorization of formal curvature jets

The supplied first and second jets are formal polynomials. Multiplication
by the opposite supported square combines two certificates and cancels
both mixed product terms exactly. Costs R and S are arbitrary polynomials,
not rational constants; no positivity of either cost or factor is assumed.

The consumer is the local-to-ORIGINAL-product frozen score-curvature join.
Actual first/second derivative pins and conditional integration are separate
obligations. In particular, a free marginal gives integral DD K = 0, not
zero integral of the log-Hessian numerator K DD K - DK DK.
-/

import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.QuaternionHaarPolynomialJetCurvature

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

/-- Formal first product jet, with every coefficient kept frozen. -/
def jetFirstProduct (p dp q dq : RatPoly) : RatPoly :=
  polyAdd (polyMul dp q) (polyMul p dq)

/-- Formal second product jet, including the literal mixed term. -/
def jetSecondProduct (p dp ddp q dq ddq : RatPoly) : RatPoly :=
  polyAdd (polyMul ddp q)
    (polyAdd (polyMul (cap 2) (polyMul dp dq)) (polyMul p ddq))

/-- Denominator-cleared formal curvature with a POLYNOMIAL cost. -/
def jetCurvature (R p dp ddp : RatPoly) : RatPoly :=
  polyAdd (polyMul R (polyMul p p))
    (polyAdd (polyMul p ddp) (polyNeg (polyMul dp dp)))

/-- Exact polynomial-cost product curvature. There is no scalar-only
restriction on R or S and no derivative acts on an adaptive coefficient.
Only the two opposite square factors require supported representatives. -/
def polynomialJet_product_curvature_certificate
    {blocks : Nat} (p dp ddp q dq ddq R S : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q)
    (P : Certificate blocks (jetCurvature R p dp ddp))
    (Q : Certificate blocks (jetCurvature S q dq ddq)) :
    Certificate blocks (jetCurvature (polyAdd R S) (polyMul p q)
      (jetFirstProduct p dp q dq) (jetSecondProduct p dp ddp q dq ddq)) := by
  have source := (Certificate.multiplySquare q hq P).add
    (Certificate.multiplySquare p hp Q)
  exact Certificate.ofCoeff
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
      (by decide)
      (fun | 0 => p | 1 => dp | 2 => ddp | 3 => q | 4 => dq | 5 => ddq
           | 6 => R | _ => S)) source

end YMGap.Continuum.QuaternionHaarPolynomialJetCurvature

#print axioms YMGap.Continuum.QuaternionHaarPolynomialJetCurvature.polynomialJet_product_curvature_certificate
