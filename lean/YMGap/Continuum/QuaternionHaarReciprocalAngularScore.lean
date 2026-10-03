/-
# The differentiated finite reciprocal retains the actual signed score

For the EXISTING polynomial reciprocal G_k of A and residual E_k,
A*G_k+E_k=1. Differentiating that exact coefficient identity yields
A*dG_k+G_k*dA+dE_k=0. Therefore the derivative of b*G_k, cleared by A^2,
equals the original score A*db-b*dA plus TWO explicit residual terms.

No configuration-valued inverse, positivity, derivative-limit exchange or
uniform estimate is assumed. The concrete block conditional-ratio producer
supplies A and b; controlling this angular remainder is distinct from its
already available weighted-norm reconstruction.
-/

import YMGap.Continuum.QuaternionHaarPositiveWindowInverse
import YMGap.Continuum.SU2QuaternionAngularDerivative
import YMGap.Continuum.SU2QuaternionAngularSupport

namespace YMGap.Continuum.QuaternionHaarReciprocalAngularScore

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport (angularDerivative_one)
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse (residual)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse

/-- The literal residual of the existing reciprocal, not an estimated error. -/
def reciprocalResidual (A : RatPoly) (u : Q') (hu : (0 : Q') < u) (k : Nat) : RatPoly :=
  residual (remainder A u hu) k

/-- The actual polynomial score, cleared without dividing by A. -/
def score (i j : Nat) (A b : RatPoly) : RatPoly :=
  polyAdd (polyMul A (angularDerivative i j b))
    (polyNeg (polyMul b (angularDerivative i j A)))

/-- Differentiated cancellation has an explicit residual derivative. -/
theorem reciprocal_angular_cancellation (i j : Nat) (A : RatPoly)
    (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    RatPolyCoeffEqv
      (polyAdd
        (polyAdd (polyMul A (angularDerivative i j (reciprocal A u hu k)))
          (polyMul (reciprocal A u hu k) (angularDerivative i j A)))
        (angularDerivative i j (reciprocalResidual A u hu k))) polyZero := by
  have h := (angularDerivative_congr i j (reciprocal_cancellation A u hu k)).trans
    (angularDerivative_one i j)
  have hex := (angularDerivative_add i j
    (polyMul A (reciprocal A u hu k)) (reciprocalResidual A u hu k)).trans
      ((angularDerivative_mul i j A (reciprocal A u hu k)).add (.refl _))
  have horder : RatPolyCoeffEqv
      (polyAdd
        (polyAdd (polyMul A (angularDerivative i j (reciprocal A u hu k)))
          (polyMul (reciprocal A u hu k) (angularDerivative i j A)))
        (angularDerivative i j (reciprocalResidual A u hu k)))
      (polyAdd
        (polyAdd (polyMul (angularDerivative i j A) (reciprocal A u hu k))
          (polyMul A (angularDerivative i j (reciprocal A u hu k))))
        (angularDerivative i j (reciprocalResidual A u hu k))) :=
    ((RatPolyCoeffEqv.add_comm _ _).trans
      ((RatPolyCoeffEqv.mul_comm _ _).add (.refl _))).add (.refl _)
  exact horder.trans (hex.symm.trans h)

/-- Exact angular error of the ORIGINAL finite reciprocal ratio. Both
residual contributions stay signed; norm convergence alone does not pay them. -/
theorem reciprocal_ratio_score_error (i j : Nat) (A b : RatPoly)
    (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    let G := reciprocal A u hu k
    let E := reciprocalResidual A u hu k
    RatPolyCoeffEqv
      (polyAdd (polyMul (polyMul A A) (angularDerivative i j (polyMul b G)))
        (polyNeg (score i j A b)))
      (polyAdd (polyNeg (polyMul E (score i j A b)))
        (polyNeg (polyMul (polyMul A b) (angularDerivative i j E)))) := by
  dsimp only
  let G := reciprocal A u hu k
  let E := reciprocalResidual A u hu k
  let dA := angularDerivative i j A
  let db := angularDerivative i j b
  let dG := angularDerivative i j G
  let dE := angularDerivative i j E
  let S := score i j A b
  have hc : RatPolyCoeffEqv (polyAdd (polyMul A G) E) polyOne :=
    reciprocal_cancellation A u hu k
  have hd : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyMul A dG) (polyMul G dA)) dE) polyZero :=
    reciprocal_angular_cancellation i j A u hu k
  have hdist : RatPolyCoeffEqv (polyMul (polyAdd (polyMul A G) E) S)
      (polyAdd (polyMul (polyMul A G) S) (polyMul E S)) := by
    rw [polyMul_add_left_exact]
    exact .refl _
  have hz : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyMul (polyMul A G) S) (polyMul E S)) (polyNeg S)) polyZero :=
    (hdist.symm.add (.refl _)).trans
      (((hc.mul_right S).trans (RatPolyCoeffEqv.one_mul S)).add (.refl _) |>.trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide) (fun _ => S) |>.trans
            (RatPolyCoeffEqv.zero_smul polyOne)))
  have hclear : RatPolyCoeffEqv
      (polyAdd (polyMul (polyMul A A) (polyAdd (polyMul db G) (polyMul b dG))) (polyNeg S))
      (polyAdd
        (polyAdd
          (polyAdd (polyAdd (polyMul (polyMul A G) S) (polyMul E S)) (polyNeg S))
          (polyMul (polyMul A b) (polyAdd (polyAdd (polyMul A dG) (polyMul G dA)) dE)))
        (polyAdd (polyNeg (polyMul E S)) (polyNeg (polyMul (polyMul A b) dE)))) := by
    unfold S score
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.mul (.var 0) (.var 0))
        (.add (.mul (.var 3) (.var 2)) (.mul (.var 1) (.var 4))))
        (.neg (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 5))))))
      (.add
        (.add
          (.add (.add
            (.mul (.mul (.var 0) (.var 2))
              (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 5)))))
            (.mul (.var 6)
              (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 5))))))
            (.neg (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 5))))))
          (.mul (.mul (.var 0) (.var 1))
            (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 2) (.var 5))) (.var 7))))
        (.add
          (.neg (.mul (.var 6)
            (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 5))))))
          (.neg (.mul (.mul (.var 0) (.var 1)) (.var 7)))))
      (by decide) (fun
        | 0 => A
        | 1 => b
        | 2 => G
        | 3 => db
        | 4 => dG
        | 5 => dA
        | 6 => E
        | _ => dE)
  exact (((angularDerivative_mul i j b G).mul_left (polyMul A A)).add (.refl _)).trans
    (hclear.trans
      (((hz.add ((hd.mul_left (polyMul A b)).trans
          (RatPolyCoeffEqv.mul_zero_right _))).trans
        (RatPolyCoeffEqv.add_zero polyZero)).add (.refl _) |>.trans
          (RatPolyCoeffEqv.zero_add _)))

#print axioms reciprocalResidual
#print axioms score
#print axioms reciprocal_angular_cancellation
#print axioms reciprocal_ratio_score_error

end YMGap.Continuum.QuaternionHaarReciprocalAngularScore
