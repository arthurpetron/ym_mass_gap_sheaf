/-
# Exact weighted score energy with its signed reciprocal correction

The literal cleared derivative is A*D(G*b)=G*S+e, where S is the
vacuum-subtracted score and e is reciprocalScoreCorrection. Expand its
square and retain BOTH the signed cross pairing and correction square.
No absolute values, square triangle, support or positivity premise occurs.
This is finite coefficient and Haar algebra, not an analytic estimate.
-/

import YMGap.Continuum.QuaternionHaarConditionalScoreGradient

namespace YMGap.Continuum.QuaternionHaarExactScoreEnergySplit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative (angularDerivative)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse (reciprocal)
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient
  (conditionalScore reciprocalScoreCorrection reciprocal_score_cleared_derivative)

local infix:50 " ≈ " => Q'.eqv

/-- Exact signed square expansion of the original finite reciprocal score.
The weight and sigma are arbitrary; no positive bound is substituted. -/
theorem reciprocal_score_weighted_energy_split (blocks i j : Nat)
    (W : RatPoly) (sigma : Q') (A b : RatPoly)
    (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    let G := reciprocal A u hu k
    let S := conditionalScore i j A b
    let e := reciprocalScoreCorrection i j A b u hu k
    (1+sigma)*quaternionHaar blocks
        (polyMul (polyMul W (polyMul G G)) (polyMul S S)) ≈
      ((quaternionHaar blocks
          (polyMul W (polyMul (polyMul A (angularDerivative i j (polyMul G b)))
            (polyMul A (angularDerivative i j (polyMul G b))))) +
        sigma*quaternionHaar blocks
          (polyMul (polyMul W (polyMul G G)) (polyMul S S))) +
        -(2*quaternionHaar blocks (polyMul W (polyMul (polyMul G S) e)))) +
        -quaternionHaar blocks (polyMul W (polyMul e e)) := by
  dsimp only
  let G := reciprocal A u hu k
  let S := conditionalScore i j A b
  let e := reciprocalScoreCorrection i j A b u hu k
  let F := polyMul A (angularDerivative i j (polyMul G b))
  let Lp := polyMul (polyMul W (polyMul G G)) (polyMul S S)
  let Cp := polyMul W (polyMul (polyMul G S) e)
  let Ep := polyMul W (polyMul e e)
  let L := quaternionHaar blocks Lp
  let C := quaternionHaar blocks Cp
  let E := quaternionHaar blocks Ep
  have hderivative : RatPolyCoeffEqv F (polyAdd (polyMul G S) e) :=
    reciprocal_score_cleared_derivative i j A b u hu k
  have hsquare : RatPolyCoeffEqv
      (polyMul W (polyMul (polyAdd (polyMul G S) e) (polyAdd (polyMul G S) e)))
      (polyAdd Lp (polyAdd Cp (polyAdd Cp Ep))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0)
        (.mul (.add (.mul (.var 1) (.var 2)) (.var 3))
          (.add (.mul (.var 1) (.var 2)) (.var 3))))
      (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))
        (.add (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
          (.add (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
            (.mul (.var 0) (.mul (.var 3) (.var 3))))))
      (by decide) (fun | 0 => W | 1 => G | 2 => S | _ => e)
  have hF : quaternionHaar blocks (polyMul W (polyMul F F)) ≈ L+(C+(C+E)) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (((hderivative.mul hderivative).mul_left W).trans hsquare))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks Lp (polyAdd Cp (polyAdd Cp Ep)))
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks Cp (polyAdd Cp Ep))
            (Q'.add_eqv_congr' (Q'.eqv_refl _) (quaternionHaar_append blocks Cp Ep)))))
  have hright :
      ((quaternionHaar blocks (polyMul W (polyMul F F))+sigma*L)+ -(2*C))+ -E ≈
      (((L+(C+(C+E)))+sigma*L)+ -(2*C))+ -E :=
    Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' hF (Q'.eqv_refl _)) (Q'.eqv_refl _))
      (Q'.eqv_refl _)
  have hcancel : (((L+(C+(C+E)))+sigma*L)+ -(2*C))+ -E ≈ (1+sigma)*L :=
    poly_identity_of_normal_eq
      (.add
        (.add
          (.add (.add (.var 0) (.add (.var 1) (.add (.var 1) (.var 2))))
            (.mul (.var 3) (.var 0)))
          (.neg (.mul (.const 2) (.var 1))))
        (.neg (.var 2)))
      (.mul (.add (.const 1) (.var 3)) (.var 0))
      (by decide) (fun | 0 => L | 1 => C | 2 => E | _ => sigma)
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hright hcancel)

#print axioms reciprocal_score_weighted_energy_split

end YMGap.Continuum.QuaternionHaarExactScoreEnergySplit
