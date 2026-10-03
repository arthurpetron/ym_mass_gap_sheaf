/-
# The cleared reciprocal score converges in the SAME weighted square form

The two signed errors from differentiated reciprocal cancellation are
estimated separately. Their budgets retain the actual score and the actual
product A*b*dR; no absolute coefficient cap or change of weight replaces
them. The derivative remainder costs (k+1)*rho^k, not merely rho^(k+1).
These are fixed-window estimates, NOT a uniform interacting-cost bound.
-/

import YMGap.Continuum.QuaternionHaarReciprocalAngularScore
import YMGap.Continuum.QuaternionHaarGeometricResidualAngularDerivative
import YMGap.Continuum.QuaternionHaarWeightedSquareTriangle
import YMGap.Continuum.QuaternionHaarIntervalSecondMoment

namespace YMGap.Continuum.QuaternionHaarReciprocalAngularScoreBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarIntervalSecondMoment
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarReciprocalAngularScore
open YMGap.Continuum.QuaternionHaarGeometricResidualAngularDerivative
open YMGap.Continuum.QuaternionHaarWeightedSquareTriangle

local infix:50 " ≈ " => Q'.eqv

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem weighted_multiplier_square_le {blocks : Nat} {W p r : RatPoly} {c : Q'}
    (M : Certificate blocks W) (P : SquareBound blocks p c)
    (hr : SupportedQuaternionBlocks blocks r) :
    quaternionHaar blocks (polyMul W (polyMul (polyMul p r) (polyMul p r))) ≤
      c * quaternionHaar blocks (polyMul W (polyMul r r)) := by
  let B := polyMul W (polyMul r r)
  let E := polyMul B (gap c p)
  have hn : (0 : Q') ≤ quaternionHaar blocks E :=
    ((M.mul (Certificate.square r hr)).mul P.certificate).haar_nonnegative
  have hid : RatPolyCoeffEqv
      (polyAdd (polyMul W (polyMul (polyMul p r) (polyMul p r))) E)
      (polyMul (cap c) B) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
        (.mul (.mul (.var 0) (.mul (.var 2) (.var 2)))
          (.add (.var 3) (.neg (.mul (.var 1) (.var 1))))))
      (.mul (.var 3) (.mul (.var 0) (.mul (.var 2) (.var 2))))
      (by decide) (fun | 0 => W | 1 => p | 2 => r | _ => cap c)
  have he :
      quaternionHaar blocks (polyMul W (polyMul (polyMul p r) (polyMul p r))) +
          quaternionHaar blocks E ≈ c * quaternionHaar blocks B :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append blocks _ _))
      (Q'.eqv_trans _ _ _ (haar_of_coeff (hid.trans (cap_mul_left c B)))
        (quaternionHaar_polySmul blocks c B))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn) (Q'.le_of_eqv he)

/-- Both signed reciprocal remainders have explicit same-weight budgets.
The actual derivative product remains on the right, not an assumed cap. -/
theorem reciprocal_ratio_score_error_square_le
    {blocks i j : Nat} {W A b : RatPoly} {ell u : Q'}
    (hi : i < 4*blocks) (hj : j < 4*blocks)
    (M : Certificate blocks W)
    (hA : SupportedQuaternionBlocks blocks A)
    (hb : SupportedQuaternionBlocks blocks b)
    (hu : (0 : Q') < u) (hle : ell ≤ u)
    (L : Certificate blocks (polyAdd A (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg A))) (k : Nat) :
    let rho := radius ell u hu
    let G := reciprocal A u hu (k+1)
    let S := score i j A b
    let R := remainder A u hu
    let e := polyAdd (polyMul (polyMul A A) (angularDerivative i j (polyMul b G)))
      (polyNeg S)
    quaternionHaar blocks (polyMul W (polyMul e e)) ≤
      sumBound
        ((rho^(k+1)*rho^(k+1)) * quaternionHaar blocks (polyMul W (polyMul S S)))
        (((Q'.ofNat (k+1)*Q'.ofNat (k+1))*(rho^k*rho^k)) *
          quaternionHaar blocks (polyMul W
            (polyMul (polyMul (polyMul A b) (angularDerivative i j R))
              (polyMul (polyMul A b) (angularDerivative i j R))))) := by
  dsimp only
  let R := remainder A u hu
  let S := score i j A b
  let p := polyNeg (polyMul (residual R (k+1)) S)
  let q := polyNeg (polyMul (polyMul A b) (angularDerivative i j (residual R (k+1))))
  let r := polyMul (polyMul A b) (angularDerivative i j R)
  let N := Q'.ofNat (k+1)
  let I := remainderInterval hA hu hle L U
  have hS : SupportedQuaternionBlocks blocks S :=
    supported_add (supported_polyMul hA (angularDerivative_supported_at hi hj hb))
      (support_neg (supported_polyMul hb (angularDerivative_supported_at hi hj hA)))
  have hR := remainder_supported hA u hu
  have hr : SupportedQuaternionBlocks blocks r :=
    supported_polyMul (supported_polyMul hA hb) (angularDerivative_supported_at hi hj hR)
  have hp : SupportedQuaternionBlocks blocks p :=
    support_neg (supported_polyMul (residualInterval I (k+1)).support hS)
  have hq : SupportedQuaternionBlocks blocks q :=
    support_neg (supported_polyMul (supported_polyMul hA hb)
      (angularDerivative_supported_at hi hj (residualInterval I (k+1)).support))
  have hpPin : RatPolyCoeffEqv p (polyMul (polyNeg (residual R (k+1))) S) :=
    coeffEvalExpr_eqv_of_normalize_eq (.neg (.mul (.var 0) (.var 1)))
      (.mul (.neg (.var 0)) (.var 1)) (by decide)
      (fun | 0 => residual R (k+1) | _ => S)
  have hqPin : RatPolyCoeffEqv q (polyMul (polyNeg (polySmul (-N) (residual R k))) r) := by
    refine (RatPolyCoeffEqv.neg
      ((residual_angularDerivative_succ i j R k).mul_left (polyMul A b))).trans ?_
    refine (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.polyMul_smul_right (-N) _ _)).trans ?_
    refine (RatPolyCoeffEqv.neg ((coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.var 2) (.mul (.mul (.var 0) (.var 1)) (.var 3))) (by decide)
      (fun | 0 => A | 1 => b | 2 => residual R k | _ => angularDerivative i j R)).smul (-N))).trans ?_
    refine (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.polyMul_smul_left (-N) _ _).symm).trans ?_
    exact coeffEvalExpr_eqv_of_normalize_eq (.neg (.mul (.var 0) (.var 1)))
      (.mul (.neg (.var 0)) (.var 1)) (by decide)
      (fun | 0 => polySmul (-N) (residual R k) | _ => r)
  let P := (QuaternionHaarIntervalSecondMoment.Interval.squareBound
    (residualInterval I (k+1))).neg
  let Q := ((QuaternionHaarIntervalSecondMoment.Interval.squareBound
    (residualInterval I k)).smul (-N)).neg
  have hcap : (-N)*(-N)*(radius ell u hu^k*radius ell u hu^k) ≈
      (N*N)*(radius ell u hu^k*radius ell u hu^k) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.neg (.var 0)) (.neg (.var 0))) (.var 1))
      (.mul (.mul (.var 0) (.var 0)) (.var 1)) (by decide)
      (fun | 0 => N | _ => radius ell u hu^k*radius ell u hu^k)
  have hpb := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (haar_of_coeff ((hpPin.mul hpPin).mul_left W)))
    (weighted_multiplier_square_le M P hS)
  have hqb := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (haar_of_coeff ((hqPin.mul hqPin).mul_left W)))
    (weighted_multiplier_square_le M (Q.changeCap hcap) hr)
  have he := reciprocal_ratio_score_error i j A b u hu (k+1)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (haar_of_coeff ((he.mul he).mul_left W)))
    (weighted_square_add_bound M hp hq hpb hqb)

#print axioms reciprocal_ratio_score_error_square_le

end YMGap.Continuum.QuaternionHaarReciprocalAngularScoreBound
