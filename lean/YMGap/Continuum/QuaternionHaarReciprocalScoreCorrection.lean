/-
The literal finite reciprocal score correction is +(k+1)*(-R)^k*b*D R.
Its square is paid in the SAME arbitrary certified Haar weight, with the
actual b*D R cost retained. A computed polynomial-geometric onset applies
to every later k, including zero radius and zero cost. This is fixed-window
control, not a family-uniform derivative or filtered-response estimate.
-/
import YMGap.Continuum.QuaternionHaarConditionalScoreGradient
import YMGap.Continuum.QuaternionHaarReciprocalAngularScore
import YMGap.Continuum.QuaternionHaarGeometricResidualAngularDerivative
import YMGap.Continuum.QuaternionHaarIntervalSecondMoment
import YMGap.Continuum.PolynomialGeometricDecay

namespace YMGap.Continuum.QuaternionHaarReciprocalScoreCorrection

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
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarReciprocalSensitivity
open YMGap.Continuum.QuaternionHaarConditionalScoreGradient (reciprocalScoreCorrection)
open YMGap.Continuum.QuaternionHaarReciprocalAngularScore (reciprocalResidual reciprocal_angular_cancellation)
open YMGap.Continuum.QuaternionHaarGeometricResidualAngularDerivative (residual_angularDerivative_succ)
open YMGap.Continuum.PolynomialGeometricDecay (polynomialCutoff polynomial_bound)
open YMGap.Continuum.ClusterCount (ofNat_nonneg ofNat_mul_eqv)

local infix:50 " ≈ " => Q'.eqv

private theorem isolate {p q : RatPoly} (h : RatPolyCoeffEqv (polyAdd p q) polyZero) :
    RatPolyCoeffEqv p (polyNeg q) :=
  (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (by decide)
    (fun | 0 => p | _ => q)).trans
    ((h.add (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.zero_add _))

/-- The correction is the signed derivative of the ORIGINAL residual.
No inverse polynomial or source derivative is substituted. -/
theorem reciprocalScoreCorrection_residual_derivative (i j : Nat) (A b : RatPoly)
    (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    RatPolyCoeffEqv (reciprocalScoreCorrection i j A b u hu k)
      (polyNeg (polyMul b (angularDerivative i j (reciprocalResidual A u hu k)))) := by
  let G := reciprocal A u hu k
  let J := reciprocalSlope A u hu k
  let dA := angularDerivative i j A
  let dE := angularDerivative i j (reciprocalResidual A u hu k)
  let F := polyMul (polyAdd G (polyNeg (polyMul A J))) dA
  have hd := reciprocal_angular_cancellation i j A u hu k
  have hstart : RatPolyCoeffEqv (polyAdd F dE)
      (polyAdd (polyAdd (polyMul A (polyNeg (polyMul J dA))) (polyMul G dA)) dE) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.add (.var 0) (.neg (.mul (.var 1) (.var 2)))) (.var 3)) (.var 4))
      (.add (.add (.mul (.var 1) (.neg (.mul (.var 2) (.var 3))))
        (.mul (.var 0) (.var 3))) (.var 4))
      (by decide) (fun | 0 => G | 1 => A | 2 => J | 3 => dA | _ => dE)
  have hzero : RatPolyCoeffEqv (polyAdd F dE) polyZero :=
    hstart.trans
      ((((reciprocal_angularDerivative i j A u hu k).symm.mul_left A).add
        (RatPolyCoeffEqv.refl _)).add (RatPolyCoeffEqv.refl _) |>.trans hd)
  exact ((isolate hzero).mul_left b).trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.var 0) (.neg (.var 1)))
      (.neg (.mul (.var 0) (.var 1))) (by decide) (fun | 0 => b | _ => dE))

/-- Exact positive successor coefficient, including k=0. -/
theorem reciprocalScoreCorrection_succ (i j : Nat) (A b : RatPoly)
    (u : Q') (hu : (0 : Q') < u) (k : Nat) :
    RatPolyCoeffEqv (reciprocalScoreCorrection i j A b u hu (k+1))
      (polyMul (polySmul (Q'.ofNat (k+1)) (residual (remainder A u hu) k))
        (polyMul b (angularDerivative i j (remainder A u hu)))) := by
  let N := Q'.ofNat (k+1)
  let E := residual (remainder A u hu) k
  let dR := angularDerivative i j (remainder A u hu)
  refine (reciprocalScoreCorrection_residual_derivative i j A b u hu (k+1)).trans ?_
  refine (RatPolyCoeffEqv.neg
    ((residual_angularDerivative_succ i j (remainder A u hu) k).mul_left b)).trans ?_
  have hn : RatPolyCoeffEqv (polyNeg (polyMul b (polySmul (-N) (polyMul E dR))))
      (polyMul (polySmul N E) (polyMul b dR)) := by
    refine (RatPolyCoeffEqv.neg
      ((cap_mul_left (-N) (polyMul E dR)).symm.mul_left b)).trans ?_
    have hc : RatPolyCoeffEqv (cap (-N)) (polyNeg (cap N)) := by
      intro weight
      change ((-N)*1)*weight []+0 ≈ (-(N*1))*weight []+0
      exact Q'.add_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.neg_mul_eqv N 1))
    refine (RatPolyCoeffEqv.neg (hc.mul_right (polyMul E dR) |>.mul_left b)).trans ?_
    exact (coeffEvalExpr_eqv_of_normalize_eq
      (.neg (.mul (.var 0) (.mul (.neg (.var 1)) (.mul (.var 2) (.var 3)))))
      (.mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3)))
      (by decide) (fun | 0 => b | 1 => cap N | 2 => E | _ => dR)).trans
      ((cap_mul_left N E).mul_right (polyMul b dR))
  exact hn

private def residual_squareBound {blocks : Nat} {R : RatPoly} {rho : Q'}
    (P : SquareBound blocks R (rho*rho)) :
    (k : Nat) → SquareBound blocks (residual R k) (rho^k*rho^k)
  | 0 => by
      simpa only [residual, Q'.pow_zero] using SquareBound.one blocks
  | k+1 => (P.neg.mul (residual_squareBound P k)).changeCap
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (by decide) (fun | 0 => rho | _ => rho^k))

private theorem weighted_multiplier_square_le {blocks : Nat} {W p r : RatPoly} {c : Q'}
    (M : Certificate blocks W) (P : SquareBound blocks p c)
    (hr : SupportedQuaternionBlocks blocks r) :
    quaternionHaar blocks (polyMul W (polyMul (polyMul p r) (polyMul p r))) ≤
      c*quaternionHaar blocks (polyMul W (polyMul r r)) := by
  let B := polyMul W (polyMul r r)
  let E := polyMul B (gap c p)
  have hn := ((M.mul (Certificate.square r hr)).mul P.certificate).haar_nonnegative
  have hid : RatPolyCoeffEqv
      (polyAdd (polyMul W (polyMul (polyMul p r) (polyMul p r))) E)
      (polyMul (cap c) B) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
        (.mul (.mul (.var 0) (.mul (.var 2) (.var 2)))
          (.add (.var 3) (.neg (.mul (.var 1) (.var 1))))))
      (.mul (.var 3) (.mul (.var 0) (.mul (.var 2) (.var 2))))
      (by decide) (fun | 0 => W | 1 => p | 2 => r | _ => cap c)
  have he := Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append blocks _ _))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (hid.trans (cap_mul_left c B)))
      (quaternionHaar_polySmul blocks c B))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn) (Q'.le_of_eqv he)

/-- Same-weight bound from a genuine radius-square certificate. SquareBound
uses a SQUARED cap; the input is therefore rho*rho, not rho. -/
theorem reciprocalScoreCorrection_square_le {blocks i j : Nat} {W A b : RatPoly} {u rho : Q'}
    (hi : i < 4*blocks) (hj : j < 4*blocks) (M : Certificate blocks W)
    (hA : SupportedQuaternionBlocks blocks A) (hb : SupportedQuaternionBlocks blocks b)
    (hu : (0 : Q') < u)
    (P : SquareBound blocks (remainder A u hu) (rho*rho)) (k : Nat) :
    let e := reciprocalScoreCorrection i j A b u hu (k+1)
    let r := polyMul b (angularDerivative i j (remainder A u hu))
    quaternionHaar blocks (polyMul W (polyMul e e)) ≤
      ((Q'.ofNat (k+1)*Q'.ofNat (k+1))*(rho^k*rho^k))*
        quaternionHaar blocks (polyMul W (polyMul r r)) := by
  dsimp only
  have hr := supported_polyMul hb
    (angularDerivative_supported_at hi hj (remainder_supported hA u hu))
  have hpin := reciprocalScoreCorrection_succ i j A b u hu k
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (haar_of_coeff ((hpin.mul hpin).mul_left W)))
    (weighted_multiplier_square_le M ((residual_squareBound P k).smul (Q'.ofNat (k+1))) hr)

/-- Actual cost and radius are retained in a computed all-later onset. -/
def correctionSquareModulus (rho cost epsilon : Q') : Nat :=
  polynomialCutoff rho cost 2 epsilon

private theorem correction_budget {rho cost epsilon : Q'}
    (hr0 : (0 : Q') ≤ rho) (hr1 : rho < 1) (hcost : (0 : Q') ≤ cost)
    (he : (0 : Q') < epsilon) (k : Nat)
    (hk : correctionSquareModulus rho cost epsilon ≤ k) :
    ((Q'.ofNat (k+1)*Q'.ofNat (k+1))*(rho^k*rho^k))*cost ≤ epsilon := by
  let N := Q'.ofNat (k+1)
  have hpow : rho^k*rho^k ≤ rho^k :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.pow_add_eqv rho k k)))
      (HKConvGen.pow_base_antitone hr0 (Q'.le_of_lt hr1) (by omega))
  have hnat : Q'.ofNat ((k+1)^2) ≈ N*N := by
    simpa only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul, N] using
      ofNat_mul_eqv (k+1) (k+1)
  have hreduce : ((N*N)*(rho^k*rho^k))*cost ≤ ((N*N)*rho^k)*cost :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hpow
        (Q'.mul_nonneg _ _ (ofNat_nonneg _) (ofNat_nonneg _))) hcost
  have horder : ((N*N)*rho^k)*cost ≈ rho^k*(cost*Q'.ofNat ((k+1)^2)) :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 2))
        (.mul (.var 1) (.mul (.var 2) (.mul (.var 0) (.var 0))))
        (by decide) (fun | 0 => N | 1 => rho^k | _ => cost))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hnat)))
  exact Q'.le_trans' _ _ _ hreduce
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv horder)
      (polynomial_bound hr0 hr1 hcost he 2 k hk))

/-- Original positive-window certificates produce the radius and both actual
cost squares. No caller-supplied derivative cost ceiling is used. -/
theorem reciprocalScoreCorrection_square_tolerance
    {blocks i j : Nat} {W A b : RatPoly} {ell u epsilon : Q'}
    (hi : i < 4*blocks) (hj : j < 4*blocks) (M : Certificate blocks W)
    (hA : SupportedQuaternionBlocks blocks A) (hb : SupportedQuaternionBlocks blocks b)
    (hell : (0 : Q') < ell) (hu : (0 : Q') < u) (hle : ell ≤ u)
    (L : Certificate blocks (polyAdd A (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg A)))
    (he : (0 : Q') < epsilon) (k : Nat)
    (hk : correctionSquareModulus (radius ell u hu)
      (quaternionHaar blocks (polyMul W
        (polyMul (polyMul b (angularDerivative i j (remainder A u hu)))
          (polyMul b (angularDerivative i j (remainder A u hu)))))) epsilon ≤ k) :
    let e := reciprocalScoreCorrection i j A b u hu (k+1)
    quaternionHaar blocks (polyMul W (polyMul e e)) ≤ epsilon := by
  have hr := supported_polyMul hb
    (angularDerivative_supported_at hi hj (remainder_supported hA u hu))
  have hcost := (M.mul (Certificate.square _ hr)).haar_nonnegative
  have P := QuaternionHaarIntervalSecondMoment.Interval.squareBound
    (remainderInterval hA hu hle L U)
  exact Q'.le_trans' _ _ _
    (reciprocalScoreCorrection_square_le hi hj M hA hb hu P k)
    (correction_budget (radius_nonnegative hu hle) (radius_lt_one hell hu) hcost he k hk)

#print axioms reciprocalScoreCorrection_residual_derivative
#print axioms reciprocalScoreCorrection_succ
#print axioms reciprocalScoreCorrection_square_le
#print axioms correctionSquareModulus
#print axioms reciprocalScoreCorrection_square_tolerance

end YMGap.Continuum.QuaternionHaarReciprocalScoreCorrection
