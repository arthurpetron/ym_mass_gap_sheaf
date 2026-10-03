/-
# Asymmetric square triangle in the SAME weighted Haar form

The certified square `(eta*p-q)^2`, with eta>0, gives coefficients
1+eta and 1+1/eta. Only the positive rational eta is inverted; the
original weight and both signed inputs remain unchanged. This permits
an arbitrarily small leading-square overhead when a separate correction
is small. It does not remove the original conditional Jensen debt or
produce an interacting variance/scaling estimate.
-/

import YMGap.Continuum.QuaternionHaarRelativePredictionFloor
import YMGap.Continuum.QuaternionHaarFamilySquare

namespace YMGap.Continuum.QuaternionHaarAsymmetricSquareTriangle

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_add)
open YMGap.Continuum.QuaternionHaarRelativePredictionFloor (weighted_square_young)

local infix:50 " ≈ " => Q'.eqv

private theorem square_add_pin (blocks : Nat) (W p q : RatPoly) :
    quaternionHaar blocks (polyMul W (polyMul (polyAdd p q) (polyAdd p q))) ≈
      (quaternionHaar blocks (polyMul W (polyMul p p)) +
        quaternionHaar blocks (polyMul W (polyMul q q))) +
      (quaternionHaar blocks (polyMul W (polyMul p q)) +
        quaternionHaar blocks (polyMul W (polyMul p q))) := by
  have hc : RatPolyCoeffEqv (polyMul (polyAdd p q) (polyAdd p q))
      (polyAdd (polyAdd (polyMul p p) (polyMul q q))
        (polyAdd (polyMul p q) (polyMul p q))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
      (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))))
      (by decide) (fun | 0 => p | _ => q)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (hc.mul_left W))
    (Q'.eqv_trans _ _ _ (haar_weighted_add blocks W _ _)
      (Q'.add_eqv_congr' (haar_weighted_add blocks W _ _)
        (haar_weighted_add blocks W _ _)))

private theorem cross_bound (eta : Q') (heta : (0 : Q') < eta)
    (p q cross : Q') (hy : 2*eta*cross ≤ eta*eta*p+q) :
    cross+cross ≤ eta*p+Q'.recipPos eta heta*q := by
  let v := Q'.recipPos eta heta
  have hv : eta*v ≈ 1 := Q'.mul_recipPos_eqv eta heta
  have hl : (2*eta*cross)*v ≈ cross+cross :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.mul (.const 2) (.var 0)) (.var 2)) (.var 1))
      (.mul (.const 2) (.mul (.mul (.var 0) (.var 1)) (.var 2)))
      (by decide) (fun | 0 => eta | 1 => v | _ => cross))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left 2 _ _ (Q'.mul_eqv_congr_right _ _ cross hv))
        (poly_identity_of_normal_eq
          (.mul (.const 2) (.mul (.const 1) (.var 0)))
          (.add (.var 0) (.var 0)) (by decide) (fun _ => cross)))
  have hr : (eta*eta*p+q)*v ≈ eta*p+v*q :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.add (.mul (.mul (.var 0) (.var 0)) (.var 2)) (.var 3)) (.var 1))
      (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
        (.mul (.var 1) (.var 3)))
      (by decide) (fun | 0 => eta | 1 => v | 2 => p | _ => q))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ (eta*p) hv)
          (Q'.eqv_refl _))
        (Q'.add_eqv_congr' (Q'.one_mul_eqv _) (Q'.eqv_refl _)))
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ v hy
    (Q'.le_of_lt (Q'.recipPos_pos eta heta))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hl))
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hr))

/-- Asymmetric triangle estimate for arbitrary supported signed inputs,
with exactly the SAME certified weight in all three Haar squares. -/
theorem weighted_square_add_le {blocks : Nat} {W p q : RatPoly}
    (eta : Q') (heta : (0 : Q') < eta)
    (P : Certificate blocks W)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    quaternionHaar blocks (polyMul W (polyMul (polyAdd p q) (polyAdd p q))) ≤
      (1+eta)*quaternionHaar blocks (polyMul W (polyMul p p)) +
        (1+Q'.recipPos eta heta)*quaternionHaar blocks (polyMul W (polyMul q q)) := by
  let pp := quaternionHaar blocks (polyMul W (polyMul p p))
  let qq := quaternionHaar blocks (polyMul W (polyMul q q))
  let pq := quaternionHaar blocks (polyMul W (polyMul p q))
  have hcross : pq+pq ≤ eta*pp+Q'.recipPos eta heta*qq :=
    cross_bound eta heta pp qq pq (weighted_square_young P hp hq eta)
  have hsum := Q'.add_le_add_left (pp+qq) _ _ hcross
  have hr : (pp+qq)+(eta*pp+Q'.recipPos eta heta*qq) ≈
      (1+eta)*pp+(1+Q'.recipPos eta heta)*qq :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1))
        (.add (.mul (.var 2) (.var 0)) (.mul (.var 3) (.var 1))))
      (.add (.mul (.add (.const 1) (.var 2)) (.var 0))
        (.mul (.add (.const 1) (.var 3)) (.var 1)))
      (by decide) (fun | 0 => pp | 1 => qq | 2 => eta | _ => Q'.recipPos eta heta)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (square_add_pin blocks W p q))
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hr))

/-- Separate rational square budgets combine with the same asymmetric
coefficients. No positivity hypotheses on a or b are needed. -/
theorem weighted_square_add_bound {blocks : Nat} {W p q : RatPoly}
    (eta : Q') (heta : (0 : Q') < eta)
    (P : Certificate blocks W)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    {a b : Q'}
    (ha : quaternionHaar blocks (polyMul W (polyMul p p)) ≤ a)
    (hb : quaternionHaar blocks (polyMul W (polyMul q q)) ≤ b) :
    quaternionHaar blocks (polyMul W (polyMul (polyAdd p q) (polyAdd p q))) ≤
      (1+eta)*a+(1+Q'.recipPos eta heta)*b := by
  have he : (0 : Q') ≤ 1+eta := Q'.zero_le_add 1 eta (by decide) (Q'.le_of_lt heta)
  have hv : (0 : Q') ≤ 1+Q'.recipPos eta heta :=
    Q'.zero_le_add 1 (Q'.recipPos eta heta) (by decide)
      (Q'.le_of_lt (Q'.recipPos_pos eta heta))
  exact Q'.le_trans' _ _ _ (weighted_square_add_le eta heta P hp hq)
    (Q'.add_le_add (Q'.mul_le_mul_of_nonneg_left _ _ _ ha he)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hb hv))

end YMGap.Continuum.QuaternionHaarAsymmetricSquareTriangle

#print axioms YMGap.Continuum.QuaternionHaarAsymmetricSquareTriangle.weighted_square_add_le
#print axioms YMGap.Continuum.QuaternionHaarAsymmetricSquareTriangle.weighted_square_add_bound
