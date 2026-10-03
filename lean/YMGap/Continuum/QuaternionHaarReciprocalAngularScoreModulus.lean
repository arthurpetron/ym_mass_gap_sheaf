/-
# A computed fixed-window modulus for the ORIGINAL cleared angular score

Both costs are actual nonnegative squares in the SAME certified Haar weight.
The geometric and differentiated-geometric tails have explicit all-later
onsets, including zero radius and zero costs. Nothing bounds either cost
uniformly in the window, action or scaling family.
-/

import YMGap.Continuum.QuaternionHaarReciprocalAngularScoreBound
import YMGap.Continuum.PolynomialGeometricDecay

namespace YMGap.Continuum.QuaternionHaarReciprocalAngularScoreModulus

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap sumBound)
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarReciprocalAngularScore
open YMGap.Continuum.QuaternionHaarReciprocalAngularScoreBound
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.PolynomialGeometricDecay (polynomialCutoff polynomial_bound)
open YMGap.Continuum.ClusterCount (ofNat_nonneg ofNat_mul_eqv)

private def quarter : Q' := Q'.mkPos 1 4 (by decide)

/-- Both thresholds retain the actual two square costs and the window radius. -/
def scoreErrorModulus (rho C0 C1 epsilon : Q') : Nat :=
  max (geometricCutoff rho C0 (quarter*epsilon))
    (polynomialCutoff rho C1 2 (quarter*epsilon))

private theorem power_square_le {rho : Q'} (hr0 : (0 : Q') ≤ rho)
    (hr1 : rho < (1 : Q')) (k : Nat) : rho^k*rho^k ≤ rho^k :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.pow_add_eqv rho k k)))
    (HKConvGen.pow_base_antitone hr0 (Q'.le_of_lt hr1) (by omega))

private theorem successor_power_square_le {rho : Q'} (hr0 : (0 : Q') ≤ rho)
    (hr1 : rho < (1 : Q')) (k : Nat) :
    rho^(k+1)*rho^(k+1) ≤ rho^k :=
  Q'.le_trans' _ _ _ (power_square_le hr0 hr1 (k+1))
    (HKConvGen.pow_base_antitone hr0 (Q'.le_of_lt hr1) (by omega))

private theorem quarter_budget (epsilon : Q') :
    Q'.eqv (sumBound (quarter*epsilon) (quarter*epsilon)) epsilon :=
  Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.add (.add (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0)))
      (.add (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))))
    (.mul (.add (.add (.var 1) (.var 1)) (.add (.var 1) (.var 1))) (.var 0))
    (by decide) (fun | 0 => epsilon | _ => quarter))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ epsilon
        (by decide : Q'.eqv ((quarter+quarter)+(quarter+quarter)) 1))
      (Q'.one_mul_eqv epsilon))

/-- The complete square-triangle budget is small at every computed later index.
No reciprocal radius occurs, so the zero-radius case is retained. -/
theorem score_error_budget_tolerance {rho C0 C1 epsilon : Q'}
    (hr0 : (0 : Q') ≤ rho) (hr1 : rho < (1 : Q'))
    (hC0 : (0 : Q') ≤ C0) (hC1 : (0 : Q') ≤ C1)
    (he : (0 : Q') < epsilon) (k : Nat)
    (hk : scoreErrorModulus rho C0 C1 epsilon ≤ k) :
    sumBound ((rho^(k+1)*rho^(k+1))*C0)
      (((Q'.ofNat (k+1)*Q'.ofNat (k+1))*(rho^k*rho^k))*C1) ≤ epsilon := by
  have heq : (0 : Q') < quarter*epsilon :=
    Q'.mul_pos (by decide : (0 : Q') < quarter) he
  have hk0 : geometricCutoff rho C0 (quarter*epsilon) ≤ k :=
    Nat.le_trans (Nat.le_max_left _ _) hk
  have hk1 : polynomialCutoff rho C1 2 (quarter*epsilon) ≤ k :=
    Nat.le_trans (Nat.le_max_right _ _) hk
  have h0 : (rho^(k+1)*rho^(k+1))*C0 ≤ quarter*epsilon :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (successor_power_square_le hr0 hr1 k) hC0)
      (geometric_bound hr0 hr1 hC0 heq k hk0)
  let N := Q'.ofNat (k+1)
  have hN : (0 : Q') ≤ N*N :=
    Q'.mul_nonneg _ _ (ofNat_nonneg _) (ofNat_nonneg _)
  have hreduce : ((N*N)*(rho^k*rho^k))*C1 ≤ ((N*N)*rho^k)*C1 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (power_square_le hr0 hr1 k) hN) hC1
  have hnat : Q'.eqv (Q'.ofNat ((k+1)^2)) (N*N) := by
    simpa only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul, N] using
      ofNat_mul_eqv (k+1) (k+1)
  have hreorder : Q'.eqv (((N*N)*rho^k)*C1)
      (rho^k*(C1*Q'.ofNat ((k+1)^2))) :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1)) (.var 2))
        (.mul (.var 1) (.mul (.var 2) (.mul (.var 0) (.var 0))))
        (by decide)
        (fun
          | 0 => N
          | 1 => rho^k
          | _ => C1))
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hnat)))
  have h1 : ((N*N)*(rho^k*rho^k))*C1 ≤ quarter*epsilon :=
    Q'.le_trans' _ _ _ hreduce (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder)
      (polynomial_bound hr0 hr1 hC1 heq 2 k hk1))
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add (Q'.add_le_add h0 h0) (Q'.add_le_add h1 h1))
    (Q'.le_of_eqv (quarter_budget epsilon))

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro term ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

/-- An actual weighted score-error tolerance, without any analytic cost cap.
The onset is computed from the two literal SAME-weight Haar squares. -/
theorem reciprocal_ratio_score_error_tolerance
    {blocks i j : Nat} {W A b : RatPoly} {ell u epsilon : Q'}
    (hi : i < 4*blocks) (hj : j < 4*blocks)
    (M : Certificate blocks W)
    (hA : SupportedQuaternionBlocks blocks A)
    (hb : SupportedQuaternionBlocks blocks b)
    (hell : (0 : Q') < ell) (hu : (0 : Q') < u) (hle : ell ≤ u)
    (L : Certificate blocks (polyAdd A (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg A)))
    (he : (0 : Q') < epsilon) (k : Nat)
    (hk : scoreErrorModulus (radius ell u hu)
      (quaternionHaar blocks (polyMul W (polyMul (score i j A b) (score i j A b))))
      (quaternionHaar blocks (polyMul W
        (polyMul (polyMul (polyMul A b) (angularDerivative i j (remainder A u hu)))
          (polyMul (polyMul A b) (angularDerivative i j (remainder A u hu)))))) epsilon ≤ k) :
    let G := reciprocal A u hu (k+1)
    let e := polyAdd (polyMul (polyMul A A) (angularDerivative i j (polyMul b G)))
      (polyNeg (score i j A b))
    quaternionHaar blocks (polyMul W (polyMul e e)) ≤ epsilon := by
  let S := score i j A b
  let R := remainder A u hu
  let r := polyMul (polyMul A b) (angularDerivative i j R)
  have hS : SupportedQuaternionBlocks blocks S :=
    supported_add (supported_polyMul hA (angularDerivative_supported_at hi hj hb))
      (support_neg (supported_polyMul hb (angularDerivative_supported_at hi hj hA)))
  have hr : SupportedQuaternionBlocks blocks r :=
    supported_polyMul (supported_polyMul hA hb)
      (angularDerivative_supported_at hi hj (remainder_supported hA u hu))
  have hC0 := (M.mul (Certificate.square S hS)).haar_nonnegative
  have hC1 := (M.mul (Certificate.square r hr)).haar_nonnegative
  exact Q'.le_trans' _ _ _
    (reciprocal_ratio_score_error_square_le hi hj M hA hb hu hle L U k)
    (score_error_budget_tolerance (radius_nonnegative hu hle) (radius_lt_one hell hu)
      hC0 hC1 he k hk)

end YMGap.Continuum.QuaternionHaarReciprocalAngularScoreModulus

#print axioms YMGap.Continuum.QuaternionHaarReciprocalAngularScoreModulus.scoreErrorModulus
#print axioms YMGap.Continuum.QuaternionHaarReciprocalAngularScoreModulus.score_error_budget_tolerance
#print axioms YMGap.Continuum.QuaternionHaarReciprocalAngularScoreModulus.reciprocal_ratio_score_error_tolerance
