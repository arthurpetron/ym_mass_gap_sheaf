/-
# Exact quartic moment with the original same-source insertion

The signed finite regrouping is applied to the actual Haar insertion,
retaining the complete spectator kernel and endpoint source. No coefficient
sign, relative-variance bound or physical scaling trajectory is assumed.
-/

import YMGap.Continuum.SU2HeatQuarticFiniteRegroup
import YMGap.Continuum.SU2QuaternionHeatQuarticExpansion
import YMGap.Continuum.SU2QuaternionHeatFusionQuadratic

namespace YMGap.Continuum.SU2QuaternionHeatQuarticMoment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionProductHeatPositive
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.SU2QuaternionHeatQuarticExpansion
open YMGap.Continuum.SU2HeatQuarticFiniteRegroup

local infix:50 " ≈ " => Q'.eqv

/-- Actual signed endpoint-source character response; no normalization changes. -/
def response (n : Nat) (W a x : RatPoly) (j : Nat) : Q' :=
  insertion n W a (characterPolynomial x j)

private theorem haar_neg (n : Nat) : ∀ p : RatPoly,
    quaternionHaar n (polyNeg p) ≈ -(quaternionHaar n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono n t.1)) (haar_neg n p))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem insertion_neg (n : Nat) (W a p : RatPoly) :
    insertion n W a (polyNeg p) ≈ -(insertion n W a p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.neg (.var 1))) (.neg (.mul (.var 0) (.var 1)))
    (by decide) (fun | 0 => polyMul W (polyMul a (liftBoundary n a)) | _ => p)))
    (haar_neg (n+n) _)

private theorem insertion_scale (n : Nat) (W a p : RatPoly) (c : Q') :
    insertion n W a (polyMul (cap c) p) ≈ c * insertion n W a p :=
  Q'.eqv_trans _ _ _ (insertion_coeff n W a (cap_mul_left c p))
    (insertion_smul n W a p c)

private theorem add_value (n : Nat) (W a : RatPoly) {p q : RatPoly}
    {u v : Q'} (hp : insertion n W a p ≈ u) (hq : insertion n W a q ≈ v) :
    insertion n W a (polyAdd p q) ≈ u+v :=
  Q'.eqv_trans _ _ _ (insertion_add n W a p q) (Q'.add_eqv_congr' hp hq)

private theorem scale_value (n : Nat) (W a : RatPoly) {p : RatPoly}
    {v : Q'} (c : Q') (hp : insertion n W a p ≈ v) :
    insertion n W a (polyMul (cap c) p) ≈ c*v :=
  Q'.eqv_trans _ _ _ (insertion_scale n W a p c)
    (Q'.mul_eqv_congr_left _ _ _ hp)

private theorem neg_value (n : Nat) (W a : RatPoly) {p : RatPoly}
    {v : Q'} (hp : insertion n W a p ≈ v) :
    insertion n W a (polyNeg p) ≈ -v :=
  Q'.eqv_trans _ _ _ (insertion_neg n W a p) (Q'.neg_eqv_congr _ _ hp)

/-- Exact response of each quartic basis row, including both exceptional spins. -/
theorem basis_value (n : Nat) (W a x : RatPoly) : ∀ j : Nat,
    insertion n W a (quarticBasis x j) ≈ quarticResponse (response n W a x) j
  | 0 =>
      add_value n W a
        (add_value n W a (scale_value n W a 5 (Q'.eqv_refl _))
          (neg_value n W a (scale_value n W a 4 (Q'.eqv_refl _))))
        (Q'.eqv_refl _)
  | 1 =>
      add_value n W a
        (add_value n W a (scale_value n W a 6 (Q'.eqv_refl _))
          (neg_value n W a (scale_value n W a 4
            (add_value n W a (Q'.eqv_refl _) (Q'.eqv_refl _)))))
        (Q'.eqv_refl _)
  | k+2 =>
      Q'.eqv_trans _ _ _ (add_value n W a
        (add_value n W a (scale_value n W a 6 (Q'.eqv_refl _))
          (neg_value n W a (scale_value n W a 4
            (add_value n W a (Q'.eqv_refl _) (Q'.eqv_refl _)))))
        (add_value n W a (Q'.eqv_refl _) (Q'.eqv_refl _)))
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

theorem insertion_sum_range (n : Nat) (W a : RatPoly) (f : Nat → RatPoly) :
    ∀ M, insertion n W a (finitePolySum f (List.range M)) ≈
      finSum (fun j => insertion n W a (f j)) M
  | 0 => haar_of_coeff (RatPolyCoeffEqv.mul_zero_right _)
  | M+1 => by
      rw [List.range_succ, PolynomialWeightedSumBounds.sum_append, finSum_succ]
      exact add_value n W a (insertion_sum_range n W a f M)
        (insertion_coeff n W a (RatPolyCoeffEqv.add_zero _))

/-- Original quartic moment before regrouping. No positivity is required. -/
theorem quartic_value (n : Nat) (W a x : RatPoly) (w : Q') (K : Nat) :
    insertion n W a (polyMul (polyMul (defect x) (defect x)) (heatPrefix w K x)) ≈
      finSum (fun j => coeffW w j * quarticResponse (response n W a x) j) (K+1) :=
  Q'.eqv_trans _ _ _ (insertion_coeff n W a (heat_quartic_expansion w K x))
    (Q'.eqv_trans _ _ _ (insertion_sum_range n W a _ (K+1))
      (finSum_eqv_congr _ _ (fun j =>
        Q'.eqv_trans _ _ _ (insertion_smul n W a _ _)
          (Q'.mul_eqv_congr_left _ _ _ (basis_value n W a x j))) (K+1)))

/-- Every coefficient on the right is formed from the same zero-extended
original prefix. Terms through output spin `K+2` are retained. -/
theorem quartic_value_regrouped (n : Nat) (W a x : RatPoly) (w : Q') (K : Nat) :
    insertion n W a (polyMul (polyMul (defect x) (defect x)) (heatPrefix w K x)) ≈
      finSum (fun j => quarticCoeff (cutCoeff w K) j * response n W a x j) (K+3) :=
  Q'.eqv_trans _ _ _ (quartic_value n W a x w K)
    (finite_regroup w K (response n W a x))

/-- The ordinary heat mass uses exactly the same responses and coefficients. -/
theorem prefix_value (n : Nat) (W a x : RatPoly) (w : Q') (K : Nat) :
    insertion n W a (heatPrefix w K x) ≈
      finSum (fun j => coeffW w j * response n W a x j) (K+1) :=
  Q'.eqv_trans _ _ _ (insertion_sum_range n W a _ (K+1))
    (finSum_eqv_congr _ _ (fun j => insertion_smul n W a _ _) (K+1))

#print axioms response
#print axioms basis_value
#print axioms insertion_sum_range
#print axioms quartic_value
#print axioms quartic_value_regrouped
#print axioms prefix_value

end YMGap.Continuum.SU2QuaternionHeatQuarticMoment
