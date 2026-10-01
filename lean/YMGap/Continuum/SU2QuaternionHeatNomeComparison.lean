/-
# Heat-nome order and floor-free additive-error absorption

For the SAME endpoint source and any retained positive-semidefinite spectator
kernel, decreasing the selected heat nome decreases its quadratic mass.
The vacuum channel also bounds the erased-link mass by that same partition.
Consequently a certified affine kernel bound c*H_u+epsilon dominates its
insertion by (c+epsilon)*Z_w when 0<=u<=w. No heat minimum is divided out.

This constructs the mass-comparison and cutoff-error consumer. It does NOT
supply a pointwise quartic heat-kernel bound or a SAME-variance scaling bound.
-/

import YMGap.Continuum.SU2QuaternionHeatFusionQuadratic
import YMGap.Continuum.QuaternionHaarWordDifference
import YMGap.Continuum.HeatKernelGap

namespace YMGap.Continuum.SU2QuaternionHeatNomeComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RGTransport (dimQ dimQ_nonneg)
open YMGap.Continuum.BondMovingStep (coeffW coeffW_zero)
open YMGap.Continuum.HeatKernelGap (qpow_mono)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (scalarAt)
open YMGap.Continuum.SU2QuaternionProductHeatPositive
open YMGap.Continuum.SU2QuaternionHeatFusionResidual (prefix_step)
open YMGap.Continuum.SU2QuaternionHeatFusionQuadratic (vacuum_le_prefix)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarWordDifference (weighted_order)

local infix:50 " ≈ " => Q'.eqv

/-- The actual dimension and Casimir coefficients, not a surrogate rate. -/
theorem coefficient_mono {u w : Q'} (hu : (0 : Q') ≤ u) (huw : u ≤ w) (j : Nat) :
    coeffW u j ≤ coeffW w j :=
  Q'.mul_le_mul_of_nonneg_left _ _ _ (qpow_mono hu huw _) (dimQ_nonneg j)

private theorem zero_pin (w : Q') (x : RatPoly) :
    RatPolyCoeffEqv (heatPrefix w 0 x) polyOne := by
  change RatPolyCoeffEqv (polyAdd (polySmul (coeffW w 0) polyOne) polyZero) polyOne
  rw [coeffW_zero]
  exact (RatPolyCoeffEqv.add_zero _).trans (RatPolyCoeffEqv.one_smul _)

private theorem value_step (n : Nat) (W a : RatPoly) (w : Q') (K : Nat) (x : RatPoly) :
    insertion n W a (heatPrefix w (K+1) x) ≈
      insertion n W a (heatPrefix w K x) +
        coeffW w (K+1) * insertion n W a (characterPolynomial x (K+1)) :=
  Q'.eqv_trans _ _ _ (insertion_coeff n W a (prefix_step w K x))
    (Q'.eqv_trans _ _ _ (insertion_add n W a _ _)
      (Q'.add_eqv_congr_left _ _ _ (insertion_smul n W a _ _)))

/-- Selected-link heat-nome monotonicity with all spectators and the SAME
signed endpoint source retained. No pointwise source positivity is needed. -/
theorem prefix_nome_mono {n i : Nat} (hi : i < n) {W a : RatPoly}
    (hW : SupportedQuaternionBlocks (n+n) W)
    (hpositive : ∀ f, SupportedQuaternionBlocks n f → (0 : Q') ≤ haarQuadratic n W f)
    (ha : SupportedQuaternionBlocks n a) {u w : Q'}
    (hu : (0 : Q') ≤ u) (huw : u ≤ w) :
    ∀ K, insertion n W a (heatPrefix u K (scalarAt (n+i) i)) ≤
      insertion n W a (heatPrefix w K (scalarAt (n+i) i))
  | 0 => Q'.le_of_eqv (insertion_coeff n W a ((zero_pin u _).trans (zero_pin w _).symm))
  | K+1 => by
      have hc := Q'.mul_le_mul_of_nonneg_right _ _ _ (coefficient_mono hu huw (K+1))
        (character_insertion_nonnegative hi hW hpositive ha (K+1))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (value_step n W a u K _))
        (Q'.le_trans' _ _ _
          (Q'.add_le_add (prefix_nome_mono hi hW hpositive ha hu huw K) hc)
          (Q'.ge_of_eqv (value_step n W a w K _)))

/-- The nome w*w is the twice-heat-time nome, but only this exact rational
comparison is used. No logarithm or physical time calibration is assumed. -/
theorem prefix_squared_nome_le {n i : Nat} (hi : i < n) {W a : RatPoly}
    (hW : SupportedQuaternionBlocks (n+n) W)
    (hpositive : ∀ f, SupportedQuaternionBlocks n f → (0 : Q') ≤ haarQuadratic n W f)
    (ha : SupportedQuaternionBlocks n a) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) :
    insertion n W a (heatPrefix (w*w) K (scalarAt (n+i) i)) ≤
      insertion n W a (heatPrefix w K (scalarAt (n+i) i)) :=
  prefix_nome_mono hi hW hpositive ha (Q'.mul_nonneg _ _ hw0 hw0)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ w hw1 hw0)
      (Q'.le_of_eqv (Q'.one_mul_eqv w))) K

/-- An additive constant kernel error costs at most its coefficient times
the original mass. The positivity used here is spectral, not a heat floor. -/
theorem constant_error_le {n i : Nat} (hi : i < n) {W a : RatPoly}
    (hW : SupportedQuaternionBlocks (n+n) W)
    (hpositive : ∀ f, SupportedQuaternionBlocks n f → (0 : Q') ≤ haarQuadratic n W f)
    (ha : SupportedQuaternionBlocks n a) {w e : Q'}
    (hw : (0 : Q') ≤ w) (he : (0 : Q') ≤ e) (K : Nat) :
    insertion n W a (cap e) ≤ e * insertion n W a (heatPrefix w K (scalarAt (n+i) i)) := by
  have hpin : insertion n W a (cap e) ≈ e * haarQuadratic n W a :=
    Q'.eqv_trans _ _ _ (insertion_smul n W a polyOne e)
      (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_one _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
    (Q'.mul_le_mul_of_nonneg_left _ _ e (vacuum_le_prefix hi hW hpositive ha hw K) he)

/-- Consume a concrete positive-polynomial kernel certificate. This is the
floor-free absorption rule, NOT a producer of the missing quartic certificate.
Pointwise positivity of the full spectator/source insertion is explicit. -/
theorem affine_prefix_bound {n i : Nat} (hi : i < n) {W a p : RatPoly}
    (hW : SupportedQuaternionBlocks (n+n) W)
    (hpositive : ∀ f, SupportedQuaternionBlocks n f → (0 : Q') ≤ haarQuadratic n W f)
    (ha : SupportedQuaternionBlocks n a)
    (R : Certificate (n+n) (polyMul W (polyMul a (liftBoundary n a))))
    {u w c e : Q'} (hu : (0 : Q') ≤ u) (huw : u ≤ w)
    (hc : (0 : Q') ≤ c) (he : (0 : Q') ≤ e) (K : Nat)
    (S : Certificate (n+n) (polyAdd
      (polyAdd (polySmul c (heatPrefix u K (scalarAt (n+i) i))) (cap e)) (polyNeg p))) :
    insertion n W a p ≤ (c+e) * insertion n W a (heatPrefix w K (scalarAt (n+i) i)) := by
  have h := weighted_order R S
  have hp : insertion n W a
      (polyAdd (polySmul c (heatPrefix u K (scalarAt (n+i) i))) (cap e)) ≈
        c * insertion n W a (heatPrefix u K (scalarAt (n+i) i)) + insertion n W a (cap e) :=
    Q'.eqv_trans _ _ _ (insertion_add n W a _ _)
      (Q'.add_eqv_congr_right _ _ _ (insertion_smul n W a _ c))
  have hs := Q'.add_le_add
    (Q'.mul_le_mul_of_nonneg_left _ _ c (prefix_nome_mono hi hW hpositive ha hu huw K) hc)
    (constant_error_le hi hW hpositive ha (Q'.le_trans' _ _ _ hu huw) he K)
  have hsum := poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
    (.mul (.add (.var 0) (.var 1)) (.var 2)) (by decide)
    (fun | 0 => c | 1 => e | _ => insertion n W a (heatPrefix w K (scalarAt (n+i) i)))
  exact Q'.le_trans' _ _ _ h
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
      (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hsum)))

#print axioms coefficient_mono
#print axioms prefix_nome_mono
#print axioms prefix_squared_nome_le
#print axioms constant_error_le
#print axioms affine_prefix_bound

end YMGap.Continuum.SU2QuaternionHeatNomeComparison
