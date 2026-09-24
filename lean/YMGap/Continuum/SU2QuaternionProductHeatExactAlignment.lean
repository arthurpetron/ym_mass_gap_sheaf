/-
# Error-free alignment in the original product heat quadratic

At the computed sufficient cutoff the final fusion channel is nonnegative.
Consequently the complete product kernel, with the SAME arbitrary signed
endpoint source on both sides, has an exact fundamental alignment bound.
The four-coordinate jump-square sum is at most `6*(1-w)` times the SAME
quadratic mass. There is no source Taylor budget, unmatched cutoff error,
number-of-links factor, or replacement by a bare Haar norm.

This is a finite quadratic-form estimate. Individual coordinate insertions
are not gauge-invariant Wilson observables, and neither a normalized variance
comparison nor a physical scaling or continuum conclusion follows here.
-/

import YMGap.Continuum.SU2HeatFusionCutoffPositive
import YMGap.Continuum.SU2QuaternionHeatFusionCutoffPositive
import YMGap.Continuum.QuaternionHaarChordalDifference

namespace YMGap.Continuum.SU2QuaternionProductHeatExactAlignment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BondMovingStep (coeffW coeffW_dev)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatPositive
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
  (heatAt_eq_prefix edgeWeight eraseIndex select_perm mem_of_mem_erase)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct_perm)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarChordalDifference
open YMGap.Continuum.QuaternionHaarWordDifference
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.SU2HeatFusionCutoffPositive (endpoint_coeff_le)
open YMGap.Continuum.SU2QuaternionHeatFusionCutoffPositive (prefix_alignment_no_error)

local infix:50 " ≈ " => Q'.eqv

/-- The original product kernel retains every factor and both complete signed
sources. Quadratic positivity, not pointwise source positivity, pays the bound. -/
theorem product_alignment_no_error (n : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K+1)
    (ids : List Nat) (hids : ∀ j, j ∈ ids → j < n) (i : Nat) (hi : i ∈ ids)
    {a : RatPoly} (ha : SupportedQuaternionBlocks n a) :
    coeffW w 1 * quaternionHaar (n+n) (edgeWeight n w (K+1) ids a) ≤
      quaternionHaar (n+n) (polyMul (edgeWeight n w (K+1) ids a)
        (characterPolynomial (scalarAt (n+i) i) 1)) := by
  let rest := eraseIndex i ids
  let W := productHeat n w (K+1) rest
  let H := heatPrefix w (K+1) (scalarAt (n+i) i)
  have hrest : ∀ j, j ∈ rest → j < n := fun j hj => hids j (mem_of_mem_erase i hj)
  have hW : SupportedQuaternionBlocks (n+n) W := productHeat_supported n w (K+1) rest hrest
  have hpositive := productHeat_quadratic_nonnegative n w hw0 (K+1) rest hrest
  have hedgeCoeff : coeffW w 1 * coeffW w (K+1) ≤ coeffW w K := by
    simpa only [Nat.add_sub_cancel] using endpoint_coeff_le hw0 hw1 hK
  have h := prefix_alignment_no_error (hids i hi) hW hpositive ha hw0
    (Q'.le_of_lt hw1) K hedgeCoeff
  have hprod : RatPolyCoeffEqv (productHeat n w (K+1) ids) (polyMul H W) := by
    have hp := polynomialProduct_perm (fun j => heatAt j (n+j) w (K+1)) (select_perm i hi)
    have hh := (heatAt_symm i (n+i) w (K+1)).mul_right W
    rw [heatAt_eq_prefix (n+i) i w (K+1)] at hh
    exact hp.trans hh
  have hedge : RatPolyCoeffEqv (edgeWeight n w (K+1) ids a)
      (polyMul (polyMul W (polyMul a (liftBoundary n a))) H) :=
    ((hprod.mul_right a).mul_right (liftBoundary n a)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
        (.mul (.mul (.var 1) (.mul (.var 2) (.var 3))) (.var 0)) (by decide)
        (fun | 0 => H | 1 => W | 2 => a | _ => liftBoundary n a))
  have hz : quaternionHaar (n+n) (edgeWeight n w (K+1) ids a) ≈ insertion n W a H :=
    haar_of_coeff hedge
  have hj : quaternionHaar (n+n) (polyMul (edgeWeight n w (K+1) ids a)
      (characterPolynomial (scalarAt (n+i) i) 1)) ≈
      insertion n W a (polyMul (characterPolynomial (scalarAt (n+i) i) 1) H) :=
    haar_of_coeff ((hedge.mul_right _).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 0) (.mul (.var 2) (.var 1))) (by decide)
        (fun
          | 0 => polyMul W (polyMul a (liftBoundary n a)) | 1 => H
          | _ => characterPolynomial (scalarAt (n+i) i) 1)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hz))
    (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv hj))

private theorem gap_subtract (c z j : Q') (h : c*z ≤ j) :
    2*z + -j ≤ (2-c)*z := by
  have hn := Q'.add_le_add_left (2*z) _ _ (Q'.neg_le_neg h)
  exact Q'.le_trans' _ _ _ hn (Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.add (.mul (.const 2) (.var 1)) (.neg (.mul (.var 0) (.var 1))))
      (.mul (.add (.const 2) (.neg (.var 0))) (.var 1))
      (by decide) (fun | 0 => c | _ => z)))

/-- The whole four-coordinate jump square, before a Wilson-word telescope.
The right side is the SAME weighted quadratic mass, not a source L2 ceiling. -/
theorem product_displacement_bound (n : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K+1)
    (ids : List Nat) (hids : ∀ j, j ∈ ids → j < n) (i : Nat) (hi : i ∈ ids)
    {a : RatPoly} (ha : SupportedQuaternionBlocks n a) :
    quaternionHaar (n+n) (polyMul (edgeWeight n w (K+1) ids a)
      (polyQuaternionNorm (difference (PolyQuaternion.coordinateVariable i)
        (PolyQuaternion.coordinateVariable (n+i))))) ≤
      (2-coeffW w 1) * quaternionHaar (n+n) (edgeWeight n w (K+1) ids a) := by
  let W := edgeWeight n w (K+1) ids a
  have hin := hids i hi
  have hc := norm_difference_character
    (haarNorm_coordinate (by omega : i < n+n))
    (haarNorm_coordinate (by omega : n+i < n+n)) W
  have hm : quaternionHaar (n+n) (polyMul W (cap 2)) ≈
      2*quaternionHaar (n+n) W :=
    Q'.eqv_trans _ _ _ (weighted_scale _ W polyOne 2)
      (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_one W)))
  have he := Q'.eqv_trans _ _ _ hc
    (Q'.eqv_trans _ _ _ (weighted_difference _ W _ _)
      (Q'.add_eqv_congr' hm (Q'.eqv_refl _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (gap_subtract _ _ _ (product_alignment_no_error n hw0 hw1 K hK ids hids i hi ha))

/-- The explicit linear nome-defect budget has no cutoff, volume or source
coefficient after the computed onset. Signed sources are still allowed. -/
theorem product_displacement_nome_bound (n : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K+1)
    (ids : List Nat) (hids : ∀ j, j ∈ ids → j < n) (i : Nat) (hi : i ∈ ids)
    {a : RatPoly} (ha : SupportedQuaternionBlocks n a) :
    quaternionHaar (n+n) (polyMul (edgeWeight n w (K+1) ids a)
      (polyQuaternionNorm (difference (PolyQuaternion.coordinateVariable i)
        (PolyQuaternion.coordinateVariable (n+i))))) ≤
      (6*(1-w)) * quaternionHaar (n+n) (edgeWeight n w (K+1) ids a) := by
  have hz : (0 : Q') ≤ quaternionHaar (n+n) (edgeWeight n w (K+1) ids a) :=
    Q'.le_trans' _ _ _ (productHeat_quadratic_nonnegative n w hw0 (K+1) ids hids a ha)
      (Q'.ge_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _)))
  have hd : 2-coeffW w 1 ≤ 6*(1-w) :=
    Q'.le_trans' _ _ _ (coeffW_dev hw0 (Q'.le_of_lt hw1) 1)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.const 2) (.mul (.const 3) (.var 0)))
        (.mul (.const 6) (.var 0)) (by decide) (fun _ => (1 : Q')-w)))
  exact Q'.le_trans' _ _ _ (product_displacement_bound n hw0 hw1 K hK ids hids i hi ha)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hd hz)

end YMGap.Continuum.SU2QuaternionProductHeatExactAlignment

#print axioms YMGap.Continuum.SU2QuaternionProductHeatExactAlignment.product_alignment_no_error
#print axioms YMGap.Continuum.SU2QuaternionProductHeatExactAlignment.product_displacement_bound
#print axioms YMGap.Continuum.SU2QuaternionProductHeatExactAlignment.product_displacement_nome_bound
