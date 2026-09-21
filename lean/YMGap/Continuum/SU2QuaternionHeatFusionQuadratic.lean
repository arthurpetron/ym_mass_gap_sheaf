/-
# Original heat-fusion alignment with an explicit cutoff error

The SAME endpoint source occurs on both sides of the remaining PSD kernel.
Its relative-character quadratics are nonnegative, and the actual SU(2)
dimension/Casimir inequality makes every bulk fusion coefficient nonnegative.
The negative boundary term is retained and bounded with a sharp character
certificate. This is a kinetic alignment bound, NOT a spatial variance gap,
pointwise positivity of the fusion residual, or a continuum theorem.
-/

import YMGap.Continuum.SU2HeatFusionCoefficientPositive
import YMGap.Continuum.SU2HeatFusionCutoffError
import YMGap.Continuum.SU2QuaternionProductHeatPositive
import YMGap.Continuum.SU2QuaternionWeightedProductLocalGap

namespace YMGap.Continuum.SU2QuaternionHeatFusionQuadratic

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RGTransport (dimQ)
open YMGap.Continuum.BondMovingStep (coeffW coeffW_zero coeffW_nonneg)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
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
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (heatAt_eq_prefix)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (edgeWeight eraseIndex select_perm mem_of_mem_erase)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct_perm)
open YMGap.Continuum.SU2HeatFusionCutoffError (cutoffError)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHeatFusionResidual
open YMGap.Continuum.SU2HeatFusionCoefficientPositive
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarUnitScalarSquare
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv

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

private theorem balance (j c b p e : Q') (h : j + -c ≈ b + (p + -e)) :
    j+e ≈ c+(b+p) :=
  Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.add (.var 0) (.var 4))
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.var 4))) (by decide)
      (fun | 0 => j | 1 => c | 2 => b | 3 => p | _ => e))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h)
      (poly_identity_of_normal_eq
        (.add (.add (.var 2) (.add (.var 3) (.neg (.var 4)))) (.add (.var 1) (.var 4)))
        (.add (.var 1) (.add (.var 2) (.var 3))) (by decide)
        (fun | 0 => j | 1 => c | 2 => b | 3 => p | _ => e)))

/-- The retained vacuum coefficient is one; all other quadratic terms are
nonnegative. This is an operator-form statement, not a pointwise heat floor. -/
theorem vacuum_le_prefix {n i : Nat} (hi : i < n) {W a : RatPoly}
    (hW : SupportedQuaternionBlocks (n+n) W)
    (hpositive : ∀ f, SupportedQuaternionBlocks n f → (0 : Q') ≤ haarQuadratic n W f)
    (ha : SupportedQuaternionBlocks n a) {w : Q'} (hw : (0 : Q') ≤ w) :
    ∀ K, haarQuadratic n W a ≤ insertion n W a (heatPrefix w K (scalarAt (n+i) i))
  | 0 => by
      have hp : RatPolyCoeffEqv (heatPrefix w 0 (scalarAt (n+i) i)) polyOne := by
        change RatPolyCoeffEqv (polyAdd (polySmul (coeffW w 0) polyOne) polyZero) polyOne
        rw [coeffW_zero]
        exact (RatPolyCoeffEqv.add_zero _).trans (RatPolyCoeffEqv.one_smul _)
      exact Q'.ge_of_eqv (Q'.eqv_trans _ _ _ (insertion_coeff n W a hp)
        (haar_of_coeff (RatPolyCoeffEqv.mul_one _)))
  | K+1 => by
      have hc := Q'.mul_nonneg _ _ (coeffW_nonneg hw (K+1))
        (character_insertion_nonnegative hi hW hpositive ha (K+1))
      have he : insertion n W a (heatPrefix w (K+1) (scalarAt (n+i) i)) ≈
          insertion n W a (heatPrefix w K (scalarAt (n+i) i)) +
            coeffW w (K+1) * insertion n W a (characterPolynomial (scalarAt (n+i) i) (K+1)) :=
        Q'.eqv_trans _ _ _ (insertion_coeff n W a (prefix_step w K _))
        (Q'.eqv_trans _ _ _ (insertion_add n W a _ _)
          (Q'.add_eqv_congr_left _ _ _ (insertion_smul n W a _ _)))
      have hinc := Q'.add_le_add_left (insertion n W a (heatPrefix w K (scalarAt (n+i) i))) _ _ hc
      rw [Q'.add_zero'] at hinc
      exact Q'.le_trans' _ _ _
        (Q'.le_trans' _ _ _ (vacuum_le_prefix hi hW hpositive ha hw K) hinc) (Q'.ge_of_eqv he)

/-- Exact original-quadratic alignment with BOTH boundary terms accounted
for. The sole error is coeffW(w,K+1)*(K+1), not an unspecified constant. -/
theorem prefix_alignment {n i : Nat} (hi : i < n) {W a : RatPoly}
    (hW : SupportedQuaternionBlocks (n+n) W)
    (hpositive : ∀ f, SupportedQuaternionBlocks n f → (0 : Q') ≤ haarQuadratic n W f)
    (ha : SupportedQuaternionBlocks n a)
    (R : Certificate (n+n) (polyMul W (polyMul a (liftBoundary n a))))
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) :
    coeffW w 1 * insertion n W a (heatPrefix w K (scalarAt (n+i) i)) ≤
      insertion n W a (polyMul (characterPolynomial (scalarAt (n+i) i) 1)
        (heatPrefix w K (scalarAt (n+i) i))) +
      (coeffW w (K+1) * dimQ K) * insertion n W a (heatPrefix w K (scalarAt (n+i) i)) := by
  let x := scalarAt (n+i) i
  let H := heatPrefix w K x
  have hb : (0 : Q') ≤ insertion n W a (bulkResidual w K x) := by
    apply sum_insertion_nonnegative
    intro j _
    exact Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ (fusionCoeff_nonnegative hw0 hw1 j)
      (character_insertion_nonnegative hi hW hpositive ha (j+1)))
      (Q'.ge_of_eqv (insertion_smul n W a _ _))
  have hp := Q'.mul_nonneg _ _ (coeffW_nonneg hw0 K)
    (character_insertion_nonnegative hi hW hpositive ha (K+1))
  have hl : insertion n W a
      (polyMul (polyAdd (characterPolynomial x 1) (polyNeg (cap (coeffW w 1)))) H) ≈
      insertion n W a (polyMul (characterPolynomial x 1) H) +
        -(coeffW w 1 * insertion n W a H) := by
    have he : RatPolyCoeffEqv
        (polyMul (polyAdd (characterPolynomial x 1) (polyNeg (cap (coeffW w 1)))) H)
        (polyAdd (polyMul (characterPolynomial x 1) H) (polyNeg (polySmul (coeffW w 1) H))) :=
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
        (by decide) (fun | 0 => characterPolynomial x 1 | 1 => cap (coeffW w 1) | _ => H)).trans
        ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul_left _ _)))
    exact Q'.eqv_trans _ _ _ (insertion_coeff n W a he)
      (Q'.eqv_trans _ _ _ (insertion_add n W a _ _)
        (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (insertion_neg n W a _)
          (Q'.neg_eqv_congr _ _ (insertion_smul n W a _ _)))))
  have hr : insertion n W a (polyAdd (bulkResidual w K x) (boundaryResidual w K x)) ≈
      insertion n W a (bulkResidual w K x) +
        (coeffW w K * insertion n W a (characterPolynomial x (K+1)) +
          -(coeffW w (K+1)*insertion n W a (characterPolynomial x K))) :=
    Q'.eqv_trans _ _ _ (insertion_add n W a _ _)
      (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (insertion_add n W a _ _)
        (Q'.add_eqv_congr' (insertion_smul n W a _ _)
          (Q'.eqv_trans _ _ _ (insertion_neg n W a _)
            (Q'.neg_eqv_congr _ _ (insertion_smul n W a _ _))))))
  have he := balance _ _ _ _ _ (Q'.eqv_trans _ _ _ (Q'.eqv_symm hl)
    (Q'.eqv_trans _ _ _ (insertion_coeff n W a (heat_fusion_residual w K x)) hr))
  have hinc := Q'.add_le_add_left (coeffW w 1 * insertion n W a H) _ _ (Q'.zero_le_add _ _ hb hp)
  rw [Q'.add_zero'] at hinc
  have hlower := Q'.le_trans' _ _ _ hinc (Q'.ge_of_eqv he)
  let word := PolyQuaternion.mul (PolyQuaternion.coordinateVariable (n+i))
    (PolyQuaternion.conj (PolyQuaternion.coordinateVariable i))
  have hs : Supported (n+n) word :=
    (Supported.coordinate (by omega)).mul (Supported.coordinate (by omega)).conj
  have hu : HaarCarrierEqv (n+n) (polyQuaternionNorm word) polyOne :=
    haarNorm_mul (haarNorm_coordinate (by omega))
      (HaarCarrierEqv.trans (RatPolyCoeffEqv.haarCarrier (polyQuaternionNorm_conj _))
        (haarNorm_coordinate (by omega)))
  have hchar := Q'.le_trans' _ _ _ (Q'.le_abs_self _)
    (character_weighted_haar_bound (SquareBound.scalar hs hu) R K)
  have herr := Q'.mul_le_mul_of_nonneg_left _ _ (coeffW w (K+1)) hchar (coeffW_nonneg hw0 _)
  have hbase := Q'.mul_le_mul_of_nonneg_left _ _ (coeffW w (K+1)*dimQ K)
    (vacuum_le_prefix hi hW hpositive ha hw0 K)
    (Q'.mul_nonneg _ _ (coeffW_nonneg hw0 _) (Q'.ofNat_nonneg _))
  exact Q'.le_trans' _ _ _ hlower
    (Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _ herr
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _)) hbase)))

/-- The bound for the ACTUAL product kernel with every other heat factor
and the full certified endpoint source retained. The coefficient has no
link-count or source dependence; its nome and cutoff dependence is explicit. -/
theorem product_alignment (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hids : ∀ j, j ∈ ids → j < n) (i : Nat) (hi : i ∈ ids)
    {a : RatPoly} (ha : SupportedQuaternionBlocks n a) (A : Certificate n a) :
    coeffW w 1 * quaternionHaar (n+n) (edgeWeight n w K ids a) ≤
      quaternionHaar (n+n) (polyMul (edgeWeight n w K ids a)
        (characterPolynomial (scalarAt (n+i) i) 1)) +
      cutoffError w K * quaternionHaar (n+n) (edgeWeight n w K ids a) := by
  let rest := eraseIndex i ids
  let W := productHeat n w K rest
  let H := heatPrefix w K (scalarAt (n+i) i)
  have hrest : ∀ j, j ∈ rest → j < n := fun j hj => hids j (mem_of_mem_erase i hj)
  have hW : SupportedQuaternionBlocks (n+n) W := productHeat_supported n w K rest hrest
  have hpositive := productHeat_quadratic_nonnegative n w (Q'.le_of_lt hw0) K rest hrest
  have R : Certificate (n+n) (polyMul W (polyMul a (liftBoundary n a))) :=
    (productHeatCertificate n hw0 hw1 K hK rest hrest).mul
      ((certificate_extend n ha A).mul (lift_certificate n A))
  have h := prefix_alignment (hids i hi) hW hpositive ha R
    (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) K
  have hprod : RatPolyCoeffEqv (productHeat n w K ids) (polyMul H W) := by
    have hp := polynomialProduct_perm (fun j => heatAt j (n+j) w K) (select_perm i hi)
    have hh := (heatAt_symm i (n+i) w K).mul_right W
    rw [heatAt_eq_prefix (n+i) i w K] at hh
    exact hp.trans hh
  have hedge : RatPolyCoeffEqv (edgeWeight n w K ids a)
      (polyMul (polyMul W (polyMul a (liftBoundary n a))) H) :=
    ((hprod.mul_right a).mul_right (liftBoundary n a)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
        (.mul (.mul (.var 1) (.mul (.var 2) (.var 3))) (.var 0)) (by decide)
        (fun | 0 => H | 1 => W | 2 => a | _ => liftBoundary n a))
  have hz : quaternionHaar (n+n) (edgeWeight n w K ids a) ≈ insertion n W a H :=
    haar_of_coeff hedge
  have hj : quaternionHaar (n+n) (polyMul (edgeWeight n w K ids a)
      (characterPolynomial (scalarAt (n+i) i) 1)) ≈
      insertion n W a (polyMul (characterPolynomial (scalarAt (n+i) i) 1) H) :=
    haar_of_coeff ((hedge.mul_right _).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 0) (.mul (.var 2) (.var 1))) (by decide)
        (fun | 0 => polyMul W (polyMul a (liftBoundary n a))
             | 1 => H | _ => characterPolynomial (scalarAt (n+i) i) 1)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hz))
    (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv
      (Q'.add_eqv_congr' hj (Q'.mul_eqv_congr_left _ _ _ hz))))

end YMGap.Continuum.SU2QuaternionHeatFusionQuadratic

#print axioms YMGap.Continuum.SU2QuaternionHeatFusionQuadratic.vacuum_le_prefix
#print axioms YMGap.Continuum.SU2QuaternionHeatFusionQuadratic.prefix_alignment
#print axioms YMGap.Continuum.SU2QuaternionHeatFusionQuadratic.product_alignment
