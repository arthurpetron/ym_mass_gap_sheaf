/-
# Polynomial approximate division by the actual local-star normalizer

The reference form retains the entire complementary action B. The actual
normalizer D has L I <= D <= U I in this form. Starting from zero, the
explicit iteration a <- a + (r-D a)/U has residual norm bounded by
(1-L/U)^(2n) times the input norm. In particular it applies to the actual
inserted numerator, without replacing the original action by Haar.

This constructs finite polynomial approximate preimages. Completion with
an explicit Cauchy modulus, the limiting conditional update and spatial
control remain separate obligations. This is not an OS or physical gap.
-/

import YMGap.Continuum.BF4ExactSlabStarInsertedNumerator
import YMGap.Continuum.PositiveContractionResidual

namespace YMGap.Continuum.BF4ExactSlabStarInverseApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabStarInsertedNumerator
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.OSReconstructionProgress

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

/-- The actual B-weighted supported exterior polynomial carrier. Its
positivity is proved from the original action, not supplied as a premise. -/
def exteriorData {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) : GNSData :=
  let n := blocks extent-1
  let b := exterior w K extent link hl
  { weightedGNSData n polyOne (.one n) with
    B := fun p q => weightedPair n b p.val q.val
    B_congr_left := fun q h => haar_of_coeff ((h.mul_right q.val).mul_right b)
    B_add_left := fun p q r => weighted_add_left n b p.val q.val r.val
    B_smul_left := fun c p q => weighted_smul_left n b c p.val q.val
    B_symm := fun p q => weighted_symm n b p.val q.val
    self_nonneg := fun p => exterior_square_nonnegative hw0 hw1 K extent hK link hl p.val p.property }

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "G" => exteriorData hw0 hw1 K extent hK link hl

/-- Multiplication by the genuine integrated star, on supported polynomials. -/
def normalizerMap (r : (G).V) : (G).V :=
  ⟨polyMul r.val (normalizer w K extent link hl),
    supported_polyMul r.property (normalizer_supported w K extent link hl)⟩

local notation "M" => normalizerMap hw0 hw1 K extent hK link hl
local notation "s" => HKConv.divPos 1 (upperFactor w)

/-- The actual normalizer multiplier preserves polynomial differences. -/
theorem normalizerMap_sub (a b : (G).V) :
    (G).veq (M ((G).sub a b)) ((G).sub (M a) (M b)) := by
  change RatPolyCoeffEqv
    (polyMul (polyAdd a.val (polySmul (-1) b.val)) (normalizer w K extent link hl))
    (polyAdd (polyMul a.val (normalizer w K extent link hl))
      (polySmul (-1) (polyMul b.val (normalizer w K extent link hl))))
  rw [polyMul_add_left_exact]
  exact (RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.polyMul_smul_left _ _ _)

/-- The original local-star floor and cap act on the SAME B-weighted form. -/
theorem normalizerMap_form_bounds (a : (G).V) :
    lowerFactor w * (G).B a a ≤ (G).B a (M a) ∧
      (G).B a (M a) ≤ upperFactor w * (G).B a a := by
  have h := normalizer_weighted_form_bounds hw0 hw1 K extent hK link hl a.val a.property
  have hp : (G).B a (M a) ≈
      quaternionHaar (blocks extent-1)
        (polyMul (polyMul (polyMul a.val a.val) (normalizer w K extent link hl))
          (exterior w K extent link hl)) :=
    haar_of_coeff ((RatPolyCoeffEqv.mul_assoc _ _ _).symm.mul_right _)
  exact ⟨Q'.le_trans' _ _ _ h.1 (Q'.ge_of_eqv hp),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) h.2⟩

/-- Boundedness of the multiplier in the actual B-weighted exterior norm. -/
theorem normalizerMap_norm (a : (G).V) :
    (G).B (M a) (M a) ≤ (upperFactor w * upperFactor w) * (G).B a a :=
  normalizer_weighted_multiplication_norm hw0 hw1 K extent hK link hl a.val a.property

def scaledNormalizer (r : (G).V) : (G).V := (G).smul s (M r)

local notation "P" => scaledNormalizer hw0 hw1 K extent hK link hl

private theorem multiplier_symmetric (a b : (G).V) : (G).B a (M b) ≈ (G).B (M a) b :=
  haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
    (fun | 0 => a.val | 1 => b.val | _ => normalizer w K extent link hl)).mul_right _)

theorem scaledNormalizer_symmetric (a b : (G).V) : (G).B a (P b) ≈ (G).B (P a) b :=
  Q'.eqv_trans _ _ _ ((G).B_smul_right s a (M b))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (multiplier_symmetric hw0 hw1 K extent hK link hl a b))
      (Q'.eqv_symm ((G).B_smul_left s (M a) b)))

include hw0 in
private theorem inverse_cap_pin : s * upperFactor w ≈ 1 :=
  HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (upperFactor_positive hw0))

include hw0 in
private theorem scaled_floor_pin : s * lowerFactor w ≈ starRatio w := by
  have hr : starRatio w * upperFactor w ≈ lowerFactor w :=
    HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (upperFactor_positive hw0))
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hr))
    (Q'.eqv_trans _ _ _ (mul_pull _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (inverse_cap_pin hw0))
        (Q'.mul_one_eqv _)))

/-- Coercivity of the scaled ACTUAL normalizer, with explicit nome rate. -/
theorem scaledNormalizer_form_bounds (a : (G).V) :
    starRatio w * (G).B a a ≤ (G).B a (P a) ∧ (G).B a (P a) ≤ (G).B a a := by
  have hs : (0 : Q') ≤ s := HKConv.divPos_nonneg (by decide)
  have h := normalizer_weighted_form_bounds hw0 hw1 K extent hK link hl a.val a.property
  have hp : (G).B a (M a) ≈
      quaternionHaar (blocks extent-1)
        (polyMul (polyMul (polyMul a.val a.val) (normalizer w K extent link hl))
          (exterior w K extent link hl)) :=
    haar_of_coeff ((RatPolyCoeffEqv.mul_assoc _ _ _).symm.mul_right _)
  have he := (G).B_smul_right s a (M a)
  have hL : s * (lowerFactor w * (G).B a a) ≈ starRatio w * (G).B a a :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_eqv_congr_right _ _ _ (scaled_floor_pin hw0))
  have hU : s * (upperFactor w * (G).B a a) ≈ (G).B a a :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (inverse_cap_pin hw0))
        (Q'.one_mul_eqv _))
  exact ⟨Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.le_trans' _ _ _ h.1 (Q'.ge_of_eqv hp)) hs) (Q'.ge_of_eqv he)),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) h.2) hs) (Q'.le_of_eqv hU))⟩

def inverseRate (w : Q') : Q' := PositiveContractionResidual.rate (starRatio w)

include hw0 hw1 in
theorem inverseRate_bounds : (0 : Q') ≤ inverseRate w ∧ inverseRate w < (1 : Q') :=
  ⟨PositiveContractionResidual.rate_nonnegative (starRatio_le_one hw0 hw1),
    PositiveContractionResidual.rate_lt_one (starRatio_positive hw0 hw1)⟩

/-- Actual polynomial iteration, not an assumed inverse or limit witness. -/
def approximateInverse (r : (G).V) : Nat → (G).V
  | 0 => (G).zero
  | n+1 =>
    let a := approximateInverse r n
    (G).add a ((G).smul s ((G).sub r (M a)))

local notation "A" => approximateInverse hw0 hw1 K extent hK link hl

private theorem defect_step (r a : (G).V) :
    (G).veq ((G).sub r (M ((G).add a ((G).smul s ((G).sub r (M a))))))
      (PositiveContractionResidual.residual G P ((G).sub r (M a))) := by
  let e := ((G).sub r (M a)).val
  have hm : RatPolyCoeffEqv
      (polyMul (polyAdd a.val (polySmul s e)) (normalizer w K extent link hl))
      (polyAdd (polyMul a.val (normalizer w K extent link hl))
        (polySmul s (polyMul e (normalizer w K extent link hl)))) := by
    rw [polyMul_add_left_exact]
    exact (RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.polyMul_smul_left _ _ _)
  exact ((RatPolyCoeffEqv.refl r.val).add
    ((hm.smul (-1)).trans (RatPolyCoeffEqv.smul_add _ _ _))).trans
    (RatPolyCoeffEqv.add_assoc _ _ _).symm

/-- Geometric error for division by D in the actual B-weighted form. -/
theorem approximateInverse_residual_norm (r : (G).V) :
    ∀ n, (G).B ((G).sub r (M (A r n))) ((G).sub r (M (A r n))) ≤
      (inverseRate w * inverseRate w)^n * (G).B r r
  | 0 => by
      have hz : (G).veq (M (G).zero) (G).zero :=
        ((RatPolyCoeffEqv.zero_smul polyOne).mul_right _).trans
          ((RatPolyCoeffEqv.mul_zero_left _).trans (RatPolyCoeffEqv.zero_smul polyOne).symm)
      have he : (G).veq ((G).sub r (M (G).zero)) r :=
        (G).veq_trans ((G).add_congr ((G).veq_refl r) ((G).neg_congr hz))
          ((G).veq_trans ((G).add_congr ((G).veq_refl r) (G).neg_zero) ((G).add_zero r))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv ((G).B_diag_congr he))
        (Q'.ge_of_eqv (Q'.one_mul_eqv _))
  | n+1 => by
      have he := (G).B_diag_congr (defect_step hw0 hw1 K extent hK link hl r (A r n))
      have hc := PositiveContractionResidual.residual_norm G P
        (scaledNormalizer_symmetric hw0 hw1 K extent hK link hl)
        (starRatio_le_one hw0 hw1)
        (fun a => (scaledNormalizer_form_bounds hw0 hw1 K extent hK link hl a).2)
        (fun a => (scaledNormalizer_form_bounds hw0 hw1 K extent hK link hl a).1)
        ((G).sub r (M (A r n)))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
        (Q'.le_trans' _ _ _ hc (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _ (approximateInverse_residual_norm r n)
            (Q'.mul_nonneg _ _ (inverseRate_bounds hw0 hw1).1 (inverseRate_bounds hw0 hw1).1))
          (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))))

/-- Finite approximation to the original-law conditional update N_p/D.
It remains an exterior polynomial with a proved support witness. -/
def conditionalApproximation (p : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks extent) p) (n : Nat) : (G).V :=
  A ⟨insertedNormalizer w K extent link hl p,
    insertedNormalizer_supported w K extent link hl p hp⟩ n

/-- The division error is controlled by the ORIGINAL full-action input
norm, uniformly in volume/placement and K>=headCutoff(w), at fixed w. -/
theorem conditionalApproximation_defect_norm (p : RatPoly)
    (hp : SupportedQuaternionBlocks (blocks extent) p) (n : Nat) :
    let r : (G).V := ⟨insertedNormalizer w K extent link hl p,
      insertedNormalizer_supported w K extent link hl p hp⟩
    let a := conditionalApproximation hw0 hw1 K extent hK link hl p hp n
    (G).B ((G).sub r (M a)) ((G).sub r (M a)) ≤
      (inverseRate w * inverseRate w)^n * (upperFactor w *
        weightedPair (blocks extent)
          (polynomialProduct (faceHeatPolynomial w K extent) (slabPhysicalFaceEdges extent)) p p) := by
  exact Q'.le_trans' _ _ _
    (approximateInverse_residual_norm hw0 hw1 K extent hK link hl _ n)
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (insertedNormalizer_weighted_norm hw0 hw1 K extent hK link hl p hp)
      (Q'.pow_nonneg _ (Q'.mul_nonneg _ _
        (inverseRate_bounds hw0 hw1).1 (inverseRate_bounds hw0 hw1).1) n))

/-- A computed iteration count for a requested squared residual tolerance.
This is approximation data, not yet a Cauchy modulus for the preimages. -/
def approximationCutoff (r : (G).V) (epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff
    (inverseRate w * inverseRate w) ((G).B r r) epsilon

theorem approximateInverse_error_le (r : (G).V) (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (n : Nat)
    (hn : approximationCutoff hw0 hw1 K extent hK link hl r epsilon ≤ n) :
    (G).B ((G).sub r (M (A r n))) ((G).sub r (M (A r n))) ≤ epsilon := by
  have hq := inverseRate_bounds hw0 hw1
  have hq2 : inverseRate w * inverseRate w < (1 : Q') :=
    Q'.lt_of_le_of_lt (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_lt hq.2) hq.1)
      (Q'.le_of_eqv (Q'.one_mul_eqv _))) hq.2
  exact Q'.le_trans' _ _ _
    (approximateInverse_residual_norm hw0 hw1 K extent hK link hl r n)
    (PositiveContractionResidual.geometric_bound
      (Q'.mul_nonneg _ _ hq.1 hq.1) hq2 ((G).self_nonneg r) hepsilon n hn)

end YMGap.Continuum.BF4ExactSlabStarInverseApproximation

#print axioms YMGap.Continuum.BF4ExactSlabStarInverseApproximation.exteriorData
#print axioms YMGap.Continuum.BF4ExactSlabStarInverseApproximation.normalizerMap
#print axioms YMGap.Continuum.BF4ExactSlabStarInverseApproximation.normalizerMap_sub
#print axioms YMGap.Continuum.BF4ExactSlabStarInverseApproximation.normalizerMap_form_bounds
#print axioms YMGap.Continuum.BF4ExactSlabStarInverseApproximation.normalizerMap_norm
#print axioms YMGap.Continuum.BF4ExactSlabStarInverseApproximation.scaledNormalizer
#print axioms YMGap.Continuum.BF4ExactSlabStarInverseApproximation.scaledNormalizer_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabStarInverseApproximation.scaledNormalizer_form_bounds
#print axioms YMGap.Continuum.BF4ExactSlabStarInverseApproximation.inverseRate
#print axioms YMGap.Continuum.BF4ExactSlabStarInverseApproximation.inverseRate_bounds
#print axioms YMGap.Continuum.BF4ExactSlabStarInverseApproximation.approximateInverse
#print axioms YMGap.Continuum.BF4ExactSlabStarInverseApproximation.approximateInverse_residual_norm
#print axioms YMGap.Continuum.BF4ExactSlabStarInverseApproximation.conditionalApproximation
#print axioms YMGap.Continuum.BF4ExactSlabStarInverseApproximation.conditionalApproximation_defect_norm
#print axioms YMGap.Continuum.BF4ExactSlabStarInverseApproximation.approximationCutoff
#print axioms YMGap.Continuum.BF4ExactSlabStarInverseApproximation.approximateInverse_error_le
