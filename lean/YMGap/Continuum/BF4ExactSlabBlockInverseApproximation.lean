/-
# Explicit polynomial division by the original finite-block normalizer

On the exact detached original background, iterate a <- a+(r-D*a)/U
starting from zero. The proved all-nome form bounds give squared residual
decay (1-L/U)^(2n), with a computed absolute tolerance cutoff. No inverse
or block-correlation estimate is assumed. Constants depend on nome and block
size, not ambient volume or late heat cutoff; this is not a scaling gap.
-/

import YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
import YMGap.Continuum.PositiveContractionResidual

namespace YMGap.Continuum.BF4ExactSlabBlockInverseApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabBlockComparisonConstants
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.OSReconstructionProgress

local infix:50 " ≈ " => Q'.eqv

def blockRatio (w : Q') (size : Nat) : Q' :=
  HKConv.divPos (blockLower w size) (blockUpper w size)

theorem blockRatio_positive {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (size : Nat) : (0 : Q') < blockRatio w size :=
  HKConv.divPos_pos (CReal.num_pos_of_pos (blockLower_positive hw0 hw1 size))

theorem blockRatio_le_one {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (size : Nat) : blockRatio w size ≤ (1 : Q') := by
  apply HKConv.divPos_le_of_le (CReal.num_pos_of_pos (blockUpper_positive hw0 size))
  exact Q'.le_trans' _ _ _
    (CRealLog.pow_le_pow_base _ _ (Q'.le_of_lt (localFloor_positive hw0 hw1))
      (Q'.le_trans' _ _ _ Q'.min_le_right (one_le_localCap hw0)) (6*size))
    (Q'.ge_of_eqv (Q'.one_mul_eqv _))

def inverseRate (w : Q') (size : Nat) : Q' :=
  PositiveContractionResidual.rate (blockRatio w size)

theorem inverseRate_bounds {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (size : Nat) :
    (0 : Q') ≤ inverseRate w size ∧ inverseRate w size < (1 : Q') :=
  ⟨PositiveContractionResidual.rate_nonnegative (blockRatio_le_one hw0 hw1 size),
    PositiveContractionResidual.rate_lt_one (blockRatio_positive hw0 hw1 size)⟩

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link)

local notation "G" => backgroundData hw0 hw1 K extent hK links
local notation "M" => normalizerMap hw0 hw1 K extent hK links
local notation "s" => HKConv.divPos 1 (blockUpper w links.length)

def scaledNormalizer (r : (G).V) : (G).V := (G).smul s (M r)

local notation "P" => scaledNormalizer hw0 hw1 K extent hK links

theorem scaledNormalizer_symmetric (a b : (G).V) :
    (G).B a (P b) ≈ (G).B (P a) b :=
  Q'.eqv_trans _ _ _ ((G).B_smul_right s a (M b))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (normalizerMap_symmetric hw0 hw1 K extent hK links a b))
      (Q'.eqv_symm ((G).B_smul_left s (M a) b)))

include hw0 in
private theorem inverse_cap_pin : s * blockUpper w links.length ≈ 1 :=
  HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (blockUpper_positive hw0 links.length))

include hw0 in
private theorem scaled_floor_pin : s * blockLower w links.length ≈ blockRatio w links.length := by
  have hr : blockRatio w links.length * blockUpper w links.length ≈ blockLower w links.length :=
    HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (blockUpper_positive hw0 links.length))
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hr))
    (Q'.eqv_trans _ _ _ (mul_pull _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (inverse_cap_pin hw0 links))
        (Q'.mul_one_eqv _)))

theorem scaledNormalizer_form_bounds
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (a : (G).V) :
    blockRatio w links.length * (G).B a a ≤ (G).B a (P a) ∧
      (G).B a (P a) ≤ (G).B a a := by
  have hs : (0 : Q') ≤ s := HKConv.divPos_nonneg (by decide)
  have h := normalizerMap_form_bounds hw0 hw1 K extent hK links hl a
  have he := (G).B_smul_right s a (M a)
  have hL : s * (blockLower w links.length * (G).B a a) ≈
      blockRatio w links.length * (G).B a a :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_eqv_congr_right _ _ _ (scaled_floor_pin hw0 links))
  have hU : s * (blockUpper w links.length * (G).B a a) ≈ (G).B a a :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (inverse_cap_pin hw0 links))
        (Q'.one_mul_eqv _))
  exact ⟨Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ h.1 hs) (Q'.ge_of_eqv he)),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ h.2 hs) (Q'.le_of_eqv hU))⟩

/-- Explicit supported polynomials, with zero initial iterate. -/
def approximateInverse (r : (G).V) : Nat → (G).V
  | 0 => (G).zero
  | n+1 =>
    let a := approximateInverse r n
    (G).add a ((G).smul s ((G).sub r (M a)))

local notation "A" => approximateInverse hw0 hw1 K extent hK links

private theorem defect_step (r a : (G).V) :
    (G).veq ((G).sub r (M ((G).add a ((G).smul s ((G).sub r (M a))))))
      (PositiveContractionResidual.residual G P ((G).sub r (M a))) := by
  let e := ((G).sub r (M a)).val
  have hm : RatPolyCoeffEqv
      (polyMul (polyAdd a.val (polySmul s e)) (normalizer w K extent links))
      (polyAdd (polyMul a.val (normalizer w K extent links))
        (polySmul s (polyMul e (normalizer w K extent links)))) := by
    rw [polyMul_add_left_exact]
    exact (RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.polyMul_smul_left _ _ _)
  exact ((RatPolyCoeffEqv.refl r.val).add
    ((hm.smul (-1)).trans (RatPolyCoeffEqv.smul_add _ _ _))).trans
    (RatPolyCoeffEqv.add_assoc _ _ _).symm

/-- Squared residual estimate on the same detached original background. -/
theorem approximateInverse_residual_norm
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent) (r : (G).V) :
    ∀ n, (G).B ((G).sub r (M (A r n))) ((G).sub r (M (A r n))) ≤
      (inverseRate w links.length * inverseRate w links.length)^n * (G).B r r
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
      have he := (G).B_diag_congr (defect_step hw0 hw1 K extent hK links r (A r n))
      have hc := PositiveContractionResidual.residual_norm G P
        (scaledNormalizer_symmetric hw0 hw1 K extent hK links)
        (blockRatio_le_one hw0 hw1 links.length)
        (fun a => (scaledNormalizer_form_bounds hw0 hw1 K extent hK links hl a).2)
        (fun a => (scaledNormalizer_form_bounds hw0 hw1 K extent hK links hl a).1)
        ((G).sub r (M (A r n)))
      have hq := (inverseRate_bounds hw0 hw1 links.length).1
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
        (Q'.le_trans' _ _ _ hc (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _ (approximateInverse_residual_norm hl r n)
            (Q'.mul_nonneg _ _ hq hq))
          (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))))

/-- Computed absolute squared-residual tolerance, including zero input norm. -/
def approximationCutoff (r : (G).V) (epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff
    (inverseRate w links.length * inverseRate w links.length) ((G).B r r) epsilon

theorem approximateInverse_error_le
    (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (r : (G).V) (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (n : Nat)
    (hn : approximationCutoff hw0 hw1 K extent hK links r epsilon ≤ n) :
    (G).B ((G).sub r (M (A r n))) ((G).sub r (M (A r n))) ≤ epsilon := by
  have hq := inverseRate_bounds hw0 hw1 links.length
  have hq2 : inverseRate w links.length * inverseRate w links.length < (1 : Q') :=
    Q'.lt_of_le_of_lt (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_lt hq.2) hq.1)
      (Q'.le_of_eqv (Q'.one_mul_eqv _))) hq.2
  exact Q'.le_trans' _ _ _
    (approximateInverse_residual_norm hw0 hw1 K extent hK links hl r n)
    (PositiveContractionResidual.geometric_bound
      (Q'.mul_nonneg _ _ hq.1 hq.1) hq2 ((G).self_nonneg r) hepsilon n hn)

#print axioms blockRatio
#print axioms blockRatio_positive
#print axioms blockRatio_le_one
#print axioms inverseRate
#print axioms inverseRate_bounds
#print axioms scaledNormalizer
#print axioms scaledNormalizer_symmetric
#print axioms scaledNormalizer_form_bounds
#print axioms approximateInverse
#print axioms approximateInverse_residual_norm
#print axioms approximationCutoff
#print axioms approximateInverse_error_le

end YMGap.Continuum.BF4ExactSlabBlockInverseApproximation
