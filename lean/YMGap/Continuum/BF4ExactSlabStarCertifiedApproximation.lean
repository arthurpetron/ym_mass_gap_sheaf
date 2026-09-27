/-
# The SAME normalizer iteration in every certified exterior weight

The original normalizer's square-test interval extends to all constructed
positive exterior weights. In particular this covers the actual variance
numerator times the retained complementary action. The polynomial iterates
are literally those already used for the original B-weighted inverse; only
the norm in which their defect is estimated changes.

The rate is explicit and nome-dependent. These are finite-parameter
approximation estimates, not global interacting coercivity or a mass gap.
-/

import YMGap.Continuum.QuaternionHaarCertificateFormBounds
import YMGap.Continuum.BF4ExactSlabStarInverseApproximation
import YMGap.Continuum.BF4ExactSlabStarVarianceReplica

namespace YMGap.Continuum.BF4ExactSlabStarCertifiedApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarVarianceReplica
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) : Nat := (boundaryCompleteSlabLinks extent).length

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)
  {v : RatPoly} (H : Certificate (blocks extent-1) v)

local notation "G" => weightedGNSData (blocks extent-1) v H
local notation "M" => normalizerMap hw0 hw1 K extent hK link hl
local notation "P" => scaledNormalizer hw0 hw1 K extent hK link hl
local notation "A" => approximateInverse hw0 hw1 K extent hK link hl
local notation "s" => HKConv.divPos 1 (upperFactor w)

/-- The original square-test interval survives every certified weight.
The inserted weight need not be independent of any remaining variable. -/
theorem certified_form_bounds (a : (G).V) :
    lowerFactor w * (G).B a a ≤ (G).B a (M a) ∧
      (G).B a (M a) ≤ upperFactor w * (G).B a a := by
  have ht := (H.multiplySquare a.val a.property).form_interval
    (normalizer w K extent link hl) (lowerFactor w) (upperFactor w)
    (normalizer_form_bounds hw0 hw1 K extent hK link hl)
  have he : (G).B a (M a) ≈
      quaternionHaar (blocks extent-1)
        (polyMul (polyMul (polyMul a.val a.val) v) (normalizer w K extent link hl)) :=
    haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 0) (.var 1))) (.var 2))
      (.mul (.mul (.mul (.var 0) (.var 0)) (.var 2)) (.var 1))
      (by decide) (fun | 0 => a.val | 1 => normalizer w K extent link hl | _ => v))
  exact ⟨Q'.le_trans' _ _ _ ht.1 (Q'.ge_of_eqv he),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he) ht.2⟩

theorem certified_scaled_symmetric (a b : (G).V) :
    (G).B a (P b) ≈ (G).B (P a) b := by
  have hm : (G).B a (M b) ≈ (G).B (M a) b :=
    haar_of_coeff ((coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => a.val | 1 => b.val | _ => normalizer w K extent link hl)).mul_right v)
  exact Q'.eqv_trans _ _ _ ((G).B_smul_right s a (M b))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hm)
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

theorem certified_scaled_form_bounds (a : (G).V) :
    starRatio w * (G).B a a ≤ (G).B a (P a) ∧
      (G).B a (P a) ≤ (G).B a a := by
  have h := certified_form_bounds hw0 hw1 K extent hK link hl H a
  have hs : (0 : Q') ≤ s := HKConv.divPos_nonneg (by decide)
  have he := (G).B_smul_right s a (M a)
  have hL : s * (lowerFactor w * (G).B a a) ≈ starRatio w * (G).B a a :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_eqv_congr_right _ _ _ (scaled_floor_pin hw0))
  have hU : s * (upperFactor w * (G).B a a) ≈ (G).B a a :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (inverse_cap_pin hw0))
        (Q'.one_mul_eqv _))
  exact ⟨Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ h.1 hs)
        (Q'.ge_of_eqv he)),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ h.2 hs)
        (Q'.le_of_eqv hU))⟩

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

/-- The EXISTING polynomial approximants have the SAME geometric defect
bound in the new certified norm, not merely in the B-only reference norm. -/
theorem certified_residual_norm (r : (G).V) :
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
      have he := (G).B_diag_congr (defect_step hw0 hw1 K extent hK link hl H r (A r n))
      have hc := PositiveContractionResidual.residual_norm G P
        (certified_scaled_symmetric hw0 hw1 K extent hK link hl H)
        (starRatio_le_one hw0 hw1)
        (fun a => (certified_scaled_form_bounds hw0 hw1 K extent hK link hl H a).2)
        (fun a => (certified_scaled_form_bounds hw0 hw1 K extent hK link hl H a).1)
        ((G).sub r (M (A r n)))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
        (Q'.le_trans' _ _ _ hc (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _ (certified_residual_norm r n)
            (Q'.mul_nonneg _ _ (inverseRate_bounds hw0 hw1).1 (inverseRate_bounds hw0 hw1).1))
          (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))))

/-- A data-level cutoff for the certified weighted defect. -/
def certifiedCutoff (r : (G).V) (epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff
    (inverseRate w * inverseRate w) ((G).B r r) epsilon

theorem certified_error_le (r : (G).V) (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (n : Nat)
    (hn : certifiedCutoff (w := w) extent H r epsilon ≤ n) :
    (G).B ((G).sub r (M (A r n))) ((G).sub r (M (A r n))) ≤ epsilon := by
  have hq := inverseRate_bounds hw0 hw1
  have hq2 : inverseRate w * inverseRate w < (1 : Q') :=
    Q'.lt_of_le_of_lt (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_lt hq.2) hq.1)
      (Q'.le_of_eqv (Q'.one_mul_eqv _))) hq.2
  exact Q'.le_trans' _ _ _
    (certified_residual_norm hw0 hw1 K extent hK link hl H r n)
    (PositiveContractionResidual.geometric_bound
      (Q'.mul_nonneg _ _ hq.1 hq.1) hq2 ((G).self_nonneg r) hepsilon n hn)

/-- Constructed positivity of the precise variance weight Phi*B. -/
def varianceWeightCertificate (p : RatPoly) :
    Certificate (blocks extent-1)
      (polyMul (varianceNumerator w K extent link hl p) (exterior w K extent link hl)) :=
  (varianceNumerator_certificate K extent link hl hw0 hw1 hK p).mul
    (exterior_certificate K extent link hl hw0 hw1 hK)

/-- Specialization to the actual variance weight, with no positivity input. -/
theorem variance_residual_norm (p : RatPoly)
    (r : (exteriorData hw0 hw1 K extent hK link hl).V) (n : Nat) :
    let V := weightedGNSData (blocks extent-1) _
      (varianceWeightCertificate hw0 hw1 K extent hK link hl p)
    V.B (V.sub r (M (A r n))) (V.sub r (M (A r n))) ≤
      (inverseRate w * inverseRate w)^n * V.B r r :=
  certified_residual_norm hw0 hw1 K extent hK link hl
    (varianceWeightCertificate hw0 hw1 K extent hK link hl p) r n

#print axioms certified_form_bounds
#print axioms certified_scaled_symmetric
#print axioms certified_scaled_form_bounds
#print axioms certified_residual_norm
#print axioms certifiedCutoff
#print axioms certified_error_le
#print axioms varianceWeightCertificate
#print axioms variance_residual_norm

end YMGap.Continuum.BF4ExactSlabStarCertifiedApproximation
