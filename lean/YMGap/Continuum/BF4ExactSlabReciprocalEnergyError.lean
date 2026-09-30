/-
# Original-action normalization error in the reciprocal energy identity

The discarded-in-the-limit term is nonnegative and bounded by rho^k
times the SAME original input norm. Its absolute tolerance cutoff is
explicit. Neither the incident star nor the complementary action is
replaced, and no uniform physical rate or coercivity is inferred.
-/

import YMGap.Continuum.BF4ExactSlabReciprocalEnergyPairing
import YMGap.Continuum.QuaternionHaarReciprocalDefectBound

namespace YMGap.Continuum.BF4ExactSlabReciprocalEnergyError

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarVarianceReplica
open YMGap.Continuum.BF4ExactSlabStarExteriorSeedNorm
open YMGap.Continuum.BF4ExactSlabStarReciprocalParameters
open YMGap.Continuum.BF4ExactSlabHeadNormalizerBand
open YMGap.Continuum.BF4ExactSlabReciprocalEnergyPairing
open YMGap.Continuum.QuaternionHaarReciprocalCrossComparison
open YMGap.Continuum.QuaternionHaarReciprocalDefectBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "rho" => starRadius hw0 hw1 extent link
local notation "err" => normalizationError hw0 hw1 K extent hK link hl
local notation "var" => varianceEnergy hw0 hw1 K extent hK link hl
local notation "loss" => finiteLoss hw0 hw1 K extent hK link

/-- The positive finite error is paid by the original norm, not a new
volume-dependent coefficient or scalar partition floor. -/
theorem normalizationError_bounds (p : (F).V) (k : Nat) :
    (0 : Q') ≤ err p k ∧ err p k ≤ rho^k * (F).B p p := by
  have h := reciprocalDefect_haar_bounds
    (normalizer_supported w K extent link hl)
    (starUpper_positive hw0 hw1 extent link)
    (starLower_le_starUpper hw0 hw1 extent link)
    (headLowerCertificate hw0 hw1 K extent link hl hK)
    (headUpperCertificate hw0 hw1 K extent link hl)
    (tailSquare_certificate hw0 hw1 K extent hK ⟨link,hl⟩ p) k
  exact ⟨h.1, Q'.le_trans' _ _ _ h.2
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (original_norm_pin hw0 hw1 K extent hK ⟨link,hl⟩ p))))⟩

def errorCutoff (p : (F).V) (epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff rho ((F).B p p) epsilon

theorem normalizationError_le (p : (F).V) (epsilon : Q')
    (he : (0 : Q') < epsilon) (k : Nat)
    (hk : errorCutoff hw0 hw1 K extent hK link p epsilon ≤ k) :
    err p k ≤ epsilon :=
  Q'.le_trans' _ _ _ (normalizationError_bounds hw0 hw1 K extent hK link hl p k).2
    (PositiveContractionResidual.geometric_bound
      (starRadius_nonnegative hw0 hw1 extent link)
      (starRadius_lt_one hw0 hw1 extent link) ((F).self_nonneg p) he k hk)

/-- The reciprocal-weighted variance is itself certified nonnegative. -/
theorem varianceEnergy_nonnegative (p : (F).V) (k : Nat) :
    (0 : Q') ≤ var p k :=
  (((varianceNumerator_certificate K extent link hl hw0 hw1 hK p.val).mul
    (reciprocalCertificate _ (starUpper_positive hw0 hw1 extent link)
      (headUpperCertificate hw0 hw1 K extent link hl) k)).mul
        (exterior_certificate K extent link hl hw0 hw1 hK)).haar_nonnegative

theorem varianceEnergy_le_finiteLoss (p : (F).V) (k : Nat) :
    var p k ≤ loss p k :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (normalizationError_bounds hw0 hw1 K extent hK link hl p k).1)
    (Q'.ge_of_eqv (finiteLoss_split hw0 hw1 K extent hK link hl p k))

/-- This two-sided comparison is the quantitative input for the SAME
residual-energy limit, with the cutoff returned as data above. -/
theorem finiteLoss_le_varianceEnergy_add (p : (F).V) (epsilon : Q')
    (he : (0 : Q') < epsilon) (k : Nat)
    (hk : errorCutoff hw0 hw1 K extent hK link p epsilon ≤ k) :
    loss p k ≤ var p k + epsilon :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (finiteLoss_split hw0 hw1 K extent hK link hl p k))
    (Q'.add_le_add (Q'.le_of_eqv (Q'.eqv_refl _))
      (normalizationError_le hw0 hw1 K extent hK link hl p epsilon he k hk))

#print axioms normalizationError_bounds
#print axioms errorCutoff
#print axioms normalizationError_le
#print axioms varianceEnergy_nonnegative
#print axioms varianceEnergy_le_finiteLoss
#print axioms finiteLoss_le_varianceEnergy_add

end YMGap.Continuum.BF4ExactSlabReciprocalEnergyError
