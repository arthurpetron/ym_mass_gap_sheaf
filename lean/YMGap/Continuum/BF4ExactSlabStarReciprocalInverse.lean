/-
# The finite positive reciprocal converges to the EXISTING star inverse

These approximants multiply the same dense exterior input by the finite
geometric reciprocal of the actual head normalizer. A certificate error
bound in the original complementary-action norm and the existing coercivity
give explicit Cauchy and cross-sequence null moduli. The limit is exactly
the previously constructed inverseState, not a replacement inverse.

The original full-action probe then identifies the corresponding conditional
limit with the existing conditional update. This is ordinary weighted L2
identification at fixed parameters, not an OS or spatial/scaling estimate.
-/

import YMGap.Continuum.BF4ExactSlabHeadNormalizerBand
import YMGap.Continuum.QuaternionHaarReciprocalWeightedError
import YMGap.Continuum.BF4ExactSlabStarVarianceReplica
import YMGap.Continuum.BF4ExactSlabStarConditionalProjection

namespace YMGap.Continuum.BF4ExactSlabStarReciprocalInverse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarCompletedInverse
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabStarReciprocalParameters
open YMGap.Continuum.BF4ExactSlabHeadNormalizerBand
open YMGap.Continuum.BF4ExactSlabCrossExteriorStar
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarReciprocalWeightedError
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "G" => exteriorData hw0 hw1 K extent hK link hl
local notation "F" => fullData hw0 hw1 K extent hK
local notation "M" => normalizerMap hw0 hw1 K extent hK link hl
local notation "rho" => starRadius hw0 hw1 extent link
local notation "L2" => lowerFactor w * lowerFactor w

/-- Actual finite multiplication, on the existing exterior carrier. -/
def reciprocalApproximation (r : (G).V) (k : Nat) : (G).V :=
  ⟨polyMul r.val (headReciprocal hw0 hw1 K extent link hl k),
    supported_polyMul r.property (headReciprocal_supported hw0 hw1 K extent link hl k)⟩

local notation "A" => reciprocalApproximation hw0 hw1 K extent hK link hl

/-- The geometric certificate is evaluated against the entire ORIGINAL
complementary action and the square of this same input. -/
theorem reciprocal_residual_norm (r : (G).V) (k : Nat) :
    (G).distSqQ r (M (A r k)) ≤ (rho^k * rho^k) * (G).B r r := by
  have he : RatPolyCoeffEqv ((G).sub r (M (A r k))).val
      (polyAdd r.val (polyNeg (polyMul
        (polyMul r.val (headReciprocal hw0 hw1 K extent link hl k))
        (normalizer w K extent link hl)))) :=
    (RatPolyCoeffEqv.refl _).add (neg_smul _).symm
  have hp := haar_of_coeff (blocks := (boundaryCompleteSlabLinks extent).length-1)
    ((he.mul he).mul_right (exterior w K extent link hl))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hp)
    (reciprocal_weighted_error_le
      (BF4ExactSlabStarVarianceReplica.exterior_certificate K extent link hl hw0 hw1 hK)
      (normalizer_supported w K extent link hl) r.property
      (starUpper_positive hw0 hw1 extent link)
      (starLower_le_starUpper hw0 hw1 extent link)
      (headLowerCertificate hw0 hw1 K extent link hl hK)
      (headUpperCertificate hw0 hw1 K extent link hl) k)

/-- Deliberately use the weaker rho^k norm budget; no square-root tolerance
or additional parameter choice is needed for the identification. -/
theorem reciprocal_residual_geometric (r : (G).V) (k : Nat) :
    (G).distSqQ r (M (A r k)) ≤ rho^k * (G).B r r := by
  have hr0 := starRadius_nonnegative hw0 hw1 extent link
  have hr1 := starRadius_lt_one hw0 hw1 extent link
  have hp : rho^k ≤ (1 : Q') :=
    HKConvGen.pow_base_antitone hr0 (Q'.le_of_lt hr1) (Nat.zero_le k)
  have hs : rho^k * rho^k ≤ rho^k :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hp (Q'.pow_nonneg _ hr0 k))
      (Q'.le_of_eqv (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ (reciprocal_residual_norm hw0 hw1 K extent hK link hl r k)
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hs ((G).self_nonneg r))

def residualCutoff (r : (G).V) (epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff rho ((G).B r r) epsilon

theorem residual_error_le (r : (G).V) (epsilon : Q') (he : (0 : Q') < epsilon)
    (k : Nat) (hk : residualCutoff hw0 hw1 K extent hK link hl r epsilon ≤ k) :
    (G).distSqQ r (M (A r k)) ≤ epsilon :=
  Q'.le_trans' _ _ _ (reciprocal_residual_geometric hw0 hw1 K extent hK link hl r k)
    (PositiveContractionResidual.geometric_bound
      (starRadius_nonnegative hw0 hw1 extent link) (starRadius_lt_one hw0 hw1 extent link)
      ((G).self_nonneg r) he k hk)

private def quarter (epsilon : Q') : Q' := HalfPow.half * (HalfPow.half * epsilon)

private theorem quarter_pos {epsilon : Q'} (h : (0 : Q') < epsilon) :
    (0 : Q') < quarter epsilon := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ h)

private theorem four_quarters (epsilon : Q') :
    (quarter epsilon + quarter epsilon) + (quarter epsilon + quarter epsilon) ≈ epsilon :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half * epsilon))
      (ExpNeg.two_halves (HalfPow.half * epsilon))) (ExpNeg.two_halves epsilon)

include hw0 hw1 in
private theorem floorSq_pos : (0 : Q') < L2 :=
  Q'.mul_pos (lowerFactor_positive hw0 hw1) (lowerFactor_positive hw0 hw1)

/-- Coercivity converts the new residual estimate into an explicit modulus
on the SAME preimages and SAME weighted exterior completion. -/
def reciprocalCauchy (r : (G).V) : CauchyGNS G where
  seq := A r
  modulus := fun epsilon => residualCutoff hw0 hw1 K extent hK link hl r (quarter (L2 * epsilon))
  isCauchy := by
    intro epsilon he p q hp hq
    have ht := quarter_pos (Q'.mul_pos (floorSq_pos hw0 hw1) he)
    have hpr := residual_error_le hw0 hw1 K extent hK link hl r _ ht p hp
    have hrq := residual_error_le hw0 hw1 K extent hK link hl r _ ht q hq
    have hpr' := Q'.le_trans' _ _ _ (Q'.le_of_eqv ((G).distSqQ_comm _ _)) hpr
    apply q_cancel_left (floorSq_pos hw0 hw1)
    exact Q'.le_trans' _ _ _ (normalizer_distance_bounds hw0 hw1 K extent hK link hl _ _).1
      (Q'.le_trans' _ _ _ ((G).distSqQ_triangle (M (A r p)) r (M (A r q)))
        (Q'.le_trans' _ _ _ (Q'.add_le_add (Q'.add_le_add hpr' hpr') (Q'.add_le_add hrq hrq))
          (Q'.le_of_eqv (four_quarters (L2 * epsilon)))))

/-- The cross-sequence modulus compares the new reciprocal sequence with
the EXISTING inverse iteration, not just with a freely specified limit. -/
def inverseNullModulus (r : (G).V) :
    CauchyNullModulus G (reciprocalCauchy hw0 hw1 K extent hK link hl r)
      (inverseCauchy hw0 hw1 K extent hK link hl r) where
  modulus := fun epsilon => max
    (residualCutoff hw0 hw1 K extent hK link hl r (quarter (L2 * epsilon)))
    (approximationCutoff hw0 hw1 K extent hK link hl r (quarter (L2 * epsilon)))
  close := by
    intro epsilon he k hk
    have ht := quarter_pos (Q'.mul_pos (floorSq_pos hw0 hw1) he)
    have hnew := residual_error_le hw0 hw1 K extent hK link hl r _ ht k
      (Nat.le_trans (Nat.le_max_left _ _) hk)
    have hold := approximateInverse_error_le hw0 hw1 K extent hK link hl r _ ht k
      (Nat.le_trans (Nat.le_max_right _ _) hk)
    have hnew' := Q'.le_trans' _ _ _ (Q'.le_of_eqv ((G).distSqQ_comm _ _)) hnew
    apply q_cancel_left (floorSq_pos hw0 hw1)
    exact Q'.le_trans' _ _ _ (normalizer_distance_bounds hw0 hw1 K extent hK link hl _ _).1
      (Q'.le_trans' _ _ _ ((G).distSqQ_triangle (M (A r k)) r
        (M (approximateInverse hw0 hw1 K extent hK link hl r k)))
        (Q'.le_trans' _ _ _ (Q'.add_le_add (Q'.add_le_add hnew' hnew') (Q'.add_le_add hold hold))
          (Q'.le_of_eqv (four_quarters (L2 * epsilon)))))

theorem reciprocal_limit_eq_inverseState (r : (G).V) :
    Quotient.mk (cauchySetoid G) (reciprocalCauchy hw0 hw1 K extent hK link hl r) =
      inverseState hw0 hw1 K extent hK link hl r :=
  Quotient.sound (inverseNullModulus hw0 hw1 K extent hK link hl r).toCauchyNull

/-- Transport the explicit cross-sequence modulus through the EXISTING
original full-action probe; both actions and carriers remain unchanged. -/
def conditionalNullModulus (p : (F).V) :
    CauchyNullModulus F
      (probeCauchy hw0 hw1 K extent hK link hl
        (reciprocalCauchy hw0 hw1 K extent hK link hl (numeratorMap hw0 hw1 K extent hK link hl p)))
      ((conditionalDenseMap hw0 hw1 K extent hK link hl).toRep p) :=
  probeNullModulus hw0 hw1 K extent hK link hl
    (inverseNullModulus hw0 hw1 K extent hK link hl (numeratorMap hw0 hw1 K extent hK link hl p))

theorem reciprocal_limit_eq_conditionalUpdate (p : (F).V) :
    Quotient.mk (cauchySetoid F)
      (probeCauchy hw0 hw1 K extent hK link hl
        (reciprocalCauchy hw0 hw1 K extent hK link hl (numeratorMap hw0 hw1 K extent hK link hl p))) =
      conditionalUpdate hw0 hw1 K extent hK link hl p :=
  Quotient.sound (conditionalNullModulus hw0 hw1 K extent hK link hl p).toCauchyNull

#print axioms reciprocalApproximation
#print axioms reciprocal_residual_norm
#print axioms reciprocal_residual_geometric
#print axioms residualCutoff
#print axioms residual_error_le
#print axioms reciprocalCauchy
#print axioms inverseNullModulus
#print axioms reciprocal_limit_eq_inverseState
#print axioms conditionalNullModulus
#print axioms reciprocal_limit_eq_conditionalUpdate

end YMGap.Continuum.BF4ExactSlabStarReciprocalInverse
