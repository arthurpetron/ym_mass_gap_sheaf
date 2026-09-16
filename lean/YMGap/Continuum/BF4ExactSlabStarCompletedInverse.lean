/-
# Completed preimages for the actual local-star normalizer

Coercivity turns the already-proved polynomial division errors into an
explicit Cauchy modulus in the SAME complementary-action weighted form B.
The actual multiplier by D is extended pointwise to this existing GNS
completion, with a rescaled modulus and null-class compatibility. Every
dense polynomial has a constructed completed preimage, with an exact image
identity and uniqueness. The actual conditional numerator is an instance.

This does not yet lift N_p/D into the original full-action completion or
prove its conditional projection law. No OS, spatial or physical gap is
claimed. The local constants remain nome-dependent.
-/

import YMGap.Continuum.BF4ExactSlabStarInverseApproximation
import YMGap.Continuum.PositiveCoerciveForm
import YMGap.Continuum.GNSModulusCompletion

namespace YMGap.Continuum.BF4ExactSlabStarCompletedInverse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabStarInsertedNumerator
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "G" => exteriorData hw0 hw1 K extent hK link hl
local notation "M" => normalizerMap hw0 hw1 K extent hK link hl
local notation "A" => approximateInverse hw0 hw1 K extent hK link hl
local notation "L2" => lowerFactor w * lowerFactor w
local notation "U2" => upperFactor w * upperFactor w

include hw0 hw1 in
private theorem floorSq_pos : (0 : Q') < L2 :=
  Q'.mul_pos (lowerFactor_positive hw0 hw1) (lowerFactor_positive hw0 hw1)

include hw0 in
private theorem capSq_nonnegative : (0 : Q') ≤ U2 :=
  Q'.mul_nonneg _ _ (Q'.le_of_lt (upperFactor_positive hw0))
    (Q'.le_of_lt (upperFactor_positive hw0))

/-- Two-sided distance control for the actual normalizer multiplier. -/
theorem normalizer_distance_bounds (a b : (G).V) :
    L2 * (G).distSqQ a b ≤ (G).distSqQ (M a) (M b) ∧
      (G).distSqQ (M a) (M b) ≤ U2 * (G).distSqQ a b := by
  have he := (G).B_diag_congr (normalizerMap_sub hw0 hw1 K extent hK link hl a b)
  have hlo := PositiveCoerciveForm.lower_norm G M
    (Q'.le_of_lt (lowerFactor_positive hw0 hw1))
    (fun v => (normalizerMap_form_bounds hw0 hw1 K extent hK link hl v).1)
    ((G).sub a b)
  have hhi := normalizerMap_norm hw0 hw1 K extent hK link hl ((G).sub a b)
  exact ⟨Q'.le_trans' _ _ _ hlo (Q'.le_of_eqv he),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hhi⟩

private def quarter (epsilon : Q') : Q' := HalfPow.half * (HalfPow.half * epsilon)

private theorem quarter_pos {epsilon : Q'} (h : (0 : Q') < epsilon) :
    (0 : Q') < quarter epsilon :=
  ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ h)

private theorem four_quarters (epsilon : Q') :
    (quarter epsilon + quarter epsilon) + (quarter epsilon + quarter epsilon) ≈ epsilon :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half * epsilon))
      (ExpNeg.two_halves (HalfPow.half * epsilon))) (ExpNeg.two_halves epsilon)

/-- The original polynomial approximants themselves are Cauchy. The
modulus is the residual cutoff at L^2*epsilon/4, with no norm division. -/
def inverseCauchy (r : (G).V) : CauchyGNS G where
  seq := A r
  modulus := fun epsilon => approximationCutoff hw0 hw1 K extent hK link hl r (quarter (L2 * epsilon))
  isCauchy := by
    intro epsilon hepsilon p q hp hq
    have ht : (0 : Q') < quarter (L2 * epsilon) :=
      quarter_pos (Q'.mul_pos (floorSq_pos hw0 hw1) hepsilon)
    have hpr := approximateInverse_error_le hw0 hw1 K extent hK link hl r _ ht p hp
    have hrq := approximateInverse_error_le hw0 hw1 K extent hK link hl r _ ht q hq
    have hpr' : (G).distSqQ (M (A r p)) r ≤ quarter (L2 * epsilon) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv ((G).distSqQ_comm _ _)) hpr
    have htri := (G).distSqQ_triangle (M (A r p)) r (M (A r q))
    have hsum := Q'.add_le_add (Q'.add_le_add hpr' hpr') (Q'.add_le_add hrq hrq)
    apply q_cancel_left (floorSq_pos hw0 hw1)
    exact Q'.le_trans' _ _ _ (normalizer_distance_bounds hw0 hw1 K extent hK link hl _ _).1
      (Q'.le_trans' _ _ _ htri
        (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (four_quarters (L2 * epsilon)))))

/-- The constructed preimage lives in the EXISTING completion of B. -/
def inverseState (r : (G).V) : GNSCompletionSpace G :=
  Quotient.mk (cauchySetoid G) (inverseCauchy hw0 hw1 K extent hK link hl r)

private def imageTolerance (w epsilon : Q') : Q' :=
  epsilon * ExpUBInstance.oneOver1p (upperFactor w * upperFactor w)

private theorem imageTolerance_pos {w epsilon : Q'} (h : (0 : Q') < epsilon) :
    (0 : Q') < imageTolerance w epsilon := Q'.mul_pos h (oneOver1p_pos _)

include hw0 in
private theorem image_budget {epsilon : Q'} (h : (0 : Q') < epsilon) :
    U2 * imageTolerance w epsilon ≤ epsilon :=
  key_bound U2 epsilon (capSq_nonnegative hw0) (Q'.le_of_lt h)

/-- Pointwise multiplication by actual D on arbitrary Cauchy representatives,
using the actual bound U^2 and an explicit rescaling of the input modulus. -/
def normalizerCauchy (X : CauchyGNS G) : CauchyGNS G where
  seq := fun n => M (X.seq n)
  modulus := fun epsilon => X.modulus (imageTolerance w epsilon)
  isCauchy := by
    intro epsilon hepsilon p q hp hq
    exact Q'.le_trans' _ _ _ (normalizer_distance_bounds hw0 hw1 K extent hK link hl _ _).2
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
        (X.isCauchy _ (imageTolerance_pos hepsilon) p q hp hq) (capSq_nonnegative hw0))
        (image_budget hw0 hepsilon))

/-- Explicit transport of null moduli; no witness is selected from a quotient. -/
def normalizerNullModulus {X Y : CauchyGNS G} (h : CauchyNullModulus G X Y) :
    CauchyNullModulus G
      (normalizerCauchy hw0 hw1 K extent hK link hl X)
      (normalizerCauchy hw0 hw1 K extent hK link hl Y) where
  modulus := fun epsilon => h.modulus (imageTolerance w epsilon)
  close := by
    intro epsilon hepsilon n hn
    exact Q'.le_trans' _ _ _ (normalizer_distance_bounds hw0 hw1 K extent hK link hl _ _).2
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
        (h.close _ (imageTolerance_pos hepsilon) n hn) (capSq_nonnegative hw0))
        (image_budget hw0 hepsilon))

private theorem normalizerCauchy_null {X Y : CauchyGNS G} (h : CauchyNull G X Y) :
    CauchyNull G (normalizerCauchy hw0 hw1 K extent hK link hl X)
      (normalizerCauchy hw0 hw1 K extent hK link hl Y) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h (imageTolerance w epsilon) (imageTolerance_pos hepsilon)
  refine ⟨N, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (normalizer_distance_bounds hw0 hw1 K extent hK link hl _ _).2
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (hN n hn) (capSq_nonnegative hw0))
      (image_budget hw0 hepsilon))

/-- The genuine extension of multiplication by D, not an arbitrary map
chosen to send the constructed inverse state to its input. -/
def normalizerCompletion : GNSCompletionSpace G → GNSCompletionSpace G :=
  Quotient.lift (fun X => Quotient.mk (cauchySetoid G) (normalizerCauchy hw0 hw1 K extent hK link hl X))
    (fun _ _ h => Quotient.sound (normalizerCauchy_null hw0 hw1 K extent hK link hl h))

theorem normalizerCompletion_embed (r : (G).V) :
    normalizerCompletion hw0 hw1 K extent hK link hl (embedV G r) = embedV G (M r) := by
  apply Quotient.sound
  intro epsilon hepsilon
  exact ⟨0, fun _ _ => Q'.le_trans' _ _ _ (Q'.le_of_eqv ((G).rad_refl (M r))) (Q'.le_of_lt hepsilon)⟩

/-- Coercivity proves injectivity of the actual completed multiplier. -/
theorem normalizerCompletion_injective (x y : GNSCompletionSpace G)
    (h : normalizerCompletion hw0 hw1 K extent hK link hl x =
      normalizerCompletion hw0 hw1 K extent hK link hl y) : x = y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro X Y h
  have hn : CauchyNull G (normalizerCauchy hw0 hw1 K extent hK link hl X)
      (normalizerCauchy hw0 hw1 K extent hK link hl Y) := Quotient.exact h
  apply Quotient.sound
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hn (L2 * epsilon) (Q'.mul_pos (floorSq_pos hw0 hw1) hepsilon)
  refine ⟨N, fun n hindex => ?_⟩
  exact q_cancel_left (floorSq_pos hw0 hw1)
    (Q'.le_trans' _ _ _ (normalizer_distance_bounds hw0 hw1 K extent hK link hl _ _).1 (hN n hindex))

/-- The limiting division identity retains its explicit null modulus. -/
def inverseImageNull (r : (G).V) :
    CauchyNullModulus G
      (normalizerCauchy hw0 hw1 K extent hK link hl (inverseCauchy hw0 hw1 K extent hK link hl r))
      (constCauchy G r) where
  modulus := approximationCutoff hw0 hw1 K extent hK link hl r
  close := by
    intro epsilon hepsilon n hn
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv ((G).distSqQ_comm _ _))
      (approximateInverse_error_le hw0 hw1 K extent hK link hl r epsilon hepsilon n hn)

/-- Exact image identity for every dense polynomial input in the SAME form. -/
theorem normalizer_inverseState (r : (G).V) :
    normalizerCompletion hw0 hw1 K extent hK link hl
      (inverseState hw0 hw1 K extent hK link hl r) = embedV G r :=
  Quotient.sound (inverseImageNull hw0 hw1 K extent hK link hl r).toCauchyNull

theorem inverseState_normalizer (r : (G).V) :
    inverseState hw0 hw1 K extent hK link hl (M r) = embedV G r := by
  apply normalizerCompletion_injective hw0 hw1 K extent hK link hl
  rw [normalizer_inverseState, normalizerCompletion_embed]

/-- Dense input null classes produce the same completed inverse state. -/
theorem inverseState_rad {r t : (G).V} (h : (G).rad r t) :
    inverseState hw0 hw1 K extent hK link hl r = inverseState hw0 hw1 K extent hK link hl t := by
  apply normalizerCompletion_injective hw0 hw1 K extent hK link hl
  rw [normalizer_inverseState, normalizer_inverseState]
  exact Quotient.sound (embed_null_of_rad G h)

/-- The actual N_p/D as a completed B-weighted exterior vector. Its lift
to the original full action and projection properties remain to be proved. -/
def conditionalState (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p) : GNSCompletionSpace G :=
  inverseState hw0 hw1 K extent hK link hl
    ⟨insertedNormalizer w K extent link hl p, insertedNormalizer_supported w K extent link hl p hp⟩

theorem normalizer_conditionalState (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p) :
    normalizerCompletion hw0 hw1 K extent hK link hl (conditionalState hw0 hw1 K extent hK link hl p hp) =
      embedV G ⟨insertedNormalizer w K extent link hl p, insertedNormalizer_supported w K extent link hl p hp⟩ :=
  normalizer_inverseState hw0 hw1 K extent hK link hl _

end YMGap.Continuum.BF4ExactSlabStarCompletedInverse

#print axioms YMGap.Continuum.BF4ExactSlabStarCompletedInverse.normalizer_distance_bounds
#print axioms YMGap.Continuum.BF4ExactSlabStarCompletedInverse.inverseCauchy
#print axioms YMGap.Continuum.BF4ExactSlabStarCompletedInverse.inverseState
#print axioms YMGap.Continuum.BF4ExactSlabStarCompletedInverse.normalizerCauchy
#print axioms YMGap.Continuum.BF4ExactSlabStarCompletedInverse.normalizerNullModulus
#print axioms YMGap.Continuum.BF4ExactSlabStarCompletedInverse.normalizerCompletion
#print axioms YMGap.Continuum.BF4ExactSlabStarCompletedInverse.normalizerCompletion_embed
#print axioms YMGap.Continuum.BF4ExactSlabStarCompletedInverse.normalizerCompletion_injective
#print axioms YMGap.Continuum.BF4ExactSlabStarCompletedInverse.inverseImageNull
#print axioms YMGap.Continuum.BF4ExactSlabStarCompletedInverse.normalizer_inverseState
#print axioms YMGap.Continuum.BF4ExactSlabStarCompletedInverse.inverseState_normalizer
#print axioms YMGap.Continuum.BF4ExactSlabStarCompletedInverse.inverseState_rad
#print axioms YMGap.Continuum.BF4ExactSlabStarCompletedInverse.conditionalState
#print axioms YMGap.Continuum.BF4ExactSlabStarCompletedInverse.normalizer_conditionalState
