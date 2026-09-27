/-
# Completed preimages for the original finite-block normalizer

Every supported polynomial source has a constructed preimage in the existing
detached-background GNS completion. The extended multiplier has the exact
image identity and is injective. All original coordinates remain in the carrier.
The constants depend on nome and block size; no uniform block gap follows.
-/

import YMGap.Continuum.BF4ExactSlabBlockInverseApproximation
import YMGap.Continuum.GNSModulusCompletion

namespace YMGap.Continuum.BF4ExactSlabBlockCompletedInverse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabBlockComparisonConstants
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockInverseApproximation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link)
  (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)

local notation "G" => backgroundData hw0 hw1 K extent hK links
local notation "M" => normalizerMap hw0 hw1 K extent hK links
local notation "A" => approximateInverse hw0 hw1 K extent hK links
local notation "L2" => blockLower w links.length * blockLower w links.length
local notation "U2" => blockUpper w links.length * blockUpper w links.length

include hw0 hw1 in
private theorem floorSq_pos : (0 : Q') < L2 :=
  Q'.mul_pos (blockLower_positive hw0 hw1 links.length)
    (blockLower_positive hw0 hw1 links.length)

include hw0 in
private theorem capSq_nonnegative : (0 : Q') ≤ U2 :=
  Q'.mul_nonneg _ _ (Q'.le_of_lt (blockUpper_positive hw0 links.length))
    (Q'.le_of_lt (blockUpper_positive hw0 links.length))

include hl in
/-- Both norm comparisons hold in the same detached original background. -/
theorem normalizer_distance_bounds (a b : (G).V) :
    L2 * (G).distSqQ a b ≤ (G).distSqQ (M a) (M b) ∧
      (G).distSqQ (M a) (M b) ≤ U2 * (G).distSqQ a b := by
  have he := (G).B_diag_congr
    (normalizerMap_sub hw0 hw1 K extent hK links a b)
  have hlo := normalizerMap_norm_lower hw0 hw1 K extent hK links hl ((G).sub a b)
  have hhi := normalizerMap_norm_upper hw0 hw1 K extent hK links hl ((G).sub a b)
  exact ⟨Q'.le_trans' _ _ _ hlo (Q'.le_of_eqv he),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hhi⟩

private def quarter (epsilon : Q') : Q' :=
  HalfPow.half * (HalfPow.half * epsilon)

private theorem quarter_pos {epsilon : Q'} (h : (0 : Q') < epsilon) :
    (0 : Q') < quarter epsilon :=
  ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ h)

private theorem four_quarters (epsilon : Q') :
    (quarter epsilon + quarter epsilon) +
      (quarter epsilon + quarter epsilon) ≈ epsilon :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half * epsilon))
      (ExpNeg.two_halves (HalfPow.half * epsilon)))
    (ExpNeg.two_halves epsilon)

/-- The polynomial inverse approximants are Cauchy with a computed residual
cutoff at `L² ε/4`; no norm division or choice of representative occurs. -/
def inverseCauchy (r : (G).V) : CauchyGNS G where
  seq := A r
  modulus := fun epsilon => approximationCutoff hw0 hw1 K extent hK links r
    (quarter (L2 * epsilon))
  isCauchy := by
    intro epsilon hepsilon p q hp hq
    have ht : (0 : Q') < quarter (L2 * epsilon) :=
      quarter_pos (Q'.mul_pos (floorSq_pos hw0 hw1 links) hepsilon)
    have hpr := approximateInverse_error_le hw0 hw1 K extent hK links hl r _ ht p hp
    have hrq := approximateInverse_error_le hw0 hw1 K extent hK links hl r _ ht q hq
    have hpr' : (G).distSqQ (M (A r p)) r ≤ quarter (L2 * epsilon) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv ((G).distSqQ_comm _ _)) hpr
    have htri := (G).distSqQ_triangle (M (A r p)) r (M (A r q))
    have hsum := Q'.add_le_add (Q'.add_le_add hpr' hpr')
      (Q'.add_le_add hrq hrq)
    apply q_cancel_left (floorSq_pos hw0 hw1 links)
    exact Q'.le_trans' _ _ _ (normalizer_distance_bounds hw0 hw1 K extent hK links hl _ _).1
      (Q'.le_trans' _ _ _ htri
        (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (four_quarters (L2 * epsilon)))))

/-- The constructed preimage is in the existing background completion. -/
def inverseState (r : (G).V) : GNSCompletionSpace G :=
  Quotient.mk (cauchySetoid G) (inverseCauchy hw0 hw1 K extent hK links hl r)

private def imageTolerance (w : Q') (size : Nat) (epsilon : Q') : Q' :=
  epsilon * ExpUBInstance.oneOver1p (blockUpper w size * blockUpper w size)

private theorem imageTolerance_pos {epsilon : Q'} (h : (0 : Q') < epsilon) :
    (0 : Q') < imageTolerance w links.length epsilon :=
  Q'.mul_pos h (oneOver1p_pos _)

include hw0 in
private theorem image_budget {epsilon : Q'} (h : (0 : Q') < epsilon) :
    U2 * imageTolerance w links.length epsilon ≤ epsilon :=
  key_bound U2 epsilon (capSq_nonnegative hw0 links) (Q'.le_of_lt h)

/-- The actual block normalizer multiplier maps Cauchy representatives to
Cauchy representatives with an explicit rescaled modulus. -/
def normalizerCauchy (X : CauchyGNS G) : CauchyGNS G where
  seq := fun n => M (X.seq n)
  modulus := fun epsilon => X.modulus (imageTolerance w links.length epsilon)
  isCauchy := by
    intro epsilon hepsilon p q hp hq
    exact Q'.le_trans' _ _ _ (normalizer_distance_bounds hw0 hw1 K extent hK links hl _ _).2
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
        (X.isCauchy _ (imageTolerance_pos (w := w) links hepsilon) p q hp hq)
        (capSq_nonnegative hw0 links))
        (image_budget hw0 links hepsilon))

/-- A null modulus transports through the actual multiplier. -/
def normalizerNullModulus {X Y : CauchyGNS G} (h : CauchyNullModulus G X Y) :
    CauchyNullModulus G
      (normalizerCauchy hw0 hw1 K extent hK links hl X)
      (normalizerCauchy hw0 hw1 K extent hK links hl Y) where
  modulus := fun epsilon => h.modulus (imageTolerance w links.length epsilon)
  close := by
    intro epsilon hepsilon n hn
    exact Q'.le_trans' _ _ _ (normalizer_distance_bounds hw0 hw1 K extent hK links hl _ _).2
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
        (h.close _ (imageTolerance_pos (w := w) links hepsilon) n hn)
        (capSq_nonnegative hw0 links))
        (image_budget hw0 links hepsilon))

private theorem normalizerCauchy_null {X Y : CauchyGNS G} (h : CauchyNull G X Y) :
    CauchyNull G (normalizerCauchy hw0 hw1 K extent hK links hl X)
      (normalizerCauchy hw0 hw1 K extent hK links hl Y) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h (imageTolerance w links.length epsilon)
    (imageTolerance_pos (w := w) links hepsilon)
  refine ⟨N, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (normalizer_distance_bounds hw0 hw1 K extent hK links hl _ _).2
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
      (hN n hn) (capSq_nonnegative hw0 links))
      (image_budget hw0 links hepsilon))

/-- Extension of multiplication by the actual family-integrated collar. -/
def normalizerCompletion : GNSCompletionSpace G → GNSCompletionSpace G :=
  Quotient.lift
    (fun X => Quotient.mk (cauchySetoid G)
      (normalizerCauchy hw0 hw1 K extent hK links hl X))
    (fun _ _ h => Quotient.sound
      (normalizerCauchy_null hw0 hw1 K extent hK links hl h))

theorem normalizerCompletion_embed (r : (G).V) :
    normalizerCompletion hw0 hw1 K extent hK links hl (embedV G r) = embedV G (M r) := by
  apply Quotient.sound
  intro epsilon hepsilon
  exact ⟨0, fun _ _ => Q'.le_trans' _ _ _
    (Q'.le_of_eqv ((G).rad_refl (M r))) (Q'.le_of_lt hepsilon)⟩

/-- Coercivity makes the completed multiplier injective. -/
theorem normalizerCompletion_injective (x y : GNSCompletionSpace G)
    (h : normalizerCompletion hw0 hw1 K extent hK links hl x =
      normalizerCompletion hw0 hw1 K extent hK links hl y) : x = y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro X Y h
  have hn : CauchyNull G
      (normalizerCauchy hw0 hw1 K extent hK links hl X)
      (normalizerCauchy hw0 hw1 K extent hK links hl Y) := Quotient.exact h
  apply Quotient.sound
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hn (L2 * epsilon)
    (Q'.mul_pos (floorSq_pos hw0 hw1 links) hepsilon)
  refine ⟨N, fun n hindex => ?_⟩
  exact q_cancel_left (floorSq_pos hw0 hw1 links)
    (Q'.le_trans' _ _ _ (normalizer_distance_bounds hw0 hw1 K extent hK links hl _ _).1
      (hN n hindex))

/-- Explicit null modulus for the limiting division identity. -/
def inverseImageNull (r : (G).V) :
    CauchyNullModulus G
      (normalizerCauchy hw0 hw1 K extent hK links hl
        (inverseCauchy hw0 hw1 K extent hK links hl r))
      (constCauchy G r) where
  modulus := approximationCutoff hw0 hw1 K extent hK links r
  close := by
    intro epsilon hepsilon n hn
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv ((G).distSqQ_comm _ _))
      (approximateInverse_error_le hw0 hw1 K extent hK links hl r epsilon hepsilon n hn)

theorem normalizer_inverseState (r : (G).V) :
    normalizerCompletion hw0 hw1 K extent hK links hl
      (inverseState hw0 hw1 K extent hK links hl r) = embedV G r :=
  Quotient.sound (inverseImageNull hw0 hw1 K extent hK links hl r).toCauchyNull

theorem inverseState_normalizer (r : (G).V) :
    inverseState hw0 hw1 K extent hK links hl (M r) = embedV G r := by
  apply normalizerCompletion_injective hw0 hw1 K extent hK links hl
  rw [normalizer_inverseState, normalizerCompletion_embed]

/-- Null-class dense inputs have the same completed inverse. -/
theorem inverseState_rad {r t : (G).V} (h : (G).rad r t) :
    inverseState hw0 hw1 K extent hK links hl r =
      inverseState hw0 hw1 K extent hK links hl t := by
  apply normalizerCompletion_injective hw0 hw1 K extent hK links hl
  rw [normalizer_inverseState, normalizer_inverseState]
  exact Quotient.sound (embed_null_of_rad G h)

/-- The actual inserted numerator divided by the block normalizer in the
existing detached-background completion. -/
def conditionalState (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p) :
    GNSCompletionSpace G :=
  inverseState hw0 hw1 K extent hK links hl
    ⟨insertedNormalizer w K extent links p,
      insertedNormalizer_supported w K extent links hp⟩

theorem normalizer_conditionalState (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p) :
    normalizerCompletion hw0 hw1 K extent hK links hl
      (conditionalState hw0 hw1 K extent hK links hl p hp) =
      embedV G ⟨insertedNormalizer w K extent links p,
        insertedNormalizer_supported w K extent links hp⟩ :=
  normalizer_inverseState hw0 hw1 K extent hK links hl _

#print axioms normalizer_distance_bounds
#print axioms inverseCauchy
#print axioms inverseState
#print axioms normalizerCauchy
#print axioms normalizerNullModulus
#print axioms normalizerCompletion
#print axioms normalizerCompletion_embed
#print axioms normalizerCompletion_injective
#print axioms inverseImageNull
#print axioms normalizer_inverseState
#print axioms inverseState_normalizer
#print axioms inverseState_rad
#print axioms conditionalState
#print axioms normalizer_conditionalState

end YMGap.Continuum.BF4ExactSlabBlockCompletedInverse
