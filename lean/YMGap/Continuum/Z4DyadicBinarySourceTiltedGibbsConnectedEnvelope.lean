/-
# A positive envelope for the surviving connected response

The exact connected response is still a signed sum.  This file replaces each
signed term by one explicit nonnegative envelope: the paired common Gibbs
background times the sum of the two oriented products of source-local tilts.
The Boolean observable difference costs at most one, and the local tilt
determinant is bounded by the sum of its two nonnegative monomials.

The triangle inequality then bounds the absolute denominator-cleared response
by the envelope summed only over the connected active carrier.  Nothing is
hidden in an opaque constant: all coarse coupling, cutoff, volume, sources,
and target states remain arguments of the displayed weight.

This file does not yet sum the envelope by paid mass, prove a strict rate,
construct a completed gap, or pass to a continuum theory.

Constructive contract: exact rational inequalities and finite list induction
only; no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, trusted external computation, enlarged heartbeat budget, or new
axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedMassFloor
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelope

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedMassFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsDisconnectedCancellation
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseDeterminant
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The explicit positive pair envelope -/

/-- The absolute-value envelope obtained by replacing the local tilt
determinant by the sum of its two oriented nonnegative monomials. -/
def finePacketLocalizedResponsePairEnvelope
    (S : SlabScalePair) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  (finePacketCommonExteriorGibbsWeight S first second pair.1 *
      finePacketCommonExteriorGibbsWeight S first second pair.2) *
    (finePacketDisagreementTilt S first first second pair.1 *
          finePacketDisagreementTilt S second first second pair.2 +
      finePacketDisagreementTilt S second first second pair.1 *
          finePacketDisagreementTilt S first first second pair.2)

theorem finePacketCommonExteriorGibbsWeight_nonnegative
    (S : SlabScalePair) (first second targetState : EdgeLabelling) :
    (0 : Q') ≤
      finePacketCommonExteriorGibbsWeight
        S first second targetState := by
  unfold finePacketCommonExteriorGibbsWeight
  exact Q'.mul_nonneg _ _
    (ofNat_nonneg'
      (finePacketCommonExteriorMultiplicityProduct
        S first second targetState))
    (slabParametricKPhysicalTerm_nonnegative
      S.coarse.coupling_nonnegative S.coarse.cutoff
        S.coarse.extent targetState)

theorem finePacketDisagreementTilt_nonnegative
    (S : SlabScalePair) (source first second targetState : EdgeLabelling) :
    (0 : Q') ≤
      finePacketDisagreementTilt
        S source first second targetState := by
  unfold finePacketDisagreementTilt
  exact ofNat_nonneg' _

theorem finePacketLocalizedResponsePairEnvelope_nonnegative
    (S : SlabScalePair) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) :
    (0 : Q') ≤
      finePacketLocalizedResponsePairEnvelope S first second pair := by
  unfold finePacketLocalizedResponsePairEnvelope
  apply Q'.mul_nonneg
  · exact Q'.mul_nonneg _ _
      (finePacketCommonExteriorGibbsWeight_nonnegative
        S first second pair.1)
      (finePacketCommonExteriorGibbsWeight_nonnegative
        S first second pair.2)
  · exact Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _
        (finePacketDisagreementTilt_nonnegative
          S first first second pair.1)
        (finePacketDisagreementTilt_nonnegative
          S second first second pair.2))
      (Q'.mul_nonneg _ _
        (finePacketDisagreementTilt_nonnegative
          S second first second pair.1)
        (finePacketDisagreementTilt_nonnegative
          S first first second pair.2))

/-! ## 2. The local determinant and observable each have unit-cost bounds -/

theorem booleanEventIndicator_sub_abs_le_one
    {A : Type} (event : A → Bool) (left right : A) :
    Q'.abs
        (booleanEventIndicator event left -
          booleanEventIndicator event right) ≤ 1 := by
  cases hleft : event left <;> cases hright : event right <;>
    simp only [booleanEventIndicator, hleft, hright,
      Bool.false_eq_true, if_false, if_true] <;> decide

private theorem abs_sub_nonnegative_le_add
    (left right : Q')
    (hleft : (0 : Q') ≤ left) (hright : (0 : Q') ≤ right) :
    Q'.abs (left - right) ≤ left + right := by
  have htriangle := abs_add_le left (-right)
  have hleftAbs : Q'.abs left = left := abs_of_nonneg hleft
  have hrightAbs : Q'.abs right = right := abs_of_nonneg hright
  have hnegAbs : Q'.abs (-right) ≤ right :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_neg' right))
      (Q'.le_of_eqv (Q'.eqv_of_eq hrightAbs))
  change Q'.abs (left + (-right)) ≤ left + right
  rw [hleftAbs] at htriangle
  exact Q'.le_trans' _ _ _ htriangle
    (Q'.add_le_add (Q'.le_refl' left) hnegAbs)

private theorem abs_background_mul_det_mul_indicator_le
    (background forward reverse indicator : Q')
    (hbackground : (0 : Q') ≤ background)
    (hforward : (0 : Q') ≤ forward)
    (hreverse : (0 : Q') ≤ reverse)
    (hindicator : Q'.abs indicator ≤ 1) :
    Q'.abs (background * ((forward - reverse) * indicator)) ≤
      background * (forward + reverse) := by
  have hdet : Q'.abs (forward - reverse) ≤ forward + reverse :=
    abs_sub_nonnegative_le_add forward reverse hforward hreverse
  have hsum : (0 : Q') ≤ forward + reverse :=
    Q'.zero_le_add _ _ hforward hreverse
  have hinner0 := abs_mul_le (forward - reverse) indicator
  have hinner1 :
      Q'.abs (forward - reverse) * Q'.abs indicator ≤
        (forward + reverse) * Q'.abs indicator :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hdet (Q'.abs_nonneg indicator)
  have hinner2 :
      (forward + reverse) * Q'.abs indicator ≤
        (forward + reverse) * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hindicator hsum
  have hinner :
      Q'.abs ((forward - reverse) * indicator) ≤
        forward + reverse := by
    refine Q'.le_trans' _ _ _ hinner0 ?_
    refine Q'.le_trans' _ _ _ hinner1 ?_
    refine Q'.le_trans' _ _ _ hinner2 ?_
    exact Q'.le_of_eqv (Q'.mul_one_eqv (forward + reverse))
  have houter := abs_mul_le
    background ((forward - reverse) * indicator)
  have hbackgroundAbs : Q'.abs background = background :=
    abs_of_nonneg hbackground
  rw [hbackgroundAbs] at houter
  exact Q'.le_trans' _ _ _ houter
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hinner hbackground)

/-! ## 3. Pointwise and finite-sum domination -/

/-- Every localized signed response term is bounded by its explicit positive
envelope, for an arbitrary Boolean observable. -/
theorem finePacketLocalizedAntisymmetricResponsePairTerm_abs_le_envelope
    (S : SlabScalePair) (first second : EdgeLabelling)
    (event : EdgeLabelling → Bool)
    (pair : EdgeLabelling × EdgeLabelling) :
    Q'.abs
        (finePacketLocalizedAntisymmetricResponsePairTerm
          S first second event pair) ≤
      finePacketLocalizedResponsePairEnvelope
        S first second pair := by
  let background :=
    finePacketCommonExteriorGibbsWeight S first second pair.1 *
      finePacketCommonExteriorGibbsWeight S first second pair.2
  let forward :=
    finePacketDisagreementTilt S first first second pair.1 *
      finePacketDisagreementTilt S second first second pair.2
  let reverse :=
    finePacketDisagreementTilt S second first second pair.1 *
      finePacketDisagreementTilt S first first second pair.2
  let indicator :=
    booleanEventIndicator event pair.1 -
      booleanEventIndicator event pair.2
  change Q'.abs (background * ((forward - reverse) * indicator)) ≤
    background * (forward + reverse)
  exact abs_background_mul_det_mul_indicator_le
    background forward reverse indicator
    (Q'.mul_nonneg _ _
      (finePacketCommonExteriorGibbsWeight_nonnegative
        S first second pair.1)
      (finePacketCommonExteriorGibbsWeight_nonnegative
        S first second pair.2))
    (Q'.mul_nonneg _ _
      (finePacketDisagreementTilt_nonnegative
        S first first second pair.1)
      (finePacketDisagreementTilt_nonnegative
        S second first second pair.2))
    (Q'.mul_nonneg _ _
      (finePacketDisagreementTilt_nonnegative
        S second first second pair.1)
      (finePacketDisagreementTilt_nonnegative
        S first first second pair.2))
    (booleanEventIndicator_sub_abs_le_one event pair.1 pair.2)

private theorem abs_listQSum_le_listQSum_of_pointwise
    {A : Type} (term envelope : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → Q'.abs (term item) ≤ envelope item) →
        Q'.abs (listQSum term items) ≤ listQSum envelope items
  | [], _ => by
      change Q'.abs (0 : Q') ≤ 0
      decide
  | head :: tail, hpointwise => by
      have hhead := hpointwise head List.mem_cons_self
      have htail := abs_listQSum_le_listQSum_of_pointwise
        term envelope tail (fun item hitem =>
          hpointwise item (List.mem_cons_of_mem head hitem))
      exact Q'.le_trans' _ _ _
        (abs_add_le (term head) (listQSum term tail))
        (Q'.add_le_add hhead htail)

/-- The absolute connected signed sum is bounded by the sum of the explicit
positive envelopes on exactly the same carrier. -/
theorem finePacketFaceResponseConnectedActivePairSum_abs_le_envelopeSum
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat) :
    Q'.abs
        (listQSum
          (finePacketLocalizedAntisymmetricResponsePairTerm
            S first second
              (slabPhysicalFacePositiveB observableFaceId))
          (finePacketFaceResponseConnectedActivePairs
            S first second observableFaceId)) ≤
      listQSum
        (finePacketLocalizedResponsePairEnvelope S first second)
        (finePacketFaceResponseConnectedActivePairs
          S first second observableFaceId) := by
  apply abs_listQSum_le_listQSum_of_pointwise
  intro pair _
  exact finePacketLocalizedAntisymmetricResponsePairTerm_abs_le_envelope
    S first second (slabPhysicalFacePositiveB observableFaceId) pair

/-- Combining exact disconnected cancellation with the positive envelope
bounds the actual denominator-cleared two-row response, without any loss on
disconnected target pairs. -/
theorem two_mul_positivePhysicalTiltedGibbsRawCross_abs_le_connectedEnvelopeSum
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    Q'.abs
        ((2 : Q') *
          positivePhysicalTiltedGibbsTwoRowRawCrossNumerator
            S first second
              (slabPhysicalFacePositiveB observableFaceId)) ≤
      listQSum
        (finePacketLocalizedResponsePairEnvelope
          S first.1 second.1)
        (finePacketFaceResponseConnectedActivePairs
          S first.1 second.1 observableFaceId) := by
  have heq :=
    two_mul_positivePhysicalTiltedGibbsRawCross_eqv_connectedPairSum
      S hfineCutoff first second observableFaceId hobservableFace
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (abs_eqv_congr heq))
    (finePacketFaceResponseConnectedActivePairSum_abs_le_envelopeSum
      S first.1 second.1 observableFaceId)

/-! ## 4. Axiom audit -/

#print axioms finePacketLocalizedResponsePairEnvelope
#print axioms finePacketCommonExteriorGibbsWeight_nonnegative
#print axioms finePacketLocalizedResponsePairEnvelope_nonnegative
#print axioms booleanEventIndicator_sub_abs_le_one
#print axioms finePacketLocalizedAntisymmetricResponsePairTerm_abs_le_envelope
#print axioms finePacketFaceResponseConnectedActivePairSum_abs_le_envelopeSum
#print axioms two_mul_positivePhysicalTiltedGibbsRawCross_abs_le_connectedEnvelopeSum

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelope
