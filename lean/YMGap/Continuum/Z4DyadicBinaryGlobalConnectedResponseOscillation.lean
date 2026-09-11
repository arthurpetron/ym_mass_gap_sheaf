/-
# Global connected response oscillation at the SU(2) anchor

The strict connected production fraction becomes an observable estimate only
after it is averaged against the actual fine source law.  This file performs
that contraction exactly.  It defines the normalized source-pair average of
the absolute difference between two tilted Gibbs face responses and proves
that it is bounded by the arithmetic mean of the forward and reverse global
connected production fractions.

The factor `1/2` is load-bearing: the connected response envelope is the
symmetrized sum of two oriented rows, while each global oriented fraction is
normalized by one row product.  Keeping that exact average lets the two
anchor bounds `1449/1700` combine with no loss.  The result is a strict,
finite-volume, volume-independent one-face posterior-response oscillation
bound at the named SU(2) anchor.

No posterior variance identity, dense form bound, completed spectral gap,
thermodynamic limit, continuum theory, or Clay theorem is asserted here.

Constructive contract: exact rational finite-sum algebra and previously
proved normalized response bounds only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, trusted external
computation, enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryGlobalConnectedVacuumPacketStrictness
import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedResponseFraction

namespace YMGap.Continuum.Z4DyadicBinaryGlobalConnectedResponseOscillation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedVacuumPacketStrictness
open YMGap.Continuum.Z4DyadicBinaryGlobalNormalizedConnectedCarrier
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedUnitCongestionSum
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelope
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelopeNormalization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedResponseFraction
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSupportSwapResponse
open YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → lower item ≤ upper item) →
      listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle => by
      simp only [listQSum]
      exact Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

private theorem finePacketFineSourceRawPairWeight_nonnegative
    (S : SlabScalePair) (pair : PositivePhysicalSourcePair S) :
    (0 : Q') ≤ finePacketFineSourceRawPairWeight
      S pair.1.1 pair.2.1 := by
  unfold finePacketFineSourceRawPairWeight
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt pair.1.2.2) (Q'.le_of_lt pair.2.2.2)

private theorem finePhysicalPartitionSquare_pos (S : SlabScalePair) :
    (0 : Q') < S.fine.physicalPartition * S.fine.physicalPartition :=
  Q'.mul_pos
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)

/-! ## 1. The global observable and its connected envelope -/

/-- The actual fine-source-pair-weighted absolute oscillation between the two
normalized tilted Gibbs responses of one coarse face. -/
def finePacketGlobalTiltedGibbsFaceResponseOscillationMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) : Q' :=
  listQSum
    (fun pair : PositivePhysicalSourcePair S =>
      finePacketFineSourceRawPairWeight S pair.1.1 pair.2.1 *
        Q'.abs
          (positivePhysicalSourceTiltedGibbsEventMass
              S hfineCutoff hcoarseCoupling pair.1
                (slabPhysicalFacePositiveB observableFaceId) -
            positivePhysicalSourceTiltedGibbsEventMass
              S hfineCutoff hcoarseCoupling pair.2
                (slabPhysicalFacePositiveB observableFaceId)))
    (positivePhysicalSourcePairs S)

/-- The same response oscillation normalized by the exact square of the fine
physical partition. -/
def finePacketGlobalTiltedGibbsFaceResponseOscillationFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) : Q' :=
  Q'.divPos
    (finePacketGlobalTiltedGibbsFaceResponseOscillationMass
      S hfineCutoff hcoarseCoupling observableFaceId)
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (finePhysicalPartitionSquare_pos S)

/-- The fine-source-pair average of the exact symmetrized connected envelope
fraction. -/
def finePacketGlobalConnectedResponseEnvelopeMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) : Q' :=
  listQSum
    (fun pair : PositivePhysicalSourcePair S =>
      finePacketFineSourceRawPairWeight S pair.1.1 pair.2.1 *
        finePacketConnectedEnvelopeFraction
          S hfineCutoff hcoarseCoupling pair.1 pair.2 observableFaceId)
    (positivePhysicalSourcePairs S)

def finePacketGlobalConnectedResponseEnvelopeFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) : Q' :=
  Q'.divPos
    (finePacketGlobalConnectedResponseEnvelopeMass
      S hfineCutoff hcoarseCoupling observableFaceId)
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (finePhysicalPartitionSquare_pos S)

theorem finePacketGlobalTiltedGibbsFaceResponseOscillationMass_le_envelopeMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketGlobalTiltedGibbsFaceResponseOscillationMass
        S hfineCutoff hcoarseCoupling observableFaceId ≤
      finePacketGlobalConnectedResponseEnvelopeMass
        S hfineCutoff hcoarseCoupling observableFaceId := by
  unfold finePacketGlobalTiltedGibbsFaceResponseOscillationMass
    finePacketGlobalConnectedResponseEnvelopeMass
  apply listQSum_mono_local
  intro pair _
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (positivePhysicalTiltedGibbsFaceResponseDifference_abs_le_connectedEnvelopeFraction
      S hfineCutoff hcoarseCoupling pair.1 pair.2 observableFaceId
        hobservableFace)
    (finePacketFineSourceRawPairWeight_nonnegative S pair)

theorem finePacketGlobalTiltedGibbsFaceResponseOscillationFraction_le_envelopeFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketGlobalTiltedGibbsFaceResponseOscillationFraction
        S hfineCutoff hcoarseCoupling observableFaceId ≤
      finePacketGlobalConnectedResponseEnvelopeFraction
        S hfineCutoff hcoarseCoupling observableFaceId := by
  unfold finePacketGlobalTiltedGibbsFaceResponseOscillationFraction
    finePacketGlobalConnectedResponseEnvelopeFraction Q'.divPos
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (finePacketGlobalTiltedGibbsFaceResponseOscillationMass_le_envelopeMass
      S hfineCutoff hcoarseCoupling observableFaceId hobservableFace)
    (Q'.le_of_lt
      (Q'.recipPos_pos _ (finePhysicalPartitionSquare_pos S)))

/-! ## 2. Preserve the exact half-sum of the two orientations -/

private theorem divPos_add_over_two_mul_eqv_half_sum
    (left right row : Q') (hrow : (0 : Q') < row) :
    Q'.divPos (left + right) ((2 : Q') * row)
        (Q'.mul_pos (Q'.ofNat_succ_pos 1) hrow) ≈
      HalfPow.half *
        (Q'.divPos left row hrow + Q'.divPos right row hrow) := by
  let denominator := (2 : Q') * row
  let leftFraction := Q'.divPos left row hrow
  let rightFraction := Q'.divPos right row hrow
  have hdenominator : (0 : Q') < denominator :=
    Q'.mul_pos (Q'.ofNat_succ_pos 1) hrow
  have hdenominatorHalf : denominator * HalfPow.half ≈ row := by
    unfold denominator
    refine Q'.eqv_trans _
      ((2 : Q') * (row * HalfPow.half)) _
      (Q'.mul_assoc_eqv (2 : Q') row HalfPow.half) ?_
    refine Q'.eqv_trans _
      ((2 : Q') * (HalfPow.half * row)) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_comm_eqv row HalfPow.half)) ?_
    refine Q'.eqv_trans _
      (((2 : Q') * HalfPow.half) * row) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (2 : Q') HalfPow.half row)) ?_
    refine Q'.eqv_trans _ ((1 : Q') * row) _ ?_ (Q'.one_mul_eqv row)
    exact Q'.mul_eqv_congr_right _ _ row (by decide)
  have hleftScaled :
      denominator *
          Q'.divPos (left + right) denominator hdenominator ≈
        left + right := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv denominator
        (Q'.divPos (left + right) denominator hdenominator))
      (Q'.divPos_mul_eqv (left + right) denominator hdenominator)
  have hrightScaled :
      denominator *
          (HalfPow.half * (leftFraction + rightFraction)) ≈
        left + right := by
    refine Q'.eqv_trans _
      ((denominator * HalfPow.half) *
        (leftFraction + rightFraction)) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv denominator HalfPow.half
          (leftFraction + rightFraction))) ?_
    refine Q'.eqv_trans _
      (row * (leftFraction + rightFraction)) _
      (Q'.mul_eqv_congr_right _ _ _ hdenominatorHalf) ?_
    refine Q'.eqv_trans _
      (row * leftFraction + row * rightFraction) _
      (Q'.mul_add_eqv row leftFraction rightFraction) ?_
    refine Q'.eqv_trans _
      (leftFraction * row + rightFraction * row) _
      (Q'.add_eqv_congr'
        (Q'.mul_comm_eqv row leftFraction)
        (Q'.mul_comm_eqv row rightFraction)) ?_
    exact Q'.add_eqv_congr'
      (Q'.divPos_mul_eqv left row hrow)
      (Q'.divPos_mul_eqv right row hrow)
  apply Q'.mul_left_cancel_of_pos hdenominator
  exact Q'.eqv_trans _ _ _ hleftScaled (Q'.eqv_symm hrightScaled)

/-- The original symmetrized connected envelope fraction is exactly the
arithmetic mean of its forward and reverse oriented fractions. -/
theorem finePacketConnectedEnvelopeFraction_eqv_orientedAverage
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat) :
    finePacketConnectedEnvelopeFraction
        S hfineCutoff hcoarseCoupling first second observableFaceId ≈
      HalfPow.half *
        (finePacketForwardConnectedEnvelopeFraction
            S hfineCutoff hcoarseCoupling first second observableFaceId +
          finePacketReverseConnectedEnvelopeFraction
            S hfineCutoff hcoarseCoupling first second observableFaceId) := by
  let left := finePacketForwardConnectedEnvelopeMass
    S first.1 second.1 observableFaceId
  let right := finePacketReverseConnectedEnvelopeMass
    S first.1 second.1 observableFaceId
  let row := finePacketOrientedEnvelopeNormalizationMass S first second
  let numerator := listQSum
    (finePacketLocalizedResponsePairEnvelope S first.1 second.1)
    (finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId)
  have hrow : (0 : Q') < row :=
    finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling first second
  have hnumerator : numerator ≈ left + right :=
    finePacketConnectedEnvelopeSum_eqv_forward_add_reverse
      S first.1 second.1 observableFaceId
  have hreplace :
      Q'.divPos numerator ((2 : Q') * row)
          (Q'.mul_pos (Q'.ofNat_succ_pos 1) hrow) ≈
        Q'.divPos (left + right) ((2 : Q') * row)
          (Q'.mul_pos (Q'.ofNat_succ_pos 1) hrow) := by
    unfold Q'.divPos
    exact Q'.mul_eqv_congr_right _ _ _ hnumerator
  refine Q'.eqv_trans _
    (Q'.divPos (left + right) ((2 : Q') * row)
      (Q'.mul_pos (Q'.ofNat_succ_pos 1) hrow)) _ ?_ ?_
  · unfold finePacketConnectedEnvelopeFraction
      finePacketConnectedEnvelopeNormalizationMass
    exact hreplace
  · unfold finePacketForwardConnectedEnvelopeFraction
      finePacketReverseConnectedEnvelopeFraction
    exact divPos_add_over_two_mul_eqv_half_sum left right row hrow

private theorem finePacketOrientedNormalizedConnectedJointMass_eqv_sourceWeight_mul_fraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat) :
    finePacketOrientedNormalizedConnectedJointMass
        S hfineCutoff hcoarseCoupling orientation first second
          observableFaceId ≈
      finePacketFineSourceRawPairWeight S first.1 second.1 *
        Q'.divPos
          (listQSum
            (finePacketOrientedLocalizedRawPairWeight
              S orientation first.1 second.1)
            (finePacketFaceResponseConnectedActivePairs
              S first.1 second.1 observableFaceId))
          (finePacketOrientedEnvelopeNormalizationMass S first second)
          (finePacketOrientedEnvelopeNormalizationMass_pos
            S hfineCutoff hcoarseCoupling first second) := by
  let sourceWeight := finePacketFineSourceRawPairWeight
    S first.1 second.1
  let targetWeight := finePacketOrientedLocalizedRawPairWeight
    S orientation first.1 second.1
  let states := finePacketFaceResponseConnectedActivePairs
    S first.1 second.1 observableFaceId
  let row := finePacketOrientedEnvelopeNormalizationMass S first second
  let reciprocal := Q'.recipPos row
    (finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling first second)
  unfold finePacketOrientedNormalizedConnectedJointMass
    finePacketOrientedNormalizedJointPairWeight
    finePacketOrientedJointGibbsRawPairWeight Q'.divPos
  change
    listQSum
        (fun entry : {pair // pair ∈ states} =>
          (sourceWeight * targetWeight entry.val) * reciprocal)
        states.attach ≈
      sourceWeight * (listQSum targetWeight states * reciprocal)
  refine Q'.eqv_trans _
    (listQSum
      (fun pair => (sourceWeight * targetWeight pair) * reciprocal)
      states) _ ?_ ?_
  · exact Q'.eqv_of_eq
      (listQSum_attach
        (fun pair => (sourceWeight * targetWeight pair) * reciprocal)
        states)
  refine Q'.eqv_trans _
    (listQSum
      (fun pair => sourceWeight * (targetWeight pair * reciprocal))
      states) _ ?_ ?_
  · apply listQSum_congr
    intro pair
    exact Q'.mul_assoc_eqv sourceWeight (targetWeight pair) reciprocal
  refine Q'.eqv_trans _
    (sourceWeight *
      listQSum (fun pair => targetWeight pair * reciprocal) states) _
    (listQSum_mul_left sourceWeight
      (fun pair => targetWeight pair * reciprocal) states) ?_
  exact Q'.mul_eqv_congr_left sourceWeight _ _
    (listQSum_mul_right targetWeight reciprocal states)

private theorem finePacketForwardNormalizedConnectedJointMass_eqv_weight_mul_fraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat) :
    finePacketOrientedNormalizedConnectedJointMass
        S hfineCutoff hcoarseCoupling .forward first second
          observableFaceId ≈
      finePacketFineSourceRawPairWeight S first.1 second.1 *
        finePacketForwardConnectedEnvelopeFraction
          S hfineCutoff hcoarseCoupling first second observableFaceId := by
  simpa only [finePacketOrientedLocalizedRawPairWeight,
    finePacketForwardConnectedEnvelopeFraction,
    finePacketForwardConnectedEnvelopeMass] using
    (finePacketOrientedNormalizedConnectedJointMass_eqv_sourceWeight_mul_fraction
      S hfineCutoff hcoarseCoupling .forward first second observableFaceId)

private theorem finePacketReverseNormalizedConnectedJointMass_eqv_weight_mul_fraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat) :
    finePacketOrientedNormalizedConnectedJointMass
        S hfineCutoff hcoarseCoupling .reverse first second
          observableFaceId ≈
      finePacketFineSourceRawPairWeight S first.1 second.1 *
        finePacketReverseConnectedEnvelopeFraction
          S hfineCutoff hcoarseCoupling first second observableFaceId := by
  simpa only [finePacketOrientedLocalizedRawPairWeight,
    finePacketReverseConnectedEnvelopeFraction,
    finePacketReverseConnectedEnvelopeMass] using
    (finePacketOrientedNormalizedConnectedJointMass_eqv_sourceWeight_mul_fraction
      S hfineCutoff hcoarseCoupling .reverse first second observableFaceId)

private theorem mul_half_sum_eqv_half_sum_mul
    (weight left right : Q') :
    weight * (HalfPow.half * (left + right)) ≈
      HalfPow.half * (weight * left + weight * right) := by
  refine Q'.eqv_trans _
    ((weight * HalfPow.half) * (left + right)) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv weight HalfPow.half (left + right))) ?_
  refine Q'.eqv_trans _
    ((HalfPow.half * weight) * (left + right)) _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv weight HalfPow.half)) ?_
  refine Q'.eqv_trans _
    (HalfPow.half * (weight * (left + right))) _
    (Q'.mul_assoc_eqv HalfPow.half weight (left + right)) ?_
  exact Q'.mul_eqv_congr_left HalfPow.half _ _
    (Q'.mul_add_eqv weight left right)

private theorem sourceWeight_mul_connectedEnvelopeFraction_eqv_orientedJointAverage
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat) :
    finePacketFineSourceRawPairWeight S first.1 second.1 *
        finePacketConnectedEnvelopeFraction
          S hfineCutoff hcoarseCoupling first second observableFaceId ≈
      HalfPow.half *
        (finePacketOrientedNormalizedConnectedJointMass
            S hfineCutoff hcoarseCoupling .forward first second
              observableFaceId +
          finePacketOrientedNormalizedConnectedJointMass
            S hfineCutoff hcoarseCoupling .reverse first second
              observableFaceId) := by
  let weight := finePacketFineSourceRawPairWeight S first.1 second.1
  let forward := finePacketForwardConnectedEnvelopeFraction
    S hfineCutoff hcoarseCoupling first second observableFaceId
  let reverse := finePacketReverseConnectedEnvelopeFraction
    S hfineCutoff hcoarseCoupling first second observableFaceId
  refine Q'.eqv_trans _
    (weight * (HalfPow.half * (forward + reverse))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left weight _ _
      (finePacketConnectedEnvelopeFraction_eqv_orientedAverage
        S hfineCutoff hcoarseCoupling first second observableFaceId)
  refine Q'.eqv_trans _
    (HalfPow.half * (weight * forward + weight * reverse)) _
    (mul_half_sum_eqv_half_sum_mul weight forward reverse) ?_
  exact Q'.mul_eqv_congr_left HalfPow.half _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_symm
        (finePacketForwardNormalizedConnectedJointMass_eqv_weight_mul_fraction
          S hfineCutoff hcoarseCoupling first second observableFaceId))
      (Q'.eqv_symm
        (finePacketReverseNormalizedConnectedJointMass_eqv_weight_mul_fraction
          S hfineCutoff hcoarseCoupling first second observableFaceId)))

/-- Averaging the symmetrized connected response envelope over the actual fine
source pair law gives exactly half the sum of the two oriented global
connected masses. -/
theorem finePacketGlobalConnectedResponseEnvelopeMass_eqv_orientedAverage
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) :
    finePacketGlobalConnectedResponseEnvelopeMass
        S hfineCutoff hcoarseCoupling observableFaceId ≈
      HalfPow.half *
        (finePacketGlobalNormalizedConnectedJointMass
            S hfineCutoff hcoarseCoupling .forward observableFaceId +
          finePacketGlobalNormalizedConnectedJointMass
            S hfineCutoff hcoarseCoupling .reverse observableFaceId) := by
  unfold finePacketGlobalConnectedResponseEnvelopeMass
  refine Q'.eqv_trans _
    (listQSum
      (fun pair : PositivePhysicalSourcePair S =>
        HalfPow.half *
          (finePacketOrientedNormalizedConnectedJointMass
              S hfineCutoff hcoarseCoupling .forward pair.1 pair.2
                observableFaceId +
            finePacketOrientedNormalizedConnectedJointMass
              S hfineCutoff hcoarseCoupling .reverse pair.1 pair.2
                observableFaceId))
      (positivePhysicalSourcePairs S)) _ ?_ ?_
  · apply listQSum_congr
    intro pair
    exact sourceWeight_mul_connectedEnvelopeFraction_eqv_orientedJointAverage
      S hfineCutoff hcoarseCoupling pair.1 pair.2 observableFaceId
  refine Q'.eqv_trans _
    (HalfPow.half *
      listQSum
        (fun pair : PositivePhysicalSourcePair S =>
          finePacketOrientedNormalizedConnectedJointMass
              S hfineCutoff hcoarseCoupling .forward pair.1 pair.2
                observableFaceId +
            finePacketOrientedNormalizedConnectedJointMass
              S hfineCutoff hcoarseCoupling .reverse pair.1 pair.2
                observableFaceId)
        (positivePhysicalSourcePairs S)) _
    (listQSum_mul_left HalfPow.half _ _) ?_
  exact Q'.mul_eqv_congr_left HalfPow.half _ _
    (by
      unfold finePacketGlobalNormalizedConnectedJointMass
      exact listQSum_add _ _ (positivePhysicalSourcePairs S))

private theorem divPos_half_sum_eqv_half_sum_divPos
    (left right denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos (HalfPow.half * (left + right)) denominator hdenominator ≈
      HalfPow.half *
        (Q'.divPos left denominator hdenominator +
          Q'.divPos right denominator hdenominator) := by
  unfold Q'.divPos
  let reciprocal := Q'.recipPos denominator hdenominator
  refine Q'.eqv_trans _
    (HalfPow.half * ((left + right) * reciprocal)) _
    (Q'.mul_assoc_eqv HalfPow.half (left + right) reciprocal) ?_
  refine Q'.eqv_trans _
    (HalfPow.half * (left * reciprocal + right * reciprocal)) _
    (Q'.mul_eqv_congr_left HalfPow.half _ _
      (Q'.add_mul_eqv left right reciprocal)) ?_
  exact Q'.eqv_refl _

/-- After division by the exact fine partition square, the global connected
response envelope remains exactly the arithmetic mean of the forward and
reverse global connected fractions. -/
theorem finePacketGlobalConnectedResponseEnvelopeFraction_eqv_orientedAverage
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat) :
    finePacketGlobalConnectedResponseEnvelopeFraction
        S hfineCutoff hcoarseCoupling observableFaceId ≈
      HalfPow.half *
        (finePacketGlobalNormalizedConnectedJointFraction
            S hfineCutoff hcoarseCoupling .forward observableFaceId +
          finePacketGlobalNormalizedConnectedJointFraction
            S hfineCutoff hcoarseCoupling .reverse observableFaceId) := by
  let denominator := S.fine.physicalPartition * S.fine.physicalPartition
  let forward := finePacketGlobalNormalizedConnectedJointMass
    S hfineCutoff hcoarseCoupling .forward observableFaceId
  let reverse := finePacketGlobalNormalizedConnectedJointMass
    S hfineCutoff hcoarseCoupling .reverse observableFaceId
  have hdenominator : (0 : Q') < denominator :=
    finePhysicalPartitionSquare_pos S
  refine Q'.eqv_trans _
    (Q'.divPos (HalfPow.half * (forward + reverse))
      denominator hdenominator) _ ?_ ?_
  · unfold finePacketGlobalConnectedResponseEnvelopeFraction
    unfold Q'.divPos
    exact Q'.mul_eqv_congr_right _ _ _
      (finePacketGlobalConnectedResponseEnvelopeMass_eqv_orientedAverage
        S hfineCutoff hcoarseCoupling observableFaceId)
  · unfold finePacketGlobalNormalizedConnectedJointFraction
    exact divPos_half_sum_eqv_half_sum_divPos
      forward reverse denominator hdenominator

/-! ## 3. The strict anchor response estimate -/

/-- The normalized global face-response oscillation is bounded by the exact
average of the two oriented connected production fractions. -/
theorem finePacketGlobalTiltedGibbsFaceResponseOscillationFraction_le_orientedAverage
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketGlobalTiltedGibbsFaceResponseOscillationFraction
        S hfineCutoff hcoarseCoupling observableFaceId ≤
      HalfPow.half *
        (finePacketGlobalNormalizedConnectedJointFraction
            S hfineCutoff hcoarseCoupling .forward observableFaceId +
          finePacketGlobalNormalizedConnectedJointFraction
            S hfineCutoff hcoarseCoupling .reverse observableFaceId) := by
  exact Q'.le_trans' _ _ _
    (finePacketGlobalTiltedGibbsFaceResponseOscillationFraction_le_envelopeFraction
      S hfineCutoff hcoarseCoupling observableFaceId hobservableFace)
    (Q'.le_of_eqv
      (finePacketGlobalConnectedResponseEnvelopeFraction_eqv_orientedAverage
        S hfineCutoff hcoarseCoupling observableFaceId))

/-- At the named SU(2) anchor the normalized global one-face posterior
response oscillation has the same explicit strict rate `1449/1700` as each
oriented connected production fraction. -/
theorem finePacketGlobalTiltedGibbsFaceResponseOscillationFraction_le_anchorVacuumPacketRate
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (cutoff half observableFaceId : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketGlobalTiltedGibbsFaceResponseOscillationFraction
        S hfineCutoff hcoarseCoupling observableFaceId ≤
      finePacketAnchorVacuumPacketStrictRate := by
  have hforward :=
    finePacketGlobalNormalizedConnectedJointFraction_le_anchorVacuumPacketRate
      S hfineCutoff hcoarseCoupling .forward cutoff half observableFaceId
        hfine hobservableFace
  have hreverse :=
    finePacketGlobalNormalizedConnectedJointFraction_le_anchorVacuumPacketRate
      S hfineCutoff hcoarseCoupling .reverse cutoff half observableFaceId
        hfine hobservableFace
  have haverage :
      HalfPow.half *
          (finePacketGlobalNormalizedConnectedJointFraction
              S hfineCutoff hcoarseCoupling .forward observableFaceId +
            finePacketGlobalNormalizedConnectedJointFraction
              S hfineCutoff hcoarseCoupling .reverse observableFaceId) ≤
        finePacketAnchorVacuumPacketStrictRate := by
    have hsum := Q'.add_le_add hforward hreverse
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      hsum HalfPow.half_nonneg
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (by
        refine Q'.eqv_trans _
          (HalfPow.half * finePacketAnchorVacuumPacketStrictRate +
            HalfPow.half * finePacketAnchorVacuumPacketStrictRate) _
          (Q'.mul_add_eqv HalfPow.half
            finePacketAnchorVacuumPacketStrictRate
            finePacketAnchorVacuumPacketStrictRate) ?_
        exact YMGap.Constructive.ExpNeg.two_halves
          finePacketAnchorVacuumPacketStrictRate))
  exact Q'.le_trans' _ _ _
    (finePacketGlobalTiltedGibbsFaceResponseOscillationFraction_le_orientedAverage
      S hfineCutoff hcoarseCoupling observableFaceId hobservableFace)
    haverage

theorem finePacketGlobalTiltedGibbsFaceResponseOscillationFraction_lt_one_at_anchor
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (cutoff half observableFaceId : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketGlobalTiltedGibbsFaceResponseOscillationFraction
        S hfineCutoff hcoarseCoupling observableFaceId < (1 : Q') := by
  exact Q'.lt_of_le_of_lt
    (finePacketGlobalTiltedGibbsFaceResponseOscillationFraction_le_anchorVacuumPacketRate
      S hfineCutoff hcoarseCoupling cutoff half observableFaceId
        hfine hobservableFace)
    finePacketAnchorVacuumPacketStrictRate_lt_one

/-! ## Axiom audit -/

#print axioms finePacketGlobalTiltedGibbsFaceResponseOscillationMass
#print axioms finePacketGlobalTiltedGibbsFaceResponseOscillationFraction
#print axioms finePacketGlobalConnectedResponseEnvelopeMass
#print axioms finePacketGlobalConnectedResponseEnvelopeFraction
#print axioms finePacketGlobalTiltedGibbsFaceResponseOscillationMass_le_envelopeMass
#print axioms finePacketGlobalTiltedGibbsFaceResponseOscillationFraction_le_envelopeFraction
#print axioms finePacketConnectedEnvelopeFraction_eqv_orientedAverage
#print axioms finePacketGlobalConnectedResponseEnvelopeMass_eqv_orientedAverage
#print axioms finePacketGlobalConnectedResponseEnvelopeFraction_eqv_orientedAverage
#print axioms finePacketGlobalTiltedGibbsFaceResponseOscillationFraction_le_orientedAverage
#print axioms finePacketGlobalTiltedGibbsFaceResponseOscillationFraction_le_anchorVacuumPacketRate
#print axioms finePacketGlobalTiltedGibbsFaceResponseOscillationFraction_lt_one_at_anchor

end YMGap.Continuum.Z4DyadicBinaryGlobalConnectedResponseOscillation
