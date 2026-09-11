/-
# Envelope bounds for the connected-observable gradients

Each term in the symmetric-gradient factorization is one localized one-face
determinant multiplied by a doubled gradient of absolute value at most two.
This file proves the corresponding pointwise and finite connected-carrier
envelope bounds, then combines the root and target pieces without losing the
factor two carried by the exact gradient identity.

The complete active sums may be replaced by the connected sums using the
preceding exact disconnected cancellation.  No two-row rational-observable
cross identity, posterior variance, dense form bound, completed gap,
thermodynamic limit, continuum theory, or Clay theorem is asserted here.

Constructive contract: rational order, finite sums, and previously proved
component cancellation only; no `Classical`, choice, `native_decide`, proof
hole, noncomputable declaration, trusted external computation, enlarged
heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryConnectedObservableGradientDisconnectedCancellation
import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelope

namespace YMGap.Continuum.Z4DyadicBinaryConnectedObservableGradientEnvelope

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryConnectedObservableGradientDisconnectedCancellation
open YMGap.Continuum.Z4DyadicBinaryConnectedObservableSymmetricGradient
open YMGap.Continuum.Z4DyadicBinaryConnectedObservableSymmetricGradientSwap
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelope
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseActiveCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseDeterminant

local infix:50 " ≈ " => Q'.eqv

private theorem abs_listQSum_le_listQSum_of_pointwise_local
    {A : Type} (term envelope : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → Q'.abs (term item) ≤ envelope item) →
        Q'.abs (listQSum term items) ≤ listQSum envelope items
  | [], _ => by
      change Q'.abs (0 : Q') ≤ 0
      decide
  | head :: tail, hpointwise => by
      have hhead := hpointwise head List.mem_cons_self
      have htail := abs_listQSum_le_listQSum_of_pointwise_local
        term envelope tail (fun item hitem =>
          hpointwise item (List.mem_cons_of_mem head hitem))
      exact Q'.le_trans' _ _ _
        (abs_add_le (term head) (listQSum term tail))
        (Q'.add_le_add hhead htail)

/-! ## 1. Pointwise doubled-gradient cost -/

theorem localizedConnectedRootGradientPairTerm_abs_le_two_envelope
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) :
    Q'.abs
        (finePacketLocalizedConnectedRootGradientPairTerm
          K M first second pair) ≤
      finePacketLocalizedResponsePairEnvelope S first second pair *
        (2 : Q') := by
  unfold finePacketLocalizedConnectedRootGradientPairTerm
  have habsMul := abs_mul_le
    (finePacketLocalizedAntisymmetricResponsePairTerm
      S first second (slabPhysicalFacePositiveB M.coarseRoot) pair)
    (connectedRemainderRootDoubledSymmetricGradient K M pair.1 pair.2)
  have hresponse :=
    finePacketLocalizedAntisymmetricResponsePairTerm_abs_le_envelope
      S first second (slabPhysicalFacePositiveB M.coarseRoot) pair
  have hgradient :=
    connectedRemainderRootDoubledSymmetricGradient_abs_le_two
      K M pair.1 pair.2
  refine Q'.le_trans' _ _ _ habsMul ?_
  refine Q'.le_trans' _
    (finePacketLocalizedResponsePairEnvelope S first second pair *
      Q'.abs
        (connectedRemainderRootDoubledSymmetricGradient
          K M pair.1 pair.2)) _ ?_ ?_
  · exact Q'.mul_le_mul_of_nonneg_right _ _ _ hresponse
      (Q'.abs_nonneg _)
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _ hgradient
      (finePacketLocalizedResponsePairEnvelope_nonnegative
        S first second pair)

theorem localizedConnectedTargetGradientPairTerm_abs_le_two_envelope
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) :
    Q'.abs
        (finePacketLocalizedConnectedTargetGradientPairTerm
          K M first second pair) ≤
      finePacketLocalizedResponsePairEnvelope S first second pair *
        (2 : Q') := by
  unfold finePacketLocalizedConnectedTargetGradientPairTerm
  have habsMul := abs_mul_le
    (finePacketLocalizedAntisymmetricResponsePairTerm
      S first second (slabPhysicalFacePositiveB M.coarseTarget) pair)
    (connectedRemainderTargetDoubledSymmetricGradient K M pair.1 pair.2)
  have hresponse :=
    finePacketLocalizedAntisymmetricResponsePairTerm_abs_le_envelope
      S first second (slabPhysicalFacePositiveB M.coarseTarget) pair
  have hgradient :=
    connectedRemainderTargetDoubledSymmetricGradient_abs_le_two
      K M pair.1 pair.2
  refine Q'.le_trans' _ _ _ habsMul ?_
  refine Q'.le_trans' _
    (finePacketLocalizedResponsePairEnvelope S first second pair *
      Q'.abs
        (connectedRemainderTargetDoubledSymmetricGradient
          K M pair.1 pair.2)) _ ?_ ?_
  · exact Q'.mul_le_mul_of_nonneg_right _ _ _ hresponse
      (Q'.abs_nonneg _)
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _ hgradient
      (finePacketLocalizedResponsePairEnvelope_nonnegative
        S first second pair)

/-! ## 2. Finite connected-carrier envelopes -/

theorem connectedRootGradientConnectedPairSum_abs_le_two_envelopeSum
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling) :
    Q'.abs
        (listQSum
          (finePacketLocalizedConnectedRootGradientPairTerm
            K M first second)
          (finePacketFaceResponseConnectedActivePairs
            S first second M.coarseRoot)) ≤
      (2 : Q') *
        listQSum
          (finePacketLocalizedResponsePairEnvelope S first second)
          (finePacketFaceResponseConnectedActivePairs
            S first second M.coarseRoot) := by
  have hbound := abs_listQSum_le_listQSum_of_pointwise_local
    (finePacketLocalizedConnectedRootGradientPairTerm K M first second)
    (fun pair =>
      finePacketLocalizedResponsePairEnvelope S first second pair * (2 : Q'))
    (finePacketFaceResponseConnectedActivePairs
      S first second M.coarseRoot)
    (fun pair _ =>
      localizedConnectedRootGradientPairTerm_abs_le_two_envelope
        K M first second pair)
  exact Q'.le_trans' _ _ _ hbound
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (listQSum_mul_right
        (finePacketLocalizedResponsePairEnvelope S first second)
        (2 : Q')
        (finePacketFaceResponseConnectedActivePairs
          S first second M.coarseRoot))
      (Q'.mul_comm_eqv _ _)))

theorem connectedTargetGradientConnectedPairSum_abs_le_two_envelopeSum
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling) :
    Q'.abs
        (listQSum
          (finePacketLocalizedConnectedTargetGradientPairTerm
            K M first second)
          (finePacketFaceResponseConnectedActivePairs
            S first second M.coarseTarget)) ≤
      (2 : Q') *
        listQSum
          (finePacketLocalizedResponsePairEnvelope S first second)
          (finePacketFaceResponseConnectedActivePairs
            S first second M.coarseTarget) := by
  have hbound := abs_listQSum_le_listQSum_of_pointwise_local
    (finePacketLocalizedConnectedTargetGradientPairTerm K M first second)
    (fun pair =>
      finePacketLocalizedResponsePairEnvelope S first second pair * (2 : Q'))
    (finePacketFaceResponseConnectedActivePairs
      S first second M.coarseTarget)
    (fun pair _ =>
      localizedConnectedTargetGradientPairTerm_abs_le_two_envelope
        K M first second pair)
  exact Q'.le_trans' _ _ _ hbound
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (listQSum_mul_right
        (finePacketLocalizedResponsePairEnvelope S first second)
        (2 : Q')
        (finePacketFaceResponseConnectedActivePairs
          S first second M.coarseTarget))
      (Q'.mul_comm_eqv _ _)))

/-! ## 3. Preserve the common factor two in the combined estimate -/

theorem connectedGradientConnectedPairSums_abs_le_two_envelopeSums
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling) :
    Q'.abs
        (listQSum
            (finePacketLocalizedConnectedRootGradientPairTerm
              K M first second)
            (finePacketFaceResponseConnectedActivePairs
              S first second M.coarseRoot) +
          listQSum
            (finePacketLocalizedConnectedTargetGradientPairTerm
              K M first second)
            (finePacketFaceResponseConnectedActivePairs
              S first second M.coarseTarget)) ≤
      (2 : Q') *
        (listQSum
            (finePacketLocalizedResponsePairEnvelope S first second)
            (finePacketFaceResponseConnectedActivePairs
              S first second M.coarseRoot) +
          listQSum
            (finePacketLocalizedResponsePairEnvelope S first second)
            (finePacketFaceResponseConnectedActivePairs
              S first second M.coarseTarget)) := by
  let rootSum := listQSum
    (finePacketLocalizedConnectedRootGradientPairTerm K M first second)
    (finePacketFaceResponseConnectedActivePairs S first second M.coarseRoot)
  let targetSum := listQSum
    (finePacketLocalizedConnectedTargetGradientPairTerm K M first second)
    (finePacketFaceResponseConnectedActivePairs S first second M.coarseTarget)
  let rootEnvelope := listQSum
    (finePacketLocalizedResponsePairEnvelope S first second)
    (finePacketFaceResponseConnectedActivePairs S first second M.coarseRoot)
  let targetEnvelope := listQSum
    (finePacketLocalizedResponsePairEnvelope S first second)
    (finePacketFaceResponseConnectedActivePairs S first second M.coarseTarget)
  have htriangle := abs_add_le rootSum targetSum
  have hroot : Q'.abs rootSum ≤ (2 : Q') * rootEnvelope :=
    connectedRootGradientConnectedPairSum_abs_le_two_envelopeSum
      K M first second
  have htarget : Q'.abs targetSum ≤ (2 : Q') * targetEnvelope :=
    connectedTargetGradientConnectedPairSum_abs_le_two_envelopeSum
      K M first second
  refine Q'.le_trans' _ _ _ htriangle ?_
  refine Q'.le_trans' _
    ((2 : Q') * rootEnvelope + (2 : Q') * targetEnvelope) _
    (Q'.add_le_add hroot htarget) ?_
  exact Q'.le_of_eqv
    (Q'.eqv_symm (Q'.mul_add_eqv (2 : Q') rootEnvelope targetEnvelope))

theorem connectedGradientActivePairSums_abs_le_two_envelopeSums
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling) :
    Q'.abs
        (listQSum
            (finePacketLocalizedConnectedRootGradientPairTerm
              K M first second)
            (finePacketLocalizedResponseActivePairs S first second
              (slabPhysicalFacePositiveB M.coarseRoot)) +
          listQSum
            (finePacketLocalizedConnectedTargetGradientPairTerm
              K M first second)
            (finePacketLocalizedResponseActivePairs S first second
              (slabPhysicalFacePositiveB M.coarseTarget))) ≤
      (2 : Q') *
        (listQSum
            (finePacketLocalizedResponsePairEnvelope S first second)
            (finePacketFaceResponseConnectedActivePairs
              S first second M.coarseRoot) +
          listQSum
            (finePacketLocalizedResponsePairEnvelope S first second)
            (finePacketFaceResponseConnectedActivePairs
              S first second M.coarseTarget)) := by
  have heq := Q'.add_eqv_congr'
    (connectedRootGradientActivePairSum_eqv_connected K M first second)
    (connectedTargetGradientActivePairSum_eqv_connected K M first second)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (abs_eqv_congr heq))
    (connectedGradientConnectedPairSums_abs_le_two_envelopeSums
      K M first second)

/-! ## 4. Axiom audit -/

#print axioms localizedConnectedRootGradientPairTerm_abs_le_two_envelope
#print axioms localizedConnectedTargetGradientPairTerm_abs_le_two_envelope
#print axioms connectedRootGradientConnectedPairSum_abs_le_two_envelopeSum
#print axioms connectedTargetGradientConnectedPairSum_abs_le_two_envelopeSum
#print axioms connectedGradientConnectedPairSums_abs_le_two_envelopeSums
#print axioms connectedGradientActivePairSums_abs_le_two_envelopeSums

end YMGap.Continuum.Z4DyadicBinaryConnectedObservableGradientEnvelope
