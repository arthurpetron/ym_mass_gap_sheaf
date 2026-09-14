/-
# Bound the entire original after-four-face remainder with OWN partitions

Deleting only zero pair terms gives the counted remainingPairs source.
The actual full remainder, including each core's own detached partition
square, is bounded by (1/8)*w^36*Z_full^2 at SU(2) nome 1/1024,
for every cutoff, margin and filter time. Neither signs nor cancellations
are replaced by a positive-model assumption.
-/

import YMGap.Continuum.BF4ExactSlabSpatialForestPairSum

namespace YMGap.Continuum.BF4ExactSlabSpatialForestRemainderBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.BF4ExactSlabSpatialForestPairCount
open YMGap.Continuum.BF4ExactSlabSpatialForestPairSum
open YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit
open YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount (shortPairs)
open YMGap.Continuum.BF4ExactSlabZeroSpatialRemainderBound (signedFamily_abs_bound)
open YMGap.Continuum.BF4ExactSlabShortDetachedPartition
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem remaining_filter_eq (margin : Nat) (xs : List (EdgeLabelling × EdgeLabelling)) :
    (xs.filter (afterFourCapKeep margin)).filter (fun pair => decide (¬pairTerm margin pair.1 pair.2 ≈ 0)) =
      xs.filter (remainingKeep margin) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro pair _
  simp only [remainingKeep,Bool.decide_and,Bool.decide_eq_true]

theorem afterFour_pair_sum_nonzero (w : Q') (K margin : Nat) (xs : List (EdgeLabelling × EdgeLabelling)) :
    listQSum (weightedPairTerm w K margin) (xs.filter (afterFourCapKeep margin)) ≈
      listQSum (weightedPairTerm w K margin) (xs.filter (remainingKeep margin)) := by
  have h := sum_filter_zero (weightedPairTerm w K margin)
    (fun pair => decide (¬pairTerm margin pair.1 pair.2 ≈ 0)) (xs.filter (afterFourCapKeep margin)) (by
      intro pair _ hf
      by_cases hz : pairTerm margin pair.1 pair.2 ≈ 0
      · exact weightedPairTerm_zero w K margin pair hz
      · exact False.elim ((of_decide_eq_false hf) hz))
  rw [remaining_filter_eq] at h
  exact h

theorem original_afterFour_remaining_eq (w : Q') (K margin time : Nat) :
    afterFourCapRemainder w K margin time ≈ branchRemainder w K margin time (remainingKeep margin) :=
  listQSum_congr_on _ _ _ (fun ids _ => Q'.mul_eqv_congr_right _ _ (detachedSquare w K margin ids)
    (afterFour_pair_sum_nonzero w K margin (corePairs K margin time ids)))

def remainingAllowance : Q' := Q'.invSucc 7*qpow nome 36

theorem remainingAllowance_pos : (0 : Q') < remainingAllowance := by decide

theorem original_remaining_abs_le_pair_sum (K margin time : Nat) :
    Q'.abs (afterFourCapRemainder nome K margin time) ≤
      listQSum (fun pair => Q'.abs (weightedPairTerm nome K margin pair)) (remainingPairs K margin time)*
        (2*partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))) := by
  have h := signedFamily_abs_bound (shortOtherCores 33 margin)
    (fun ids => (corePairs K margin time ids).filter (remainingKeep margin))
    (weightedPairTerm nome K margin) (detachedSquare nome K margin)
    (2*partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)))
    (fun _ _ => SumOfSquares.q_mul_self_nonneg _)
    (fun _ hs => original_short_detached_square_le_two K margin hs)
  apply Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (original_afterFour_remaining_eq nome K margin time)))
  simpa only [remainingPairs,shortPairs,List.filter_flatMap,corePairs] using h

theorem original_remaining_remainder_bound (K margin time : Nat) :
    Q'.abs (afterFourCapRemainder nome K margin time) ≤
      remainingAllowance*partitionSquare nome K (responseExtent margin)
        (slabPhysicalFaceEdges (responseExtent margin)) := by
  have hb := Q'.mul_le_mul_of_nonneg_right _ _
    (2*partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)))
    (original_remaining_pair_sum_small K margin time)
    (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) (SumOfSquares.q_mul_self_nonneg _))
  have he (W Z : Q') : (Q'.invSucc 15*W)*(2*Z) ≈ (Q'.invSucc 7*W)*Z := by
    have h := poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.const 2) (.var 2)))
      (.mul (.mul (.mul (.var 0) (.const 2)) (.var 1)) (.var 2)) (by decide)
      (fun i => if i=0 then Q'.invSucc 15 else if i=1 then W else Z)
    exact Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_right _ _ Z
      (Q'.mul_eqv_congr_right _ _ W (by decide : Q'.invSucc 15*2 ≈ Q'.invSucc 7)))
  exact Q'.le_trans' _ _ _ (original_remaining_abs_le_pair_sum K margin time)
    (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (he _ _)))

end YMGap.Continuum.BF4ExactSlabSpatialForestRemainderBound

#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestRemainderBound.remaining_filter_eq
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestRemainderBound.afterFour_pair_sum_nonzero
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestRemainderBound.original_afterFour_remaining_eq
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestRemainderBound.remainingAllowance
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestRemainderBound.remainingAllowance_pos
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestRemainderBound.original_remaining_abs_le_pair_sum
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestRemainderBound.original_remaining_remainder_bound
