/-
# The whole original remaining two-cap remainder is small

Restore each short core's OWN detached partition square after the actual
pair-weight sum. The established short-collar comparison costs at most
two, independently of cutoff and margin. At unchanged nome 1/1024 this
gives |twoCapRemainder| <= 2^-14*w^36*Z_full^2.
This does not bound spatial families with four or more odd faces.
-/

import YMGap.Continuum.BF4ExactSlabTwoCapPairSum

namespace YMGap.Continuum.BF4ExactSlabTwoCapRemainderBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.BF4ExactSlabTwoCapPairCount
open YMGap.Continuum.BF4ExactSlabTwoCapPairSum
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit
open YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount (shortPairs)
open YMGap.Continuum.BF4ExactSlabZeroSpatialRemainderBound
open YMGap.Continuum.BF4ExactSlabShortDetachedPartition
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

def twoCapRemainder (w : Q') (K margin time : Nat) : Q' :=
  branchRemainder w K margin time (twoCapKeep margin)

def twoCapAllowance : Q' := Q'.invSucc (2^14-1)*qpow nome 36

theorem twoCapAllowance_pos : (0 : Q') < twoCapAllowance := by decide

theorem original_twoCap_abs_le_pair_sum (K margin time : Nat) :
    Q'.abs (twoCapRemainder nome K margin time) ≤
      listQSum (fun pair => Q'.abs (weightedPairTerm nome K margin pair)) (twoCapPairs K margin time)*
        (2*partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))) := by
  have h := signedFamily_abs_bound (shortOtherCores 33 margin)
    (fun ids => (corePairs K margin time ids).filter (twoCapKeep margin))
    (weightedPairTerm nome K margin) (detachedSquare nome K margin)
    (2*partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)))
    (fun _ _ => SumOfSquares.q_mul_self_nonneg _)
    (fun _ hs => original_short_detached_square_le_two K margin hs)
  simpa only [twoCapPairs,shortPairs,List.filter_flatMap,corePairs] using h

/-- All original cutoffs, margins and cut-filter times; fixed SU(2) nome, OWN detached squares. -/
theorem original_twoCap_remainder_bound (K margin time : Nat) :
    Q'.abs (twoCapRemainder nome K margin time) ≤
      twoCapAllowance*partitionSquare nome K (responseExtent margin)
        (slabPhysicalFaceEdges (responseExtent margin)) := by
  have hb := Q'.mul_le_mul_of_nonneg_right _ _
    (2*partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)))
    (original_twoCap_pair_sum_small K margin time)
    (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) (SumOfSquares.q_mul_self_nonneg _))
  have he (W Z : Q') : (Q'.invSucc (2^15-1)*W)*(2*Z) ≈ (Q'.invSucc (2^14-1)*W)*Z := by
    have h := poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.const 2) (.var 2)))
      (.mul (.mul (.mul (.var 0) (.const 2)) (.var 1)) (.var 2)) (by decide)
      (fun i => if i=0 then Q'.invSucc (2^15-1) else if i=1 then W else Z)
    exact Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_right _ _ Z
      (Q'.mul_eqv_congr_right _ _ W (by decide : Q'.invSucc (2^15-1)*2 ≈ Q'.invSucc (2^14-1))))
  exact Q'.le_trans' _ _ _ (original_twoCap_abs_le_pair_sum K margin time)
    (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (he _ _)))

end YMGap.Continuum.BF4ExactSlabTwoCapRemainderBound

#print axioms YMGap.Continuum.BF4ExactSlabTwoCapRemainderBound.twoCapRemainder
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapRemainderBound.twoCapAllowance
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapRemainderBound.twoCapAllowance_pos
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapRemainderBound.original_twoCap_abs_le_pair_sum
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapRemainderBound.original_twoCap_remainder_bound
