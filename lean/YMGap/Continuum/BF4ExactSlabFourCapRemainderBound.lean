/-
# Bound the original four-face remainder with every OWN detached square

The absolute original pair sum and the established short-collar comparison
give 2^-14*w^36*Z_full^2, at fixed SU(2) nome 1/1024 and every K, margin
and cut-filter time. No sign of a Haar coefficient is assumed. Six-or-more
spatial faces, positive full response and continuum/Clay remain open.
-/

import YMGap.Continuum.BF4ExactSlabFourCapPairSum

namespace YMGap.Continuum.BF4ExactSlabFourCapRemainderBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.BF4ExactSlabFourCapPairCount
open YMGap.Continuum.BF4ExactSlabFourCapPairSum
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

def fourCapRemainder (w : Q') (K margin time : Nat) : Q' :=
  branchRemainder w K margin time (fourCapKeep margin)

def fourCapAllowance : Q' := Q'.invSucc (2^14-1)*qpow nome 36

theorem fourCapAllowance_pos : (0 : Q') < fourCapAllowance := by decide

theorem original_fourCap_abs_le_pair_sum (K margin time : Nat) :
    Q'.abs (fourCapRemainder nome K margin time) ≤
      listQSum (fun pair => Q'.abs (weightedPairTerm nome K margin pair)) (fourCapPairs K margin time)*
        (2*partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))) := by
  have h := signedFamily_abs_bound (shortOtherCores 33 margin)
    (fun ids => (corePairs K margin time ids).filter (fourCapKeep margin))
    (weightedPairTerm nome K margin) (detachedSquare nome K margin)
    (2*partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)))
    (fun _ _ => SumOfSquares.q_mul_self_nonneg _)
    (fun _ hs => original_short_detached_square_le_two K margin hs)
  simpa only [fourCapPairs,shortPairs,List.filter_flatMap,corePairs] using h

theorem original_fourCap_remainder_bound (K margin time : Nat) :
    Q'.abs (fourCapRemainder nome K margin time) ≤
      fourCapAllowance*partitionSquare nome K (responseExtent margin)
        (slabPhysicalFaceEdges (responseExtent margin)) := by
  have hb := Q'.mul_le_mul_of_nonneg_right _ _
    (2*partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)))
    (original_fourCap_pair_sum_small K margin time)
    (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) (SumOfSquares.q_mul_self_nonneg _))
  have he (W Z : Q') : (Q'.invSucc (2^15-1)*W)*(2*Z) ≈ (Q'.invSucc (2^14-1)*W)*Z := by
    have h := poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.const 2) (.var 2)))
      (.mul (.mul (.mul (.var 0) (.const 2)) (.var 1)) (.var 2)) (by decide)
      (fun i => if i=0 then Q'.invSucc (2^15-1) else if i=1 then W else Z)
    exact Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_right _ _ Z
      (Q'.mul_eqv_congr_right _ _ W (by decide : Q'.invSucc (2^15-1)*2 ≈ Q'.invSucc (2^14-1))))
  exact Q'.le_trans' _ _ _ (original_fourCap_abs_le_pair_sum K margin time)
    (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (he _ _)))

end YMGap.Continuum.BF4ExactSlabFourCapRemainderBound

#print axioms YMGap.Continuum.BF4ExactSlabFourCapRemainderBound.fourCapRemainder
#print axioms YMGap.Continuum.BF4ExactSlabFourCapRemainderBound.fourCapAllowance
#print axioms YMGap.Continuum.BF4ExactSlabFourCapRemainderBound.fourCapAllowance_pos
#print axioms YMGap.Continuum.BF4ExactSlabFourCapRemainderBound.original_fourCap_abs_le_pair_sum
#print axioms YMGap.Continuum.BF4ExactSlabFourCapRemainderBound.original_fourCap_remainder_bound
