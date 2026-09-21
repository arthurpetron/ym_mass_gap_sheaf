/-
# Selected covariance using the descent-count spatial rate

This is the existing finite covariance adapter with the original 625-guard
specialized through the descent-coded 96-count estimate.  No completed
operator or continuum identification is asserted.
-/

import YMGap.Continuum.BF4ExactSlabDescentDistanceDecay
import YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance

namespace YMGap.Continuum.BF4ExactSlabDescentSelectedCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (ProbeCarrier)
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount (totalProbeSize)
open YMGap.Continuum.BF4ExactSlabDescentCoreCount (countPrefactor)
open YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay (minimumCoreSize)
open YMGap.Continuum.SepLatticeZ4Linf (linfDist)
open YMGap.Continuum.BF4ExactSlabDescentDistanceDecay
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem oldGuardBudget_factor {left right : List Z4Link}
    (P : ProbeCarrier left) (Q : ProbeCarrier right) (w : Q')
    (hd : heatRemainderBound w < 1) (c d : Q') :
    oldGuardBudget P Q w hd c d ≈
      ((((c*d+c*d)*probePrefactor w hd (left++right).length) *
        Q'.ofNat (countPrefactor P Q)) *
        Q'.recipPos (1 + -entropyRate 96 comparisonCoreRate)
          (HKPos.one_sub_pos comparison_guard)) *
      (entropyRate 96 comparisonCoreRate)^(linfDist P.animal.root Q.animal.root+1-
        totalProbeSize P Q) := by
  unfold oldGuardBudget tailBudget minimumCoreSize
  exact poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.var 2)) (by decide)
    (fun
      | 0 => (c*d+c*d)*probePrefactor w hd (left++right).length
      | 1 => Q'.ofNat (countPrefactor P Q)
      | 2 => (entropyRate 96 comparisonCoreRate)^(linfDist P.animal.root Q.animal.root+1-totalProbeSize P Q)
      | _ => Q'.recipPos (1 + -entropyRate 96 comparisonCoreRate)
        (HKPos.one_sub_pos comparison_guard))

theorem finite_covariance_distance_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (extent : Nat) (ids : List Nat) (hn : ids.Nodup)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (p q : RatPoly) (c d : Q')
    (Ip : Interval (boundaryCompleteSlabLinks extent).length p c)
    (Iq : Interval (boundaryCompleteSlabLinks extent).length q d)
    (left right : List Z4Link) (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q) (stage : Nat) :
    Q'.abs (finiteCovariance w hw0 hw1 extent ids hi p q stage) ≤
      oldGuardBudget P Q w hd c d := by
  have hz : (0 : Q') < partitionSample w extent ids stage :=
    Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
      (partitionSample_floor w hw0 hw1 extent ids hi stage)
  have hzz := Q'.mul_pos hz hz
  have he := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (TsumDeriv.abs_mul_nonneg_right _ (Q'.le_of_lt hzz)))
    (Q'.abs_eqv_congr (finite_covariance_cleared w hw0 hw1 extent ids hi p q stage))
  have h := oldGuard_distance_bound (W := w)
    (fun _ => w) (fun _ => headCutoff w + stage) extent
    (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
    (fun _ _ => Q'.le_of_lt hw0) (fun _ _ => Q'.le_refl' _)
    hsmall hd hs p q c d Ip Iq left right P Q hl hr ids hn hi
  apply Q'.le_of_mul_le_mul_left
    (c := partitionSample w extent ids stage * partitionSample w extent ids stage) _ hzz
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))))

theorem covariance_distance_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (extent : Nat) (ids : List Nat) (hn : ids.Nodup)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (p q : RatPoly) (c d : Q')
    (Ip : Interval (boundaryCompleteSlabLinks extent).length p c)
    (Iq : Interval (boundaryCompleteSlabLinks extent).length q d)
    (left right : List Z4Link) (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q) :
    leEv (CReal.abs (covariance w hw0 hw1 extent ids hi p q))
      (ofQ' (oldGuardBudget P Q w hd c d)) := by
  have hc : ConvergesTo
      (fun stage => ofQ' (Q'.abs (finiteCovariance w hw0 hw1 extent ids hi p q stage)))
      (CReal.abs (covariance w hw0 hw1 extent ids hi p q)) := by
    refine TrigAddCReal.convergesTo_congr_seq ?_
      (convergesTo_abs (finite_covariance_converges w hw0 hw1 extent ids hi p q))
    intro stage
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  apply leEv_of_ofQ'_limit_le hc (convergesTo_const (ofQ' (oldGuardBudget P Q w hd c d)))
  intro epsilon he
  refine ⟨0, fun stage _ => ?_⟩
  exact Q'.le_trans' _ _ _
    (finite_covariance_distance_bound hw0 hw1 hsmall hd hs extent ids hn hi
      p q c d Ip Iq left right P Q hl hr stage)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))

end YMGap.Continuum.BF4ExactSlabDescentSelectedCovariance

#print axioms YMGap.Continuum.BF4ExactSlabDescentSelectedCovariance.oldGuardBudget_factor
#print axioms YMGap.Continuum.BF4ExactSlabDescentSelectedCovariance.finite_covariance_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabDescentSelectedCovariance.covariance_distance_bound
