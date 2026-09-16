/-
# Normalized two-probe decay for an arbitrary selected original action

The existing signed connected-numerator estimate applies to every physical
duplicate-free face list. Its SAME original partition square cancels against
the exact finite covariance. No reciprocal ceiling enters the amplitude.
The bound also passes to the existing cutoff-removed face-set covariance.

The rate is 625*adjustedCoreRate(w), with explicit small-nome guards. The
exponent is the natural-number difference rootDistance+1-totalProbeSize.
The amplitude depends only on the nome, observable caps and carrier sizes
and link counts, not on the selected action's size or representation cutoff.
Concrete reflected placement, thermodynamic transport, physical operator
decay and continuum scaling are not claimed by this generic consumer.
-/

import YMGap.Continuum.BF4ExactSlabConnectedFaceResponse

namespace YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance

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
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
open YMGap.Continuum.BF4ExactSlabTwoProbeTailBudget
open YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.SepLatticeZ4Linf (linfDist)

local infix:50 " ≈ " => Q'.eqv

/-- Coefficient congruence preserves the SAME normalized cutoff moment. -/
theorem finiteValue_coeff_congr (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (p q : RatPoly) (he : RatPolyCoeffEqv p q) (stage : Nat) :
    finiteValue w hw0 hw1 extent ids hi p stage ≈
      finiteValue w hw0 hw1 extent ids hi q stage := by
  unfold finiteValue numerator
  exact Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff_eqv _ (he.mul_right _))

/-- Existing constants, displayed as an amplitude times the geometric rate.
The size loss is truncated natural subtraction, including coincident roots. -/
theorem distanceBudget_factor {left right : List Z4Link}
    (P : ProbeCarrier left) (Q : ProbeCarrier right) (w : Q')
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (c d : Q') :
    distanceBudget P Q w hd hs c d ≈
      ((((c*d+c*d)*probePrefactor w hd (left++right).length) *
        Q'.ofNat (countPrefactor P Q)) *
        Q'.recipPos (1 + -entropyRate 625 (adjustedCoreRate w hd)) (HKPos.one_sub_pos hs)) *
      (entropyRate 625 (adjustedCoreRate w hd))^
        (linfDist P.animal.root Q.animal.root+1-totalProbeSize P Q) := by
  unfold distanceBudget twoProbeBudget tailBudget minimumCoreSize
  exact poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.var 3)))
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.var 2)) (by decide)
    (fun
      | 0 => (c*d+c*d)*probePrefactor w hd (left++right).length
      | 1 => Q'.ofNat (countPrefactor P Q)
      | 2 => (entropyRate 625 (adjustedCoreRate w hd))^
          (linfDist P.animal.root Q.animal.root+1-totalProbeSize P Q)
      | _ => Q'.recipPos (1 + -entropyRate 625 (adjustedCoreRate w hd)) (HKPos.one_sub_pos hs))

/-- The actual selected-action covariance at cutoff headCutoff(w)+stage.
Both supplied locality and interval witnesses concern the actual p and q. -/
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
      distanceBudget P Q w hd hs c d := by
  have hz : (0 : Q') < partitionSample w extent ids stage :=
    Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
      (partitionSample_floor w hw0 hw1 extent ids hi stage)
  have hzz := Q'.mul_pos hz hz
  have he := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (TsumDeriv.abs_mul_nonneg_right _ (Q'.le_of_lt hzz)))
    (Q'.abs_eqv_congr (finite_covariance_cleared w hw0 hw1 extent ids hi p q stage))
  have h := connectedNumerator_distance_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
    hsmall hd hs (headCutoff w+stage) extent p q c d Ip Iq left right P Q hl hr ids hn hi
  apply Q'.le_of_mul_le_mul_left
    (c := partitionSample w extent ids stage * partitionSample w extent ids stage) _ hzz
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))))

/-- The same amplitude bounds the existing cutoff-removed selected-action
covariance. The action, two observables and carriers stay fixed in this limit. -/
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
      (ofQ' (distanceBudget P Q w hd hs c d)) := by
  have hc : ConvergesTo
      (fun stage => ofQ' (Q'.abs (finiteCovariance w hw0 hw1 extent ids hi p q stage)))
      (CReal.abs (covariance w hw0 hw1 extent ids hi p q)) := by
    refine TrigAddCReal.convergesTo_congr_seq ?_
      (convergesTo_abs (finite_covariance_converges w hw0 hw1 extent ids hi p q))
    intro stage
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  apply leEv_of_ofQ'_limit_le hc (convergesTo_const (ofQ' (distanceBudget P Q w hd hs c d)))
  intro epsilon he
  refine ⟨0, fun stage _ => ?_⟩
  exact Q'.le_trans' _ _ _
    (finite_covariance_distance_bound hw0 hw1 hsmall hd hs extent ids hn hi
      p q c d Ip Iq left right P Q hl hr stage)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))

end YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance

#print axioms YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance.finiteValue_coeff_congr
#print axioms YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance.distanceBudget_factor
#print axioms YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance.finite_covariance_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance.covariance_distance_bound
