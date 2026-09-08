/-
# Fully raw covariance cross for the connected physical remainder

The structured-observable cross still contains normalized face moments in its
observable coefficients.  This module clears those coefficients as well.  It
expresses the blocked and coarse Boolean covariances as quotients of literal
raw event numerators, then cross-multiplies their difference.

The final numerator contains only raw pushed event sums, raw coarse event
sums, and the two physical partitions.  A relative bound on this fully raw
covariance cross is sufficient for the connected `O(a)` producer.  No such
bound is inhabited here.

Constructive contract: finite rational sums and explicit positive-denominator
algebra only; no choice, `Classical`, `native_decide`, `sorry`, noncomputable
declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedObservableRawCross

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedObservableRawCross
open YMGap.Continuum.CompactDualPhysicalRemainderLocality
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem divPos_eqv_of_eqv_mul_local {p q c : Q'}
    (hq : (0 : Q') < q) (h : p ≈ c * q) :
    Q'.divPos p q hq ≈ c := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv c q (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _
      (Q'.mul_recipPos_eqv q hq)) ?_
  exact Q'.mul_one_eqv c

/-! ## 1. Literal raw event numerators -/

def physicalEventNumerator
    (D : SlabPhysicalData) (event : SlabLabelling → Bool) : Q' :=
  physicalObservableNumerator D
    (weightedCylinderObservable event 1)

def pushedPhysicalEventNumerator
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : SlabLabelling → Bool) : Q' :=
  pushedPhysicalObservableNumerator K
    (weightedCylinderObservable event 1)

private theorem observableExpectation_indicator_eqv_eventMass
    (mass : SlabLabelling → Q') (states : List SlabLabelling)
    (event : SlabLabelling → Bool) :
    observableExpectation mass states
        (weightedCylinderObservable event 1) ≈
      finiteEventMass mass states event := by
  unfold observableExpectation weightedCylinderObservable finiteEventMass
  exact listQSum_congr_on _ _ states
    (fun state _ => by
      cases hevent : event state
      · simp only [Bool.false_eq_true, if_false]
        exact Q'.mul_zero_eqv (mass state)
      · simp only [if_true]
        exact Q'.mul_one_eqv (mass state))

theorem normalizedEventMass_eqv_raw_divPos
    (D : SlabPhysicalData) (event : SlabLabelling → Bool) :
    normalizedSlabEventMass D event ≈
      Q'.divPos (physicalEventNumerator D event)
        D.physicalPartition
        (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent) := by
  refine Q'.eqv_trans _
    (observableExpectation D.normalizedMass D.physicalLabellings
      (weightedCylinderObservable event 1)) _ ?_ ?_
  · exact Q'.eqv_symm
      (observableExpectation_indicator_eqv_eventMass
        D.normalizedMass D.physicalLabellings event)
  exact normalizedObservableExpectation_eqv_raw_divPos D
    (weightedCylinderObservable event 1)

theorem blockedEventMass_eqv_pushedRaw_divPos
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : SlabLabelling → Bool) :
    PhysicalKernel.blockedCylinderMass K event ≈
      Q'.divPos (pushedPhysicalEventNumerator K event)
        S.fine.physicalPartition
        (slabParametricKPhysicalPartition_pos
          S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent) := by
  refine Q'.eqv_trans _
    (observableExpectation K.blockedMass S.coarse.physicalLabellings
      (weightedCylinderObservable event 1)) _ ?_ ?_
  · exact Q'.eqv_symm
      (observableExpectation_indicator_eqv_eventMass
        K.blockedMass S.coarse.physicalLabellings event)
  exact blockedObservableExpectation_eqv_pushedRaw_divPos K
    (weightedCylinderObservable event 1)

/-! ## 2. Raw covariance numerators -/

/-- Cubic raw numerator for a covariance.  The redundant partition factor
keeps the quotient proof completely cancellation-free. -/
def rawCovarianceNumerator
    (joint root target partition : Q') : Q' :=
  joint * (partition * partition) -
    (root * target) * partition

def rawCovarianceDenominator (partition : Q') : Q' :=
  partition * (partition * partition)

private theorem mul_divPos_same_denominator_eqv
    (root target partition : Q')
    (hpartition : (0 : Q') < partition) :
    Q'.divPos root partition hpartition *
        Q'.divPos target partition hpartition ≈
      Q'.divPos (root * target) (partition * partition)
        (Q'.mul_pos hpartition hpartition) := by
  apply Q'.eqv_symm
  apply divPos_eqv_of_eqv_mul_local
  let rootRatio := Q'.divPos root partition hpartition
  let targetRatio := Q'.divPos target partition hpartition
  refine Q'.eqv_trans _
    ((rootRatio * partition) * (targetRatio * partition)) _ ?_ ?_
  · exact Q'.eqv_symm
      (mul_eqv_both_local
        (Q'.divPos_mul_eqv root partition hpartition)
        (Q'.divPos_mul_eqv target partition hpartition))
  unfold rootRatio targetRatio
  ring_qeqv

private theorem covariance_of_ratio_moments_eqv_raw
    (jointMoment rootMoment targetMoment
      jointNumerator rootNumerator targetNumerator partition : Q')
    (hpartition : (0 : Q') < partition)
    (hjoint : jointMoment ≈
      Q'.divPos jointNumerator partition hpartition)
    (hroot : rootMoment ≈
      Q'.divPos rootNumerator partition hpartition)
    (htarget : targetMoment ≈
      Q'.divPos targetNumerator partition hpartition) :
    jointMoment - rootMoment * targetMoment ≈
      Q'.divPos
        (rawCovarianceNumerator jointNumerator rootNumerator
          targetNumerator partition)
        (rawCovarianceDenominator partition)
        (Q'.mul_pos hpartition (Q'.mul_pos hpartition hpartition)) := by
  have hproduct :
      rootMoment * targetMoment ≈
        Q'.divPos (rootNumerator * targetNumerator)
          (partition * partition)
          (Q'.mul_pos hpartition hpartition) :=
    Q'.eqv_trans _ _ _
      (mul_eqv_both_local hroot htarget)
      (mul_divPos_same_denominator_eqv
        rootNumerator targetNumerator partition hpartition)
  refine Q'.eqv_trans _
    (Q'.divPos jointNumerator partition hpartition -
      Q'.divPos (rootNumerator * targetNumerator)
        (partition * partition)
        (Q'.mul_pos hpartition hpartition)) _ ?_ ?_
  · exact sub_eqv_both_local hjoint hproduct
  simpa only [rawCovarianceNumerator, rawCovarianceDenominator] using
    (divPos_sub_divPos_eq_crossDifference
      jointNumerator (rootNumerator * targetNumerator)
      partition (partition * partition)
      hpartition (Q'.mul_pos hpartition hpartition))

def coarseFaceRawCovarianceNumerator
    (D : SlabPhysicalData) (root target : Nat) : Q' :=
  rawCovarianceNumerator
    (physicalEventNumerator D
      (slabPhysicalFacePairPositiveB root target))
    (physicalEventNumerator D (slabPhysicalFacePositiveB root))
    (physicalEventNumerator D (slabPhysicalFacePositiveB target))
    D.physicalPartition

def pushedFaceRawCovarianceNumerator
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  rawCovarianceNumerator
    (pushedPhysicalEventNumerator K
      (slabPhysicalFacePairPositiveB root target))
    (pushedPhysicalEventNumerator K (slabPhysicalFacePositiveB root))
    (pushedPhysicalEventNumerator K (slabPhysicalFacePositiveB target))
    S.fine.physicalPartition

theorem normalizedFaceCovariance_eqv_raw_divPos
    (D : SlabPhysicalData) (root target : Nat) :
    normalizedSlabFaceBooleanCovariance D root target ≈
      Q'.divPos (coarseFaceRawCovarianceNumerator D root target)
        (rawCovarianceDenominator D.physicalPartition)
        (Q'.mul_pos
          (slabParametricKPhysicalPartition_pos
            D.coupling_nonnegative D.cutoff D.extent)
          (Q'.mul_pos
            (slabParametricKPhysicalPartition_pos
              D.coupling_nonnegative D.cutoff D.extent)
            (slabParametricKPhysicalPartition_pos
              D.coupling_nonnegative D.cutoff D.extent))) := by
  unfold normalizedSlabFaceBooleanCovariance
    coarseFaceRawCovarianceNumerator
  exact covariance_of_ratio_moments_eqv_raw _ _ _ _ _ _ _
    (slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent)
    (normalizedEventMass_eqv_raw_divPos D _)
    (normalizedEventMass_eqv_raw_divPos D _)
    (normalizedEventMass_eqv_raw_divPos D _)

theorem blockedFaceCovariance_eqv_raw_divPos
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    blockedSlabFaceBooleanCovariance K M ≈
      Q'.divPos
        (pushedFaceRawCovarianceNumerator K M.coarseRoot M.coarseTarget)
        (rawCovarianceDenominator S.fine.physicalPartition)
        (Q'.mul_pos
          (slabParametricKPhysicalPartition_pos
            S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
          (Q'.mul_pos
            (slabParametricKPhysicalPartition_pos
              S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
            (slabParametricKPhysicalPartition_pos
              S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent))) := by
  unfold blockedSlabFaceBooleanCovariance blockedFacePairMoment
    blockedFaceMoment pushedFaceRawCovarianceNumerator
  exact covariance_of_ratio_moments_eqv_raw _ _ _ _ _ _ _
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
    (blockedEventMass_eqv_pushedRaw_divPos K _)
    (blockedEventMass_eqv_pushedRaw_divPos K _)
    (blockedEventMass_eqv_pushedRaw_divPos K _)

/-! ## 3. Fully raw connected covariance cross -/

def connectedCovarianceRawCrossDefect
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) : Q' :=
  coarseFaceRawCovarianceNumerator
      S.coarse M.coarseRoot M.coarseTarget *
      rawCovarianceDenominator S.fine.physicalPartition -
    pushedFaceRawCovarianceNumerator
        K M.coarseRoot M.coarseTarget *
      rawCovarianceDenominator S.coarse.physicalPartition

def connectedCovarianceRawCrossDenominator (S : SlabScalePair) : Q' :=
  rawCovarianceDenominator S.coarse.physicalPartition *
    rawCovarianceDenominator S.fine.physicalPartition

theorem centeredCylinderRemainder_eqv_covarianceRawCross_divPos
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    centeredCylinderRemainder K M ≈
      Q'.divPos (connectedCovarianceRawCrossDefect K M)
        (connectedCovarianceRawCrossDenominator S)
        (Q'.mul_pos
          (Q'.mul_pos
            (slabParametricKPhysicalPartition_pos
              S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)
            (Q'.mul_pos
              (slabParametricKPhysicalPartition_pos
                S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)
              (slabParametricKPhysicalPartition_pos
                S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)))
          (Q'.mul_pos
            (slabParametricKPhysicalPartition_pos
              S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
            (Q'.mul_pos
              (slabParametricKPhysicalPartition_pos
                S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
              (slabParametricKPhysicalPartition_pos
                S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)))) := by
  let hcoarse := slabParametricKPhysicalPartition_pos
    S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent
  let hfine := slabParametricKPhysicalPartition_pos
    S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent
  let hcoarseCube := Q'.mul_pos hcoarse (Q'.mul_pos hcoarse hcoarse)
  let hfineCube := Q'.mul_pos hfine (Q'.mul_pos hfine hfine)
  refine Q'.eqv_trans _
    (normalizedSlabFaceBooleanCovariance
        S.coarse M.coarseRoot M.coarseTarget -
      blockedSlabFaceBooleanCovariance K M) _ ?_ ?_
  · exact Q'.eqv_symm
      (coarse_sub_blocked_covariance_eqv_centeredCylinderRemainder K M)
  refine Q'.eqv_trans _
    (Q'.divPos
        (coarseFaceRawCovarianceNumerator
          S.coarse M.coarseRoot M.coarseTarget)
        (rawCovarianceDenominator S.coarse.physicalPartition) hcoarseCube -
      Q'.divPos
        (pushedFaceRawCovarianceNumerator
          K M.coarseRoot M.coarseTarget)
        (rawCovarianceDenominator S.fine.physicalPartition) hfineCube) _ ?_ ?_
  · exact sub_eqv_both_local
      (normalizedFaceCovariance_eqv_raw_divPos
        S.coarse M.coarseRoot M.coarseTarget)
      (blockedFaceCovariance_eqv_raw_divPos K M)
  simpa only [connectedCovarianceRawCrossDefect,
      connectedCovarianceRawCrossDenominator] using
    (divPos_sub_divPos_eq_crossDifference
      (coarseFaceRawCovarianceNumerator
        S.coarse M.coarseRoot M.coarseTarget)
      (pushedFaceRawCovarianceNumerator
        K M.coarseRoot M.coarseTarget)
      (rawCovarianceDenominator S.coarse.physicalPartition)
      (rawCovarianceDenominator S.fine.physicalPartition)
      hcoarseCube hfineCube)

private theorem abs_divPos_le_of_abs_le_mul_local
    {numerator denominator budget : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hcross : Q'.abs numerator ≤ budget * denominator) :
    Q'.abs (Q'.divPos numerator denominator hdenominator) ≤ budget := by
  apply Q'.abs_le
  · apply Q'.le_divPos_of_mul_le
    have hnegCross := Q'.neg_le_neg hcross
    have hnegAbs : -(Q'.abs numerator) ≤ numerator := by
      have h := Q'.neg_le_neg (Q'.neg_le_abs numerator)
      exact Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.neg_neg_eqv numerator))
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.neg_mul_eqv budget denominator))
      (Q'.le_trans' _ _ _ hnegCross hnegAbs)
  · apply Q'.divPos_le_of_le_mul
    exact Q'.le_trans' _ _ _ (Q'.le_abs_self numerator) hcross

theorem centeredCylinderRemainder_abs_le_of_covarianceRawCross
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (budget : Q')
    (hcross : Q'.abs (connectedCovarianceRawCrossDefect K M) ≤
      budget * connectedCovarianceRawCrossDenominator S) :
    Q'.abs (centeredCylinderRemainder K M) ≤ budget := by
  let hcoarse := slabParametricKPhysicalPartition_pos
    S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent
  let hfine := slabParametricKPhysicalPartition_pos
    S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent
  let hdenominator := Q'.mul_pos
    (Q'.mul_pos hcoarse (Q'.mul_pos hcoarse hcoarse))
    (Q'.mul_pos hfine (Q'.mul_pos hfine hfine))
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (centeredCylinderRemainder_eqv_covarianceRawCross_divPos K M))) ?_
  exact abs_divPos_le_of_abs_le_mul_local hdenominator hcross

#print axioms physicalEventNumerator
#print axioms pushedPhysicalEventNumerator
#print axioms normalizedEventMass_eqv_raw_divPos
#print axioms blockedEventMass_eqv_pushedRaw_divPos
#print axioms rawCovarianceNumerator
#print axioms normalizedFaceCovariance_eqv_raw_divPos
#print axioms blockedFaceCovariance_eqv_raw_divPos
#print axioms connectedCovarianceRawCrossDefect
#print axioms centeredCylinderRemainder_eqv_covarianceRawCross_divPos
#print axioms centeredCylinderRemainder_abs_le_of_covarianceRawCross

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
