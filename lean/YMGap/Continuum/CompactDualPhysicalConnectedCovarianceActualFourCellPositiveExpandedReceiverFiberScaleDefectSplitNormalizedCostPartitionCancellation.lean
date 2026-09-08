/-
# Cancel the common physical-partition factor in the split density cost

The five split-sector density budgets all carry the same coarse--fine
physical-partition factor.  The covariance denominator contains three copies
of each partition.  This module cancels one coarse and one fine copy exactly,
leaving the dimensionless analytic cost with only the squared coarse and fine
partitions in its denominator.

Thus the connected matched-AF input can be stated directly for the unscaled
sum of the five literal budgets.  No estimate on that sum is supplied here.
In particular, this module proves no uniform normalized-cost bound, physical
gap floor, continuum measure, OS/GNS reconstruction, Hamiltonian gap, or Clay
conclusion.

Constructive contract: exact rational identities and positivity only; no
choice, `Classical`, `native_decide`, `sorry`, noncomputable declaration, or
new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCost

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostPartitionCancellation

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransportCalibration
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Int.mul_one];
             ac_rfl))

private theorem divPos_eqv_of_eqv_mul_local {p q c : Q'}
    (hq : (0 : Q') < q) (h : p ≈ c * q) :
    Q'.divPos p q hq ≈ c := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv c q (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _ (Q'.mul_recipPos_eqv q hq)) ?_
  exact Q'.mul_one_eqv c

private theorem divPos_eqv_divPos_of_cross_local
    {p q p' q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : p * q' ≈ p' * q) :
    Q'.divPos p q hq ≈ Q'.divPos p' q' hq' := by
  let c := Q'.divPos p' q' hq'
  have hright : (c * q) * q' ≈ p' * q := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c q q') ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left c _ _ (Q'.mul_comm_eqv q q')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv c q' q)) ?_
    exact Q'.mul_eqv_congr_right _ _ q
      (Q'.divPos_mul_eqv p' q' hq')
  have hmul : p * q' ≈ (c * q) * q' :=
    Q'.eqv_trans _ _ _ hcross (Q'.eqv_symm hright)
  have hcancel : p ≈ c * q := by
    apply Q'.mul_left_cancel_of_pos hq'
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q' p) ?_
    refine Q'.eqv_trans _ _ _ hmul ?_
    exact Q'.mul_comm_eqv (c * q) q'
  exact divPos_eqv_of_eqv_mul_local hq hcancel

private theorem fiveScaledTerms_eqv_factor_mul_sum
    (factor first second third fourth fifth : Q') :
    (((factor * first + factor * second) + factor * third) +
        (factor * fourth + factor * fifth)) ≈
      factor * (((first + second) + third) + (fourth + fifth)) := by
  apply Q'.eqv_symm
  refine Q'.eqv_trans _
    (factor * ((first + second) + third) +
      factor * (fourth + fifth)) _
    (Q'.mul_add_eqv factor ((first + second) + third)
      (fourth + fifth)) ?_
  exact Q'.add_eqv_congr'
    (Q'.eqv_trans _
      (factor * (first + second) + factor * third) _
      (Q'.mul_add_eqv factor (first + second) third)
      (Q'.add_eqv_congr_right _ _ _
        (Q'.mul_add_eqv factor first second)))
    (Q'.mul_add_eqv factor fourth fifth)

/-! ## 1. Remove the common numerator factor -/

/-- The literal sum of the five surviving density/calibration budgets before
multiplication by the common coarse--fine physical-partition factor. -/
def actualPositiveExpandedReceiverFiberScaleDefectUnscaledSplitDensityBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  let S := schedule.scalePair scale
  let root := (schedule.faceMap scale).coarseRoot
  let target := (schedule.faceMap scale).coarseTarget
  let htarget := (schedule.faceMap scale).coarseTarget_mem
  ((actualPositiveExpandedReceiverFiberScaleDefectConnectedRowCalibrationL1
          S rfl (schedule.effectiveCoupling_pos scale)
          root target htarget +
        actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDensityVariationL1
          S rfl (schedule.effectiveCoupling_pos scale)
          root target htarget) +
      actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnCalibrationL1
        S rfl (schedule.effectiveCoupling_pos scale)
        root target htarget) +
    (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDensityVariationL1
        S rfl (schedule.effectiveCoupling_pos scale)
        root target htarget +
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnCalibrationL1
        S rfl (schedule.effectiveCoupling_pos scale)
        root target htarget)

theorem physicalPartitionProduct_pos
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    (0 : Q') <
      (schedule.scalePair scale).coarse.physicalPartition *
        (schedule.scalePair scale).fine.physicalPartition :=
  Q'.mul_pos
    (slabParametricKPhysicalPartition_pos
      (schedule.scalePair scale).coarse.coupling_nonnegative
      (schedule.scalePair scale).coarse.cutoff
      (schedule.scalePair scale).coarse.extent)
    (slabParametricKPhysicalPartition_pos
      (schedule.scalePair scale).fine.coupling_nonnegative
      (schedule.scalePair scale).fine.cutoff
      (schedule.scalePair scale).fine.extent)

theorem actualPositiveExpandedReceiverFiberScaleDefectSplitDensityBudget_eqv_partitionProduct_mul_unscaled
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectSplitDensityBudget
        schedule scale ≈
      ((schedule.scalePair scale).coarse.physicalPartition *
          (schedule.scalePair scale).fine.physicalPartition) *
        actualPositiveExpandedReceiverFiberScaleDefectUnscaledSplitDensityBudget
          schedule scale := by
  have hnonnegative :
      (0 : Q') ≤
        (schedule.scalePair scale).coarse.physicalPartition *
          (schedule.scalePair scale).fine.physicalPartition :=
    Q'.le_of_lt (physicalPartitionProduct_pos schedule scale)
  have habs :
      Q'.abs
          ((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) =
        (schedule.scalePair scale).coarse.physicalPartition *
          (schedule.scalePair scale).fine.physicalPartition := by
    unfold Q'.abs
    rw [if_pos hnonnegative]
  dsimp only [
    actualPositiveExpandedReceiverFiberScaleDefectSplitDensityBudget,
    actualPositiveExpandedReceiverFiberScaleDefectUnscaledSplitDensityBudget]
  rw [habs]
  exact fiveScaledTerms_eqv_factor_mul_sum _ _ _ _ _ _

/-! ## 2. Cancel one coarse and one fine partition copy -/

/-- The two remaining copies of each physical partition after cancellation of
one coarse and one fine copy from the cubic covariance denominator. -/
def partitionCancelledCovarianceDenominator (S : SlabScalePair) : Q' :=
  (S.coarse.physicalPartition * S.coarse.physicalPartition) *
    (S.fine.physicalPartition * S.fine.physicalPartition)

theorem partitionCancelledCovarianceDenominator_pos (S : SlabScalePair) :
    (0 : Q') < partitionCancelledCovarianceDenominator S := by
  exact Q'.mul_pos
    (Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)
      (slabParametricKPhysicalPartition_pos
        S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent))
    (Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent))

/-- The covariance normalization remaining after removal of the common
coarse--fine partition product. -/
def partitionCancelledSplitDensityDenominator
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  schedule.spacing.spacing scale *
    partitionCancelledCovarianceDenominator (schedule.scalePair scale)

theorem partitionCancelledSplitDensityDenominator_pos
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    (0 : Q') < partitionCancelledSplitDensityDenominator schedule scale := by
  exact Q'.mul_pos (schedule.spacing.spacing_pos scale)
    (partitionCancelledCovarianceDenominator_pos
      (schedule.scalePair scale))

theorem splitDensityNormalizationDenominator_eqv_partitionProduct_mul_cancelled
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    schedule.spacing.spacing scale *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale) ≈
      ((schedule.scalePair scale).coarse.physicalPartition *
          (schedule.scalePair scale).fine.physicalPartition) *
        partitionCancelledSplitDensityDenominator schedule scale := by
  unfold connectedCovarianceRawCrossDenominator rawCovarianceDenominator
    partitionCancelledSplitDensityDenominator
    partitionCancelledCovarianceDenominator
  ring_qeqv

/-- The sharp dimensionless split-density cost after exact cancellation of
the common coarse--fine physical-partition product. -/
def actualPositiveExpandedReceiverFiberScaleDefectPartitionCancelledSplitDensityNormalizedCost
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  Q'.divPos
    (actualPositiveExpandedReceiverFiberScaleDefectUnscaledSplitDensityBudget
      schedule scale)
    (partitionCancelledSplitDensityDenominator schedule scale)
    (partitionCancelledSplitDensityDenominator_pos schedule scale)

theorem actualPositiveExpandedReceiverFiberScaleDefectSplitDensityNormalizedCost_eqv_partitionCancelled
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectSplitDensityNormalizedCost
        schedule scale ≈
      actualPositiveExpandedReceiverFiberScaleDefectPartitionCancelledSplitDensityNormalizedCost
        schedule scale := by
  unfold actualPositiveExpandedReceiverFiberScaleDefectSplitDensityNormalizedCost
    actualPositiveExpandedReceiverFiberScaleDefectPartitionCancelledSplitDensityNormalizedCost
  refine divPos_eqv_divPos_of_cross_local
    (splitDensityNormalizationDenominator_pos schedule scale)
    (partitionCancelledSplitDensityDenominator_pos schedule scale) ?_
  let factor :=
      (schedule.scalePair scale).coarse.physicalPartition *
        (schedule.scalePair scale).fine.physicalPartition
  let unscaled :=
    actualPositiveExpandedReceiverFiberScaleDefectUnscaledSplitDensityBudget
      schedule scale
  let cancelled := partitionCancelledSplitDensityDenominator schedule scale
  have hbudget :
      actualPositiveExpandedReceiverFiberScaleDefectSplitDensityBudget
          schedule scale ≈ factor * unscaled := by
    simpa only [factor, unscaled] using
      actualPositiveExpandedReceiverFiberScaleDefectSplitDensityBudget_eqv_partitionProduct_mul_unscaled
        schedule scale
  have hdenominator :
      schedule.spacing.spacing scale *
          connectedCovarianceRawCrossDenominator
            (schedule.scalePair scale) ≈
        factor * cancelled := by
    simpa only [factor, cancelled] using
      splitDensityNormalizationDenominator_eqv_partitionProduct_mul_cancelled
        schedule scale
  refine Q'.eqv_trans _ ((factor * unscaled) * cancelled) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ cancelled hbudget
  · refine Q'.eqv_trans _ (unscaled * (factor * cancelled)) _ ?_ ?_
    · refine Q'.eqv_trans _ (factor * (unscaled * cancelled)) _
        (Q'.mul_assoc_eqv factor unscaled cancelled) ?_
      refine Q'.eqv_trans _ ((unscaled * cancelled) * factor) _
        (Q'.mul_comm_eqv factor (unscaled * cancelled)) ?_
      refine Q'.eqv_trans _ (unscaled * (cancelled * factor)) _
        (Q'.mul_assoc_eqv unscaled cancelled factor) ?_
      exact Q'.mul_eqv_congr_left unscaled _ _
        (Q'.mul_comm_eqv cancelled factor)
    · exact Q'.mul_eqv_congr_left unscaled _ _
        (Q'.eqv_symm hdenominator)

#print axioms actualPositiveExpandedReceiverFiberScaleDefectUnscaledSplitDensityBudget
#print axioms physicalPartitionProduct_pos
#print axioms actualPositiveExpandedReceiverFiberScaleDefectSplitDensityBudget_eqv_partitionProduct_mul_unscaled
#print axioms partitionCancelledCovarianceDenominator
#print axioms partitionCancelledCovarianceDenominator_pos
#print axioms partitionCancelledSplitDensityDenominator
#print axioms partitionCancelledSplitDensityDenominator_pos
#print axioms splitDensityNormalizationDenominator_eqv_partitionProduct_mul_cancelled
#print axioms actualPositiveExpandedReceiverFiberScaleDefectPartitionCancelledSplitDensityNormalizedCost
#print axioms actualPositiveExpandedReceiverFiberScaleDefectSplitDensityNormalizedCost_eqv_partitionCancelled

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostPartitionCancellation
