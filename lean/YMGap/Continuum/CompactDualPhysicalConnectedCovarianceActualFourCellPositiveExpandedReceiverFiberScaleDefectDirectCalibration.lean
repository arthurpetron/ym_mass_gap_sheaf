/-
# Control the receiver scale defect directly by partition-density calibration

The conditional receiver-transport route compares source and target
coefficients through a shared-column posterior.  There is also a stronger but
posterior-free route: control both coefficient fields directly against the
same exact partition density `Z_fine^2 / Z_coarse^2`.

This module defines the literal finite source- and target-cell calibration
`l1` budgets.  Their sum bounds the complete receiver-fiber scale-defect cross,
and two separate linear-in-spacing hypotheses compile to the existing matched
covariance consumer.  No schedule-level posterior is required on this branch.

The direct calibration hypotheses can be stronger than a transport estimate
that uses cancellation between nearby receiver fibers.  No calibration bound,
refining-scale estimate, continuum measure, OS/GNS reconstruction,
Hamiltonian gap, or Clay conclusion is supplied here.

Constructive contract: positive rational division, finite exact identities,
inequalities, and Type-valued witnesses only; no choice, `Classical`,
`native_decide`, `sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration
import YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectDirectCalibration

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberDensity
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem abs_listQSum_le_sum_abs_local {A : Type}
    (value : A → Q') : ∀ items : List A,
      Q'.abs (listQSum value items) ≤
        listQSum (fun item => Q'.abs (value item)) items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.le_trans' _ _ _
        (Q'.abs_add_le' (value head) (listQSum value tail))
        (Q'.add_le_add
          (Q'.le_refl' (Q'.abs (value head)))
          (abs_listQSum_le_sum_abs_local value tail))

private theorem add_two_scaled_eqv
    (source target spacing denominator : Q') :
    (source * spacing) * denominator +
        (target * spacing) * denominator ≈
      ((source + target) * spacing) * denominator := by
  refine Q'.eqv_trans _
    ((source * spacing + target * spacing) * denominator) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.add_mul_eqv
        (source * spacing) (target * spacing) denominator)
  · exact Q'.mul_eqv_congr_right _ _ denominator
      (Q'.eqv_symm (Q'.add_mul_eqv source target spacing))

/-! ## 1. Literal source and target calibration budgets -/

/-- Weighted `l1` calibration budget on the complete source four-cell. -/
def actualPositiveExpandedReceiverFiberScaleDefectSourceCalibrationL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
    (fun receiver =>
      Q'.abs
        (((positiveExpandedReceiverFiberPartitionDensity S -
              positiveExpandedFourCellSourceReceiverFiberDensity
                S hfineCutoff hcoarseCoupling root target receiver) *
            (S.coarse.physicalPartition *
              S.coarse.physicalPartition)) *
          slabObservableTwoReplicaPairWeight S.coarse receiver))
    (slabObservableFourCellSourcePairs S.coarse root target)

/-- Weighted `l1` calibration budget on the complete target four-cell. -/
def actualPositiveExpandedReceiverFiberScaleDefectTargetCalibrationL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
    (fun receiver =>
      Q'.abs
        (((positiveExpandedReceiverFiberPartitionDensity S -
              positiveExpandedFourCellTargetReceiverFiberDensity
                S hfineCutoff hcoarseCoupling root target receiver) *
            (S.coarse.physicalPartition *
              S.coarse.physicalPartition)) *
          slabObservableTwoReplicaPairWeight S.coarse receiver))
    (slabObservableFourCellTargetPairs S.coarse root target)

/-- The complete source coefficient mass is exactly its partition-density
calibration sum. -/
theorem positiveExpandedFourCellSourceReceiverFiberScaleDefectMass_eqv_calibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    positiveExpandedFourCellSourceReceiverFiberScaleDefectMass
        S hfineCutoff hcoarseCoupling root target ≈
      listQSum
        (fun receiver =>
          ((positiveExpandedReceiverFiberPartitionDensity S -
                positiveExpandedFourCellSourceReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target receiver) *
              (S.coarse.physicalPartition *
                S.coarse.physicalPartition)) *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (slabObservableFourCellSourcePairs S.coarse root target) := by
  unfold positiveExpandedFourCellSourceReceiverFiberScaleDefectMass
  apply listQSum_congr
  intro receiver
  exact Q'.mul_eqv_congr_right _ _
    (slabObservableTwoReplicaPairWeight S.coarse receiver)
    (positiveExpandedFourCellSourceReceiverFiberScaleDefect_eqv_calibration
      S hfineCutoff hcoarseCoupling root target receiver)

theorem positiveExpandedFourCellSourceReceiverFiberScaleDefectMass_abs_le_calibrationL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    Q'.abs
        (positiveExpandedFourCellSourceReceiverFiberScaleDefectMass
          S hfineCutoff hcoarseCoupling root target) ≤
      actualPositiveExpandedReceiverFiberScaleDefectSourceCalibrationL1
        S hfineCutoff hcoarseCoupling root target := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (positiveExpandedFourCellSourceReceiverFiberScaleDefectMass_eqv_calibration
          S hfineCutoff hcoarseCoupling root target)))
    (abs_listQSum_le_sum_abs_local _ _)

/-- The complete target coefficient mass is exactly its partition-density
calibration sum. -/
theorem positiveExpandedFourCellTargetReceiverFiberScaleDefectMass_eqv_calibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    positiveExpandedFourCellTargetReceiverFiberScaleDefectMass
        S hfineCutoff hcoarseCoupling root target ≈
      listQSum
        (fun receiver =>
          ((positiveExpandedReceiverFiberPartitionDensity S -
                positiveExpandedFourCellTargetReceiverFiberDensity
                  S hfineCutoff hcoarseCoupling root target receiver) *
              (S.coarse.physicalPartition *
                S.coarse.physicalPartition)) *
            slabObservableTwoReplicaPairWeight S.coarse receiver)
        (slabObservableFourCellTargetPairs S.coarse root target) := by
  unfold positiveExpandedFourCellTargetReceiverFiberScaleDefectMass
  apply listQSum_congr
  intro receiver
  exact Q'.mul_eqv_congr_right _ _
    (slabObservableTwoReplicaPairWeight S.coarse receiver)
    (positiveExpandedFourCellTargetReceiverFiberScaleDefect_eqv_calibration
      S hfineCutoff hcoarseCoupling root target receiver)

theorem positiveExpandedFourCellTargetReceiverFiberScaleDefectMass_abs_le_calibrationL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    Q'.abs
        (positiveExpandedFourCellTargetReceiverFiberScaleDefectMass
          S hfineCutoff hcoarseCoupling root target) ≤
      actualPositiveExpandedReceiverFiberScaleDefectTargetCalibrationL1
        S hfineCutoff hcoarseCoupling root target := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (positiveExpandedFourCellTargetReceiverFiberScaleDefectMass_eqv_calibration
          S hfineCutoff hcoarseCoupling root target)))
    (abs_listQSum_le_sum_abs_local _ _)

/-! ## 2. Posterior-free control of the complete scale-defect cross -/

/-- The complete source-minus-target coefficient cross is bounded directly by
the two absolute calibration budgets. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectCross_abs_le_calibrationL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    Q'.abs
        (actualPositiveExpandedReceiverFiberScaleDefectCross
          S hfineCutoff hcoarseCoupling root target) ≤
      actualPositiveExpandedReceiverFiberScaleDefectSourceCalibrationL1
          S hfineCutoff hcoarseCoupling root target +
        actualPositiveExpandedReceiverFiberScaleDefectTargetCalibrationL1
          S hfineCutoff hcoarseCoupling root target := by
  unfold actualPositiveExpandedReceiverFiberScaleDefectCross
  exact Q'.le_trans' _ _ _
    (Q'.abs_add_le'
      (positiveExpandedFourCellSourceReceiverFiberScaleDefectMass
        S hfineCutoff hcoarseCoupling root target)
      (-positiveExpandedFourCellTargetReceiverFiberScaleDefectMass
        S hfineCutoff hcoarseCoupling root target))
    (Q'.add_le_add
      (positiveExpandedFourCellSourceReceiverFiberScaleDefectMass_abs_le_calibrationL1
        S hfineCutoff hcoarseCoupling root target)
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.abs_neg'
            (positiveExpandedFourCellTargetReceiverFiberScaleDefectMass
              S hfineCutoff hcoarseCoupling root target)))
        (positiveExpandedFourCellTargetReceiverFiberScaleDefectMass_abs_le_calibrationL1
          S hfineCutoff hcoarseCoupling root target)))

/-- An arbitrary outer normalization factors in front of the two direct
calibration budgets. -/
theorem actualPositiveExpandedReceiverFiberScaleDefect_scaledCross_abs_le_calibrationL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (factor : Q') :
    Q'.abs
        (factor *
          actualPositiveExpandedReceiverFiberScaleDefectCross
            S hfineCutoff hcoarseCoupling root target) ≤
      Q'.abs factor *
        (actualPositiveExpandedReceiverFiberScaleDefectSourceCalibrationL1
            S hfineCutoff hcoarseCoupling root target +
          actualPositiveExpandedReceiverFiberScaleDefectTargetCalibrationL1
            S hfineCutoff hcoarseCoupling root target) := by
  exact Q'.le_trans' _ _ _
    (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le factor _)
    (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.abs factor)
      (actualPositiveExpandedReceiverFiberScaleDefectCross_abs_le_calibrationL1
        S hfineCutoff hcoarseCoupling root target)
      (Q'.abs_nonneg factor))

/-! ## 3. Direct-calibration schedule producer -/

namespace PhysicalObservableRefinementSchedule

/-- Posterior-free analytic input: direct source and target receiver-density
calibration budgets on an eventual physical refinement tail. -/
structure ActualPositiveExpandedReceiverFiberScaleDefectDirectCalibrationLinearRawTransportTail
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  sourceCeiling : Q'
  sourceCeiling_pos : (0 : Q') < sourceCeiling
  targetCeiling : Q'
  targetCeiling_pos : (0 : Q') < targetCeiling
  mismatch_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget schedule scale ≤
      mismatchCeiling * schedule.spacing.spacing scale
  sourceCalibrationL1_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
          ((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
        actualPositiveExpandedReceiverFiberScaleDefectSourceCalibrationL1
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget ≤
      (sourceCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)
  targetCalibrationL1_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
          ((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
        actualPositiveExpandedReceiverFiberScaleDefectTargetCalibrationL1
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget ≤
      (targetCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)

namespace ActualPositiveExpandedReceiverFiberScaleDefectDirectCalibrationLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

def connectedCeiling
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectDirectCalibrationLinearRawTransportTail
        schedule) : Q' :=
  tail.sourceCeiling + tail.targetCeiling

theorem connectedCeiling_pos
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectDirectCalibrationLinearRawTransportTail
        schedule) :
    (0 : Q') < tail.connectedCeiling :=
  Q'.add_pos tail.sourceCeiling_pos tail.targetCeiling_pos

/-- The two direct calibration hypotheses bound the partition-scaled receiver
cross with coefficient `sourceCeiling + targetCeiling`. -/
theorem scaledCross_abs_le_connectedCeiling
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectDirectCalibrationLinearRawTransportTail
        schedule)
    (scale : Nat) (hscale : tail.start ≤ scale) :
    Q'.abs
        (((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
          actualPositiveExpandedReceiverFiberScaleDefectCross
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget) ≤
      (tail.connectedCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale) := by
  let factor :=
    (schedule.scalePair scale).coarse.physicalPartition *
      (schedule.scalePair scale).fine.physicalPartition
  let sourceBudget :=
    actualPositiveExpandedReceiverFiberScaleDefectSourceCalibrationL1
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
  let targetBudget :=
    actualPositiveExpandedReceiverFiberScaleDefectTargetCalibrationL1
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
  have hdirect :=
    actualPositiveExpandedReceiverFiberScaleDefect_scaledCross_abs_le_calibrationL1
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget factor
  have hsplit :
      Q'.abs factor * (sourceBudget + targetBudget) ≤
        Q'.abs factor * sourceBudget + Q'.abs factor * targetBudget :=
    Q'.le_of_eqv (Q'.mul_add_eqv (Q'.abs factor) sourceBudget targetBudget)
  have hbudgets :
      Q'.abs factor * sourceBudget + Q'.abs factor * targetBudget ≤
        (tail.sourceCeiling * schedule.spacing.spacing scale) *
            connectedCovarianceRawCrossDenominator (schedule.scalePair scale) +
          (tail.targetCeiling * schedule.spacing.spacing scale) *
            connectedCovarianceRawCrossDenominator (schedule.scalePair scale) :=
    Q'.add_le_add
      (by simpa only [factor, sourceBudget] using
        tail.sourceCalibrationL1_le scale hscale)
      (by simpa only [factor, targetBudget] using
        tail.targetCalibrationL1_le scale hscale)
  exact Q'.le_trans' _ _ _
    (by simpa only [factor, sourceBudget, targetBudget] using hdirect)
    (Q'.le_trans' _ _ _ hsplit
      (Q'.le_trans' _ _ _ hbudgets
        (Q'.le_of_eqv
          (add_two_scaled_eqv
            tail.sourceCeiling tail.targetCeiling
            (schedule.spacing.spacing scale)
            (connectedCovarianceRawCrossDenominator
              (schedule.scalePair scale))))))

def toScaleDefectSeparatedLinearRawTransportTail
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectDirectCalibrationLinearRawTransportTail
        schedule) :
    ActualPositiveExpandedReceiverFiberScaleDefectSeparatedLinearRawTransportTail
      schedule where
  start := tail.start
  mismatchCeiling := tail.mismatchCeiling
  mismatchCeiling_pos := tail.mismatchCeiling_pos
  connectedCeiling := tail.connectedCeiling
  connectedCeiling_pos := tail.connectedCeiling_pos
  mismatch_le := tail.mismatch_le
  actualPositiveExpandedReceiverFiberScaleDefect_le :=
    fun scale hscale => tail.scaledCross_abs_le_connectedCeiling scale hscale

def toConnectedSeparatedLinearRawTransportTail
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectDirectCalibrationLinearRawTransportTail
        schedule) :
    ConnectedSeparatedLinearRawTransportTail schedule :=
  tail.toScaleDefectSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail

theorem combinedCeiling_eq
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectDirectCalibrationLinearRawTransportTail
        schedule) :
    tail.toConnectedSeparatedLinearRawTransportTail.combinedCeiling =
      tail.mismatchCeiling +
        (tail.sourceCeiling + tail.targetCeiling) :=
  rfl

/-- Final covariance consumer for the posterior-free direct-calibration
branch. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectDirectCalibrationLinearRawTransportTail
        schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      tail.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  tail.toConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end ActualPositiveExpandedReceiverFiberScaleDefectDirectCalibrationLinearRawTransportTail
end PhysicalObservableRefinementSchedule

#print axioms actualPositiveExpandedReceiverFiberScaleDefectSourceCalibrationL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectTargetCalibrationL1
#print axioms positiveExpandedFourCellSourceReceiverFiberScaleDefectMass_eqv_calibration
#print axioms positiveExpandedFourCellSourceReceiverFiberScaleDefectMass_abs_le_calibrationL1
#print axioms positiveExpandedFourCellTargetReceiverFiberScaleDefectMass_eqv_calibration
#print axioms positiveExpandedFourCellTargetReceiverFiberScaleDefectMass_abs_le_calibrationL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCross_abs_le_calibrationL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefect_scaledCross_abs_le_calibrationL1
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectDirectCalibrationLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectDirectCalibrationLinearRawTransportTail.connectedCeiling_pos
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectDirectCalibrationLinearRawTransportTail.scaledCross_abs_le_connectedCeiling
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectDirectCalibrationLinearRawTransportTail.toScaleDefectSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectDirectCalibrationLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectDirectCalibrationLinearRawTransportTail.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectDirectCalibrationLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectDirectCalibration
