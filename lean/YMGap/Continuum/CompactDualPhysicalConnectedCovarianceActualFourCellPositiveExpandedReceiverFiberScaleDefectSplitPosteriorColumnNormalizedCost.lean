/-
# Normalize the three split posterior-column costs

The explicit split receiver transport has been compressed from five signed
debts to one connected row debt and two posterior-column debts.  This module
normalizes that sharper three-term budget without losing its columnwise
structure.

Each physical receiver coefficient is exactly a dimensionless
partition-density calibration coefficient multiplied by the positive coarse
physical-partition square.  Generic coefficient-rescaling therefore removes
that square from the row defect and both posterior-column `l1` sums.  The
outer coarse--fine partition product then cancels against the cubic covariance
denominator, leaving only

```text
dimensionless three-term posterior budget / (spacing * Z_fine^2).
```

A uniform bound on this computed cost and the raw mismatch cost compiles to
the existing matched covariance consumer.  No uniform bound is inhabited
here.  In particular, this proves no physical gap floor, continuum measure,
OS/GNS reconstruction, Hamiltonian gap, or Clay conclusion.

Constructive contract: finite exact rational algebra, positivity, and
Type-valued witnesses only; no choice, `Classical`, `native_decide`, proof
hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumn
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostCoarseSquareCancellation
import YMGap.Continuum.FiniteDependentKernelCoefficientPosteriorRescaling

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberDensity
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCost.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostCoarseSquareCancellation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostPartitionCancellation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumn
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransport
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport.FiniteDependentCoefficientTransport
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local instance splitPosteriorNormalizedPairDecidableEq
    (S : SlabScalePair) (root : Nat) :
    DecidableEq (Receiver S root) :=
  slabObservableTwoReplicaPairDecidableEq S.coarse root

private theorem abs_scaled_eqv_factor_mul_abs_local
    (factor base : Q') (hfactor : (0 : Q') ≤ factor) :
    Q'.abs (base * factor) ≈ factor * Q'.abs base := by
  refine Q'.eqv_trans _ (Q'.abs base * factor) _
    (YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right base hfactor) ?_
  exact Q'.mul_comm_eqv (Q'.abs base) factor

private theorem threeScaledTerms_eqv_factor_mul_sum
    (factor first second third : Q') :
    (factor * first + factor * second) + factor * third ≈
      factor * ((first + second) + third) := by
  apply Q'.eqv_symm
  refine Q'.eqv_trans _
    (factor * (first + second) + factor * third) _
    (Q'.mul_add_eqv factor (first + second) third) ?_
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.mul_add_eqv factor first second)

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

private theorem commonFactorCross_local
    (factor left right : Q') :
    (factor * left) * right ≈ left * (factor * right) := by
  refine Q'.eqv_trans _ (factor * (left * right)) _
    (Q'.mul_assoc_eqv factor left right) ?_
  refine Q'.eqv_trans _ ((left * right) * factor) _
    (Q'.mul_comm_eqv factor (left * right)) ?_
  refine Q'.eqv_trans _ (left * (right * factor)) _
    (Q'.mul_assoc_eqv left right factor) ?_
  exact Q'.mul_eqv_congr_left left _ _
    (Q'.mul_comm_eqv right factor)

private theorem normalized_le_scaled_of_divPos_le
    (numerator denominator ceiling : Q')
    (hdenominator : (0 : Q') < denominator)
    (hle : Q'.divPos numerator denominator hdenominator ≤ ceiling) :
    numerator ≤ ceiling * denominator := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.divPos_mul_eqv numerator denominator hdenominator)))
    (Q'.mul_le_mul_of_nonneg_right
      (Q'.divPos numerator denominator hdenominator)
      ceiling denominator hle (Q'.le_of_lt hdenominator))

/-! ## 1. Dimensionless coefficient transports -/

def actualPositiveExpandedReceiverFiberSourceDensityCoefficient
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : Receiver S root) : Q' :=
  positiveExpandedReceiverFiberPartitionDensity S -
    positiveExpandedFourCellSourceReceiverFiberDensity
      S hfineCutoff hcoarseCoupling root target receiver

def actualPositiveExpandedReceiverFiberTargetDensityCoefficient
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (receiver : Receiver S root) : Q' :=
  positiveExpandedReceiverFiberPartitionDensity S -
    positiveExpandedFourCellTargetReceiverFiberDensity
      S hfineCutoff hcoarseCoupling root target receiver

def actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :=
  (actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
    S hfineCutoff hcoarseCoupling root target htarget).replaceCoefficients
      (fun source =>
        actualPositiveExpandedReceiverFiberSourceDensityCoefficient
          S hfineCutoff hcoarseCoupling root target source.1)
      (actualPositiveExpandedReceiverFiberTargetDensityCoefficient
        S hfineCutoff hcoarseCoupling root target)

def actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :=
  (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
    S hfineCutoff hcoarseCoupling root target htarget).replaceCoefficients
      (fun source =>
        actualPositiveExpandedReceiverFiberSourceDensityCoefficient
          S hfineCutoff hcoarseCoupling root target source.1)
      (actualPositiveExpandedReceiverFiberTargetDensityCoefficient
        S hfineCutoff hcoarseCoupling root target)

def actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDebt
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  (actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
    S hfineCutoff hcoarseCoupling root target htarget).rowCoefficientDefect

def actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDensityL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  (actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
    S hfineCutoff hcoarseCoupling root target htarget
  ).posteriorColumnCoefficientL1

def actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDensityL1
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) : Q' :=
  (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
    S hfineCutoff hcoarseCoupling root target htarget
  ).posteriorColumnCoefficientL1

/-! ## 2. Remove the common coarse partition square exactly -/

theorem actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt_eqv_density_mul_coarseSquare
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
        S hfineCutoff hcoarseCoupling root target htarget ≈
      actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDebt
          S hfineCutoff hcoarseCoupling root target htarget *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) := by
  unfold actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
    actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDebt
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
  apply FiniteDependentCoefficientTransport.rowCoefficientDefect_eqv_replaceCoefficients_mul
  intro source
  simpa only [actualPositiveExpandedReceiverFiberSourceDensityCoefficient] using
    positiveExpandedFourCellSourceReceiverFiberScaleDefect_eqv_calibration
      S hfineCutoff hcoarseCoupling root target source.1

theorem actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnL1_eqv_coarseSquare_mul_density
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnL1
        S hfineCutoff hcoarseCoupling root target htarget ≈
      (S.coarse.physicalPartition * S.coarse.physicalPartition) *
        actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDensityL1
          S hfineCutoff hcoarseCoupling root target htarget := by
  unfold actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnL1
    actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDensityL1
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
  apply FiniteDependentCoefficientTransport.posteriorColumnCoefficientL1_eqv_factor_mul_replaceCoefficients
  · exact Q'.le_of_lt (coarsePhysicalPartitionSquare_pos S)
  · intro source
    simpa only [actualPositiveExpandedReceiverFiberSourceDensityCoefficient] using
      positiveExpandedFourCellSourceReceiverFiberScaleDefect_eqv_calibration
        S hfineCutoff hcoarseCoupling root target source.1
  · intro receiver
    simpa only [actualPositiveExpandedReceiverFiberTargetDensityCoefficient] using
      positiveExpandedFourCellTargetReceiverFiberScaleDefect_eqv_calibration
        S hfineCutoff hcoarseCoupling root target receiver

theorem actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnL1_eqv_coarseSquare_mul_density
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat)
    (htarget : target ∈ slabPhysicalFaceEdges S.coarse.extent) :
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnL1
        S hfineCutoff hcoarseCoupling root target htarget ≈
      (S.coarse.physicalPartition * S.coarse.physicalPartition) *
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDensityL1
          S hfineCutoff hcoarseCoupling root target htarget := by
  unfold actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnL1
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDensityL1
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
  apply FiniteDependentCoefficientTransport.posteriorColumnCoefficientL1_eqv_factor_mul_replaceCoefficients
  · exact Q'.le_of_lt (coarsePhysicalPartitionSquare_pos S)
  · intro source
    simpa only [actualPositiveExpandedReceiverFiberSourceDensityCoefficient] using
      positiveExpandedFourCellSourceReceiverFiberScaleDefect_eqv_calibration
        S hfineCutoff hcoarseCoupling root target source.1
  · intro receiver
    simpa only [actualPositiveExpandedReceiverFiberTargetDensityCoefficient] using
      positiveExpandedFourCellTargetReceiverFiberScaleDefect_eqv_calibration
        S hfineCutoff hcoarseCoupling root target receiver

/-- The exact dimensionless three-term posterior budget after removal of the
common coarse physical-partition square. -/
def actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  let S := schedule.scalePair scale
  let root := (schedule.faceMap scale).coarseRoot
  let target := (schedule.faceMap scale).coarseTarget
  let htarget := (schedule.faceMap scale).coarseTarget_mem
  (Q'.abs
      (actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDebt
        S rfl (schedule.effectiveCoupling_pos scale) root target htarget) +
    actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDensityL1
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget) +
  actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDensityL1
    S rfl (schedule.effectiveCoupling_pos scale) root target htarget

theorem actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnL1_eqv_coarseSquare_mul_cancelled
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnL1
        (schedule.scalePair scale) rfl
        (schedule.effectiveCoupling_pos scale)
        (schedule.faceMap scale).coarseRoot
        (schedule.faceMap scale).coarseTarget
        (schedule.faceMap scale).coarseTarget_mem ≈
      ((schedule.scalePair scale).coarse.physicalPartition *
          (schedule.scalePair scale).coarse.physicalPartition) *
        actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
          schedule scale := by
  let S := schedule.scalePair scale
  let root := (schedule.faceMap scale).coarseRoot
  let target := (schedule.faceMap scale).coarseTarget
  let htarget := (schedule.faceMap scale).coarseTarget_mem
  let factor := S.coarse.physicalPartition * S.coarse.physicalPartition
  let row :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDebt
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDensityL1
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDensityL1
      S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  have hrow :
      Q'.abs
          (actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
            S rfl (schedule.effectiveCoupling_pos scale)
            root target htarget) ≈
        factor * Q'.abs row := by
    refine Q'.eqv_trans _ (Q'.abs (row * factor)) _ ?_ ?_
    · exact Q'.abs_eqv_congr (by
        simpa only [S, root, target, htarget, factor, row] using
          actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt_eqv_density_mul_coarseSquare
            S rfl (schedule.effectiveCoupling_pos scale)
            root target htarget)
    · exact abs_scaled_eqv_factor_mul_abs_local factor row
        (Q'.le_of_lt (coarsePhysicalPartitionSquare_pos S))
  have hconnected :
      actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnL1
          S rfl (schedule.effectiveCoupling_pos scale)
          root target htarget ≈ factor * connected := by
    simpa only [factor, connected] using
      actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnL1_eqv_coarseSquare_mul_density
        S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  have hdisconnected :
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnL1
          S rfl (schedule.effectiveCoupling_pos scale)
          root target htarget ≈ factor * disconnected := by
    simpa only [factor, disconnected] using
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnL1_eqv_coarseSquare_mul_density
        S rfl (schedule.effectiveCoupling_pos scale) root target htarget
  refine Q'.eqv_trans _
    ((factor * Q'.abs row + factor * connected) +
      factor * disconnected) _ ?_ ?_
  · simpa only [S, root, target, htarget, factor, row, connected,
      disconnected,
      actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnL1]
      using Q'.add_eqv_congr'
        (Q'.add_eqv_congr' hrow hconnected) hdisconnected
  · simpa only [S, root, target, htarget, factor, row, connected,
      disconnected,
      actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget]
      using threeScaledTerms_eqv_factor_mul_sum
        factor (Q'.abs row) connected disconnected

/-! ## 3. Cancel all common partition factors from the physical cost -/

def splitPosteriorColumnPartitionFactor (S : SlabScalePair) : Q' :=
  (S.coarse.physicalPartition * S.fine.physicalPartition) *
    (S.coarse.physicalPartition * S.coarse.physicalPartition)

theorem splitPosteriorColumnPartitionFactor_pos (S : SlabScalePair) :
    (0 : Q') < splitPosteriorColumnPartitionFactor S := by
  exact Q'.mul_pos
    (Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent))
    (coarsePhysicalPartitionSquare_pos S)

theorem actualPositiveExpandedReceiverFiberScaleDefectScaledSplitPosteriorColumnBudget_eqv_partitionFactor_mul_cancelled
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectScaledSplitPosteriorColumnBudget
        schedule scale ≈
      splitPosteriorColumnPartitionFactor (schedule.scalePair scale) *
        actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
          schedule scale := by
  let S := schedule.scalePair scale
  let outer := S.coarse.physicalPartition * S.fine.physicalPartition
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let reduced :=
    actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
      schedule scale
  have houterNonnegative : (0 : Q') ≤ outer :=
    Q'.le_of_lt (physicalPartitionProduct_pos schedule scale)
  have habs : Q'.abs outer = outer := by
    unfold Q'.abs
    rw [if_pos houterNonnegative]
  have hbudget :
      actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnL1
          S rfl (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (schedule.faceMap scale).coarseTarget_mem ≈
        coarseSquare * reduced := by
    simpa only [S, coarseSquare, reduced] using
      actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnL1_eqv_coarseSquare_mul_cancelled
        schedule scale
  unfold actualPositiveExpandedReceiverFiberScaleDefectScaledSplitPosteriorColumnBudget
  change Q'.abs outer *
      actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnL1
        S rfl (schedule.effectiveCoupling_pos scale)
        (schedule.faceMap scale).coarseRoot
        (schedule.faceMap scale).coarseTarget
        (schedule.faceMap scale).coarseTarget_mem ≈ _
  rw [habs]
  refine Q'.eqv_trans _ (outer * (coarseSquare * reduced)) _
    (Q'.mul_eqv_congr_left outer _ _ hbudget) ?_
  simpa only [S, outer, coarseSquare, reduced,
    splitPosteriorColumnPartitionFactor] using
      (Q'.eqv_symm (Q'.mul_assoc_eqv outer coarseSquare reduced))

theorem splitDensityNormalizationDenominator_eqv_splitPosteriorColumnPartitionFactor_mul_cancelled
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    schedule.spacing.spacing scale *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale) ≈
      splitPosteriorColumnPartitionFactor (schedule.scalePair scale) *
        coarseSquareCancelledSplitDensityDenominator schedule scale := by
  let S := schedule.scalePair scale
  let outer := S.coarse.physicalPartition * S.fine.physicalPartition
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let reducedDenominator :=
    coarseSquareCancelledSplitDensityDenominator schedule scale
  refine Q'.eqv_trans _
    (outer * partitionCancelledSplitDensityDenominator schedule scale) _ ?_ ?_
  · simpa only [S, outer] using
      splitDensityNormalizationDenominator_eqv_partitionProduct_mul_cancelled
        schedule scale
  refine Q'.eqv_trans _
    (outer * (coarseSquare * reducedDenominator)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left outer _ _ (by
      simpa only [S, coarseSquare, reducedDenominator] using
        partitionCancelledSplitDensityDenominator_eqv_coarseSquare_mul_cancelled
          schedule scale)
  · simpa only [S, outer, coarseSquare, reducedDenominator,
      splitPosteriorColumnPartitionFactor] using
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv outer coarseSquare reducedDenominator))

theorem splitPosteriorColumnNormalizationDenominator_pos
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    (0 : Q') <
      schedule.spacing.spacing scale *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale) :=
  splitDensityNormalizationDenominator_pos schedule scale

def actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  Q'.divPos
    (actualPositiveExpandedReceiverFiberScaleDefectScaledSplitPosteriorColumnBudget
      schedule scale)
    (schedule.spacing.spacing scale *
      connectedCovarianceRawCrossDenominator (schedule.scalePair scale))
    (splitPosteriorColumnNormalizationDenominator_pos schedule scale)

theorem actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost_mul_denominator_eqv
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost
          schedule scale *
        (schedule.spacing.spacing scale *
          connectedCovarianceRawCrossDenominator
            (schedule.scalePair scale)) ≈
      actualPositiveExpandedReceiverFiberScaleDefectScaledSplitPosteriorColumnBudget
        schedule scale := by
  exact Q'.divPos_mul_eqv _ _ _

def actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnNormalizedCost
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  Q'.divPos
    (actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
      schedule scale)
    (coarseSquareCancelledSplitDensityDenominator schedule scale)
    (coarseSquareCancelledSplitDensityDenominator_pos schedule scale)

/-- Exact cancellation identifies the physical three-term cost with the
dimensionless posterior budget divided by `spacing * Z_fine^2`. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost_eqv_coarseSquareCancelled
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost
        schedule scale ≈
      actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnNormalizedCost
        schedule scale := by
  unfold actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost
    actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnNormalizedCost
  refine divPos_eqv_divPos_of_cross_local
    (splitPosteriorColumnNormalizationDenominator_pos schedule scale)
    (coarseSquareCancelledSplitDensityDenominator_pos schedule scale) ?_
  let factor := splitPosteriorColumnPartitionFactor (schedule.scalePair scale)
  let reduced :=
    actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
      schedule scale
  let denominator := coarseSquareCancelledSplitDensityDenominator schedule scale
  have hbudget :
      actualPositiveExpandedReceiverFiberScaleDefectScaledSplitPosteriorColumnBudget
          schedule scale ≈ factor * reduced := by
    simpa only [factor, reduced] using
      actualPositiveExpandedReceiverFiberScaleDefectScaledSplitPosteriorColumnBudget_eqv_partitionFactor_mul_cancelled
        schedule scale
  have hdenominator :
      schedule.spacing.spacing scale *
          connectedCovarianceRawCrossDenominator (schedule.scalePair scale) ≈
        factor * denominator := by
    simpa only [factor, denominator] using
      splitDensityNormalizationDenominator_eqv_splitPosteriorColumnPartitionFactor_mul_cancelled
        schedule scale
  refine Q'.eqv_trans _ ((factor * reduced) * denominator) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ denominator hbudget
  · refine Q'.eqv_trans _ (reduced * (factor * denominator)) _
      (commonFactorCross_local factor reduced denominator) ?_
    exact Q'.mul_eqv_congr_left reduced _ _
      (Q'.eqv_symm hdenominator)

/-! ## 4. Uniform posterior cost bounds compile to covariance control -/

namespace PhysicalObservableRefinementSchedule

/-- The sharpened analytic frontier: uniformly bound the raw mismatch cost
and the exact three-term posterior-column cost after one start scale. -/
structure ActualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCostBound
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  connectedCeiling : Q'
  connectedCeiling_pos : (0 : Q') < connectedCeiling
  mismatchNormalizedCost_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchNormalizedCost schedule scale ≤ mismatchCeiling
  splitPosteriorColumnNormalizedCost_le : ∀ scale : Nat, start ≤ scale →
    actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost
      schedule scale ≤ connectedCeiling

namespace ActualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCostBound

variable {schedule : PhysicalObservableRefinementSchedule}

def toScaleDefectSeparatedLinearRawTransportTail
    (bound :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCostBound
        schedule) :
    ActualPositiveExpandedReceiverFiberScaleDefectSeparatedLinearRawTransportTail
      schedule where
  start := bound.start
  mismatchCeiling := bound.mismatchCeiling
  mismatchCeiling_pos := bound.mismatchCeiling_pos
  connectedCeiling := bound.connectedCeiling
  connectedCeiling_pos := bound.connectedCeiling_pos
  mismatch_le := fun scale hscale =>
    normalized_le_scaled_of_divPos_le
      (rawMismatchBudget schedule scale)
      (schedule.spacing.spacing scale)
      bound.mismatchCeiling
      (schedule.spacing.spacing_pos scale)
      (bound.mismatchNormalizedCost_le scale hscale)
  actualPositiveExpandedReceiverFiberScaleDefect_le :=
    fun scale hscale => by
      let denominator :=
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)
      have hbudget :
          actualPositiveExpandedReceiverFiberScaleDefectScaledSplitPosteriorColumnBudget
              schedule scale ≤
            bound.connectedCeiling *
              (schedule.spacing.spacing scale * denominator) :=
        normalized_le_scaled_of_divPos_le
          (actualPositiveExpandedReceiverFiberScaleDefectScaledSplitPosteriorColumnBudget
            schedule scale)
          (schedule.spacing.spacing scale * denominator)
          bound.connectedCeiling
          (by simpa only [denominator] using
            splitPosteriorColumnNormalizationDenominator_pos schedule scale)
          (bound.splitPosteriorColumnNormalizedCost_le scale hscale)
      exact Q'.le_trans' _ _ _
        (actualPositiveExpandedReceiverFiberScaleDefectScaledCross_abs_le_splitPosteriorColumnBudget
          schedule scale)
        (Q'.le_trans' _ _ _ hbudget
          (Q'.le_of_eqv
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv bound.connectedCeiling
                (schedule.spacing.spacing scale) denominator))))

def toConnectedSeparatedLinearRawTransportTail
    (bound :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCostBound
        schedule) :
    ConnectedSeparatedLinearRawTransportTail schedule :=
  bound.toScaleDefectSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail

theorem combinedCeiling_eq
    (bound :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCostBound
        schedule) :
    bound.toConnectedSeparatedLinearRawTransportTail.combinedCeiling =
      bound.mismatchCeiling + bound.connectedCeiling :=
  rfl

theorem fineCovariance_le_anchorRate_add_epsilon
    (bound :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCostBound
        schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      bound.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  bound.toConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end ActualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCostBound
end PhysicalObservableRefinementSchedule

#print axioms actualPositiveExpandedReceiverFiberSourceDensityCoefficient
#print axioms actualPositiveExpandedReceiverFiberTargetDensityCoefficient
#print axioms actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
#print axioms actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
#print axioms actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDebt
#print axioms actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDensityL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDensityL1
#print axioms actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt_eqv_density_mul_coarseSquare
#print axioms actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnL1_eqv_coarseSquare_mul_density
#print axioms actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnL1_eqv_coarseSquare_mul_density
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
#print axioms actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnL1_eqv_coarseSquare_mul_cancelled
#print axioms splitPosteriorColumnPartitionFactor
#print axioms splitPosteriorColumnPartitionFactor_pos
#print axioms actualPositiveExpandedReceiverFiberScaleDefectScaledSplitPosteriorColumnBudget_eqv_partitionFactor_mul_cancelled
#print axioms splitDensityNormalizationDenominator_eqv_splitPosteriorColumnPartitionFactor_mul_cancelled
#print axioms splitPosteriorColumnNormalizationDenominator_pos
#print axioms actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost
#print axioms actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost_mul_denominator_eqv
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnNormalizedCost
#print axioms actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost_eqv_coarseSquareCancelled
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCostBound
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCostBound.toScaleDefectSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCostBound.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCostBound.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCostBound.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost
