/-
# Posterior-column producer for the fully raw connected aggregate

The literal fully raw event expansion ultimately consumes one signed
receiver-column cross.  Independently, the accepted-fiber transport branch
compresses that same physical covariance defect into one connected row debt
and two posterior-column debts.  This module joins those branches without a
new analytic hypothesis.

First, the assignment-saturated raw-column cross and the accepted receiver-
fiber scale-defect cross are shown to be exactly equal: both multiply by the
same strictly positive coarse--fine partition factor to give the physical raw
covariance defect.  The established three-term posterior `l1` bound and its
exact coarse-square cancellation then compile a posterior quadratic-cost
control into the existing raw-column quadratic-cost control.  Consequently
the same posterior field supplies the cancellation-preserving fully raw
signed source-average calibration at every controlled matched-AF scale.

The signed route now cancels the common positive coarse partition square
before any absolute value is taken.  Its exact analytic residue is the sum of
one dimensionless connected row-density debt and the two dimensionless
posterior-column density debts.  This residue is exactly the concrete Gibbs-
refresh-versus-production signed cross.  Bounding it by `K*g^2*Z_fine^2` is
therefore the already exposed Gibbs-refresh physical-kernel calibration and,
with no constant loss, is equivalent to the physical signed posterior and
fully raw source-average calibrations.

No posterior smallness estimate is inhabited here.  Cutoff/volume uniformity,
continuum persistence, OS/GNS reconstruction, the Hamiltonian gap, and the
Yang--Mills mass gap remain open.

Constructive contract: exact rational cancellation and inequalities only; no
choice, `Classical`, `native_decide`, proof hole, noncomputable declaration,
or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedFullyRawEventCrossAverage
import YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshReferenceCross
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnMatchedAFQuadraticCost

namespace YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedFullyRawPosteriorColumn

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransport
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumn
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnNormalizedCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostCoarseSquareCancellation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnMatchedAFQuadraticCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalMatchedAFTrajectory
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCoefficientTransport
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedFullyRawEventCrossAverage
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRemainder
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshReferenceCross
open YMGap.Continuum.Z4DyadicSpinFourReceiverRawColumnCrossCalibration
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local instance fullyRawPosteriorColumnPairDecidableEq
    (S : SlabScalePair) (root : Nat) :
    DecidableEq (Receiver S root) :=
  splitTransportPairDecidableEq S root

/-! ## 1. The posterior and raw-column crosses are the same signed object -/

/-- The assignment-saturated raw column and the accepted receiver-fiber
scale-defect cross are exactly equal.  Both presentations produce the same
physical raw covariance defect after multiplication by the common positive
factor `Z_coarse * Z_fine`, which can therefore be cancelled constructively. -/
theorem positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_receiverFiber
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget ≈
      actualPositiveExpandedReceiverFiberScaleDefectCross
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget := by
  let factor := S.coarse.physicalPartition * S.fine.physicalPartition
  let rawDefect :=
    physicalConnectedCovarianceRawCrossDefect
      S hfineCutoff hcoarseCoupling M
  let rawColumn :=
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
  let receiverFiber :=
    actualPositiveExpandedReceiverFiberScaleDefectCross
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
  have hfactor : (0 : Q') < factor :=
    Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
  have hrawColumn : rawDefect ≈ factor * rawColumn := by
    refine Q'.eqv_trans _
      (factor *
        actualPositiveExpandedAssignmentSaturatedScaleDefectCross
          S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget) _ ?_ ?_
    · simpa only [factor, rawDefect] using
        (physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedAssignmentSaturatedScaleDefect
          S hfineCutoff hcoarseCoupling M)
    · exact Q'.mul_eqv_congr_left factor _ _
        (by
          simpa only [rawColumn] using
            (actualPositiveExpandedAssignmentSaturatedScaleDefectCross_eqv_rawColumn
              S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget))
  have hreceiverFiber : rawDefect ≈ factor * receiverFiber := by
    simpa only [factor, rawDefect, receiverFiber] using
      (physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedReceiverFiberScaleDefect
        S hfineCutoff hcoarseCoupling M)
  apply Q'.mul_left_cancel_of_pos hfactor
  exact Q'.eqv_trans _ rawDefect _
    (Q'.eqv_symm hrawColumn) hreceiverFiber

/-! ## 2. Preserve the signed three-debt posterior cancellation -/

/-- The exact signed posterior expression: one connected row loss plus the
connected and disconnected posterior-column mismatches. -/
def positivePhysicalConnectedSignedPosteriorDebtSum
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  (actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
      M.coarseTarget_mem +
    actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDebt
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
      M.coarseTarget_mem) +
  actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDebt
    S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
    M.coarseTarget_mem

/-- The assignment-saturated raw column is exactly the signed three-debt
posterior expression, before any triangle inequality splits its cancellation. -/
theorem positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_signedPosteriorDebtSum
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget ≈
      positivePhysicalConnectedSignedPosteriorDebtSum
        S hfineCutoff hcoarseCoupling M := by
  refine Q'.eqv_trans _
    (actualPositiveExpandedReceiverFiberScaleDefectCross
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget) _
    (positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_receiverFiber
      S hfineCutoff hcoarseCoupling M) ?_
  simpa only [positivePhysicalConnectedSignedPosteriorDebtSum] using
    (actualPositiveExpandedReceiverFiberScaleDefectCross_eqv_splitThreePosteriorDebts
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
      M.coarseTarget_mem)

/-- Cancellation-preserving posterior premise.  The absolute value is taken
only after the three signed debts have been assembled. -/
def PositivePhysicalConnectedSignedPosteriorDebtCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') : Prop :=
  Q'.abs
      (positivePhysicalConnectedSignedPosteriorDebtSum
        S hfineCutoff hcoarseCoupling M) ≤
    (kernelCeiling * (g * g)) *
      ((S.coarse.physicalPartition * S.coarse.physicalPartition) *
        (S.fine.physicalPartition * S.fine.physicalPartition))

/-- The signed posterior premise is exactly the raw-column calibration; no
triangle inequality or change of constant occurs in either direction. -/
theorem positiveSignedPosteriorDebtCalibration_iff_rawColumnCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') :
    PositivePhysicalConnectedSignedPosteriorDebtCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling ↔
      PositiveExpandedAssignmentSaturatedRawColumnCrossCalibration
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
          (kernelCeiling * (g * g)) := by
  unfold PositivePhysicalConnectedSignedPosteriorDebtCalibration
    PositiveExpandedAssignmentSaturatedRawColumnCrossCalibration
  have hexact :=
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_signedPosteriorDebtSum
      S hfineCutoff hcoarseCoupling M
  constructor
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hexact)) h
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_symm hexact))) h

/-- The weakest signed posterior premise exposed here is equivalent to the
signed fully raw source-average calibration.  Both directions retain every
row/column sign and the same quadratic constant. -/
theorem positiveSignedPosteriorDebtCalibration_iff_fullyRawSignedSourceAverage
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') :
    PositivePhysicalConnectedSignedPosteriorDebtCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling ↔
      PositivePhysicalConnectedFullyRawSignedSourceAverageCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  exact Iff.trans
    (positiveSignedPosteriorDebtCalibration_iff_rawColumnCross
      S hfineCutoff hcoarseCoupling M g kernelCeiling)
    (Iff.symm
      (positiveFullyRawSignedSourceAverageCalibration_iff_rawColumnCross
        S hfineCutoff hcoarseCoupling M g kernelCeiling))

/-! ## 3. The three posterior `l1` debts produce raw-column calibration -/

def positivePhysicalConnectedSignedPosteriorDensityDebtSum
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  let connected :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
      M.coarseTarget_mem
  let disconnected :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
      M.coarseTarget_mem
  (connected.rowCoefficientDefect +
      connected.posteriorColumnCoefficientDefect) +
    disconnected.posteriorColumnCoefficientDefect

/-- Every signed scale-defect debt contains the same coarse physical
partition square.  It is removed here before taking an absolute value, so no
row or column cancellation is lost. -/
theorem positivePhysicalConnectedSignedPosteriorDebtSum_eqv_density_mul_coarseSquare
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    positivePhysicalConnectedSignedPosteriorDebtSum
        S hfineCutoff hcoarseCoupling M ≈
      positivePhysicalConnectedSignedPosteriorDensityDebtSum
          S hfineCutoff hcoarseCoupling M *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) := by
  let factor :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let connectedScale :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
      M.coarseTarget_mem
  let disconnectedScale :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedCoefficientTransport
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
      M.coarseTarget_mem
  let connectedDensity :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
      M.coarseTarget_mem
  let disconnectedDensity :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
      M.coarseTarget_mem
  have hrow :
      connectedScale.rowCoefficientDefect ≈
        connectedDensity.rowCoefficientDefect * factor := by
    simpa only [factor, connectedScale, connectedDensity,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDensityDebt]
      using
        (actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt_eqv_density_mul_coarseSquare
          S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
          M.coarseTarget_mem)
  have hconnected :
      connectedScale.posteriorColumnCoefficientDefect ≈
        connectedDensity.posteriorColumnCoefficientDefect * factor := by
    unfold connectedScale connectedDensity
      actualPositiveExpandedReceiverFiberScaleDefectConnectedDensityTransport
    apply
      FiniteDependentCoefficientTransport.posteriorColumnCoefficientDefect_eqv_replaceCoefficients_mul
    · intro source
      simpa only [factor,
        actualPositiveExpandedReceiverFiberSourceDensityCoefficient] using
        (positiveExpandedFourCellSourceReceiverFiberScaleDefect_eqv_calibration
          S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget source.1)
    · intro receiver
      simpa only [factor,
        actualPositiveExpandedReceiverFiberTargetDensityCoefficient] using
        (positiveExpandedFourCellTargetReceiverFiberScaleDefect_eqv_calibration
          S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget receiver)
  have hdisconnected :
      disconnectedScale.posteriorColumnCoefficientDefect ≈
        disconnectedDensity.posteriorColumnCoefficientDefect * factor := by
    unfold disconnectedScale disconnectedDensity
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedDensityTransport
    apply
      FiniteDependentCoefficientTransport.posteriorColumnCoefficientDefect_eqv_replaceCoefficients_mul
    · intro source
      simpa only [factor,
        actualPositiveExpandedReceiverFiberSourceDensityCoefficient] using
        (positiveExpandedFourCellSourceReceiverFiberScaleDefect_eqv_calibration
          S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget source.1)
    · intro receiver
      simpa only [factor,
        actualPositiveExpandedReceiverFiberTargetDensityCoefficient] using
        (positiveExpandedFourCellTargetReceiverFiberScaleDefect_eqv_calibration
          S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget receiver)
  refine Q'.eqv_trans _
    ((connectedDensity.rowCoefficientDefect * factor +
        connectedDensity.posteriorColumnCoefficientDefect * factor) +
      disconnectedDensity.posteriorColumnCoefficientDefect * factor) _ ?_ ?_
  · simpa only [positivePhysicalConnectedSignedPosteriorDebtSum,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt,
      actualPositiveExpandedReceiverFiberScaleDefectConnectedPosteriorColumnDebt,
      actualPositiveExpandedReceiverFiberScaleDefectDisconnectedPosteriorColumnDebt,
      connectedScale, disconnectedScale] using
        Q'.add_eqv_congr' (Q'.add_eqv_congr' hrow hconnected) hdisconnected
  refine Q'.eqv_trans _
    ((connectedDensity.rowCoefficientDefect +
        connectedDensity.posteriorColumnCoefficientDefect) * factor +
      disconnectedDensity.posteriorColumnCoefficientDefect * factor) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_symm
        (Q'.add_mul_eqv connectedDensity.rowCoefficientDefect
          connectedDensity.posteriorColumnCoefficientDefect factor))
  simpa only [positivePhysicalConnectedSignedPosteriorDensityDebtSum,
    connectedDensity, disconnectedDensity] using
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          (connectedDensity.rowCoefficientDefect +
            connectedDensity.posteriorColumnCoefficientDefect)
          disconnectedDensity.posteriorColumnCoefficientDefect factor))

/-- The normalized signed posterior debt is not a new analytic object: it is
exactly the signed discrepancy between the concrete coarse Gibbs refresh and
the production physical kernel at the selected receiver column.  The proof
cancels the common strictly positive coarse partition square before applying
any absolute value. -/
theorem positivePhysicalConnectedSignedPosteriorDensityDebtSum_eqv_gibbsRefresh_sub_physicalKernel
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    positivePhysicalConnectedSignedPosteriorDensityDebtSum
        S hfineCutoff hcoarseCoupling M ≈
      coarseGibbsRefreshPushedRawFourCellCross
          S M.coarseRoot M.coarseTarget -
        pushedFaceRawFourCellCross
          (physicalKernel S hfineCutoff hcoarseCoupling)
          M.coarseRoot M.coarseTarget := by
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let density :=
    positivePhysicalConnectedSignedPosteriorDensityDebtSum
      S hfineCutoff hcoarseCoupling M
  let discrepancy :=
    coarseGibbsRefreshPushedRawFourCellCross
        S M.coarseRoot M.coarseTarget -
      pushedFaceRawFourCellCross
        (physicalKernel S hfineCutoff hcoarseCoupling)
        M.coarseRoot M.coarseTarget
  let rawDefect :=
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
  have hcoarseSquare : (0 : Q') < coarseSquare := by
    simpa only [coarseSquare] using coarsePhysicalPartitionSquare_pos S
  have hrawDensity : rawDefect ≈ density * coarseSquare := by
    refine Q'.eqv_trans _
      (positivePhysicalConnectedSignedPosteriorDebtSum
        S hfineCutoff hcoarseCoupling M) _ ?_ ?_
    · simpa only [rawDefect] using
        (positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_signedPosteriorDebtSum
          S hfineCutoff hcoarseCoupling M)
    · simpa only [density, coarseSquare] using
        (positivePhysicalConnectedSignedPosteriorDebtSum_eqv_density_mul_coarseSquare
          S hfineCutoff hcoarseCoupling M)
  have hrawDiscrepancy : rawDefect ≈ coarseSquare * discrepancy := by
    simpa only [rawDefect, coarseSquare, discrepancy] using
      (positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_refresh_sub_physicalKernel
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget)
  apply Q'.mul_left_cancel_of_pos hcoarseSquare
  refine Q'.eqv_trans _ (density * coarseSquare) _ ?_ ?_
  · exact Q'.mul_comm_eqv coarseSquare density
  exact Q'.eqv_trans _ rawDefect _
    (Q'.eqv_symm hrawDensity) hrawDiscrepancy

/-- Equivalently, the signed posterior-density sum is the fine partition
square times the single centered-cylinder remainder already isolated on the
Gibbs-refresh branch.  This is the direct join between the posterior-column
and connected-observable analytic frontiers. -/
theorem positivePhysicalConnectedSignedPosteriorDensityDebtSum_eqv_finePartitionSquare_mul_centeredRemainder
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    positivePhysicalConnectedSignedPosteriorDensityDebtSum
        S hfineCutoff hcoarseCoupling M ≈
      (S.fine.physicalPartition * S.fine.physicalPartition) *
        centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M := by
  exact Q'.eqv_trans _
    (coarseGibbsRefreshPushedRawFourCellCross
        S M.coarseRoot M.coarseTarget -
      pushedFaceRawFourCellCross
        (physicalKernel S hfineCutoff hcoarseCoupling)
        M.coarseRoot M.coarseTarget) _
    (positivePhysicalConnectedSignedPosteriorDensityDebtSum_eqv_gibbsRefresh_sub_physicalKernel
      S hfineCutoff hcoarseCoupling M)
    (coarseGibbsRefreshCross_sub_physicalKernelCross_eqv_finePartitionSquare_mul_centeredRemainder
      S hfineCutoff hcoarseCoupling M)

/-- The normalized cancellation-preserving analytic premise after exact
removal of the coarse partition square. -/
def PositivePhysicalConnectedSignedPosteriorDensityDebtCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') : Prop :=
  Q'.abs
      (positivePhysicalConnectedSignedPosteriorDensityDebtSum
        S hfineCutoff hcoarseCoupling M) ≤
    (kernelCeiling * (g * g)) *
      (S.fine.physicalPartition * S.fine.physicalPartition)

/-- The normalized signed posterior-density calibration is precisely the
existing Gibbs-refresh physical-kernel cross calibration at the face map's
selected coarse root and target. -/
theorem positiveSignedPosteriorDensityDebtCalibration_iff_gibbsRefreshPhysicalKernelCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') :
    PositivePhysicalConnectedSignedPosteriorDensityDebtCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling ↔
      CoarseGibbsRefreshPhysicalKernelCrossCalibration
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
        g kernelCeiling := by
  unfold PositivePhysicalConnectedSignedPosteriorDensityDebtCalibration
    CoarseGibbsRefreshPhysicalKernelCrossCalibration
  have hexact :=
    positivePhysicalConnectedSignedPosteriorDensityDebtSum_eqv_gibbsRefresh_sub_physicalKernel
      S hfineCutoff hcoarseCoupling M
  constructor
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_symm hexact))) h
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hexact)) h

/-- Exact positive-factor cancellation makes the dimensionless signed-density
premise equivalent to the physical signed posterior premise. -/
theorem positiveSignedPosteriorDensityDebtCalibration_iff_physical
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') :
    PositivePhysicalConnectedSignedPosteriorDensityDebtCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling ↔
      PositivePhysicalConnectedSignedPosteriorDebtCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  let factor :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let density :=
    positivePhysicalConnectedSignedPosteriorDensityDebtSum
      S hfineCutoff hcoarseCoupling M
  let physical :=
    positivePhysicalConnectedSignedPosteriorDebtSum
      S hfineCutoff hcoarseCoupling M
  let bound :=
    (kernelCeiling * (g * g)) *
      (S.fine.physicalPartition * S.fine.physicalPartition)
  have hfactor : (0 : Q') < factor :=
    coarsePhysicalPartitionSquare_pos S
  have hphysical : physical ≈ density * factor := by
    simpa only [factor, density, physical] using
      (positivePhysicalConnectedSignedPosteriorDebtSum_eqv_density_mul_coarseSquare
        S hfineCutoff hcoarseCoupling M)
  have habs : Q'.abs physical ≈ factor * Q'.abs density := by
    refine Q'.eqv_trans _ (Q'.abs (density * factor)) _
      (Q'.abs_eqv_congr hphysical) ?_
    refine Q'.eqv_trans _ (Q'.abs density * factor) _
      (YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right density
        (Q'.le_of_lt hfactor)) ?_
    exact Q'.mul_comm_eqv (Q'.abs density) factor
  have hbound :
      (kernelCeiling * (g * g)) *
          ((S.coarse.physicalPartition * S.coarse.physicalPartition) *
            (S.fine.physicalPartition * S.fine.physicalPartition)) ≈
        factor * bound := by
    unfold factor bound
    refine Q'.eqv_trans _
      (((kernelCeiling * (g * g)) *
          (S.coarse.physicalPartition * S.coarse.physicalPartition)) *
        (S.fine.physicalPartition * S.fine.physicalPartition)) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (kernelCeiling * (g * g))
          (S.coarse.physicalPartition * S.coarse.physicalPartition)
          (S.fine.physicalPartition * S.fine.physicalPartition))) ?_
    refine Q'.eqv_trans _
      (((S.coarse.physicalPartition * S.coarse.physicalPartition) *
          (kernelCeiling * (g * g))) *
        (S.fine.physicalPartition * S.fine.physicalPartition)) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_comm_eqv
          (kernelCeiling * (g * g))
          (S.coarse.physicalPartition * S.coarse.physicalPartition))) ?_
    exact Q'.mul_assoc_eqv
      (S.coarse.physicalPartition * S.coarse.physicalPartition)
      (kernelCeiling * (g * g))
      (S.fine.physicalPartition * S.fine.physicalPartition)
  unfold PositivePhysicalConnectedSignedPosteriorDensityDebtCalibration
    PositivePhysicalConnectedSignedPosteriorDebtCalibration
  change Q'.abs density ≤ bound ↔ Q'.abs physical ≤ _
  constructor
  · intro hdensity
    refine Q'.le_trans' _ (factor * Q'.abs density) _
      (Q'.le_of_eqv habs) ?_
    refine Q'.le_trans' _ (factor * bound) _
      (Q'.mul_le_mul_of_nonneg_left
        (Q'.abs density) bound factor hdensity (Q'.le_of_lt hfactor)) ?_
    exact Q'.le_of_eqv (Q'.eqv_symm hbound)
  · intro hphysicalBound
    apply Q'.le_of_mul_le_mul_left
      (c := factor) (a := Q'.abs density) (b := bound) _ hfactor
    refine Q'.le_trans' _ (Q'.abs physical) _
      (Q'.le_of_eqv (Q'.eqv_symm habs)) ?_
    exact Q'.le_trans' _ _ _ hphysicalBound (Q'.le_of_eqv hbound)

/-- The posterior-density calibration and the one-observable centered-
remainder calibration are the same analytic premise.  The intervening raw
column and partition factors cancel exactly, so neither direction changes
the quadratic constant. -/
theorem positiveSignedPosteriorDensityDebtCalibration_iff_connectedRemainder
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') :
    PositivePhysicalConnectedSignedPosteriorDensityDebtCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling ↔
      CoarseGibbsRefreshConnectedRemainderCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  exact Iff.trans
    (positiveSignedPosteriorDensityDebtCalibration_iff_physical
      S hfineCutoff hcoarseCoupling M g kernelCeiling)
    (Iff.trans
      (positiveSignedPosteriorDebtCalibration_iff_rawColumnCross
        S hfineCutoff hcoarseCoupling M g kernelCeiling)
      (Iff.symm
        (coarseGibbsRefreshConnectedRemainderCalibration_iff_rawColumnCross
          S hfineCutoff hcoarseCoupling M g kernelCeiling)))

/-- After exact coarse-square cancellation, the dimensionless signed
posterior-density estimate is still equivalent to the fully raw signed
source-average calibration, with the same quadratic constant. -/
theorem positiveSignedPosteriorDensityDebtCalibration_iff_fullyRawSignedSourceAverage
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') :
    PositivePhysicalConnectedSignedPosteriorDensityDebtCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling ↔
      PositivePhysicalConnectedFullyRawSignedSourceAverageCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  exact Iff.trans
    (positiveSignedPosteriorDensityDebtCalibration_iff_physical
      S hfineCutoff hcoarseCoupling M g kernelCeiling)
    (positiveSignedPosteriorDebtCalibration_iff_fullyRawSignedSourceAverage
      S hfineCutoff hcoarseCoupling M g kernelCeiling)

/-- A bound on the exact coarse-square-cancelled posterior budget gives the
signed raw-column calibration with no cardinality factor and no loss in the
relative constant. -/
theorem positiveExpandedAssignmentSaturatedRawColumnCrossCalibration_of_splitPosteriorColumn
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) (relative : Q')
    (hposterior :
      actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
          schedule scale ≤
        relative *
          coarseSquareCancelledCovarianceDenominator
            (schedule.scalePair scale)) :
    PositiveExpandedAssignmentSaturatedRawColumnCrossCalibration
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget relative := by
  let S := schedule.scalePair scale
  let M := schedule.faceMap scale
  let rawColumn :=
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
      S rfl (schedule.effectiveCoupling_pos scale)
      M.coarseRoot M.coarseTarget
  let receiverFiber :=
    actualPositiveExpandedReceiverFiberScaleDefectCross
      S rfl (schedule.effectiveCoupling_pos scale)
      M.coarseRoot M.coarseTarget
  let posterior :=
    actualPositiveExpandedReceiverFiberScaleDefectCoarseSquareCancelledSplitPosteriorColumnBudget
      schedule scale
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let fineSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  let fullPosterior :=
    actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnL1
      S rfl (schedule.effectiveCoupling_pos scale)
      M.coarseRoot M.coarseTarget M.coarseTarget_mem
  have hrawFiber : rawColumn ≈ receiverFiber := by
    simpa only [S, M, rawColumn, receiverFiber] using
      (positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_receiverFiber
        S rfl (schedule.effectiveCoupling_pos scale) M)
  have hcross : Q'.abs rawColumn ≤ fullPosterior :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hrawFiber))
      (by
        simpa only [S, M, receiverFiber, fullPosterior] using
          (actualPositiveExpandedReceiverFiberScaleDefectCross_abs_le_splitPosteriorColumnL1
            S rfl (schedule.effectiveCoupling_pos scale)
            M.coarseRoot M.coarseTarget M.coarseTarget_mem))
  have hfullPosterior : fullPosterior ≈ coarseSquare * posterior := by
    simpa only [S, M, coarseSquare, posterior, fullPosterior] using
      (actualPositiveExpandedReceiverFiberScaleDefectSplitPosteriorColumnL1_eqv_coarseSquare_mul_cancelled
        schedule scale)
  have hposterior' : posterior ≤ relative * fineSquare := by
    simpa only [S, posterior, fineSquare,
      coarseSquareCancelledCovarianceDenominator] using hposterior
  have hcoarseNonnegative : (0 : Q') ≤ coarseSquare :=
    Q'.le_of_lt
      (Q'.mul_pos
        (slabParametricKPhysicalPartition_pos
          S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)
        (slabParametricKPhysicalPartition_pos
          S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent))
  have hscaled :
      coarseSquare * posterior ≤
        coarseSquare * (relative * fineSquare) :=
    Q'.mul_le_mul_of_nonneg_left posterior (relative * fineSquare)
      coarseSquare hposterior' hcoarseNonnegative
  unfold PositiveExpandedAssignmentSaturatedRawColumnCrossCalibration
  refine Q'.le_trans' _ fullPosterior _ ?_ ?_
  · simpa only [S, M, rawColumn] using hcross
  refine Q'.le_trans' _ (coarseSquare * posterior) _
    (Q'.le_of_eqv hfullPosterior) ?_
  refine Q'.le_trans' _ (coarseSquare * (relative * fineSquare)) _
    hscaled (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ ((coarseSquare * relative) * fineSquare) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv coarseSquare relative fineSquare)) ?_
  refine Q'.eqv_trans _ ((relative * coarseSquare) * fineSquare) _
    (Q'.mul_eqv_congr_right _ _ fineSquare
      (Q'.mul_comm_eqv coarseSquare relative)) ?_
  simpa only [S, coarseSquare, fineSquare] using
    (Q'.mul_assoc_eqv relative coarseSquare fineSquare)

/-! ## 4. Matched-AF posterior control supplies the fully raw aggregate -/

namespace MatchedShiftedAFSplitPosteriorColumnQuadraticCostControl

variable
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {C : AFTrajectoryCertificate}
    {coupling : Nat → Q'}
    {coupling_pos : ∀ scale, (0 : Q') < coupling scale}
    {coupling_le_window : ∀ scale, coupling scale ≤ law.g₁}
    {identification : ShiftedAFTrajectoryIdentification C coupling}
    {nested : NestedCutoffOneFaceGeometry}

/-- The existing posterior three-budget field is sufficient to populate the
cancellation-preserving raw-column control. -/
def toRawColumnCrossQuadraticCostControl
    (control : MatchedShiftedAFSplitPosteriorColumnQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested) :
    MatchedShiftedAFSpinFourRawColumnCrossQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested where
  start := control.start
  spacingFloor := control.spacingFloor
  spacingFloor_pos := control.spacingFloor_pos
  mismatchQuadraticCeiling := control.mismatchQuadraticCeiling
  mismatchQuadraticCeiling_pos := control.mismatchQuadraticCeiling_pos
  rawColumnCrossQuadraticCeiling := control.connectedQuadraticCeiling
  rawColumnCrossQuadraticCeiling_pos := control.connectedQuadraticCeiling_pos
  spacingQuadratic_lower := control.spacingQuadratic_lower
  rawMismatch_quadratic_le := control.rawMismatch_quadratic_le
  rawColumnCross_quadratic := fun scale hscale => by
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    apply
      positiveExpandedAssignmentSaturatedRawColumnCrossCalibration_of_splitPosteriorColumn
        schedule scale
        (control.connectedQuadraticCeiling *
          (coupling scale * coupling scale))
    simpa only [schedule] using
      (control.posteriorColumn_quadratic_le scale hscale)

/-- The posterior three-budget control therefore supplies the exact signed
fully raw source-average calibration at every controlled scale. -/
theorem fullyRawSignedSourceAverage_quadratic
    (control : MatchedShiftedAFSplitPosteriorColumnQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested)
    (scale : Nat) (hscale : control.start ≤ scale) :
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let M := schedule.faceMap scale
    PositivePhysicalConnectedFullyRawSignedSourceAverageCalibration
      S rfl (schedule.effectiveCoupling_pos scale) M
        (coupling scale) control.connectedQuadraticCeiling := by
  simpa only [toRawColumnCrossQuadraticCostControl] using
    (YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedFullyRawEventCrossAverage.MatchedShiftedAFSpinFourRawColumnCrossQuadraticCostControl.fullyRawSignedSourceAverage_quadratic
      (toRawColumnCrossQuadraticCostControl control) scale hscale)

end MatchedShiftedAFSplitPosteriorColumnQuadraticCostControl

#print axioms positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_receiverFiber
#print axioms positivePhysicalConnectedSignedPosteriorDebtSum
#print axioms positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_signedPosteriorDebtSum
#print axioms PositivePhysicalConnectedSignedPosteriorDebtCalibration
#print axioms positiveSignedPosteriorDebtCalibration_iff_rawColumnCross
#print axioms positiveSignedPosteriorDebtCalibration_iff_fullyRawSignedSourceAverage
#print axioms positivePhysicalConnectedSignedPosteriorDensityDebtSum
#print axioms positivePhysicalConnectedSignedPosteriorDebtSum_eqv_density_mul_coarseSquare
#print axioms positivePhysicalConnectedSignedPosteriorDensityDebtSum_eqv_gibbsRefresh_sub_physicalKernel
#print axioms positivePhysicalConnectedSignedPosteriorDensityDebtSum_eqv_finePartitionSquare_mul_centeredRemainder
#print axioms PositivePhysicalConnectedSignedPosteriorDensityDebtCalibration
#print axioms positiveSignedPosteriorDensityDebtCalibration_iff_gibbsRefreshPhysicalKernelCross
#print axioms positiveSignedPosteriorDensityDebtCalibration_iff_physical
#print axioms positiveSignedPosteriorDensityDebtCalibration_iff_connectedRemainder
#print axioms positiveSignedPosteriorDensityDebtCalibration_iff_fullyRawSignedSourceAverage
#print axioms positiveExpandedAssignmentSaturatedRawColumnCrossCalibration_of_splitPosteriorColumn
#print axioms MatchedShiftedAFSplitPosteriorColumnQuadraticCostControl.toRawColumnCrossQuadraticCostControl
#print axioms MatchedShiftedAFSplitPosteriorColumnQuadraticCostControl.fullyRawSignedSourceAverage_quadratic

end YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedFullyRawPosteriorColumn
