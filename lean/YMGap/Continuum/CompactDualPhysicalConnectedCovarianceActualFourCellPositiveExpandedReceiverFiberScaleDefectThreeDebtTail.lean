/-
# Compile separate receiver row, edge, and column debts

The partition-scaled receiver-fiber coefficient cross has already been split
exactly into row-retention, successful-edge variation, and realized-column
debts, conditional on a complete-cell aggregate posterior.  This module makes
the next analytic seam explicit: three independent linear-in-spacing bounds
compile, without coefficient loss, to the existing connected covariance tail.

This is a conditional reduction.  It neither constructs the schedule-level
aggregate posterior nor proves any of the three bounds.  The fixed-anchor
guarded aggregate theorem is not an inhabitant of the schedule-level posterior
field below.  Consequently no refining-scale estimate, continuum measure,
OS/GNS reconstruction, Hamiltonian gap, or Clay conclusion is claimed.

Constructive contract: exact rational identities, inequalities, and
Type-valued witnesses only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectTransport
import YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectThreeDebtTail

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectTransport
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule

local infix:50 " ≈ " => Q'.eqv

private theorem add_three_scaled_eqv
    (row edge column spacing denominator : Q') :
    ((row * spacing) * denominator + (edge * spacing) * denominator) +
        (column * spacing) * denominator ≈
      (((row + edge) + column) * spacing) * denominator := by
  have hpair :
      (row * spacing) * denominator + (edge * spacing) * denominator ≈
        (row * spacing + edge * spacing) * denominator :=
    Q'.eqv_symm
      (Q'.add_mul_eqv (row * spacing) (edge * spacing) denominator)
  have hthree :
      ((row * spacing) * denominator + (edge * spacing) * denominator) +
          (column * spacing) * denominator ≈
        ((row * spacing + edge * spacing) + column * spacing) * denominator := by
    refine Q'.eqv_trans _
      ((row * spacing + edge * spacing) * denominator +
        (column * spacing) * denominator) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _ hpair
    · exact Q'.eqv_symm
        (Q'.add_mul_eqv
          (row * spacing + edge * spacing) (column * spacing) denominator)
  have hinside :
      (row * spacing + edge * spacing) + column * spacing ≈
        ((row + edge) + column) * spacing := by
    have hpairSpacing :
        row * spacing + edge * spacing ≈ (row + edge) * spacing :=
      Q'.eqv_symm (Q'.add_mul_eqv row edge spacing)
    refine Q'.eqv_trans _
      ((row + edge) * spacing + column * spacing) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _ hpairSpacing
    · exact Q'.eqv_symm
        (Q'.add_mul_eqv (row + edge) column spacing)
  exact Q'.eqv_trans _
    (((row * spacing + edge * spacing) + column * spacing) * denominator) _
    hthree
    (Q'.mul_eqv_congr_right _ _ denominator hinside)

namespace PhysicalObservableRefinementSchedule

/-- Three independent analytic debts for the conditional schedule-level
receiver transport.  The posterior is supplied as Type-level data only on the
eventual tail where the estimates are asserted. -/
structure ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail
    (schedule : PhysicalObservableRefinementSchedule) : Type 2 where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  rowCeiling : Q'
  rowCeiling_pos : (0 : Q') < rowCeiling
  edgeCeiling : Q'
  edgeCeiling_pos : (0 : Q') < edgeCeiling
  columnCeiling : Q'
  columnCeiling_pos : (0 : Q') < columnCeiling
  mismatch_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget schedule scale ≤
      mismatchCeiling * schedule.spacing.spacing scale
  posterior : ∀ scale : Nat, start ≤ scale →
    SlabObservablePairedAggregatePosteriorTransport
      (schedule.scalePair scale).coarse
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
  rowDebt_le : ∀ scale : Nat, ∀ hscale : start ≤ scale,
    Q'.abs
        (((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
          actualPositiveExpandedReceiverFiberScaleDefectRowDebt
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget
            (posterior scale hscale)) ≤
      (rowCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)
  edgeDebt_le : ∀ scale : Nat, ∀ hscale : start ≤ scale,
    Q'.abs
        (((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
          actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget
            (posterior scale hscale)) ≤
      (edgeCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)
  columnDebt_le : ∀ scale : Nat, ∀ hscale : start ≤ scale,
    Q'.abs
        (((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
          actualPositiveExpandedReceiverFiberScaleDefectColumnDebt
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget
            (posterior scale hscale)) ≤
      (columnCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)

namespace ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

def connectedCeiling
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail
        schedule) : Q' :=
  (tail.rowCeiling + tail.edgeCeiling) + tail.columnCeiling

theorem connectedCeiling_pos
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail
        schedule) :
    (0 : Q') < tail.connectedCeiling := by
  unfold connectedCeiling
  exact Q'.add_pos
    (Q'.add_pos tail.rowCeiling_pos tail.edgeCeiling_pos)
    tail.columnCeiling_pos

/-- The partition-scaled cross inherits the exact three-debt split. -/
theorem scaledCross_eqv_threeDebts
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail
        schedule)
    (scale : Nat) (hscale : tail.start ≤ scale) :
    let factor :=
      (schedule.scalePair scale).coarse.physicalPartition *
        (schedule.scalePair scale).fine.physicalPartition
    let data := tail.posterior scale hscale
    factor *
        actualPositiveExpandedReceiverFiberScaleDefectCross
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget ≈
      (factor *
          actualPositiveExpandedReceiverFiberScaleDefectRowDebt
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget data +
        factor *
          actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget data) +
        factor *
          actualPositiveExpandedReceiverFiberScaleDefectColumnDebt
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget data := by
  dsimp only
  let factor :=
    (schedule.scalePair scale).coarse.physicalPartition *
      (schedule.scalePair scale).fine.physicalPartition
  let row :=
    actualPositiveExpandedReceiverFiberScaleDefectRowDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (tail.posterior scale hscale)
  let edge :=
    actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (tail.posterior scale hscale)
  let column :=
    actualPositiveExpandedReceiverFiberScaleDefectColumnDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (tail.posterior scale hscale)
  have hsplit :=
    actualPositiveExpandedReceiverFiberScaleDefectCross_eqv_threeDebts
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (tail.posterior scale hscale)
  refine Q'.eqv_trans _ (factor * ((row + edge) + column)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left factor _ _ (by
      simpa only [row, edge, column] using hsplit)
  · refine Q'.eqv_trans _ (factor * (row + edge) + factor * column) _
      (Q'.mul_add_eqv factor (row + edge) column) ?_
    exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_add_eqv factor row edge)

/-- Three independent scaled debt bounds imply the combined scaled cross
bound with coefficient `rowCeiling + edgeCeiling + columnCeiling`. -/
theorem scaledCross_abs_le_connectedCeiling
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail
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
  let data := tail.posterior scale hscale
  let row :=
    actualPositiveExpandedReceiverFiberScaleDefectRowDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget data
  let edge :=
    actualPositiveExpandedReceiverFiberScaleDefectEdgeDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget data
  let column :=
    actualPositiveExpandedReceiverFiberScaleDefectColumnDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget data
  have htriangle :
      Q'.abs
          (factor *
            actualPositiveExpandedReceiverFiberScaleDefectCross
              (schedule.scalePair scale) rfl
              (schedule.effectiveCoupling_pos scale)
              (schedule.faceMap scale).coarseRoot
              (schedule.faceMap scale).coarseTarget) ≤
        (Q'.abs (factor * row) + Q'.abs (factor * edge)) +
          Q'.abs (factor * column) := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr
          (tail.scaledCross_eqv_threeDebts scale hscale))) ?_
    exact Q'.le_trans' _ _ _
      (Q'.abs_add_le' (factor * row + factor * edge) (factor * column))
      (Q'.add_le_add
        (Q'.abs_add_le' (factor * row) (factor * edge))
        (Q'.le_refl' (Q'.abs (factor * column))))
  have hdebts :
      (Q'.abs (factor * row) + Q'.abs (factor * edge)) +
          Q'.abs (factor * column) ≤
        ((tail.rowCeiling * schedule.spacing.spacing scale) *
            connectedCovarianceRawCrossDenominator (schedule.scalePair scale) +
          (tail.edgeCeiling * schedule.spacing.spacing scale) *
            connectedCovarianceRawCrossDenominator (schedule.scalePair scale)) +
          (tail.columnCeiling * schedule.spacing.spacing scale) *
            connectedCovarianceRawCrossDenominator (schedule.scalePair scale) := by
    exact Q'.add_le_add
      (Q'.add_le_add
        (by simpa only [factor, row, data] using tail.rowDebt_le scale hscale)
        (by simpa only [factor, edge, data] using tail.edgeDebt_le scale hscale))
      (by simpa only [factor, column, data] using
        tail.columnDebt_le scale hscale)
  exact Q'.le_trans' _ _ _ htriangle
    (Q'.le_trans' _ _ _ hdebts
      (Q'.le_of_eqv
        (add_three_scaled_eqv
          tail.rowCeiling tail.edgeCeiling tail.columnCeiling
          (schedule.spacing.spacing scale)
          (connectedCovarianceRawCrossDenominator
            (schedule.scalePair scale)))))

/-- Compile the three analytic debts to the existing one-cross producer. -/
def toScaleDefectSeparatedLinearRawTransportTail
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail
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
      ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail
        schedule) :
    ConnectedSeparatedLinearRawTransportTail schedule :=
  tail.toScaleDefectSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail

theorem combinedCeiling_eq
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail
        schedule) :
    tail.toConnectedSeparatedLinearRawTransportTail.combinedCeiling =
      tail.mismatchCeiling +
        ((tail.rowCeiling + tail.edgeCeiling) + tail.columnCeiling) :=
  rfl

/-- Final covariance consumer for separate receiver row, edge, and column
debts. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail
        schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      tail.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  tail.toConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail
end PhysicalObservableRefinementSchedule

#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail.connectedCeiling_pos
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail.scaledCross_eqv_threeDebts
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail.scaledCross_abs_le_connectedCeiling
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail.toScaleDefectSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectThreeDebtTail
