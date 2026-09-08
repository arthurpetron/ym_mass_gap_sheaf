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

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration
import YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectThreeDebtTail

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectCalibration
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectEdgeVariation
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

/-! ## Density-variation refinement of the edge producer -/

/-- A sharper three-debt input in which the edge estimate is stated on the
literal receiver-density-variation `l1` budget.  Row and column estimates are
unchanged; the exact edge cancellation compiles this structure to the direct
three-debt tail above. -/
structure ActualPositiveExpandedReceiverFiberScaleDefectDensityVariationLinearRawTransportTail
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
  edgeDensityVariationL1_le : ∀ scale : Nat, ∀ hscale : start ≤ scale,
    Q'.abs
          ((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
        actualPositiveExpandedReceiverFiberScaleDefectEdgeDensityVariationL1
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (posterior scale hscale) ≤
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

namespace ActualPositiveExpandedReceiverFiberScaleDefectDensityVariationLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

/-- The literal density-variation edge estimate implies the signed scaled-edge
estimate required by the direct three-debt compiler. -/
def toThreeDebtLinearRawTransportTail
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectDensityVariationLinearRawTransportTail
        schedule) :
    ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail
      schedule where
  start := tail.start
  mismatchCeiling := tail.mismatchCeiling
  mismatchCeiling_pos := tail.mismatchCeiling_pos
  rowCeiling := tail.rowCeiling
  rowCeiling_pos := tail.rowCeiling_pos
  edgeCeiling := tail.edgeCeiling
  edgeCeiling_pos := tail.edgeCeiling_pos
  columnCeiling := tail.columnCeiling
  columnCeiling_pos := tail.columnCeiling_pos
  mismatch_le := tail.mismatch_le
  posterior := tail.posterior
  rowDebt_le := tail.rowDebt_le
  edgeDebt_le := fun scale hscale => by
    let factor :=
      (schedule.scalePair scale).coarse.physicalPartition *
        (schedule.scalePair scale).fine.physicalPartition
    exact Q'.le_trans' _ _ _
      (actualPositiveExpandedReceiverFiberScaleDefect_scaledEdgeDebt_abs_le_densityVariationL1
        (schedule.scalePair scale) rfl
        (schedule.effectiveCoupling_pos scale)
        (schedule.faceMap scale).coarseRoot
        (schedule.faceMap scale).coarseTarget
        (tail.posterior scale hscale) factor)
      (by simpa only [factor] using
        tail.edgeDensityVariationL1_le scale hscale)
  columnDebt_le := tail.columnDebt_le

def toConnectedSeparatedLinearRawTransportTail
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectDensityVariationLinearRawTransportTail
        schedule) :
    ConnectedSeparatedLinearRawTransportTail schedule :=
  tail.toThreeDebtLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail

theorem combinedCeiling_eq
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectDensityVariationLinearRawTransportTail
        schedule) :
    tail.toConnectedSeparatedLinearRawTransportTail.combinedCeiling =
      tail.mismatchCeiling +
        ((tail.rowCeiling + tail.edgeCeiling) + tail.columnCeiling) :=
  rfl

/-- Final matched covariance consumer with the edge producer stated directly
as a receiver-fiber density-variation `l1` estimate. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectDensityVariationLinearRawTransportTail
        schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      tail.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  tail.toConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end ActualPositiveExpandedReceiverFiberScaleDefectDensityVariationLinearRawTransportTail

/-! ## Fully receiver-density-calibrated producer -/

/-- The three analytic debt hypotheses stated on their literal finite
receiver-density budgets: row and column partition-density calibration, and
successful-edge density variation.  These hypotheses are sufficient inputs;
the structure does not assert that any of the three budgets is uniformly
linear in the lattice spacing. -/
structure ActualPositiveExpandedReceiverFiberScaleDefectCalibratedLinearRawTransportTail
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
  rowCalibrationL1_le : ∀ scale : Nat, ∀ hscale : start ≤ scale,
    Q'.abs
          ((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
        actualPositiveExpandedReceiverFiberScaleDefectRowCalibrationL1
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (posterior scale hscale) ≤
      (rowCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)
  edgeDensityVariationL1_le : ∀ scale : Nat, ∀ hscale : start ≤ scale,
    Q'.abs
          ((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
        actualPositiveExpandedReceiverFiberScaleDefectEdgeDensityVariationL1
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (posterior scale hscale) ≤
      (edgeCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)
  columnCalibrationL1_le : ∀ scale : Nat, ∀ hscale : start ≤ scale,
    Q'.abs
          ((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
        actualPositiveExpandedReceiverFiberScaleDefectColumnCalibrationL1
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget
          (posterior scale hscale) ≤
      (columnCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator (schedule.scalePair scale)

namespace ActualPositiveExpandedReceiverFiberScaleDefectCalibratedLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

/-- Exact row/edge/column calibration inequalities compile to the preceding
density-variation producer. -/
def toDensityVariationLinearRawTransportTail
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectCalibratedLinearRawTransportTail
        schedule) :
    ActualPositiveExpandedReceiverFiberScaleDefectDensityVariationLinearRawTransportTail
      schedule where
  start := tail.start
  mismatchCeiling := tail.mismatchCeiling
  mismatchCeiling_pos := tail.mismatchCeiling_pos
  rowCeiling := tail.rowCeiling
  rowCeiling_pos := tail.rowCeiling_pos
  edgeCeiling := tail.edgeCeiling
  edgeCeiling_pos := tail.edgeCeiling_pos
  columnCeiling := tail.columnCeiling
  columnCeiling_pos := tail.columnCeiling_pos
  mismatch_le := tail.mismatch_le
  posterior := tail.posterior
  rowDebt_le := fun scale hscale => by
    let factor :=
      (schedule.scalePair scale).coarse.physicalPartition *
        (schedule.scalePair scale).fine.physicalPartition
    exact Q'.le_trans' _ _ _
      (actualPositiveExpandedReceiverFiberScaleDefect_scaledRowDebt_abs_le_calibrationL1
        (schedule.scalePair scale) rfl
        (schedule.effectiveCoupling_pos scale)
        (schedule.faceMap scale).coarseRoot
        (schedule.faceMap scale).coarseTarget
        (tail.posterior scale hscale) factor)
      (by simpa only [factor] using tail.rowCalibrationL1_le scale hscale)
  edgeDensityVariationL1_le := tail.edgeDensityVariationL1_le
  columnDebt_le := fun scale hscale => by
    let factor :=
      (schedule.scalePair scale).coarse.physicalPartition *
        (schedule.scalePair scale).fine.physicalPartition
    exact Q'.le_trans' _ _ _
      (actualPositiveExpandedReceiverFiberScaleDefect_scaledColumnDebt_abs_le_calibrationL1
        (schedule.scalePair scale) rfl
        (schedule.effectiveCoupling_pos scale)
        (schedule.faceMap scale).coarseRoot
        (schedule.faceMap scale).coarseTarget
        (tail.posterior scale hscale) factor)
      (by simpa only [factor] using tail.columnCalibrationL1_le scale hscale)

def toConnectedSeparatedLinearRawTransportTail
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectCalibratedLinearRawTransportTail
        schedule) :
    ConnectedSeparatedLinearRawTransportTail schedule :=
  tail.toDensityVariationLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail

theorem combinedCeiling_eq
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectCalibratedLinearRawTransportTail
        schedule) :
    tail.toConnectedSeparatedLinearRawTransportTail.combinedCeiling =
      tail.mismatchCeiling +
        ((tail.rowCeiling + tail.edgeCeiling) + tail.columnCeiling) :=
  rfl

/-- Final matched covariance consumer with all three receiver debts stated on
literal finite receiver-density `l1` budgets. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail :
      ActualPositiveExpandedReceiverFiberScaleDefectCalibratedLinearRawTransportTail
        schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      tail.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  tail.toConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end ActualPositiveExpandedReceiverFiberScaleDefectCalibratedLinearRawTransportTail
end PhysicalObservableRefinementSchedule

#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail.connectedCeiling_pos
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail.scaledCross_eqv_threeDebts
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail.scaledCross_abs_le_connectedCeiling
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail.toScaleDefectSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectThreeDebtLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectDensityVariationLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectDensityVariationLinearRawTransportTail.toThreeDebtLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectDensityVariationLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectDensityVariationLinearRawTransportTail.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectDensityVariationLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectCalibratedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectCalibratedLinearRawTransportTail.toDensityVariationLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectCalibratedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectCalibratedLinearRawTransportTail.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectCalibratedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectThreeDebtTail
