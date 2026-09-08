/-
# Normalize the explicit split-sector transport costs

The split receiver transport has reduced the complete coefficient cross to
five literal finite density budgets.  This module divides the two remaining
schedule costs by their exact physical scales:

* the raw mismatch cost is divided by the positive lattice spacing;
* the sum of the five scaled density budgets is divided by the product of the
  positive lattice spacing and the positive covariance denominator.

Multiplying either normalized cost back by its denominator is exact.  Thus a
uniform bound on these two explicit sequences supplies the existing linear
raw-transport tail.  No such uniform bound is inhabited here.  In particular,
this module proves no physical gap floor, continuum measure, OS/GNS
reconstruction, Hamiltonian gap, or Clay conclusion.

Constructive contract: exact rational identities, inequalities, and
Type-valued witnesses only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransportCalibration

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCost

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransport
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitTransportCalibration
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem scaled_abs_le_local
    (factor debt budget : Q')
    (hdebt : Q'.abs debt ≤ budget) :
    Q'.abs (factor * debt) ≤ Q'.abs factor * budget := by
  exact Q'.le_trans' _ _ _
    (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le factor debt)
    (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.abs factor)
      hdebt (Q'.abs_nonneg factor))

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

/-! ## 1. One combined literal density budget -/

/-- Sum of the five surviving split-sector density budgets after the exact
physical partition scaling used by the covariance receiver. -/
def actualPositiveExpandedReceiverFiberScaleDefectSplitDensityBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  let S := schedule.scalePair scale
  let factor := Q'.abs
    (S.coarse.physicalPartition * S.fine.physicalPartition)
  let root := (schedule.faceMap scale).coarseRoot
  let target := (schedule.faceMap scale).coarseTarget
  let htarget := (schedule.faceMap scale).coarseTarget_mem
  ((factor *
          actualPositiveExpandedReceiverFiberScaleDefectConnectedRowCalibrationL1
            S rfl (schedule.effectiveCoupling_pos scale)
            root target htarget +
        factor *
          actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDensityVariationL1
            S rfl (schedule.effectiveCoupling_pos scale)
            root target htarget) +
      factor *
        actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnCalibrationL1
          S rfl (schedule.effectiveCoupling_pos scale)
          root target htarget) +
    (factor *
          actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDensityVariationL1
            S rfl (schedule.effectiveCoupling_pos scale)
            root target htarget +
      factor *
        actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnCalibrationL1
          S rfl (schedule.effectiveCoupling_pos scale)
          root target htarget)

/-- The exact five-debt identity commutes with the physical partition factor,
without introducing any schedule hypothesis. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectScaledCross_eqv_splitFiveDebts
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    let factor :=
      (schedule.scalePair scale).coarse.physicalPartition *
        (schedule.scalePair scale).fine.physicalPartition
    factor *
        actualPositiveExpandedReceiverFiberScaleDefectCross
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale).coarseRoot
          (schedule.faceMap scale).coarseTarget ≈
      (((factor *
              actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
                (schedule.scalePair scale) rfl
                (schedule.effectiveCoupling_pos scale)
                (schedule.faceMap scale).coarseRoot
                (schedule.faceMap scale).coarseTarget
                (schedule.faceMap scale).coarseTarget_mem +
            factor *
              actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt
                (schedule.scalePair scale) rfl
                (schedule.effectiveCoupling_pos scale)
                (schedule.faceMap scale).coarseRoot
                (schedule.faceMap scale).coarseTarget
                (schedule.faceMap scale).coarseTarget_mem) +
          factor *
            actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt
              (schedule.scalePair scale) rfl
              (schedule.effectiveCoupling_pos scale)
              (schedule.faceMap scale).coarseRoot
              (schedule.faceMap scale).coarseTarget
              (schedule.faceMap scale).coarseTarget_mem) +
        (factor *
              actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt
                (schedule.scalePair scale) rfl
                (schedule.effectiveCoupling_pos scale)
                (schedule.faceMap scale).coarseRoot
                (schedule.faceMap scale).coarseTarget
                (schedule.faceMap scale).coarseTarget_mem +
          factor *
            actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt
              (schedule.scalePair scale) rfl
              (schedule.effectiveCoupling_pos scale)
              (schedule.faceMap scale).coarseRoot
              (schedule.faceMap scale).coarseTarget
              (schedule.faceMap scale).coarseTarget_mem)) := by
  dsimp only
  let factor :=
    (schedule.scalePair scale).coarse.physicalPartition *
      (schedule.scalePair scale).fine.physicalPartition
  let connectedRow :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  let connectedEdge :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  let connectedColumn :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  let disconnectedEdge :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  let disconnectedColumn :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  have hsplit :=
    actualPositiveExpandedReceiverFiberScaleDefectCross_eqv_splitFiveDebts
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  refine Q'.eqv_trans _
    (factor *
      (((connectedRow + connectedEdge) + connectedColumn) +
        (disconnectedEdge + disconnectedColumn))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left factor _ _ (by
      simpa only [connectedRow, connectedEdge, connectedColumn,
        disconnectedEdge, disconnectedColumn] using hsplit)
  · refine Q'.eqv_trans _
      (factor * ((connectedRow + connectedEdge) + connectedColumn) +
        factor * (disconnectedEdge + disconnectedColumn)) _
      (Q'.mul_add_eqv factor
        ((connectedRow + connectedEdge) + connectedColumn)
        (disconnectedEdge + disconnectedColumn)) ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_trans _
        (factor * (connectedRow + connectedEdge) +
          factor * connectedColumn) _
        (Q'.mul_add_eqv factor (connectedRow + connectedEdge)
          connectedColumn)
        (Q'.add_eqv_congr_right _ _ _
          (Q'.mul_add_eqv factor connectedRow connectedEdge)))
      (Q'.mul_add_eqv factor disconnectedEdge disconnectedColumn)

/-- The complete scaled receiver cross is bounded by the single explicit sum
of its five literal density budgets. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectScaledCross_abs_le_splitDensityBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    Q'.abs
        (((schedule.scalePair scale).coarse.physicalPartition *
            (schedule.scalePair scale).fine.physicalPartition) *
          actualPositiveExpandedReceiverFiberScaleDefectCross
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget) ≤
      actualPositiveExpandedReceiverFiberScaleDefectSplitDensityBudget
        schedule scale := by
  let factor :=
    (schedule.scalePair scale).coarse.physicalPartition *
      (schedule.scalePair scale).fine.physicalPartition
  let connectedRow :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  let connectedEdge :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  let connectedColumn :=
    actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  let disconnectedEdge :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  let disconnectedColumn :=
    actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale).coarseRoot
      (schedule.faceMap scale).coarseTarget
      (schedule.faceMap scale).coarseTarget_mem
  have htriangle :
      Q'.abs
          (factor *
            actualPositiveExpandedReceiverFiberScaleDefectCross
              (schedule.scalePair scale) rfl
              (schedule.effectiveCoupling_pos scale)
              (schedule.faceMap scale).coarseRoot
              (schedule.faceMap scale).coarseTarget) ≤
        ((Q'.abs (factor * connectedRow) +
            Q'.abs (factor * connectedEdge)) +
          Q'.abs (factor * connectedColumn)) +
        (Q'.abs (factor * disconnectedEdge) +
          Q'.abs (factor * disconnectedColumn)) := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr
          (actualPositiveExpandedReceiverFiberScaleDefectScaledCross_eqv_splitFiveDebts
            schedule scale))) ?_
    exact Q'.le_trans' _ _ _
      (Q'.abs_add_le'
        ((factor * connectedRow + factor * connectedEdge) +
          factor * connectedColumn)
        (factor * disconnectedEdge + factor * disconnectedColumn))
      (Q'.add_le_add
        (Q'.le_trans' _ _ _
          (Q'.abs_add_le'
            (factor * connectedRow + factor * connectedEdge)
            (factor * connectedColumn))
          (Q'.add_le_add
            (Q'.abs_add_le'
              (factor * connectedRow) (factor * connectedEdge))
            (Q'.le_refl' (Q'.abs (factor * connectedColumn)))))
        (Q'.abs_add_le'
          (factor * disconnectedEdge) (factor * disconnectedColumn)))
  have hdebts :
      ((Q'.abs (factor * connectedRow) +
          Q'.abs (factor * connectedEdge)) +
        Q'.abs (factor * connectedColumn)) +
        (Q'.abs (factor * disconnectedEdge) +
          Q'.abs (factor * disconnectedColumn)) ≤
      actualPositiveExpandedReceiverFiberScaleDefectSplitDensityBudget
        schedule scale := by
    exact Q'.add_le_add
      (Q'.add_le_add
        (Q'.add_le_add
          (scaled_abs_le_local factor _ _
            (actualPositiveExpandedReceiverFiberScaleDefectConnectedRowDebt_abs_le_calibrationL1
              (schedule.scalePair scale) rfl
              (schedule.effectiveCoupling_pos scale)
              (schedule.faceMap scale).coarseRoot
              (schedule.faceMap scale).coarseTarget
              (schedule.faceMap scale).coarseTarget_mem))
          (scaled_abs_le_local factor _ _
            (actualPositiveExpandedReceiverFiberScaleDefectConnectedEdgeDebt_abs_le_densityVariationL1
              (schedule.scalePair scale) rfl
              (schedule.effectiveCoupling_pos scale)
              (schedule.faceMap scale).coarseRoot
              (schedule.faceMap scale).coarseTarget
              (schedule.faceMap scale).coarseTarget_mem)))
        (scaled_abs_le_local factor _ _
          (actualPositiveExpandedReceiverFiberScaleDefectConnectedColumnDebt_abs_le_calibrationL1
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget
            (schedule.faceMap scale).coarseTarget_mem)))
      (Q'.add_le_add
        (scaled_abs_le_local factor _ _
          (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedEdgeDebt_abs_le_densityVariationL1
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget
            (schedule.faceMap scale).coarseTarget_mem))
        (scaled_abs_le_local factor _ _
          (actualPositiveExpandedReceiverFiberScaleDefectDisconnectedColumnDebt_abs_le_calibrationL1
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale).coarseRoot
            (schedule.faceMap scale).coarseTarget
            (schedule.faceMap scale).coarseTarget_mem)))
  simpa only [factor, connectedRow, connectedEdge, connectedColumn,
    disconnectedEdge, disconnectedColumn,
    actualPositiveExpandedReceiverFiberScaleDefectSplitDensityBudget] using
      (Q'.le_trans' _ _ _ htriangle hdebts)

/-! ## 2. Exact physical normalization -/

theorem connectedCovarianceRawCrossDenominator_pos
    (S : SlabScalePair) :
    (0 : Q') < connectedCovarianceRawCrossDenominator S := by
  let hcoarse := slabParametricKPhysicalPartition_pos
    S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent
  let hfine := slabParametricKPhysicalPartition_pos
    S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent
  unfold connectedCovarianceRawCrossDenominator rawCovarianceDenominator
  exact Q'.mul_pos
    (Q'.mul_pos hcoarse (Q'.mul_pos hcoarse hcoarse))
    (Q'.mul_pos hfine (Q'.mul_pos hfine hfine))

def rawMismatchNormalizedCost
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  Q'.divPos (rawMismatchBudget schedule scale)
    (schedule.spacing.spacing scale)
    (schedule.spacing.spacing_pos scale)

theorem rawMismatchNormalizedCost_mul_spacing_eqv
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    rawMismatchNormalizedCost schedule scale *
        schedule.spacing.spacing scale ≈
      rawMismatchBudget schedule scale := by
  exact Q'.divPos_mul_eqv _ _ _

theorem splitDensityNormalizationDenominator_pos
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    (0 : Q') <
      schedule.spacing.spacing scale *
        connectedCovarianceRawCrossDenominator
          (schedule.scalePair scale) :=
  Q'.mul_pos (schedule.spacing.spacing_pos scale)
    (connectedCovarianceRawCrossDenominator_pos
      (schedule.scalePair scale))

def actualPositiveExpandedReceiverFiberScaleDefectSplitDensityNormalizedCost
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  Q'.divPos
    (actualPositiveExpandedReceiverFiberScaleDefectSplitDensityBudget
      schedule scale)
    (schedule.spacing.spacing scale *
      connectedCovarianceRawCrossDenominator (schedule.scalePair scale))
    (splitDensityNormalizationDenominator_pos schedule scale)

theorem actualPositiveExpandedReceiverFiberScaleDefectSplitDensityNormalizedCost_mul_denominator_eqv
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectSplitDensityNormalizedCost
          schedule scale *
        (schedule.spacing.spacing scale *
          connectedCovarianceRawCrossDenominator
            (schedule.scalePair scale)) ≈
      actualPositiveExpandedReceiverFiberScaleDefectSplitDensityBudget
        schedule scale := by
  exact Q'.divPos_mul_eqv _ _ _

/-! ## 3. Uniform bounds on the two explicit normalized sequences -/

namespace PhysicalObservableRefinementSchedule

/-- The exact analytic frontier for the split receiver route.  An inhabitant
must bound two concrete normalized sequences uniformly after `start`; the
per-scale linear-in-spacing identities are already proved above. -/
structure ActualPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostBound
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  connectedCeiling : Q'
  connectedCeiling_pos : (0 : Q') < connectedCeiling
  mismatchNormalizedCost_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchNormalizedCost schedule scale ≤ mismatchCeiling
  splitDensityNormalizedCost_le : ∀ scale : Nat, start ≤ scale →
    actualPositiveExpandedReceiverFiberScaleDefectSplitDensityNormalizedCost
      schedule scale ≤ connectedCeiling

namespace ActualPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostBound

variable {schedule : PhysicalObservableRefinementSchedule}

/-- Compile the two uniform normalized-cost bounds to the existing
partition-scaled receiver-cross tail. -/
def toScaleDefectSeparatedLinearRawTransportTail
    (bound :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostBound
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
          actualPositiveExpandedReceiverFiberScaleDefectSplitDensityBudget
              schedule scale ≤
            bound.connectedCeiling *
              (schedule.spacing.spacing scale * denominator) :=
        normalized_le_scaled_of_divPos_le
          (actualPositiveExpandedReceiverFiberScaleDefectSplitDensityBudget
            schedule scale)
          (schedule.spacing.spacing scale * denominator)
          bound.connectedCeiling
          (by simpa only [denominator] using
            splitDensityNormalizationDenominator_pos schedule scale)
          (bound.splitDensityNormalizedCost_le scale hscale)
      exact Q'.le_trans' _ _ _
        (actualPositiveExpandedReceiverFiberScaleDefectScaledCross_abs_le_splitDensityBudget
          schedule scale)
        (Q'.le_trans' _ _ _ hbudget
          (Q'.le_of_eqv
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv bound.connectedCeiling
                (schedule.spacing.spacing scale) denominator))))

def toConnectedSeparatedLinearRawTransportTail
    (bound :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostBound
        schedule) :
    ConnectedSeparatedLinearRawTransportTail schedule :=
  bound.toScaleDefectSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail

theorem combinedCeiling_eq
    (bound :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostBound
        schedule) :
    bound.toConnectedSeparatedLinearRawTransportTail.combinedCeiling =
      bound.mismatchCeiling + bound.connectedCeiling :=
  rfl

/-- Final matched covariance consumer from uniform bounds on the two explicit
normalized cost sequences. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (bound :
      ActualPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostBound
        schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      bound.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  bound.toConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end ActualPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostBound
end PhysicalObservableRefinementSchedule

#print axioms actualPositiveExpandedReceiverFiberScaleDefectSplitDensityBudget
#print axioms actualPositiveExpandedReceiverFiberScaleDefectScaledCross_eqv_splitFiveDebts
#print axioms actualPositiveExpandedReceiverFiberScaleDefectScaledCross_abs_le_splitDensityBudget
#print axioms connectedCovarianceRawCrossDenominator_pos
#print axioms rawMismatchNormalizedCost
#print axioms rawMismatchNormalizedCost_mul_spacing_eqv
#print axioms splitDensityNormalizationDenominator_pos
#print axioms actualPositiveExpandedReceiverFiberScaleDefectSplitDensityNormalizedCost
#print axioms actualPositiveExpandedReceiverFiberScaleDefectSplitDensityNormalizedCost_mul_denominator_eqv
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostBound
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostBound.toScaleDefectSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostBound.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostBound.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostBound.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCost
