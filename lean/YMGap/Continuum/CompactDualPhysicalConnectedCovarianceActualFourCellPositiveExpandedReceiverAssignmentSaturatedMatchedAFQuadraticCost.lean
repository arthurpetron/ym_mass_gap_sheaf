/-
# Compile assignment-saturated receiver estimates on the matched AF chart

The assignment-saturated receiver variation is an exact control of the same
physical connected covariance raw cross used by the existing transport tail.
This module first clears its positive `Z_fine^2` normalization and proves that

  saturated normalized variation <= ceiling * Z_coarse^2

implies

  |physical raw cross| <= ceiling * (Z_coarse^3 * Z_fine^3).

It then places that implication on the matched asymptotically-free schedule.
The producer-facing structure asks for four explicit quadratic inputs: a
lower physical-spacing comparison, raw event mismatch, covered saturated
calibration, and physically unreachable endpoint mass.  A positive-coverage
variant replaces the last input by the equivalent near-full receiver-cell
coverage inequality.

No one of those analytic estimates is inhabited here.  Consequently this is
a finite exact compiler, not an arbitrary-cutoff contraction, continuum
measure, OS/GNS reconstruction, Hamiltonian gap, or Yang--Mills mass gap.

Constructive contract: exact rational positive division and inequalities
only; no choice, `Classical`, `native_decide`, `sorry`, noncomputable
declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedNormalizedVariation
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectAggregateNormalizedVariation

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedMatchedAFQuadraticCost

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedNormalizedVariation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedPhysicalCoverage
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectAggregateCoverageDeficit
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalMatchedAFTrajectory
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Int.add_mul,
               Int.mul_add, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem quadraticCost_le_normalizedSpacing_local
    (spacingFloor coefficient g spacingValue : Q')
    (hspacingFloor : (0 : Q') < spacingFloor)
    (hcoefficient : (0 : Q') < coefficient)
    (hlower : spacingFloor * (g * g) ≤ spacingValue) :
    coefficient * (g * g) ≤
      Q'.divPos coefficient spacingFloor hspacingFloor * spacingValue := by
  let normalized := Q'.divPos coefficient spacingFloor hspacingFloor
  have hnormalized : (0 : Q') ≤ normalized :=
    Q'.le_of_lt
      (Q'.divPos_pos coefficient spacingFloor hspacingFloor hcoefficient)
  have hmul := Q'.mul_le_mul_of_nonneg_left
    (spacingFloor * (g * g)) spacingValue normalized
    hlower hnormalized
  have hleft :
      normalized * (spacingFloor * (g * g)) ≈
        coefficient * (g * g) := by
    refine Q'.eqv_trans _
      ((normalized * spacingFloor) * (g * g)) _ ?_ ?_
    · exact Q'.eqv_symm
        (Q'.mul_assoc_eqv normalized spacingFloor (g * g))
    · exact Q'.mul_eqv_congr_right _ _ (g * g)
        (Q'.divPos_mul_eqv coefficient spacingFloor hspacingFloor)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hleft)) hmul

/-! ## 1. Exact fixed-scale normalization compiler -/

/-- Clearing the positive fine partition square recovers the literal
assignment-saturated scale-defect `l1` sum. -/
theorem actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1_mul_fineSquare_eqv
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1
          S hfineCutoff hcoarseCoupling root target *
        (S.fine.physicalPartition * S.fine.physicalPartition) ≈
      actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1
        S hfineCutoff hcoarseCoupling root target := by
  unfold actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1
  exact Q'.divPos_mul_eqv _ _ (finePhysicalPartitionSquare_pos S)

/-- A coarse-law quadratic-sized saturated variation is already a relative
bound for the full physical covariance raw-cross denominator. -/
theorem physicalConnectedCovarianceRawCrossDefect_abs_le_of_assignmentSaturatedCoarseNormalizedVariationL1_le
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (ceiling : Q')
    (hvariation :
      actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1
          S hfineCutoff hcoarseCoupling
          M.coarseRoot M.coarseTarget ≤
        ceiling *
          (S.coarse.physicalPartition * S.coarse.physicalPartition)) :
    Q'.abs
        (physicalConnectedCovarianceRawCrossDefect
          S hfineCutoff hcoarseCoupling M) ≤
      ceiling * connectedCovarianceRawCrossDenominator S := by
  let variation :=
    actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
  let full :=
    actualPositiveExpandedAssignmentSaturatedFullScaleDefectL1
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let fineSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  have hrecover : variation * fineSquare ≈ full := by
    simpa only [variation, full, fineSquare] using
      (actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1_mul_fineSquare_eqv
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget)
  have hscaledVariation := Q'.mul_le_mul_of_nonneg_right
    variation (ceiling * coarseSquare) fineSquare
    (by simpa only [variation, coarseSquare] using hvariation)
    (Q'.le_of_lt (finePhysicalPartitionSquare_pos S))
  have hfull : full ≤ (ceiling * coarseSquare) * fineSquare :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hrecover) hscaledVariation
  have hraw :
      Q'.abs
          (physicalConnectedCovarianceRawCrossDefect
            S hfineCutoff hcoarseCoupling M) ≤
        Q'.abs
            (S.coarse.physicalPartition * S.fine.physicalPartition) *
          full :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr
          (physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedAssignmentSaturated
            S hfineCutoff hcoarseCoupling M)))
      (by simpa only [full] using
        (physicalConnectedCovariancePositiveExpandedAssignmentSaturatedRawCrossDefect_abs_le_fullScaleDefectL1
          S hfineCutoff hcoarseCoupling M))
  have hscaledFull := Q'.mul_le_mul_of_nonneg_left
    full ((ceiling * coarseSquare) * fineSquare)
    (Q'.abs
      (S.coarse.physicalPartition * S.fine.physicalPartition))
    hfull
    (Q'.abs_nonneg _)
  refine Q'.le_trans' _ _ _ hraw
    (Q'.le_trans' _ _ _ hscaledFull (Q'.le_of_eqv ?_))
  refine Q'.eqv_trans _
    ((S.coarse.physicalPartition * S.fine.physicalPartition) *
      ((ceiling * coarseSquare) * fineSquare)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
        (Q'.mul_nonneg _ _
          (Q'.le_of_lt
            (slabParametricKPhysicalPartition_pos
              S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent))
          (Q'.le_of_lt
            (slabParametricKPhysicalPartition_pos
              S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent))))
  · unfold connectedCovarianceRawCrossDenominator rawCovarianceDenominator
    simp only [coarseSquare, fineSquare]
    ring_qeqv

/-! ## 2. Matched-AF quadratic producer -/

/-- Producer-facing inputs after all exact receiver bookkeeping has been
compressed to physical endpoints. -/
structure MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (C : AFTrajectoryCertificate)
    (coupling : Nat → Q')
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (identification : ShiftedAFTrajectoryIdentification C coupling)
    (nested : NestedCutoffOneFaceGeometry) : Type where
  start : Nat
  spacingFloor : Q'
  spacingFloor_pos : (0 : Q') < spacingFloor
  mismatchQuadraticCeiling : Q'
  mismatchQuadraticCeiling_pos : (0 : Q') < mismatchQuadraticCeiling
  coveredVariationQuadraticCeiling : Q'
  coveredVariationQuadraticCeiling_pos :
    (0 : Q') < coveredVariationQuadraticCeiling
  unreachableMassQuadraticCeiling : Q'
  unreachableMassQuadraticCeiling_pos :
    (0 : Q') < unreachableMassQuadraticCeiling
  spacingQuadratic_lower : ∀ scale : Nat, start ≤ scale →
    spacingFloor * (coupling scale * coupling scale) ≤
      spacing.a (coupling scale)
  rawMismatch_quadratic_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget
        (matchedShiftedAFPhysicalObservableRefinementSchedule
          family law spacing C coupling coupling_pos coupling_le_window
          identification nested)
        scale ≤
      mismatchQuadraticCeiling * (coupling scale * coupling scale)
  coveredVariation_quadratic_le : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    actualPositiveExpandedAssignmentSaturatedCoveredCoarseNormalizedVariationL1
          S rfl (schedule.effectiveCoupling_pos scale) root target ≤
      (coveredVariationQuadraticCeiling *
          (coupling scale * coupling scale)) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition)
  unreachableMass_quadratic_le : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass
          S root target ≤
      (unreachableMassQuadraticCeiling *
          (coupling scale * coupling scale)) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition)

namespace MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl

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

def normalizedVariationQuadraticCeiling
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) : Q' :=
  control.coveredVariationQuadraticCeiling +
    control.unreachableMassQuadraticCeiling

theorem normalizedVariationQuadraticCeiling_pos
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :
    (0 : Q') < control.normalizedVariationQuadraticCeiling :=
  Q'.add_pos control.coveredVariationQuadraticCeiling_pos
    control.unreachableMassQuadraticCeiling_pos

def mismatchCeiling
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) : Q' :=
  Q'.divPos control.mismatchQuadraticCeiling control.spacingFloor
    control.spacingFloor_pos

theorem mismatchCeiling_pos
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :
    (0 : Q') < control.mismatchCeiling :=
  Q'.divPos_pos _ _ control.spacingFloor_pos
    control.mismatchQuadraticCeiling_pos

def connectedCeiling
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) : Q' :=
  Q'.divPos control.normalizedVariationQuadraticCeiling
    control.spacingFloor control.spacingFloor_pos

theorem connectedCeiling_pos
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :
    (0 : Q') < control.connectedCeiling :=
  Q'.divPos_pos _ _ control.spacingFloor_pos
    control.normalizedVariationQuadraticCeiling_pos

/-- The two receiver estimates combine exactly to the one normalized
variation estimate used by the raw-cross compiler. -/
theorem normalizedVariation_quadratic_le
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested)
    (scale : Nat) (hscale : control.start ≤ scale) :
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1
          S rfl (schedule.effectiveCoupling_pos scale) root target ≤
      (control.normalizedVariationQuadraticCeiling *
          (coupling scale * coupling scale)) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) := by
  let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
    family law spacing C coupling coupling_pos coupling_le_window
    identification nested
  let S := schedule.scalePair scale
  let root := (schedule.faceMap scale).coarseRoot
  let target := (schedule.faceMap scale).coarseTarget
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  have hcombined :=
    actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1_le_of_covered_and_unreachable
      S rfl (schedule.effectiveCoupling_pos scale) root target
      ((control.coveredVariationQuadraticCeiling *
          (coupling scale * coupling scale)) * coarseSquare)
      ((control.unreachableMassQuadraticCeiling *
          (coupling scale * coupling scale)) * coarseSquare)
      (by simpa only [schedule, S, root, target, coarseSquare] using
        control.coveredVariation_quadratic_le scale hscale)
      (by simpa only [schedule, S, root, target, coarseSquare] using
        control.unreachableMass_quadratic_le scale hscale)
  refine Q'.le_trans' _ _ _ hcombined (Q'.le_of_eqv ?_)
  simp only [normalizedVariationQuadraticCeiling, coarseSquare]
  ring_qeqv

/-- Quadratic physical endpoint estimates compile directly to the generic
division-free covariance raw-cross tail. -/
def toCovarianceRawCrossSeparatedLinearRawTransportTail
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :
    CovarianceRawCrossSeparatedLinearRawTransportTail
      (matchedShiftedAFPhysicalObservableRefinementSchedule
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) where
  start := control.start
  mismatchCeiling := control.mismatchCeiling
  mismatchCeiling_pos := control.mismatchCeiling_pos
  connectedCeiling := control.connectedCeiling
  connectedCeiling_pos := control.connectedCeiling_pos
  mismatch_le := fun scale hscale => by
    exact Q'.le_trans' _ _ _
      (control.rawMismatch_quadratic_le scale hscale)
      (by
        simpa only [mismatchCeiling,
          matchedShiftedAFPhysicalObservableRefinementSchedule_spacing] using
          (quadraticCost_le_normalizedSpacing_local
            control.spacingFloor control.mismatchQuadraticCeiling
            (coupling scale) (spacing.a (coupling scale))
            control.spacingFloor_pos
            control.mismatchQuadraticCeiling_pos
            (control.spacingQuadratic_lower scale hscale)))
  connectedCovarianceRawCross_le := fun scale hscale => by
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let M := schedule.faceMap scale
    let quadratic :=
      control.normalizedVariationQuadraticCeiling *
        (coupling scale * coupling scale)
    let denominator := connectedCovarianceRawCrossDenominator S
    have hvariation :
        actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1
              S rfl (schedule.effectiveCoupling_pos scale)
              M.coarseRoot M.coarseTarget ≤
          quadratic *
            (S.coarse.physicalPartition * S.coarse.physicalPartition) := by
      simpa only [schedule, S, M, quadratic] using
        control.normalizedVariation_quadratic_le scale hscale
    have hphysical :
        Q'.abs
            (physicalConnectedCovarianceRawCrossDefect
              S rfl (schedule.effectiveCoupling_pos scale) M) ≤
          quadratic * denominator := by
      simpa only [denominator] using
        (physicalConnectedCovarianceRawCrossDefect_abs_le_of_assignmentSaturatedCoarseNormalizedVariationL1_le
          S rfl (schedule.effectiveCoupling_pos scale) M quadratic hvariation)
    have hspecialization :=
      connectedCovarianceRawCrossDefect_physicalKernel_eqv_actualRaw
        S rfl (schedule.effectiveCoupling_pos scale) M
    have hgeneric :
        Q'.abs
            (connectedCovarianceRawCrossDefect
              (schedule.kernel scale) M) ≤
          quadratic * denominator :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.abs_eqv_congr (by
            simpa only [kernel] using hspecialization)))
        hphysical
    have hquadratic :
        quadratic ≤ control.connectedCeiling *
          spacing.a (coupling scale) := by
      simpa only [quadratic, connectedCeiling] using
        (quadraticCost_le_normalizedSpacing_local
          control.spacingFloor control.normalizedVariationQuadraticCeiling
          (coupling scale) (spacing.a (coupling scale))
          control.spacingFloor_pos
          control.normalizedVariationQuadraticCeiling_pos
          (control.spacingQuadratic_lower scale hscale))
    have hscaled := Q'.mul_le_mul_of_nonneg_right
      quadratic
      (control.connectedCeiling * spacing.a (coupling scale))
      denominator hquadratic
      (Q'.le_of_lt (connectedCovarianceRawCrossDenominator_pos S))
    exact Q'.le_trans' _ _ _ hgeneric
      (by simpa only [schedule, S, M, denominator,
          matchedShiftedAFPhysicalObservableRefinementSchedule_spacing] using
        hscaled)

def toConnectedSeparatedLinearRawTransportTail
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :=
  control.toCovarianceRawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail

theorem fineCovariance_le_anchorRate_add_epsilon
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      control.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  control.toCovarianceRawCrossSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl

/-! ## 3. Equivalent positive coverage interface -/

/-- The same producer with the unreachable-mass input stated as near-full
coverage of the literal source-plus-target receiver cells. -/
structure MatchedShiftedAFAssignmentSaturatedCoveredVariationCoverageDeficitQuadraticCostControl
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (C : AFTrajectoryCertificate)
    (coupling : Nat → Q')
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (identification : ShiftedAFTrajectoryIdentification C coupling)
    (nested : NestedCutoffOneFaceGeometry) : Type where
  start : Nat
  spacingFloor : Q'
  spacingFloor_pos : (0 : Q') < spacingFloor
  mismatchQuadraticCeiling : Q'
  mismatchQuadraticCeiling_pos : (0 : Q') < mismatchQuadraticCeiling
  coveredVariationQuadraticCeiling : Q'
  coveredVariationQuadraticCeiling_pos :
    (0 : Q') < coveredVariationQuadraticCeiling
  coverageDeficitQuadraticCeiling : Q'
  coverageDeficitQuadraticCeiling_pos :
    (0 : Q') < coverageDeficitQuadraticCeiling
  spacingQuadratic_lower : ∀ scale : Nat, start ≤ scale →
    spacingFloor * (coupling scale * coupling scale) ≤
      spacing.a (coupling scale)
  rawMismatch_quadratic_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget
        (matchedShiftedAFPhysicalObservableRefinementSchedule
          family law spacing C coupling coupling_pos coupling_le_window
          identification nested)
        scale ≤
      mismatchQuadraticCeiling * (coupling scale * coupling scale)
  coveredVariation_quadratic_le : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    actualPositiveExpandedAssignmentSaturatedCoveredCoarseNormalizedVariationL1
          S rfl (schedule.effectiveCoupling_pos scale) root target ≤
      (coveredVariationQuadraticCeiling *
          (coupling scale * coupling scale)) *
        (S.coarse.physicalPartition * S.coarse.physicalPartition)
  receiverCoverage_quadratic : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
          S root target ≤
      actualPositiveExpandedAssignmentSaturatedCoveredFullReceiverMass
          S root target +
        (coverageDeficitQuadraticCeiling *
            (coupling scale * coupling scale)) *
          (S.coarse.physicalPartition * S.coarse.physicalPartition)

namespace MatchedShiftedAFAssignmentSaturatedCoveredVariationCoverageDeficitQuadraticCostControl

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

/-- Exact complement cancellation changes near-full physical endpoint
coverage into the unreachable-mass field of the direct compiler. -/
def toCoveredVariationUnreachableMassQuadraticCostControl
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationCoverageDeficitQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :
    MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested where
  start := control.start
  spacingFloor := control.spacingFloor
  spacingFloor_pos := control.spacingFloor_pos
  mismatchQuadraticCeiling := control.mismatchQuadraticCeiling
  mismatchQuadraticCeiling_pos := control.mismatchQuadraticCeiling_pos
  coveredVariationQuadraticCeiling :=
    control.coveredVariationQuadraticCeiling
  coveredVariationQuadraticCeiling_pos :=
    control.coveredVariationQuadraticCeiling_pos
  unreachableMassQuadraticCeiling :=
    control.coverageDeficitQuadraticCeiling
  unreachableMassQuadraticCeiling_pos :=
    control.coverageDeficitQuadraticCeiling_pos
  spacingQuadratic_lower := control.spacingQuadratic_lower
  rawMismatch_quadratic_le := control.rawMismatch_quadratic_le
  coveredVariation_quadratic_le := control.coveredVariation_quadratic_le
  unreachableMass_quadratic_le := fun scale hscale => by
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    apply
      (actualPositiveExpandedAssignmentSaturatedUnreachableFullReceiverMass_le_iff_fullReceiverCellMass_le_covered_add
        S root target
        ((control.coverageDeficitQuadraticCeiling *
            (coupling scale * coupling scale)) *
          (S.coarse.physicalPartition * S.coarse.physicalPartition))).mpr
    simpa only [schedule, S, root, target] using
      control.receiverCoverage_quadratic scale hscale

def toConnectedSeparatedLinearRawTransportTail
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationCoverageDeficitQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :=
  control.toCoveredVariationUnreachableMassQuadraticCostControl.toConnectedSeparatedLinearRawTransportTail

theorem fineCovariance_le_anchorRate_add_epsilon
    (control :
      MatchedShiftedAFAssignmentSaturatedCoveredVariationCoverageDeficitQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      control.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  control.toCoveredVariationUnreachableMassQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end MatchedShiftedAFAssignmentSaturatedCoveredVariationCoverageDeficitQuadraticCostControl

#print axioms actualPositiveExpandedAssignmentSaturatedCoarseNormalizedVariationL1_mul_fineSquare_eqv
#print axioms physicalConnectedCovarianceRawCrossDefect_abs_le_of_assignmentSaturatedCoarseNormalizedVariationL1_le
#print axioms MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl
#print axioms MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl.normalizedVariation_quadratic_le
#print axioms MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl.toCovarianceRawCrossSeparatedLinearRawTransportTail
#print axioms MatchedShiftedAFAssignmentSaturatedCoveredVariationUnreachableMassQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon
#print axioms MatchedShiftedAFAssignmentSaturatedCoveredVariationCoverageDeficitQuadraticCostControl
#print axioms MatchedShiftedAFAssignmentSaturatedCoveredVariationCoverageDeficitQuadraticCostControl.toCoveredVariationUnreachableMassQuadraticCostControl
#print axioms MatchedShiftedAFAssignmentSaturatedCoveredVariationCoverageDeficitQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedMatchedAFQuadraticCost
