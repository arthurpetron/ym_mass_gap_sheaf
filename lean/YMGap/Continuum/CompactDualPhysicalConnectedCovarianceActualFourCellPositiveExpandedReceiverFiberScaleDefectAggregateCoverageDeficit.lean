/-
# Replace uncovered receiver mass by a positive coverage deficit

The normalized aggregate receiver variation splits into calibration on the
supported-path image plus physical mass outside that image.  This module
rewrites the second input as a positive lower-coverage statement.  It defines
the physical mass of the covered source and target receiver cells and proves
exactly

  full receiver-cell mass
    ~= covered receiver-image mass + uncovered receiver mass.

Consequently an upper bound on uncovered mass is equivalent to saying that
the covered image captures the full cell mass up to the same additive budget.
The matched-AF compiler accepts this positive coverage-deficit formulation
and feeds it to the existing normalized-variation covariance consumer.

No quantitative coverage or calibration estimate is inhabited here.  This
is a finite-cutoff exact reduction, not a cutoff-uniform contraction,
continuum construction, OS/GNS reconstruction, Hamiltonian gap, or Clay
closure.

Constructive contract: exact rational finite sums and Type-valued witnesses
only; no choice, `Classical`, `native_decide`, proof hole, noncomputable
declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectAggregateNormalizedVariation

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectAggregateCoverageDeficit

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectAggregateNormalizedVariation
open YMGap.Continuum.CompactDualSlabObservablePhysicalMatchedAFTrajectory
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

local instance aggregateCoverageReceiverDecidableEq
    (S : SlabScalePair) (root : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair S.coarse root) :=
  slabObservableTwoReplicaPairDecidableEq S.coarse root

private theorem le_of_add_le_add_left_local {common left right : Q'}
    (h : common + left ≤ common + right) : left ≤ right := by
  have hadd := Q'.add_le_add_left (-common)
    (common + left) (common + right) h
  have hleft : -common + (common + left) ≈ left := by
    refine Q'.eqv_trans _ ((-common + common) + left) _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-common) common left)) ?_
    refine Q'.eqv_trans _ ((0 : Q') + left) _
      (Q'.add_eqv_congr_right _ _ left
        (Q'.neg_add_self_eqv common)) ?_
    exact QPoly.q_zero_add_eqv left
  have hright : -common + (common + right) ≈ right := by
    refine Q'.eqv_trans _ ((-common + common) + right) _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-common) common right)) ?_
    refine Q'.eqv_trans _ ((0 : Q') + right) _
      (Q'.add_eqv_congr_right _ _ right
        (Q'.neg_add_self_eqv common)) ?_
    exact QPoly.q_zero_add_eqv right
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright))

/-! ## 1. Physical mass captured by the two supported receiver images -/

/-- Physical source-cell mass whose receiver lies in the supported source
path image. -/
def actualPositiveExpandedReceiverFiberScaleDefectSourceCoveredReceiverMass
    (S : SlabScalePair) (root target : Nat) : Q' :=
  listQSum (slabObservableTwoReplicaPairWeight S.coarse)
    ((slabObservableFourCellSourcePairs S.coarse root target).filter
      (fun receiver => decide
        (receiver ∈
          positiveExpandedFourCellSourceSupportedReceiverImage
            S root target)))

/-- Physical target-cell mass whose receiver lies in the supported target
path image. -/
def actualPositiveExpandedReceiverFiberScaleDefectTargetCoveredReceiverMass
    (S : SlabScalePair) (root target : Nat) : Q' :=
  listQSum (slabObservableTwoReplicaPairWeight S.coarse)
    ((slabObservableFourCellTargetPairs S.coarse root target).filter
      (fun receiver => decide
        (receiver ∈
          positiveExpandedFourCellTargetSupportedReceiverImage
            S root target)))

/-- Complete physical mass of the source and target determinant cells. -/
def actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
    (S : SlabScalePair) (root target : Nat) : Q' :=
  listQSum (slabObservableTwoReplicaPairWeight S.coarse)
      (slabObservableFourCellSourcePairs S.coarse root target) +
    listQSum (slabObservableTwoReplicaPairWeight S.coarse)
      (slabObservableFourCellTargetPairs S.coarse root target)

/-- Total physical receiver-cell mass captured by the two supported images. -/
def actualPositiveExpandedReceiverFiberScaleDefectCoveredFullReceiverMass
    (S : SlabScalePair) (root target : Nat) : Q' :=
  actualPositiveExpandedReceiverFiberScaleDefectSourceCoveredReceiverMass
      S root target +
    actualPositiveExpandedReceiverFiberScaleDefectTargetCoveredReceiverMass
      S root target

/-- The source receiver cell is exactly its supported image plus the missed
physical mass defined in the normalized-variation module. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectSourceReceiverCellMass_eqv_covered_add_uncovered
    (S : SlabScalePair) (root target : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight S.coarse)
        (slabObservableFourCellSourcePairs S.coarse root target) ≈
      actualPositiveExpandedReceiverFiberScaleDefectSourceCoveredReceiverMass
          S root target +
        actualPositiveExpandedReceiverFiberScaleDefectSourceUncoveredReceiverMass
          S root target := by
  simpa only [
    actualPositiveExpandedReceiverFiberScaleDefectSourceCoveredReceiverMass,
    actualPositiveExpandedReceiverFiberScaleDefectSourceUncoveredReceiverMass]
    using
      (listQSum_filter_partition
        (slabObservableTwoReplicaPairWeight S.coarse)
        (fun receiver : SlabObservableTwoReplicaPair S.coarse root =>
          decide
            (receiver ∈
              positiveExpandedFourCellSourceSupportedReceiverImage
                S root target))
        (slabObservableFourCellSourcePairs S.coarse root target))

/-- The target receiver cell has the analogous exact coverage split. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectTargetReceiverCellMass_eqv_covered_add_uncovered
    (S : SlabScalePair) (root target : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight S.coarse)
        (slabObservableFourCellTargetPairs S.coarse root target) ≈
      actualPositiveExpandedReceiverFiberScaleDefectTargetCoveredReceiverMass
          S root target +
        actualPositiveExpandedReceiverFiberScaleDefectTargetUncoveredReceiverMass
          S root target := by
  simpa only [
    actualPositiveExpandedReceiverFiberScaleDefectTargetCoveredReceiverMass,
    actualPositiveExpandedReceiverFiberScaleDefectTargetUncoveredReceiverMass]
    using
      (listQSum_filter_partition
        (slabObservableTwoReplicaPairWeight S.coarse)
        (fun receiver : SlabObservableTwoReplicaPair S.coarse root =>
          decide
            (receiver ∈
              positiveExpandedFourCellTargetSupportedReceiverImage
                S root target))
        (slabObservableFourCellTargetPairs S.coarse root target))

/-- The full two-cell physical mass is exactly covered image mass plus total
uncovered mass. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass_eqv_covered_add_uncovered
    (S : SlabScalePair) (root target : Nat) :
    actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
        S root target ≈
      actualPositiveExpandedReceiverFiberScaleDefectCoveredFullReceiverMass
          S root target +
        actualPositiveExpandedReceiverFiberScaleDefectUncoveredFullReceiverMass
          S root target := by
  let sourceFull :=
    listQSum (slabObservableTwoReplicaPairWeight S.coarse)
      (slabObservableFourCellSourcePairs S.coarse root target)
  let targetFull :=
    listQSum (slabObservableTwoReplicaPairWeight S.coarse)
      (slabObservableFourCellTargetPairs S.coarse root target)
  let sourceCovered :=
    actualPositiveExpandedReceiverFiberScaleDefectSourceCoveredReceiverMass
      S root target
  let targetCovered :=
    actualPositiveExpandedReceiverFiberScaleDefectTargetCoveredReceiverMass
      S root target
  let sourceUncovered :=
    actualPositiveExpandedReceiverFiberScaleDefectSourceUncoveredReceiverMass
      S root target
  let targetUncovered :=
    actualPositiveExpandedReceiverFiberScaleDefectTargetUncoveredReceiverMass
      S root target
  have hsource : sourceFull ≈ sourceCovered + sourceUncovered := by
    simpa only [sourceFull, sourceCovered, sourceUncovered] using
      (actualPositiveExpandedReceiverFiberScaleDefectSourceReceiverCellMass_eqv_covered_add_uncovered
        S root target)
  have htarget : targetFull ≈ targetCovered + targetUncovered := by
    simpa only [targetFull, targetCovered, targetUncovered] using
      (actualPositiveExpandedReceiverFiberScaleDefectTargetReceiverCellMass_eqv_covered_add_uncovered
        S root target)
  refine Q'.eqv_trans _
    ((sourceCovered + sourceUncovered) +
      (targetCovered + targetUncovered)) _ ?_ ?_
  · simpa only [
      actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass,
      sourceFull, targetFull] using Q'.add_eqv_congr' hsource htarget
  simpa only [
    actualPositiveExpandedReceiverFiberScaleDefectCoveredFullReceiverMass,
    actualPositiveExpandedReceiverFiberScaleDefectUncoveredFullReceiverMass,
    sourceCovered, targetCovered, sourceUncovered, targetUncovered] using
      (Q'.add_swap_inner sourceCovered sourceUncovered
        targetCovered targetUncovered)

/-! ## 2. Missing mass is exactly additive coverage deficit -/

/-- Bounding missed physical mass is equivalent to saying that the supported
receiver images capture the complete source-plus-target cell mass up to the
same additive budget. -/
theorem actualPositiveExpandedReceiverFiberScaleDefectUncoveredFullReceiverMass_le_iff_fullReceiverCellMass_le_covered_add
    (S : SlabScalePair) (root target : Nat) (budget : Q') :
    actualPositiveExpandedReceiverFiberScaleDefectUncoveredFullReceiverMass
          S root target ≤ budget ↔
      actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
          S root target ≤
        actualPositiveExpandedReceiverFiberScaleDefectCoveredFullReceiverMass
            S root target + budget := by
  let full :=
    actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
      S root target
  let covered :=
    actualPositiveExpandedReceiverFiberScaleDefectCoveredFullReceiverMass
      S root target
  let uncovered :=
    actualPositiveExpandedReceiverFiberScaleDefectUncoveredFullReceiverMass
      S root target
  have hsplit : full ≈ covered + uncovered := by
    simpa only [full, covered, uncovered] using
      (actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass_eqv_covered_add_uncovered
        S root target)
  constructor
  · intro huncovered
    have hadd := Q'.add_le_add_left covered uncovered budget huncovered
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) hadd
  · intro hcoverage
    have hadd : covered + uncovered ≤ covered + budget :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsplit) hcoverage
    exact le_of_add_le_add_left_local hadd

/-! ## 3. Matched-AF positive coverage compiler -/

/-- Producer-facing matched-AF input.  The missing-mass hypothesis is stated
as near-full physical coverage of the actual receiver cells. -/
structure MatchedShiftedAFCoveredVariationCoverageDeficitQuadraticCostControl
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
    actualPositiveExpandedReceiverFiberScaleDefectCoveredCoarseNormalizedVariationL1
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
      actualPositiveExpandedReceiverFiberScaleDefectCoveredFullReceiverMass
          S root target +
        (coverageDeficitQuadraticCeiling *
            (coupling scale * coupling scale)) *
          (S.coarse.physicalPartition * S.coarse.physicalPartition)

namespace MatchedShiftedAFCoveredVariationCoverageDeficitQuadraticCostControl

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

/-- Exact complement cancellation turns positive near-full coverage into the
uncovered-mass field of the existing quantitative-coverage compiler. -/
def toMatchedShiftedAFCoveredVariationUncoveredMassQuadraticCostControl
    (control :
      MatchedShiftedAFCoveredVariationCoverageDeficitQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :
    MatchedShiftedAFCoveredVariationUncoveredMassQuadraticCostControl
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
  uncoveredMassQuadraticCeiling :=
    control.coverageDeficitQuadraticCeiling
  uncoveredMassQuadraticCeiling_pos :=
    control.coverageDeficitQuadraticCeiling_pos
  spacingQuadratic_lower := control.spacingQuadratic_lower
  rawMismatch_quadratic_le := control.rawMismatch_quadratic_le
  coveredVariation_quadratic_le := control.coveredVariation_quadratic_le
  uncoveredMass_quadratic_le := fun scale hscale => by
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let root := (schedule.faceMap scale).coarseRoot
    let target := (schedule.faceMap scale).coarseTarget
    apply
      (actualPositiveExpandedReceiverFiberScaleDefectUncoveredFullReceiverMass_le_iff_fullReceiverCellMass_le_covered_add
        S root target
        ((control.coverageDeficitQuadraticCeiling *
            (coupling scale * coupling scale)) *
          (S.coarse.physicalPartition * S.coarse.physicalPartition))).mpr
    simpa only [schedule, S, root, target] using
      control.receiverCoverage_quadratic scale hscale

/-- Final covariance consumer for the positive coverage-deficit route. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (control :
      MatchedShiftedAFCoveredVariationCoverageDeficitQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      control.toMatchedShiftedAFCoveredVariationUncoveredMassQuadraticCostControl.toMatchedShiftedAFSplitPosteriorColumnNormalizedVariationQuadraticCostControl.toMatchedShiftedAFSplitPosteriorColumnAggregateCoefficientL1QuadraticCostControl.toMatchedShiftedAFSplitPosteriorColumnQuadraticCostControl.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  control.toMatchedShiftedAFCoveredVariationUncoveredMassQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end MatchedShiftedAFCoveredVariationCoverageDeficitQuadraticCostControl

#print axioms actualPositiveExpandedReceiverFiberScaleDefectSourceCoveredReceiverMass
#print axioms actualPositiveExpandedReceiverFiberScaleDefectTargetCoveredReceiverMass
#print axioms actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass
#print axioms actualPositiveExpandedReceiverFiberScaleDefectCoveredFullReceiverMass
#print axioms actualPositiveExpandedReceiverFiberScaleDefectSourceReceiverCellMass_eqv_covered_add_uncovered
#print axioms actualPositiveExpandedReceiverFiberScaleDefectTargetReceiverCellMass_eqv_covered_add_uncovered
#print axioms actualPositiveExpandedReceiverFiberScaleDefectFullReceiverCellMass_eqv_covered_add_uncovered
#print axioms actualPositiveExpandedReceiverFiberScaleDefectUncoveredFullReceiverMass_le_iff_fullReceiverCellMass_le_covered_add
#print axioms MatchedShiftedAFCoveredVariationCoverageDeficitQuadraticCostControl
#print axioms MatchedShiftedAFCoveredVariationCoverageDeficitQuadraticCostControl.toMatchedShiftedAFCoveredVariationUncoveredMassQuadraticCostControl
#print axioms MatchedShiftedAFCoveredVariationCoverageDeficitQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectAggregateCoverageDeficit
