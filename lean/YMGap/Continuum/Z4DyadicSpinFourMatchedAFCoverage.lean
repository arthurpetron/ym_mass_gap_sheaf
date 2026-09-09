/-
# Compile spin-four endpoint coverage into the matched-AF contraction route

Every scale of the matched physical observable schedule has fine cutoff one.
The concrete spin-zero-through-four endpoint construction therefore supplies
the exact endpoint coverage required by the assignment-saturated receiver
compiler automatically.  This module removes that now-redundant field from
the producer-facing quantitative interface.

The remaining fields are precisely the three analytic estimates which the
finite construction does not prove: a quadratic physical-spacing lower
bound, a quadratic raw-mismatch upper bound, and a quadratic covered-image
normalized-variation upper bound.  Once those are supplied, the existing
consumer still yields the eventual covariance comparison

  fineCovariance scale <= anchorRate scale + epsilon.

This is an interface reduction on a finite cutoff-one schedule, not a proof
of any of those estimates, an all-cutoff contraction, a continuum measure,
OS/GNS reconstruction, a Hamiltonian gap, or the Yang--Mills mass gap.

Constructive contract: no choice, `Classical`, `native_decide`, proof hole,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourEndpointLift

namespace YMGap.Continuum.Z4DyadicSpinFourMatchedAFCoverage

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedEndpointLiftCoverage
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedMatchedAFQuadraticCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedNormalizedVariation
open YMGap.Continuum.CompactDualSlabObservablePhysicalMatchedAFTrajectory
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.Z4DyadicSpinFourEndpointLift

/-! ## 1. Endpoint coverage is automatic on the matched schedule -/

/-- Every matched-AF schedule scale has fine cutoff one, so the concrete
spin-zero-through-four lift covers every attached accepted endpoint. -/
def matchedShiftedAFSpinFourEndpointCoverage
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (C : AFTrajectoryCertificate)
    (coupling : Nat → Q')
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (identification : ShiftedAFTrajectoryIdentification C coupling)
    (nested : NestedCutoffOneFaceGeometry)
    (scale : Nat) :
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    EvenBinarySupportEndpointCoverage (schedule.scalePair scale) :=
  attachedEndpointSpinFourEvenBinarySupportCoverage _ rfl

/-! ## 2. Quantitative compiler with no endpoint-coverage field -/

/-- Producer-facing matched-AF inputs after exact spin-four endpoint coverage
has been discharged.  Only the still-open analytic estimates remain. -/
structure MatchedShiftedAFSpinFourCoveredVariationQuadraticCostControl
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

namespace MatchedShiftedAFSpinFourCoveredVariationQuadraticCostControl

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

/-- Insert the now-theorematic spin-four endpoint coverage into the previous
exact-coverage compiler. -/
def toEndpointCoverageQuadraticCostControl
    (control : MatchedShiftedAFSpinFourCoveredVariationQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested) :
    MatchedShiftedAFAssignmentSaturatedCoveredVariationEndpointCoverageQuadraticCostControl
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
  spacingQuadratic_lower := control.spacingQuadratic_lower
  rawMismatch_quadratic_le := control.rawMismatch_quadratic_le
  coveredVariation_quadratic_le := control.coveredVariation_quadratic_le
  endpointCoverage := fun scale _ =>
    matchedShiftedAFSpinFourEndpointCoverage family law spacing C coupling
      coupling_pos coupling_le_window identification nested scale

/-- Exact endpoint coverage is compiled further into the zero-unreachable-
mass quantitative interface. -/
def toCoveredVariationUnreachableMassQuadraticCostControl
    (control : MatchedShiftedAFSpinFourCoveredVariationQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested) :=
  control.toEndpointCoverageQuadraticCostControl.toCoveredVariationUnreachableMassQuadraticCostControl

/-- The completed finite coverage chain feeds the connected separated raw
transport tail without exposing an endpoint-coverage assumption. -/
def toConnectedSeparatedLinearRawTransportTail
    (control : MatchedShiftedAFSpinFourCoveredVariationQuadraticCostControl
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested) :=
  control.toEndpointCoverageQuadraticCostControl.toConnectedSeparatedLinearRawTransportTail

/-- Final covariance consumer for the minimized spin-four quantitative
interface.  The three analytic bounds in `control` remain genuine inputs. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (control : MatchedShiftedAFSpinFourCoveredVariationQuadraticCostControl
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
  control.toEndpointCoverageQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end MatchedShiftedAFSpinFourCoveredVariationQuadraticCostControl

#print axioms matchedShiftedAFSpinFourEndpointCoverage
#print axioms MatchedShiftedAFSpinFourCoveredVariationQuadraticCostControl.toEndpointCoverageQuadraticCostControl
#print axioms MatchedShiftedAFSpinFourCoveredVariationQuadraticCostControl.toCoveredVariationUnreachableMassQuadraticCostControl
#print axioms MatchedShiftedAFSpinFourCoveredVariationQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.Z4DyadicSpinFourMatchedAFCoverage
