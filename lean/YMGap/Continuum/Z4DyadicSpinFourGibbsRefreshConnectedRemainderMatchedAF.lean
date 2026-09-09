/-
# Put the Gibbs-refresh connected producer on the matched AF schedule

The concrete Gibbs-refresh comparison has reduced the aggregate receiver
column cross to one cancellation-aware scalar:

  |centeredCylinderRemainder| <= K_c * g^2.

This module places that exact premise on the existing shifted matched-AF
schedule.  Together with the independent quadratic raw-mismatch estimate and
the lower quadratic comparison between the AF coordinate and physical
spacing, it compiles to the final finite `anchor + epsilon` covariance
consumer.  No raw-column determinant or receiver normalization is left in
the producer-facing interface.

No estimate is inhabited here.  In particular, the centered remainder, raw
mismatch, and lower physical-spacing comparison remain genuine analytic
inputs.  Arbitrary-cutoff persistence, a continuum measure and observable
algebra, same-object OS/GNS reconstruction, a Hamiltonian gap, and the
Yang--Mills mass gap remain open.

Constructive contract: Type-valued witnesses and exact rational inequalities
only; no choice, `Classical`, `native_decide`, proof hole, noncomputable
declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRemainder

namespace YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRemainderMatchedAF

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualSlabObservablePhysicalMatchedAFTrajectory
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRemainder
open YMGap.Continuum.Z4DyadicSpinFourReceiverRawColumnCrossCalibration

/-! ## 1. Direct schedule-level producer -/

/-- The preferred matched-AF finite producer after the Gibbs-refresh
normalization has been cancelled.  Its connected field is exactly the
selected centered physical remainder, rather than a receiver-column cross or
a full total-variation norm. -/
structure MatchedShiftedAFSpinFourGibbsRefreshConnectedRemainderQuadraticCostControl
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
  connectedRemainderQuadraticCeiling : Q'
  connectedRemainderQuadraticCeiling_pos :
    (0 : Q') < connectedRemainderQuadraticCeiling
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
  connectedRemainder_quadratic : ∀ scale : Nat, start ≤ scale →
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let M := schedule.faceMap scale
    CoarseGibbsRefreshConnectedRemainderCalibration
      S rfl (schedule.effectiveCoupling_pos scale) M
        (coupling scale) connectedRemainderQuadraticCeiling

namespace MatchedShiftedAFSpinFourGibbsRefreshConnectedRemainderQuadraticCostControl

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

/-! ## 2. Exact compilation through the aggregate raw-column cross -/

/-- The direct centered-remainder producer inhabits the previously exposed
aggregate raw-column producer with exactly the same quadratic coefficient. -/
def toRawColumnCrossQuadraticCostControl
    (control :
      MatchedShiftedAFSpinFourGibbsRefreshConnectedRemainderQuadraticCostControl
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
  rawColumnCrossQuadraticCeiling :=
    control.connectedRemainderQuadraticCeiling
  rawColumnCrossQuadraticCeiling_pos :=
    control.connectedRemainderQuadraticCeiling_pos
  spacingQuadratic_lower := control.spacingQuadratic_lower
  rawMismatch_quadratic_le := control.rawMismatch_quadratic_le
  rawColumnCross_quadratic := fun scale hscale => by
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    let S := schedule.scalePair scale
    let M := schedule.faceMap scale
    exact
      positiveExpandedAssignmentSaturatedRawColumnCrossCalibration_of_gibbsRefreshConnectedRemainder
        S rfl (schedule.effectiveCoupling_pos scale) M
        (coupling scale) control.connectedRemainderQuadraticCeiling
        (control.connectedRemainder_quadratic scale hscale)

/-- The cancellation-aware matched-AF producer reaches the exact production
kernel raw-cross tail without any additional analytic field. -/
def toActualCovarianceRawCrossSeparatedLinearRawTransportTail
    (control :
      MatchedShiftedAFSpinFourGibbsRefreshConnectedRemainderQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) :=
  control.toRawColumnCrossQuadraticCostControl.toActualCovarianceRawCrossSeparatedLinearRawTransportTail

/-- Final finite covariance consumer for the direct Gibbs-refresh connected
producer.  The three quantitative fields remain explicit in `control`. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (control :
      MatchedShiftedAFSpinFourGibbsRefreshConnectedRemainderQuadraticCostControl
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      control.toRawColumnCrossQuadraticCostControl.toActualCovarianceRawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    let schedule := matchedShiftedAFPhysicalObservableRefinementSchedule
      family law spacing C coupling coupling_pos coupling_le_window
      identification nested
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  control.toRawColumnCrossQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end MatchedShiftedAFSpinFourGibbsRefreshConnectedRemainderQuadraticCostControl

#print axioms MatchedShiftedAFSpinFourGibbsRefreshConnectedRemainderQuadraticCostControl
#print axioms MatchedShiftedAFSpinFourGibbsRefreshConnectedRemainderQuadraticCostControl.toRawColumnCrossQuadraticCostControl
#print axioms MatchedShiftedAFSpinFourGibbsRefreshConnectedRemainderQuadraticCostControl.toActualCovarianceRawCrossSeparatedLinearRawTransportTail
#print axioms MatchedShiftedAFSpinFourGibbsRefreshConnectedRemainderQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRemainderMatchedAF
