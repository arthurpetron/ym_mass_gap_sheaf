/-
# Quadratic-cost bridge on the matched AF chart

The two normalized split-transport costs are now explicit, but the existing
`PhysicalSpacingEnvelope` supplies only an upper quadratic bound on physical
spacing.  An upper bound cannot control division by the spacing.  This module
therefore names the missing lower comparison and proves the exact sufficient
bridge on the matched shifted-AF chart.

If, eventually,

```text
spacingFloor * g^2 <= a(g),
rawMismatchBudget <= mismatchQuadraticCeiling * g^2,
unscaledSplitDensityBudget <=
  (connectedQuadraticCeiling * g^2) * cancelledCovarianceDenominator,
```

then the two normalized costs are uniformly bounded by the corresponding
quadratic ceilings divided by `spacingFloor`.  The existing matched covariance
consumer follows constructively.

No inhabitant of these three analytic estimates is supplied.  In particular,
this module proves no dimensional transmutation, physical gap floor, continuum
measure, OS/GNS reconstruction, Hamiltonian gap, or Clay conclusion.

Constructive contract: exact rational identities, inequalities, and
Type-valued witnesses only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostPartitionCancellation
import YMGap.Continuum.CompactDualSlabObservablePhysicalMatchedAFTrajectory

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitMatchedAFQuadraticCost

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCost
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCost.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostPartitionCancellation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePhysicalMatchedAFTrajectory
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule

local infix:50 " ≈ " => Q'.eqv

private theorem quadraticCost_le_normalizedSpacing
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

/-! ## 1. The exact matched-chart analytic input -/

/-- Three natural coupling-square estimates sufficient for the two uniform
normalized-cost bounds.  The physical lower comparison is deliberately
separate from the existing upper `PhysicalSpacingEnvelope.spacing_quad` field.
-/
structure MatchedShiftedAFSplitQuadraticCostControl
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
  connectedQuadraticCeiling : Q'
  connectedQuadraticCeiling_pos : (0 : Q') < connectedQuadraticCeiling
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
  unscaledSplitDensity_quadratic_le : ∀ scale : Nat, start ≤ scale →
    actualPositiveExpandedReceiverFiberScaleDefectUnscaledSplitDensityBudget
        (matchedShiftedAFPhysicalObservableRefinementSchedule
          family law spacing C coupling coupling_pos coupling_le_window
          identification nested)
        scale ≤
      (connectedQuadraticCeiling * (coupling scale * coupling scale)) *
        partitionCancelledCovarianceDenominator
          ((matchedShiftedAFPhysicalObservableRefinementSchedule
            family law spacing C coupling coupling_pos coupling_le_window
            identification nested).scalePair scale)

namespace MatchedShiftedAFSplitQuadraticCostControl

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

def mismatchCeiling
    (control : MatchedShiftedAFSplitQuadraticCostControl family law spacing C
      coupling coupling_pos coupling_le_window identification nested) : Q' :=
  Q'.divPos control.mismatchQuadraticCeiling control.spacingFloor
    control.spacingFloor_pos

theorem mismatchCeiling_pos
    (control : MatchedShiftedAFSplitQuadraticCostControl family law spacing C
      coupling coupling_pos coupling_le_window identification nested) :
    (0 : Q') < control.mismatchCeiling :=
  Q'.divPos_pos _ _ control.spacingFloor_pos
    control.mismatchQuadraticCeiling_pos

def connectedCeiling
    (control : MatchedShiftedAFSplitQuadraticCostControl family law spacing C
      coupling coupling_pos coupling_le_window identification nested) : Q' :=
  Q'.divPos control.connectedQuadraticCeiling control.spacingFloor
    control.spacingFloor_pos

theorem connectedCeiling_pos
    (control : MatchedShiftedAFSplitQuadraticCostControl family law spacing C
      coupling coupling_pos coupling_le_window identification nested) :
    (0 : Q') < control.connectedCeiling :=
  Q'.divPos_pos _ _ control.spacingFloor_pos
    control.connectedQuadraticCeiling_pos

/-! ## 2. Compile quadratic estimates to uniform normalized costs -/

def toSplitNormalizedCostBound
    (control : MatchedShiftedAFSplitQuadraticCostControl family law spacing C
      coupling coupling_pos coupling_le_window identification nested) :
    ActualPositiveExpandedReceiverFiberScaleDefectSplitNormalizedCostBound
      (matchedShiftedAFPhysicalObservableRefinementSchedule
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested) where
  start := control.start
  mismatchCeiling := control.mismatchCeiling
  mismatchCeiling_pos := control.mismatchCeiling_pos
  connectedCeiling := control.connectedCeiling
  connectedCeiling_pos := control.connectedCeiling_pos
  mismatchNormalizedCost_le := fun scale hscale => by
    unfold rawMismatchNormalizedCost
    apply Q'.divPos_le_of_le_mul
    exact Q'.le_trans' _ _ _
      (control.rawMismatch_quadratic_le scale hscale)
      (by
        simpa only [mismatchCeiling,
          matchedShiftedAFPhysicalObservableRefinementSchedule_spacing] using
          (quadraticCost_le_normalizedSpacing
            control.spacingFloor control.mismatchQuadraticCeiling
            (coupling scale) (spacing.a (coupling scale))
            control.spacingFloor_pos
            control.mismatchQuadraticCeiling_pos
            (control.spacingQuadratic_lower scale hscale)))
  splitDensityNormalizedCost_le := fun scale hscale => by
    let schedule :=
      matchedShiftedAFPhysicalObservableRefinementSchedule
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested
    apply Q'.le_trans' _
      (actualPositiveExpandedReceiverFiberScaleDefectPartitionCancelledSplitDensityNormalizedCost
        schedule scale) _
    · exact Q'.le_of_eqv
        (actualPositiveExpandedReceiverFiberScaleDefectSplitDensityNormalizedCost_eqv_partitionCancelled
          schedule scale)
    unfold actualPositiveExpandedReceiverFiberScaleDefectPartitionCancelledSplitDensityNormalizedCost
    apply Q'.divPos_le_of_le_mul
    let denominator :=
      partitionCancelledCovarianceDenominator (schedule.scalePair scale)
    have hquadratic :
        control.connectedQuadraticCeiling *
            (coupling scale * coupling scale) ≤
          control.connectedCeiling * spacing.a (coupling scale) := by
      simpa only [connectedCeiling] using
        (quadraticCost_le_normalizedSpacing
          control.spacingFloor control.connectedQuadraticCeiling
          (coupling scale) (spacing.a (coupling scale))
          control.spacingFloor_pos
          control.connectedQuadraticCeiling_pos
          (control.spacingQuadratic_lower scale hscale))
    have hdenominator : (0 : Q') ≤ denominator :=
      Q'.le_of_lt
        (partitionCancelledCovarianceDenominator_pos
          (schedule.scalePair scale))
    have hscaled := Q'.mul_le_mul_of_nonneg_right
      (control.connectedQuadraticCeiling *
        (coupling scale * coupling scale))
      (control.connectedCeiling * spacing.a (coupling scale))
      denominator hquadratic hdenominator
    exact Q'.le_trans' _ _ _
      (by simpa only [schedule, denominator] using
        control.unscaledSplitDensity_quadratic_le scale hscale)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (by
          simpa only [schedule,
            matchedShiftedAFPhysicalObservableRefinementSchedule_spacing,
            denominator] using
              (Q'.mul_assoc_eqv control.connectedCeiling
                (spacing.a (coupling scale)) denominator))))

def toConnectedSeparatedLinearRawTransportTail
    (control : MatchedShiftedAFSplitQuadraticCostControl family law spacing C
      coupling coupling_pos coupling_le_window identification nested) :=
  control.toSplitNormalizedCostBound.toConnectedSeparatedLinearRawTransportTail

theorem combinedCeiling_eq
    (control : MatchedShiftedAFSplitQuadraticCostControl family law spacing C
      coupling coupling_pos coupling_le_window identification nested) :
    control.toConnectedSeparatedLinearRawTransportTail.combinedCeiling =
      control.mismatchCeiling + control.connectedCeiling :=
  rfl

/-- Matched covariance control from the three explicit coupling-square
estimates. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (control : MatchedShiftedAFSplitQuadraticCostControl family law spacing C
      coupling coupling_pos coupling_le_window identification nested)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      control.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    let schedule :=
      matchedShiftedAFPhysicalObservableRefinementSchedule
        family law spacing C coupling coupling_pos coupling_le_window
        identification nested
    schedule.fineCovariance scale ≤ schedule.anchorRate scale + epsilon :=
  control.toSplitNormalizedCostBound.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end MatchedShiftedAFSplitQuadraticCostControl

#print axioms MatchedShiftedAFSplitQuadraticCostControl
#print axioms MatchedShiftedAFSplitQuadraticCostControl.mismatchCeiling
#print axioms MatchedShiftedAFSplitQuadraticCostControl.mismatchCeiling_pos
#print axioms MatchedShiftedAFSplitQuadraticCostControl.connectedCeiling
#print axioms MatchedShiftedAFSplitQuadraticCostControl.connectedCeiling_pos
#print axioms MatchedShiftedAFSplitQuadraticCostControl.toSplitNormalizedCostBound
#print axioms MatchedShiftedAFSplitQuadraticCostControl.toConnectedSeparatedLinearRawTransportTail
#print axioms MatchedShiftedAFSplitQuadraticCostControl.combinedCeiling_eq
#print axioms MatchedShiftedAFSplitQuadraticCostControl.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefectSplitMatchedAFQuadraticCost
