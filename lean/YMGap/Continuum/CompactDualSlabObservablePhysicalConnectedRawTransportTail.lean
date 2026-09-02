/-
# Preserve the connected pushed-law remainder in the physical transport tail

The exact physical raw-transport budget is already

  raw event-mismatch cost + |connected pushed-law remainder|.

The later `remainderL1` bound is conservative: it replaces the connected term
by three copies of total variation.  This module keeps the exact connected
quantity and splits its linear-in-spacing estimate from the raw-mismatch
estimate.  Separate bounds with coefficients `C_m` and `C_c` compile to the
existing complete tail with coefficient `C_m + C_c`.

This is the cancellation-preserving analytic branch.  No estimate is
inhabited here.  In particular, this module proves no refining-scale decay,
continuum measure, OS/GNS reconstruction, or physical mass gap.

Constructive contract: exact rational identities, inequalities, and
Type-valued witnesses only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail

namespace YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule

namespace PhysicalObservableRefinementSchedule

/-! ## 1. Exact connected budget split -/

/-- The cancellation-preserving pushed-law term in the exact transport
budget. -/
def connectedRemainderBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  Q'.abs
    (centeredCylinderRemainder
      (schedule.kernel scale) (schedule.faceMap scale))

/-- The exact transport budget displayed as its raw and connected parts. -/
def connectedSeparatedRawTransportBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  rawMismatchBudget schedule scale +
    connectedRemainderBudget schedule scale

/-- This split is exact; unlike the `remainderL1` branch, it introduces no
majorization factor. -/
theorem rawTransportBudget_eq_connectedSeparatedRawTransportBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    schedule.rawTransportBudget scale =
      connectedSeparatedRawTransportBudget schedule scale :=
  rfl

/-! ## 2. Separate linear producers and exact compilation -/

/-- The two sharp physical estimates: raw event mismatch and the exact
connected pushed-law remainder are each linear in the same physical spacing.
No inhabitant is supplied. -/
structure ConnectedSeparatedLinearRawTransportTail
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  connectedCeiling : Q'
  connectedCeiling_pos : (0 : Q') < connectedCeiling
  mismatch_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget schedule scale ≤
      mismatchCeiling * schedule.spacing.spacing scale
  connectedRemainder_le : ∀ scale : Nat, start ≤ scale →
    connectedRemainderBudget schedule scale ≤
      connectedCeiling * schedule.spacing.spacing scale

namespace ConnectedSeparatedLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

/-- No factor three is paid on the cancellation-preserving branch. -/
def combinedCeiling
    (tail : ConnectedSeparatedLinearRawTransportTail schedule) : Q' :=
  tail.mismatchCeiling + tail.connectedCeiling

theorem combinedCeiling_pos
    (tail : ConnectedSeparatedLinearRawTransportTail schedule) :
    (0 : Q') < tail.combinedCeiling :=
  Q'.add_pos tail.mismatchCeiling_pos tail.connectedCeiling_pos

/-- The two sharp producers imply the exact complete raw-transport tail. -/
theorem rawTransportBudget_le_combinedCeiling_mul_spacing
    (tail : ConnectedSeparatedLinearRawTransportTail schedule)
    (scale : Nat) (hscale : tail.start ≤ scale) :
    schedule.rawTransportBudget scale ≤
      tail.combinedCeiling * schedule.spacing.spacing scale := by
  let spacing := schedule.spacing.spacing scale
  have hmismatch :
      rawMismatchBudget schedule scale ≤
        tail.mismatchCeiling * spacing :=
    tail.mismatch_le scale hscale
  have hconnected :
      connectedRemainderBudget schedule scale ≤
        tail.connectedCeiling * spacing :=
    tail.connectedRemainder_le scale hscale
  have hsum :
      connectedSeparatedRawTransportBudget schedule scale ≤
        tail.mismatchCeiling * spacing +
          tail.connectedCeiling * spacing := by
    unfold connectedSeparatedRawTransportBudget
    exact Q'.add_le_add hmismatch hconnected
  rw [rawTransportBudget_eq_connectedSeparatedRawTransportBudget]
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          tail.mismatchCeiling tail.connectedCeiling spacing)))

/-- Compile the cancellation-preserving split into the existing complete
budget tail. -/
def toLinearRawTransportTail
    (tail : ConnectedSeparatedLinearRawTransportTail schedule) :
    LinearRawTransportTail schedule where
  start := tail.start
  ceiling := tail.combinedCeiling
  ceiling_pos := tail.combinedCeiling_pos
  budget_le := fun scale hscale =>
    tail.rawTransportBudget_le_combinedCeiling_mul_spacing scale hscale

/-- Final scale consumer for the sharp connected formulation. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail : ConnectedSeparatedLinearRawTransportTail schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale : tail.toLinearRawTransportTail.eventualStart epsilon ≤ scale) :
    schedule.fineCovariance scale ≤
      schedule.anchorRate scale + epsilon :=
  tail.toLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end ConnectedSeparatedLinearRawTransportTail
end PhysicalObservableRefinementSchedule

#print axioms PhysicalObservableRefinementSchedule.connectedRemainderBudget
#print axioms PhysicalObservableRefinementSchedule.connectedSeparatedRawTransportBudget
#print axioms PhysicalObservableRefinementSchedule.rawTransportBudget_eq_connectedSeparatedRawTransportBudget
#print axioms PhysicalObservableRefinementSchedule.ConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ConnectedSeparatedLinearRawTransportTail.combinedCeiling_pos
#print axioms PhysicalObservableRefinementSchedule.ConnectedSeparatedLinearRawTransportTail.rawTransportBudget_le_combinedCeiling_mul_spacing
#print axioms PhysicalObservableRefinementSchedule.ConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail
