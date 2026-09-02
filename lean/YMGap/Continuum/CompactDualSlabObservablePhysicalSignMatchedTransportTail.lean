/-
# Replace the pushforward L1 tail by its exact sign-observable match defect

At every point of the physical refinement schedule, the actual kernel's
candidate-dependent sign observable has matching defect exactly equal to the
pushforward `remainderL1`.  This module substitutes that identity into the
separated raw-transport tail.

The remaining physical inputs can therefore be stated uniformly as:

* the raw root/target/joint event-mismatch cost is `O(a)`; and
* the sign-observable matching defect of the actual selected kernel is `O(a)`.

No such bounds are inhabited.  In particular, the candidate dependence of the
sign observable is retained and no fixed-observable argmin is claimed to
minimize total variation.

Constructive contract: exact rational equivalences, inequalities, and
Type-valued witnesses only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalRemainderL1DualObservable
import YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail

namespace YMGap.Continuum.CompactDualSlabObservablePhysicalSignMatchedTransportTail

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualPhysicalRemainderL1DualObservable
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule

local infix:50 " ≈ " => Q'.eqv

namespace PhysicalObservableRefinementSchedule

/-- Existing physical observable-matching defect evaluated on the actual
selected candidate's own remainder-sign observable. -/
def signObservableMatchBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  observableMatchDefect
    (schedule.geometry scale).block
    (schedule.fineCoupling scale)
    (Q'.le_of_lt (schedule.fineCoupling_pos scale))
    (schedule.effectiveCoupling scale)
    (schedule.effectiveCoupling_pos scale)
    (physicalRemainderSignObservable
      (schedule.geometry scale).block
      (schedule.fineCoupling scale)
      (Q'.le_of_lt (schedule.fineCoupling_pos scale))
      (schedule.effectiveCoupling scale)
      (schedule.effectiveCoupling_pos scale))

/-- At every schedule index, the candidate-dependent sign-observable match
budget is exactly the actual pushforward `L1` remainder. -/
theorem signObservableMatchBudget_eqv_remainderL1
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    signObservableMatchBudget schedule scale ≈
      (schedule.kernel scale).remainderL1 := by
  simpa only [signObservableMatchBudget, kernel, scalePair] using
    (physicalObservableMatchDefect_sign_eqv_remainderL1
      (schedule.geometry scale).block
      (schedule.fineCoupling scale)
      (Q'.le_of_lt (schedule.fineCoupling_pos scale))
      (schedule.effectiveCoupling scale)
      (schedule.effectiveCoupling_pos scale))

/-- The separated physical tail stated entirely through the raw event mismatch
and the exact observable-matching defect.  No inhabitant is supplied. -/
structure SignMatchedSeparatedLinearRawTransportTail
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  signMatchCeiling : Q'
  signMatchCeiling_pos : (0 : Q') < signMatchCeiling
  mismatch_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget schedule scale ≤
      mismatchCeiling * schedule.spacing.spacing scale
  signMatch_le : ∀ scale : Nat, start ≤ scale →
    signObservableMatchBudget schedule scale ≤
      signMatchCeiling * schedule.spacing.spacing scale

namespace SignMatchedSeparatedLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

/-- Exact sign-observable matching control is losslessly the `L1` control
required by the separated transport compiler. -/
def toSeparatedLinearRawTransportTail
    (tail : SignMatchedSeparatedLinearRawTransportTail schedule) :
    SeparatedLinearRawTransportTail schedule where
  start := tail.start
  mismatchCeiling := tail.mismatchCeiling
  mismatchCeiling_pos := tail.mismatchCeiling_pos
  remainderCeiling := tail.signMatchCeiling
  remainderCeiling_pos := tail.signMatchCeiling_pos
  mismatch_le := tail.mismatch_le
  remainderL1_le := fun scale hscale =>
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (signObservableMatchBudget_eqv_remainderL1 schedule scale))
      (tail.signMatch_le scale hscale)

/-- The combined physical coefficient remains `C_m + 3*C_sign`, because the
sign-matching defect equals `remainderL1` exactly. -/
theorem combinedCeiling_eq
    (tail : SignMatchedSeparatedLinearRawTransportTail schedule) :
    tail.toSeparatedLinearRawTransportTail.combinedCeiling =
      tail.mismatchCeiling +
        (tail.signMatchCeiling +
          (tail.signMatchCeiling + tail.signMatchCeiling)) :=
  rfl

/-- Final scale consumer for the sign-matched formulation. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail : SignMatchedSeparatedLinearRawTransportTail schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      tail.toSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤
      schedule.anchorRate scale + epsilon :=
  tail.toSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end SignMatchedSeparatedLinearRawTransportTail
end PhysicalObservableRefinementSchedule

#print axioms PhysicalObservableRefinementSchedule.signObservableMatchBudget
#print axioms PhysicalObservableRefinementSchedule.signObservableMatchBudget_eqv_remainderL1
#print axioms PhysicalObservableRefinementSchedule.SignMatchedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.SignMatchedSeparatedLinearRawTransportTail.toSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.SignMatchedSeparatedLinearRawTransportTail.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.SignMatchedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualSlabObservablePhysicalSignMatchedTransportTail
