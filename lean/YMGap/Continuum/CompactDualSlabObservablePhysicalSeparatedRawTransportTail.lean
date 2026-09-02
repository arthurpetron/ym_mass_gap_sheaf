/-
# Separate the physical raw-transport tail into mismatch and L1 producers

The complete actual transport budget is bounded by

  raw pullback mismatch cost + 3 * physical pushforward remainderL1.

This module turns separate linear-in-spacing estimates for those two literal
quantities into the combined `LinearRawTransportTail` consumed by the scale
compiler.  The construction preserves the exact physical kernel, face map,
and spacing schedule.

No separate linear estimate is inhabited here.  The result is a lossless
interface reduction, not a decay theorem for four-dimensional Yang--Mills.

Constructive contract: exact rational inequalities and Type-valued witnesses
only; no choice, `Classical`, `native_decide`, `sorry`, noncomputable
declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderL1Bound
import YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail

namespace YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderL1Bound
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackRawMismatch
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule

local infix:50 " ≈ " => Q'.eqv

private theorem add_three_mul_eqv
    (mismatch remainder spacing : Q') :
    mismatch * spacing +
        (remainder * spacing +
          (remainder * spacing + remainder * spacing)) ≈
      (mismatch + (remainder + (remainder + remainder))) * spacing := by
  have hpair :
      remainder * spacing + remainder * spacing ≈
        (remainder + remainder) * spacing :=
    Q'.eqv_symm (Q'.add_mul_eqv remainder remainder spacing)
  have htriple :
      remainder * spacing +
          (remainder * spacing + remainder * spacing) ≈
        (remainder + (remainder + remainder)) * spacing := by
    refine Q'.eqv_trans _
      (remainder * spacing +
        (remainder + remainder) * spacing) _ ?_ ?_
    · exact Q'.add_eqv_congr_left (remainder * spacing) _ _ hpair
    · exact Q'.eqv_symm
        (Q'.add_mul_eqv remainder (remainder + remainder) spacing)
  refine Q'.eqv_trans _
    (mismatch * spacing +
      (remainder + (remainder + remainder)) * spacing) _ ?_ ?_
  · exact Q'.add_eqv_congr_left (mismatch * spacing) _ _ htriple
  · exact Q'.eqv_symm
      (Q'.add_mul_eqv mismatch
        (remainder + (remainder + remainder)) spacing)

namespace PhysicalObservableRefinementSchedule

/-- The raw mismatch part of the actual physical transport budget. -/
def rawMismatchBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  physicalObservableRawMismatchCost
    (schedule.scalePair scale) rfl
    (schedule.effectiveCoupling_pos scale)
    (schedule.faceMap scale)

/-- Three copies of the actual physical pushforward `L1` remainder. -/
def pushedLawL1Budget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  threePhysicalRemainderCost (schedule.kernel scale)

/-- Separated majorant for the exact connected physical transport budget. -/
def separatedRawTransportBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  rawMismatchBudget schedule scale + pushedLawL1Budget schedule scale

/-- The exact connected pushed-law term is bounded by the literal `L1`
producer, leaving the raw mismatch term unchanged. -/
theorem rawTransportBudget_le_separatedRawTransportBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    schedule.rawTransportBudget scale ≤
      separatedRawTransportBudget schedule scale := by
  unfold rawTransportBudget separatedRawTransportBudget
    rawMismatchBudget pushedLawL1Budget
  exact Q'.add_le_add_left _ _ _
    (centeredCylinderRemainder_abs_le_threePhysicalRemainderCost
      (schedule.kernel scale) (schedule.faceMap scale))

/-- The two independent physical estimates that suffice for the complete
linear transport tail.  Both refer to the literal quantities at the same
scale and the same spacing.  No inhabitant is supplied. -/
structure SeparatedLinearRawTransportTail
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  remainderCeiling : Q'
  remainderCeiling_pos : (0 : Q') < remainderCeiling
  mismatch_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget schedule scale ≤
      mismatchCeiling * schedule.spacing.spacing scale
  remainderL1_le : ∀ scale : Nat, start ≤ scale →
    (schedule.kernel scale).remainderL1 ≤
      remainderCeiling * schedule.spacing.spacing scale

namespace SeparatedLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

/-- Combined coefficient after paying the connected remainder with three
copies of its `L1` norm. -/
def combinedCeiling
    (tail : SeparatedLinearRawTransportTail schedule) : Q' :=
  tail.mismatchCeiling +
    (tail.remainderCeiling +
      (tail.remainderCeiling + tail.remainderCeiling))

theorem combinedCeiling_pos
    (tail : SeparatedLinearRawTransportTail schedule) :
    (0 : Q') < tail.combinedCeiling := by
  unfold combinedCeiling
  exact Q'.pos_add_nonneg tail.mismatchCeiling_pos
    (Q'.zero_le_add _ _
      (Q'.le_of_lt tail.remainderCeiling_pos)
      (Q'.zero_le_add _ _
        (Q'.le_of_lt tail.remainderCeiling_pos)
        (Q'.le_of_lt tail.remainderCeiling_pos)))

/-- The separate raw-mismatch and pushforward-`L1` bounds imply the combined
linear bound required by the existing vanishing compiler. -/
theorem rawTransportBudget_le_combinedCeiling_mul_spacing
    (tail : SeparatedLinearRawTransportTail schedule)
    (scale : Nat) (hscale : tail.start ≤ scale) :
    schedule.rawTransportBudget scale ≤
      tail.combinedCeiling * schedule.spacing.spacing scale := by
  let spacing := schedule.spacing.spacing scale
  have hmismatch :
      rawMismatchBudget schedule scale ≤
        tail.mismatchCeiling * spacing :=
    tail.mismatch_le scale hscale
  have hremainder :
      (schedule.kernel scale).remainderL1 ≤
        tail.remainderCeiling * spacing :=
    tail.remainderL1_le scale hscale
  have hthree :
      pushedLawL1Budget schedule scale ≤
        tail.remainderCeiling * spacing +
          (tail.remainderCeiling * spacing +
            tail.remainderCeiling * spacing) := by
    unfold pushedLawL1Budget threePhysicalRemainderCost
    exact Q'.add_le_add hremainder
      (Q'.add_le_add hremainder hremainder)
  have hseparated :
      separatedRawTransportBudget schedule scale ≤
        tail.mismatchCeiling * spacing +
          (tail.remainderCeiling * spacing +
            (tail.remainderCeiling * spacing +
              tail.remainderCeiling * spacing)) := by
    unfold separatedRawTransportBudget
    exact Q'.add_le_add hmismatch hthree
  exact Q'.le_trans' _ _ _
    (rawTransportBudget_le_separatedRawTransportBudget schedule scale)
    (Q'.le_trans' _ _ _ hseparated
      (Q'.le_of_eqv
        (add_three_mul_eqv tail.mismatchCeiling
          tail.remainderCeiling spacing)))

/-- Compile the separated producers into the existing complete-budget tail. -/
def toLinearRawTransportTail
    (tail : SeparatedLinearRawTransportTail schedule) :
    LinearRawTransportTail schedule where
  start := tail.start
  ceiling := tail.combinedCeiling
  ceiling_pos := tail.combinedCeiling_pos
  budget_le := fun scale hscale =>
    tail.rawTransportBudget_le_combinedCeiling_mul_spacing scale hscale

/-- The separated physical estimates therefore give the same explicit
eventual covariance theorem as a direct complete-budget estimate. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail : SeparatedLinearRawTransportTail schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      tail.toLinearRawTransportTail.eventualStart epsilon ≤ scale) :
    schedule.fineCovariance scale ≤
      schedule.anchorRate scale + epsilon :=
  tail.toLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end SeparatedLinearRawTransportTail
end PhysicalObservableRefinementSchedule

#print axioms PhysicalObservableRefinementSchedule.rawMismatchBudget
#print axioms PhysicalObservableRefinementSchedule.pushedLawL1Budget
#print axioms PhysicalObservableRefinementSchedule.rawTransportBudget_le_separatedRawTransportBudget
#print axioms PhysicalObservableRefinementSchedule.SeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.SeparatedLinearRawTransportTail.combinedCeiling_pos
#print axioms PhysicalObservableRefinementSchedule.SeparatedLinearRawTransportTail.rawTransportBudget_le_combinedCeiling_mul_spacing
#print axioms PhysicalObservableRefinementSchedule.SeparatedLinearRawTransportTail.toLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.SeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
