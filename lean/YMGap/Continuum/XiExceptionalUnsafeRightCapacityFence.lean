/-
# Unsafe-right fixed-path capacity fence

At a path-incompatible occurrence the terminal-background bit must be false.
If the occurrence activity is retained without changing the chain, the sole
external bit must be true.  Consequently the two side states have identical
two-slot payloads.  Swapping the router orientation does not supply a tag;
an unsafe-right repair must change some other carrier field (for example the
chain) or allocate genuinely different target terms.
-/

import YMGap.Continuum.XiExceptionalRightSafeSummation

namespace YMGap.Continuum.XiExceptionalUnsafeRightCapacityFence

open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalBranchRouter

inductive UnsafeSide : Type
  | left
  | right
deriving DecidableEq

/-- Universal two-bit capacity statement: once both output bits are forced,
the two input side states collide for every proposed fixed-path encoder. -/
theorem forced_two_slot_collision
    (encode : UnsafeSide → Bool × Bool)
    (hbackground : ∀ side, (encode side).1 = false)
    (hexternal : ∀ side, (encode side).2 = true) :
    encode .left = encode .right := by
  apply Prod.ext
  · exact (hbackground .left).trans (hbackground .right).symm
  · exact (hexternal .left).trans (hexternal .right).symm

private def oneTrue : OccBitVec 1 := .cons true .nil
private def oneFalse : OccBitVec 1 := .cons false .nil
private def leftState : MaskPair 1 := (oneTrue, oneFalse)
private def rightState : MaskPair 1 := (oneFalse, oneTrue)
private def noSafe : Nat → Bool := fun _ => false

private def leftOrientedPayload (pair : MaskPair 1) : MaskPair 1 :=
  routedMaskPair noSafe pair.1 pair.2

private def rightOrientedPayload (pair : MaskPair 1) : MaskPair 1 :=
  routedMaskPair noSafe pair.2 pair.1

theorem unsafe_states_ne : leftState ≠ rightState := by
  intro hpairs
  have hat := congrArg (fun pair => pair.1.at 0) hpairs
  cases hat

/-- The original left-oriented router cannot distinguish the unsafe sides. -/
theorem left_oriented_unsafe_collision :
    leftOrientedPayload leftState = leftOrientedPayload rightState := by
  rfl

/-- Reversing the router orientation produces the same collision. -/
theorem right_oriented_unsafe_collision :
    rightOrientedPayload leftState = rightOrientedPayload rightState := by
  rfl

/-- Even the orientation choice itself is invisible on either one-bit state. -/
theorem orientation_tag_is_invisible :
    leftOrientedPayload leftState = rightOrientedPayload leftState ∧
      leftOrientedPayload rightState = rightOrientedPayload rightState := by
  exact ⟨rfl, rfl⟩

#print axioms forced_two_slot_collision
#print axioms unsafe_states_ne
#print axioms left_oriented_unsafe_collision
#print axioms right_oriented_unsafe_collision
#print axioms orientation_tag_is_invisible

end YMGap.Continuum.XiExceptionalUnsafeRightCapacityFence
