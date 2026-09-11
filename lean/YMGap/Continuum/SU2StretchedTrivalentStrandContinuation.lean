/-
# Exact strand continuation through a stretched SU(2) trivalent vertex

The stretched Clebsch--Gordan channel `left + right` has an especially rigid
strand resolution.  No strand joins the two input legs.  Every right-leg
strand continues to the initial segment of the summed leg, and every
left-leg strand continues to the following segment.

This file records that fact as explicit bounded port maps and exact equations
for the canonical trivalent mate.  It is the local non-abelian compiler needed
to unfold an inward-mate stretched debt root into a source strand network.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.SU2TrivalentStrandPortPairing

namespace YMGap.Continuum.SU2StretchedTrivalentStrandContinuation

set_option autoImplicit false

open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2TrivalentStrandPeeling
open YMGap.Continuum.SU2TrivalentStrandPortPairing

/-! ## 1. The rigid stretched resolution -/

/-- The explicit resolution of `(left, right, left + right)`: all strands
continue to the summed leg and none directly join the input legs. -/
def stretchedTrivalentStrandResolution (left right : Nat) :
    TrivalentStrandResolution left right (left + right) where
  ab := 0
  bc := right
  ca := left
  a_balance := by omega
  b_balance := by omega
  c_balance := by omega

theorem fusionOK_stretched (left right : Nat) :
    fusionOK left right (left + right) = true :=
  (stretchedTrivalentStrandResolution left right).admissible

/-- Uniqueness identifies the canonical resolution with the explicit
stretched one. -/
theorem canonicalTrivalentStrandResolution_stretched
    (left right : Nat) :
    canonicalTrivalentStrandResolution left right (left + right)
        (fusionOK_stretched left right) =
      stretchedTrivalentStrandResolution left right :=
  TrivalentStrandResolution.unique _ _

@[simp] theorem canonicalAB_stretched (left right : Nat) :
    canonicalAB left right (left + right) = 0 := by
  have h := congrArg TrivalentStrandResolution.ab
    (canonicalTrivalentStrandResolution_stretched left right)
  exact h

@[simp] theorem canonicalBC_stretched (left right : Nat) :
    canonicalBC left right (left + right) = right := by
  have h := congrArg TrivalentStrandResolution.bc
    (canonicalTrivalentStrandResolution_stretched left right)
  exact h

@[simp] theorem canonicalCA_stretched (left right : Nat) :
    canonicalCA left right (left + right) = left := by
  have h := congrArg TrivalentStrandResolution.ca
    (canonicalTrivalentStrandResolution_stretched left right)
  exact h

/-! ## 2. Explicit continuation maps into the summed leg -/

def leftInputPort {left right : Nat} (slot : Fin left) :
    TrivalentStrandPort left right (left + right) :=
  .onA slot

def rightInputPort {left right : Nat} (slot : Fin right) :
    TrivalentStrandPort left right (left + right) :=
  .onB slot

/-- Left slots occupy the upper, `right`-shifted segment of the summed leg. -/
def leftSummedPort {left right : Nat} (slot : Fin left) :
    TrivalentStrandPort left right (left + right) :=
  .onC ⟨right + slot.val, by omega⟩

/-- Right slots occupy the initial segment of the summed leg. -/
def rightSummedPort {left right : Nat} (slot : Fin right) :
    TrivalentStrandPort left right (left + right) :=
  .onC ⟨slot.val, by omega⟩

theorem strandMate_stretched_left {left right : Nat} (slot : Fin left) :
    strandMate (stretchedTrivalentStrandResolution left right)
        (leftInputPort (right := right) slot) =
      leftSummedPort (right := right) slot := by
  simp [strandMate, stretchedTrivalentStrandResolution,
    leftInputPort, leftSummedPort, slot.isLt]

theorem strandMate_stretched_right {left right : Nat} (slot : Fin right) :
    strandMate (stretchedTrivalentStrandResolution left right)
        (rightInputPort (left := left) slot) =
      rightSummedPort (left := left) slot := by
  simp [strandMate, stretchedTrivalentStrandResolution,
    rightInputPort, rightSummedPort, slot.isLt]

theorem canonicalTrivalentPortMate_stretched_left
    {left right : Nat} (slot : Fin left) :
    canonicalTrivalentPortMate left right (left + right)
        (fusionOK_stretched left right)
        (leftInputPort (right := right) slot) =
      leftSummedPort (right := right) slot := by
  unfold canonicalTrivalentPortMate
  rw [canonicalTrivalentStrandResolution_stretched]
  exact strandMate_stretched_left slot

theorem canonicalTrivalentPortMate_stretched_right
    {left right : Nat} (slot : Fin right) :
    canonicalTrivalentPortMate left right (left + right)
        (fusionOK_stretched left right)
        (rightInputPort (left := left) slot) =
      rightSummedPort (left := left) slot := by
  unfold canonicalTrivalentPortMate
  rw [canonicalTrivalentStrandResolution_stretched]
  exact strandMate_stretched_right slot

/-- The two continuation ranges in the summed leg are disjoint. -/
theorem leftSummedPort_ne_rightSummedPort
    {left right : Nat} (leftSlot : Fin left) (rightSlot : Fin right) :
    leftSummedPort (right := right) leftSlot ≠
      rightSummedPort (left := left) rightSlot := by
  intro heq
  have hslot := congrArg TrivalentStrandPort.slot heq
  have hright := rightSlot.isLt
  simp only [leftSummedPort, rightSummedPort,
    TrivalentStrandPort.slot] at hslot
  omega

end YMGap.Continuum.SU2StretchedTrivalentStrandContinuation

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.SU2StretchedTrivalentStrandContinuation.fusionOK_stretched
#print axioms
  YMGap.Continuum.SU2StretchedTrivalentStrandContinuation.canonicalTrivalentStrandResolution_stretched
#print axioms
  YMGap.Continuum.SU2StretchedTrivalentStrandContinuation.canonicalTrivalentPortMate_stretched_left
#print axioms
  YMGap.Continuum.SU2StretchedTrivalentStrandContinuation.leftSummedPort_ne_rightSummedPort
