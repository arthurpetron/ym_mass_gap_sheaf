/-
# Canonical bundle blocks do not preserve same-slot continuation

The two local colored embeddings into a summed trivalent resolution commute
with the local mate.  They do not, however, automatically commute with the
production convention that an internal edge continues at the same numerical
slot between its two vertex occurrences.

This module records the smallest explicit witness.  A left internal edge has
one strand.  At its first endpoint that strand lies in a `ca` bundle while the
right summand contributes one preceding `bc` strand, so the local left block
is embedded at summed slot one.  At the other endpoint the same left strand
lies in the first `ca` block and is embedded at summed slot zero.  Both source
slots are zero and both summed internal-edge labels are two.

The theorem refutes only the naive vertexwise block lift.  It does not refute
the existence of a coherent edgewise permutation or a different global
colored isomorphism; constructing or obstructing that stronger witness is the
next mathematical frontier.

Constructive contract: three literal trivalent resolutions and reduction of
their finite addresses only; no `Classical`, choice, `native_decide`, `sorry`,
new axiom, or noncomputable declaration.
-/

import YMGap.Continuum.SU2TrivalentStrandPortAddition

namespace YMGap.Continuum.SU2TrivalentStrandPortContinuationObstruction

set_option autoImplicit false

open YMGap.Continuum.SU2TrivalentStrandPeeling
open YMGap.Continuum.SU2TrivalentStrandPortAddition
open YMGap.Continuum.SU2TrivalentStrandPortPairing

/-! ## 1. Three unit bundle resolutions -/

/-- One `ca` strand: labels `(1,0,1)`. -/
def unitCAResolution : TrivalentStrandResolution 1 0 1 where
  ab := 0
  bc := 0
  ca := 1
  a_balance := rfl
  b_balance := rfl
  c_balance := rfl

/-- One `bc` strand: labels `(0,1,1)`. -/
def unitBCResolution : TrivalentStrandResolution 0 1 1 where
  ab := 0
  bc := 1
  ca := 0
  a_balance := rfl
  b_balance := rfl
  c_balance := rfl

/-- One `ab` strand: labels `(1,1,0)`. -/
def unitABResolution : TrivalentStrandResolution 1 1 0 where
  ab := 1
  bc := 0
  ca := 0
  a_balance := rfl
  b_balance := rfl
  c_balance := rfl

/-! ## 2. One left internal strand at its two occurrences -/

/-- The left internal strand as the `c` leg of the first vertex. -/
def leftInternalAtFirst : TrivalentStrandPort 1 0 1 :=
  .onC ⟨0, by omega⟩

/-- The same numerical source slot as the `a` leg of the next vertex. -/
def leftInternalAtSecond : TrivalentStrandPort 1 0 1 :=
  .onA ⟨0, by omega⟩

theorem leftInternal_source_slots_equal :
    leftInternalAtFirst.slot = leftInternalAtSecond.slot := rfl

/-- At both endpoints the left and right internal labels sum to two. -/
theorem summed_internal_edge_labels_equal :
    (1 + 1 : Nat) = 1 + 1 := rfl

/-! ## 3. The vertexwise block addresses disagree -/

/-- At the first endpoint, the right `bc` block precedes the left `ca`
strand, placing the latter at summed slot one. -/
theorem leftBlockAtFirst_slot :
    (trivalentStrandPortInSumLeft
      unitCAResolution unitBCResolution leftInternalAtFirst).slot = 1 := rfl

/-- At the next endpoint, the left `ca` strand begins the summed `a` leg and
therefore remains at slot zero. -/
theorem leftBlockAtSecond_slot :
    (trivalentStrandPortInSumLeft
      unitCAResolution unitABResolution leftInternalAtSecond).slot = 0 := rfl

/-- **Continuation obstruction for the naive lift.**  Equal source slots on
one internal edge acquire unequal summed slots under the independent local
bundle-block embeddings. -/
theorem vertexwise_left_blocks_do_not_preserve_same_slot :
    (trivalentStrandPortInSumLeft
      unitCAResolution unitBCResolution leftInternalAtFirst).slot ≠
    (trivalentStrandPortInSumLeft
      unitCAResolution unitABResolution leftInternalAtSecond).slot := by
  rw [leftBlockAtFirst_slot, leftBlockAtSecond_slot]
  omega

end YMGap.Continuum.SU2TrivalentStrandPortContinuationObstruction

#print axioms YMGap.Continuum.SU2TrivalentStrandPortContinuationObstruction.unitCAResolution
#print axioms YMGap.Continuum.SU2TrivalentStrandPortContinuationObstruction.unitBCResolution
#print axioms YMGap.Continuum.SU2TrivalentStrandPortContinuationObstruction.unitABResolution
#print axioms YMGap.Continuum.SU2TrivalentStrandPortContinuationObstruction.vertexwise_left_blocks_do_not_preserve_same_slot
