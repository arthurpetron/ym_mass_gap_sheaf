/-
# Cutoff quantifier fence for the legacy six-j carrier

`PartitionBeyondTree.SixJRecoupling.biedenharn_elliott` quantifies over every
cutoff `D` without requiring the admissible fusion support to lie below `D`.
At `D = 0` its right side is the empty sum, while the all-zero fusion channel
on the left has weight one.  The carrier is therefore uninhabitable as stated.

This is a semantic fence around the legacy reduction, not a six-j no-go
theorem.  A corrected carrier must impose an explicit support/cutoff condition
(as the later guarded Dougall statement does).
-/

import YMGap.Continuum.PartitionBeyondTree

namespace YMGap.Continuum.SixJRecouplingCutoffFence

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PartitionBeyondTree

/-- The legacy all-cutoff six-j carrier is contradictory already at the empty
cutoff and the all-zero fusion labels. -/
theorem sixJRecoupling_uninhabited : ¬ Nonempty SixJRecoupling := by
  intro hnonempty
  obtain ⟨R⟩ := hnonempty
  have h := R.biedenharn_elliott 0 0 0 0 0 0
  have hleft : fusionInd 0 0 0 = 1 := by
    unfold fusionInd
    rw [if_pos]
    decide
  rw [hleft] at h
  change ((1 : Q') * 1).eqv 0 at h
  have hone : (1 : Q').eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv 1)) h
  exact absurd hone (by decide)

/-- In particular no term of the legacy carrier can be supplied to the
beyond-tree partition wrapper. -/
theorem no_sixJRecoupling : SixJRecoupling → False := by
  intro R
  exact sixJRecoupling_uninhabited ⟨R⟩

end YMGap.Continuum.SixJRecouplingCutoffFence

#print axioms YMGap.Continuum.SixJRecouplingCutoffFence.sixJRecoupling_uninhabited
#print axioms YMGap.Continuum.SixJRecouplingCutoffFence.no_sixJRecoupling
