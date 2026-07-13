/-
# A scalar tree-to-tree recoupling cannot encode a mixed SU(2) F-move

The abstract scalar carrier `UniqueRecoupling` is adequate only when the entire
recoupling space has one channel.  Trivalent multiplicity-freeness does not
imply that: four factors have several admissible intermediate labels, and a
physical F-move is a matrix.

This file banks a concrete kernel-checked fence.  In the already-derived
mixed-label `(2,2,1) -> 1` transvectant block, the `e=0` source map has a
nonzero coefficient on an input/output cell where the `f=1` target map is zero.
Therefore no rational scalar multiple of that one target channel can equal the
source map.  The missing `f=3` channel is essential.

No classical reasoning, native decision procedure, proof hole, or new axiom.
-/

import YMGap.Continuum.SU2TransvectantMixedPentagon

namespace YMGap.Continuum.ScalarRecouplingMultichannelFence

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantMixedPentagon

/-- The separating cell: on `(mono 0, mono 2, mono 1)` at output slot `1`, the
source `e=0` map is `4`, the `f=1` target map is zero, and the omitted `f=3`
target map is `12`. -/
theorem mixed221_separating_cell :
    (triLeft 2 2 1 1 0 (mono 0) (mono 2) (mono 1) 1).eqv 4 ∧
    (triRight 2 2 1 1 1 (mono 0) (mono 2) (mono 1) 1).eqv 0 ∧
    (triRight 2 2 1 1 3 (mono 0) (mono 2) (mono 1) 1).eqv 12 := by
  decide

/-- **Scalar-collapse fence.**  No rational scalar times the single `f=1`
channel represents the physical mixed `e=0` source map. -/
theorem no_scalar_represents_mixed221_e0 (q : Q') :
    ¬ TriMapEqv 2 2 1 1 (triLeft 2 2 1 1 0)
      (fun x y z => scaleForm q (triRight 2 2 1 1 1 x y z)) := by
  intro h
  have hcell := h 0 (by decide) 2 (by decide) 1 (by decide) 1 (by decide)
  have hleft := mixed221_separating_cell.1
  have hright := mixed221_separating_cell.2.1
  have hscaled :
      (scaleForm q (triRight 2 2 1 1 1 (mono 0) (mono 2) (mono 1)) 1).eqv 0 := by
    refine Q'.eqv_trans _ (q * 0) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left q _ 0 hright
    · exact Q'.mul_zero_eqv q
  have hfourzero : ((4 : Q')).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
      (Q'.eqv_trans _ _ _ hcell hscaled)
  exact (by decide : ¬ ((4 : Q')).eqv 0) hfourzero

/-- In particular the first row's off-diagonal `f=3` contribution is not
dispensable: the exact mixed associator cannot be replaced by a one-channel
scalar recoupling. -/
theorem mixed221_requires_multiple_channels :
    ∀ q : Q',
      ¬ TriMapEqv 2 2 1 1 (triLeft 2 2 1 1 0)
        (fun x y z => scaleForm q (triRight 2 2 1 1 1 x y z)) :=
  no_scalar_represents_mixed221_e0

end YMGap.Continuum.ScalarRecouplingMultichannelFence

#print axioms YMGap.Continuum.ScalarRecouplingMultichannelFence.mixed221_separating_cell
#print axioms YMGap.Continuum.ScalarRecouplingMultichannelFence.no_scalar_represents_mixed221_e0
#print axioms YMGap.Continuum.ScalarRecouplingMultichannelFence.mixed221_requires_multiple_channels
