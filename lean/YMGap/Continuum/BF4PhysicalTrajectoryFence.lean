/-
# BF4 physical block-trajectory fence

The BF4 scalar arithmetic is now strong enough to consume a genuine
four-dimensional block trajectory:

* `AFTrajectoryCertificate` consumes a cubic asymptotic-freedom recurrence;
* `BF4AFHeatSpacing` turns an `AFEnvelope` into the needed heat-time/spacing
  inequality;
* `GroupedAllLabelHaarRefresh` supplies exact scalar heat-semigroup arithmetic;
* `ConstructiveRefreshContraction` consumes a finite refresh certificate.

None of those declarations identifies its scalar data with the iterate of an
actual four-dimensional grouped Haar block operator.  This file makes one
operator-level obstruction kernel-checkable.

`HeatKernelRGStep.BondMovingResidual` is documented as bounding the deviation of
`fullStepWeight` from `decimatedWeight`.  Its field `residual_bound`, however,
contains only

    0 <= delta  and  delta <= resC * a * cutoff.

It does not mention either weight.  Consequently the record permits replacing
`fullStepWeight` by an arbitrary rational while preserving every residual-budget
field.  In particular it admits a record with `delta = 0` whose full-step weight
is not the decimated weight.  The theorems below exhibit that countermodel.

`CoupledBondMovingResidual` is the fail-closed repair: it adds the missing
inequality

    |fullStepWeight - decimatedWeight| <= delta.

For this strengthened interface, `delta = 0` really does imply exact
form-preservation.  `LinkedBondMovingTrajectory` then names the second missing
piece: the full-step output at scale `k` must be identified with the input weight
at scale `k+1`.

This file deliberately constructs no four-dimensional inhabitant.  It proves
that the existing `BondMovingResidual` cannot supply the physical trajectory
identification advertised in prose, and states the minimum repaired interface
that a genuine grouped block-map construction must inhabit before its AF
envelope or bare linear floor can be called physical.
-/

import YMGap.Continuum.BF4AFHeatSpacing
import YMGap.Continuum.GroupedAllLabelHaarRefresh
import YMGap.Continuum.PhysicalRGSelfSimilar
import YMGap.Continuum.ConstructiveRefreshContraction

namespace YMGap.Continuum.BF4PhysicalTrajectoryFence

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.HeatKernelRGStep

/-! ## 1. The present residual record is underdetermined -/

/-- Replace the alleged physical full-step weight while preserving every
residual-budget field and the exact decimated weight.

This constructor is possible precisely because `BondMovingResidual.residual_bound`
does not relate `fullStepWeight` to `decimatedWeight` or `delta`. -/
def replaceFullStepWeight
    {b : Nat} {a w : Q'} (R : BondMovingResidual b a w) (replacement : Q') :
    BondMovingResidual b a w where
  delta := R.delta
  delta_nonneg := R.delta_nonneg
  resC := R.resC
  resC_nonneg := R.resC_nonneg
  cutoff := R.cutoff
  cutoff_nonneg := R.cutoff_nonneg
  fullStepWeight := replacement
  decimatedWeight := R.decimatedWeight
  decimated_eq := R.decimated_eq
  residual_bound := R.residual_bound

theorem replaceFullStepWeight_delta
    {b : Nat} {a w : Q'} (R : BondMovingResidual b a w) (replacement : Q') :
    (replaceFullStepWeight R replacement).delta = R.delta :=
  rfl

theorem replaceFullStepWeight_fullStep
    {b : Nat} {a w : Q'} (R : BondMovingResidual b a w) (replacement : Q') :
    (replaceFullStepWeight R replacement).fullStepWeight = replacement :=
  rfl

theorem replaceFullStepWeight_decimated
    {b : Nat} {a w : Q'} (R : BondMovingResidual b a w) (replacement : Q') :
    (replaceFullStepWeight R replacement).decimatedWeight =
      R.decimatedWeight :=
  rfl

/-- Closed countermodel: start with the exact hierarchical record at
`b = a = w = 1`, retain its zero residual budget, and replace the full-step
weight by zero. -/
def zeroDeltaWrongFullStep : BondMovingResidual 1 1 1 :=
  replaceFullStepWeight
    (hierarchicalBondMovingResidual 1 1 1 (by decide)) 0

/-- The countermodel still reports zero bond-moving deviation. -/
theorem zeroDeltaWrongFullStep_delta_zero :
    zeroDeltaWrongFullStep.delta = 0 :=
  rfl

/-- The countermodel still carries the exact decimated weight `1`. -/
theorem zeroDeltaWrongFullStep_decimated_one :
    zeroDeltaWrongFullStep.decimatedWeight.eqv 1 := by
  decide

/-- But its alleged full-step weight is `0`, not its decimated weight. -/
theorem zeroDeltaWrongFullStep_not_exact :
    ¬ zeroDeltaWrongFullStep.fullStepWeight.eqv
        zeroDeltaWrongFullStep.decimatedWeight := by
  decide

/-- **Kernel-checked no-go.**  On the current record, `delta = 0` does not imply
that the full block step preserves the heat-kernel/decimated weight. -/
theorem delta_zero_does_not_imply_form_preservation :
    ¬ (∀ R : BondMovingResidual 1 1 1,
        R.delta = 0 → R.fullStepWeight.eqv R.decimatedWeight) := by
  intro h
  exact zeroDeltaWrongFullStep_not_exact
    (h zeroDeltaWrongFullStep zeroDeltaWrongFullStep_delta_zero)

/-! ## 2. A fail-closed residual interface -/

/-- A bond-moving residual whose deviation budget actually controls the two
weights it is meant to compare.

This is intentionally a wrapper rather than a modification of the legacy
record: existing inhabitants do not silently acquire the missing theorem. -/
structure CoupledBondMovingResidual (b : Nat) (a w : Q') : Type where
  base : BondMovingResidual b a w
  deviation_control :
    Q'.abs (base.fullStepWeight - base.decimatedWeight) ≤ base.delta

namespace CoupledBondMovingResidual

/-- Under the repaired interface, a zero residual forces equality of the
full-step and decimated weights. -/
theorem form_preserving_of_delta_zero
    {b : Nat} {a w : Q'} (R : CoupledBondMovingResidual b a w)
    (hzero : R.base.delta.eqv 0) :
    R.base.fullStepWeight.eqv R.base.decimatedWeight := by
  let difference :=
    R.base.fullStepWeight - R.base.decimatedWeight
  have habs_le_zero : Q'.abs difference ≤ (0 : Q') :=
    Q'.le_trans' _ _ _ R.deviation_control (Q'.le_of_eqv hzero)
  have hdifference_le_zero : difference ≤ (0 : Q') :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self difference) habs_le_zero
  have hneg_difference_le_zero : -difference ≤ (0 : Q') :=
    Q'.le_trans' _ _ _ (Q'.neg_le_abs difference) habs_le_zero
  have hzero_le_difference : (0 : Q') ≤ difference := by
    have hnegated : -(0 : Q') ≤ -(-difference) :=
      Q'.neg_le_neg hneg_difference_le_zero
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (by decide : (0 : Q').eqv (-(0 : Q'))))
      (Q'.le_trans' _ _ _ hnegated
        (Q'.le_of_eqv (Q'.neg_neg_eqv difference)))
  have hdifference_zero : difference.eqv 0 :=
    Int.le_antisymm hdifference_le_zero hzero_le_difference
  exact q_eqv_of_sub_zero hdifference_zero

/-- The exact hierarchical residual lifts to the repaired interface. -/
def hierarchical
    (b : Nat) (a w : Q') (ha : (0 : Q') ≤ a) :
    CoupledBondMovingResidual b a w where
  base := hierarchicalBondMovingResidual b a w ha
  deviation_control := by
    change Q'.abs (mkDecimate b w - mkDecimate b w) ≤ (0 : Q')
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.abs_eqv_congr (Q'.add_neg_self_eqv (mkDecimate b w)))
        (by decide))

theorem hierarchical_form_preserving
    (b : Nat) (a w : Q') (ha : (0 : Q') ≤ a) :
    (hierarchical b a w ha).base.fullStepWeight.eqv
      (hierarchical b a w ha).base.decimatedWeight :=
  form_preserving_of_delta_zero (hierarchical b a w ha)
    (by exact Q'.eqv_refl 0)

/-- The closed countermodel cannot be lifted to the repaired interface using its
claimed zero deviation: the missing inequality is genuinely false for it. -/
theorem wrongFullStep_fails_deviation_control :
    ¬ Q'.abs
        (zeroDeltaWrongFullStep.fullStepWeight -
          zeroDeltaWrongFullStep.decimatedWeight) ≤
        zeroDeltaWrongFullStep.delta := by
  decide

end CoupledBondMovingResidual

/-! ## 3. The minimum iterate-identification fence -/

/-- A sequence of weights and spacings is a linked block-map trajectory only
when each full-step output is explicitly identified with the next input.

The legacy `BondMovingResidual`, the scalar grouped heat coordinate, and the AF
spacing schedule do not provide such a field.  A genuine four-dimensional BF4
constructor must produce this data (and then separately relate `weight` and
`spacing` to its AF heat time and physical lattice scale). -/
structure LinkedBondMovingTrajectory (b : Nat) : Type where
  spacing : Nat → Q'
  spacing_pos : ∀ k, (0 : Q') < spacing k
  weight : Nat → Q'
  step :
    ∀ k, CoupledBondMovingResidual b (spacing k) (weight k)
  next_identification :
    ∀ k, (weight (k + 1)).eqv (step k).base.fullStepWeight

/-- On a linked trajectory, an exact (`delta = 0`) step really sends the current
weight to its exact decimation.  This is the implication that the legacy
residual record alone cannot prove. -/
theorem linked_exact_step
    {b : Nat} (T : LinkedBondMovingTrajectory b) (k : Nat)
    (hzero : (T.step k).base.delta.eqv 0) :
    (T.weight (k + 1)).eqv (mkDecimate b (T.weight k)) := by
  refine Q'.eqv_trans _ _ _
    (T.next_identification k) ?_
  refine Q'.eqv_trans _ _ _
    (CoupledBondMovingResidual.form_preserving_of_delta_zero
      (T.step k) hzero) ?_
  exact Q'.eqv_of_eq (T.step k).base.decimated_eq

/-! ## 4. Audit conclusion

The countermodel is a theorem about the current Lean declarations, not an
argument from a failed repository search.  Therefore:

* `BondMovingResidual.delta = 0` cannot discharge the tower descent claimed by
  `PhysicalRGSelfSimilar` without an additional coupling theorem;
* `groupedHeatCoordinate` is exact scalar `qpow` arithmetic, but is not the
  output of a source-indexed physical block operator in the current interface;
* `PhysicalCorridorDominationMass` supplies only a positive scalar coefficient;
* `AFTrajectoryCertificate` and `AFExpLift.blockSpacing` supply scalar running
  and a constructed spacing schedule, but no equality with a physical block
  iterate.

The next legitimate milestone is therefore an inhabitant of
`LinkedBondMovingTrajectory` for the actual four-dimensional grouped operator,
plus the heat-coordinate and physical-spacing identifications.  Until then the
Padé `AFEnvelope` and `BareAFImpliesLinearFloor` remain bare scalar diagnostics.
-/

end YMGap.Continuum.BF4PhysicalTrajectoryFence

#print axioms YMGap.Continuum.BF4PhysicalTrajectoryFence.replaceFullStepWeight
#print axioms YMGap.Continuum.BF4PhysicalTrajectoryFence.zeroDeltaWrongFullStep
#print axioms YMGap.Continuum.BF4PhysicalTrajectoryFence.zeroDeltaWrongFullStep_not_exact
#print axioms YMGap.Continuum.BF4PhysicalTrajectoryFence.delta_zero_does_not_imply_form_preservation
#print axioms YMGap.Continuum.BF4PhysicalTrajectoryFence.CoupledBondMovingResidual.form_preserving_of_delta_zero
#print axioms YMGap.Continuum.BF4PhysicalTrajectoryFence.CoupledBondMovingResidual.hierarchical
#print axioms YMGap.Continuum.BF4PhysicalTrajectoryFence.CoupledBondMovingResidual.wrongFullStep_fails_deviation_control
#print axioms YMGap.Continuum.BF4PhysicalTrajectoryFence.linked_exact_step
