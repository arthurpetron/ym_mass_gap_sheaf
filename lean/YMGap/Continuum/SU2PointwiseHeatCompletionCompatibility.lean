/-
# Compatibility of the two SU(2) pointwise heat completions

There are two constructive completions of the same SU(2) pointwise character
series in this library:

* `allLabelPointwiseHeat`, using the uniform strong-coupling tail estimate
  on `0 <= w <= 1/2`;
* `pointwiseHeatCReal`, using a spacing-dependent initial label cutoff for
  every `0 < w < 1`.

On their overlap `0 < w <= 1/2`, this module proves that the two `CReal`
values are constructively equivalent.  The proof uses a common cofinal
sequence, not equality of their raw approximation indices:

    spacing prefix at 2+M
      ≈ standard prefix at 2 + (spacingLabelCutoff w + M)
      ≈ fixed partial at spacingLabelCutoff w + M.

Both shifted sequences converge to their respective completions, so
`CReal.Equiv_of_limit_of_equal` identifies the limits.

Honest scope: this is a pointwise overlap theorem.  It supplies neither a
spacing-uniform strong-coupling window along an asymptotically-free trajectory
nor an interacting BF4 slab identification.

## Axiom gate

Constructive `CReal.ConvergesTo` and exact `Q'` arithmetic only.  No
`Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
import YMGap.Continuum.SU2AllLabelPointwiseHeatLimitBridge

namespace YMGap.Continuum.SU2PointwiseHeatCompletionCompatibility

open YMGap.Constructive
open YMGap.Continuum.BF4CompletedHeatRetainedConsumer
open YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
open YMGap.Continuum.SU2AllLabelPointwiseHeatLimitBridge
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Cofinal convergence and the exact prefix bridge -/

/-- A fixed additive shift of the term index preserves
`CReal.ConvergesTo`.  The old convergence stage still works because
`N <= shift + N`. -/
private theorem convergesTo_add_shift
    {sequence : Nat → CReal} {limit : CReal}
    (h : CReal.ConvergesTo sequence limit)
    (shift : Nat) :
    CReal.ConvergesTo
      (fun N => sequence (shift + N)) limit := by
  intro ε hε
  obtain ⟨stage, hstage⟩ := h ε hε
  refine ⟨stage, fun N hN => ?_⟩
  exact hstage (shift + N) (by omega)

/-- Shifting the spacing-dependent prefix by two labels makes it exactly,
up to rational setoid equality, a cofinal shift of the fixed displayed
partial sequence.  This avoids any need to prove
`2 <= spacingLabelCutoff w`. -/
theorem spacingPointwiseHeatPartial_two_add_eqv
    (w x : Q') (M : Nat) :
    spacingPointwiseHeatPartial w x (2 + M) ≈
      pointwiseHeatPartial
        w x (spacingLabelCutoff w + M) := by
  unfold spacingPointwiseHeatPartial
  rw [show
    spacingLabelCutoff w + (2 + M) =
      2 + (spacingLabelCutoff w + M) by omega]
  exact standardPointwiseHeatPartial_eqv
    w x (spacingLabelCutoff w + M)

private theorem equiv_ofQ'_of_eqv
    {a b : Q'} (h : a ≈ b) :
    CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) :=
  SumOfSquares.Equiv_of_approx_eqv
    (fun _ => h)

/-- The two-shifted spacing-dependent prefix sequence converges to the
spacing-dependent completion. -/
theorem spacingPointwiseHeatPartial_two_add_converges
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    CReal.ConvergesTo
      (fun M =>
        CReal.ofQ'
          (spacingPointwiseHeatPartial w x (2 + M)))
      (pointwiseHeatCReal
        hw0 hw1 hxLower hxUpper) :=
  convergesTo_add_shift
    (spacingPointwiseHeatPartial_converges
      hw0 hw1 hxLower hxUpper)
    2

/-- The fixed partial sequence shifted by the spacing-dependent label cutoff
still converges to the fixed all-label completion. -/
theorem pointwiseHeatPartial_spacingShift_converges
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    CReal.ConvergesTo
      (fun M =>
        CReal.ofQ'
          (pointwiseHeatPartial
            w x (spacingLabelCutoff w + M)))
      (allLabelPointwiseHeat
        w x hw0 hw hxLower hxUpper) :=
  convergesTo_add_shift
    (pointwiseHeatPartials_converge
      hw0 hw hxLower hxUpper)
    (spacingLabelCutoff w)

/-! ## 2. Compatibility and corridor transfer on the overlap -/

/-- **Compatibility of the two completed pointwise heat kernels.**
For `0 < w <= 1/2` and `x ∈ [-1,1]`, the arbitrary-spacing completion is
constructively equivalent to the fixed-corridor all-label completion. -/
theorem pointwiseHeatCReal_equiv_allLabelPointwiseHeat
    {w x : Q'} (hw0 : (0 : Q') < w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    CReal.Equiv
      (pointwiseHeatCReal
        hw0
        (Q'.lt_of_le_of_lt hw (by decide))
        hxLower hxUpper)
      (allLabelPointwiseHeat
        w x (Q'.le_of_lt hw0) hw hxLower hxUpper) := by
  let hw1 : w < (1 : Q') :=
    Q'.lt_of_le_of_lt hw (by decide)
  exact CReal.Equiv_of_limit_of_equal
    (fun M =>
      equiv_ofQ'_of_eqv
        (spacingPointwiseHeatPartial_two_add_eqv
          w x M))
    (spacingPointwiseHeatPartial_two_add_converges
      hw0 hw1 hxLower hxUpper)
    (pointwiseHeatPartial_spacingShift_converges
      (Q'.le_of_lt hw0) hw hxLower hxUpper)

/-- On the overlap, the arbitrary-spacing completion inherits the exact
completed one-factor corridor from the fixed completion. -/
def pointwiseHeatCReal_completedCorridor
    {w x : Q'} (hw0 : (0 : Q') < w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    CompletedOneFactorHeatCorridor
      (pointwiseHeatCReal
        hw0
        (Q'.lt_of_le_of_lt hw (by decide))
        hxLower hxUpper) := by
  let completionEquiv :=
    pointwiseHeatCReal_equiv_allLabelPointwiseHeat
      hw0 hw hxLower hxUpper
  exact
    { lower :=
        YMGap.Constructive.SU3CharFactor.geRat_of_equiv
          completionEquiv
          (allLabelPointwiseHeat_ge_floor
            (Q'.le_of_lt hw0) hw hxLower hxUpper)
      upper :=
        CReal.leRat_of_equiv
          completionEquiv
          (allLabelPointwiseHeat_le_ceiling
            (Q'.le_of_lt hw0) hw hxLower hxUpper) }

end YMGap.Continuum.SU2PointwiseHeatCompletionCompatibility

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.SU2PointwiseHeatCompletionCompatibility.spacingPointwiseHeatPartial_two_add_eqv
#print axioms YMGap.Continuum.SU2PointwiseHeatCompletionCompatibility.spacingPointwiseHeatPartial_two_add_converges
#print axioms YMGap.Continuum.SU2PointwiseHeatCompletionCompatibility.pointwiseHeatPartial_spacingShift_converges
#print axioms YMGap.Continuum.SU2PointwiseHeatCompletionCompatibility.pointwiseHeatCReal_equiv_allLabelPointwiseHeat
#print axioms YMGap.Continuum.SU2PointwiseHeatCompletionCompatibility.pointwiseHeatCReal_completedCorridor
