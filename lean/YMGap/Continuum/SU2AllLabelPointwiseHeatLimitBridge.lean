/-
# Limit bridge for the completed SU(2) pointwise heat kernel

`SU2AllLabelPointwiseHeatCompletion` constructs a `CReal` whose rational
approximations are exactly the finite pointwise heat partials.  This small
bridge records the corresponding external convergence statement:

    N |-> ofQ' (pointwiseHeatPartial w x N)

converges to `allLabelPointwiseHeat w x ...` in `CReal.ConvergesTo`.

It then packages the completed value in the one-factor corridor consumed by
`BF4CompletedHeatRetainedConsumer`, and proves constructive uniqueness:
every other `CReal` limit of the same lifted finite partials is `CReal.Equiv`
to the canonical completion.

Honest scope: this is a value/completion bridge at one rational nome and one
class coordinate.  It does not identify the value with an interacting BF4
slab factor and does not assert a spacing-uniform physical nome window.

## Axiom gate

Constructive `CReal` convergence and exact `Q'` arithmetic only.  No
`Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion
import YMGap.Continuum.BF4CompletedHeatRetainedConsumer
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.SU2AllLabelPointwiseHeatLimitBridge

open YMGap.Constructive
open YMGap.Continuum.BF4CompletedHeatRetainedConsumer
open YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor

/-! ## 1. The finite partials converge to the canonical completion -/

/-- The `CReal`-embedded finite pointwise heat partials converge to the
canonical all-label completion.  This is the direct bridge from the internal
approximation field of `allLabelPointwiseHeat` to the external
`CReal.ConvergesTo` API. -/
theorem pointwiseHeatPartials_converge
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    CReal.ConvergesTo
      (fun N =>
        CReal.ofQ' (pointwiseHeatPartial w x N))
      (allLabelPointwiseHeat
        w x hw0 hw hxLower hxUpper) := by
  simpa only [allLabelPointwiseHeat_approx] using
    (CReal.convergesTo_self
      (allLabelPointwiseHeat
        w x hw0 hw hxLower hxUpper))

/-! ## 2. Completed one-factor corridor package -/

/-- The canonical all-label pointwise heat value, packaged directly in the
completed one-factor corridor used by the retained BF4 product consumer. -/
def allLabelPointwiseHeat_completedCorridor
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    CompletedOneFactorHeatCorridor
      (allLabelPointwiseHeat
        w x hw0 hw hxLower hxUpper) where
  lower :=
    allLabelPointwiseHeat_ge_floor
      hw0 hw hxLower hxUpper
  upper :=
    allLabelPointwiseHeat_le_ceiling
      hw0 hw hxLower hxUpper

/-- Witness-bearing completion certificate type: a completed value, its
convergence from the specified finite partials, and its exact one-factor
corridor. -/
structure PointwiseHeatLimitCertificate (w x : Q') : Type where
  value : CReal
  convergence :
    CReal.ConvergesTo
      (fun N =>
        CReal.ofQ' (pointwiseHeatPartial w x N))
      value
  corridor : CompletedOneFactorHeatCorridor value

/-- Witness-bearing completion certificate: the canonical completed value,
its convergence from finite partials, and its exact one-factor corridor are
returned together as `Type`-level data. -/
def allLabelPointwiseHeat_limitCertificate
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    PointwiseHeatLimitCertificate w x where
  value :=
    allLabelPointwiseHeat
      w x hw0 hw hxLower hxUpper
  convergence :=
    pointwiseHeatPartials_converge
      hw0 hw hxLower hxUpper
  corridor :=
    allLabelPointwiseHeat_completedCorridor
      hw0 hw hxLower hxUpper

/-! ## 3. Constructive uniqueness of the completed value -/

private theorem crealEquiv_refl (value : CReal) :
    CReal.Equiv value value :=
  SumOfSquares.Equiv_of_approx_eqv
    (fun _ => Q'.eqv_refl _)

/-- Any other constructive-real limit of the same lifted finite pointwise
heat partials is equivalent to the canonical all-label heat value. -/
theorem allLabelPointwiseHeat_equiv_of_converges
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (other : CReal)
    (other_converges :
      CReal.ConvergesTo
        (fun N =>
          CReal.ofQ' (pointwiseHeatPartial w x N))
        other) :
    CReal.Equiv
      (allLabelPointwiseHeat
        w x hw0 hw hxLower hxUpper)
      other :=
  CReal.Equiv_of_limit_of_equal
    (fun N =>
      crealEquiv_refl
        (CReal.ofQ' (pointwiseHeatPartial w x N)))
    (pointwiseHeatPartials_converge
      hw0 hw hxLower hxUpper)
    other_converges

/-- Symmetric uniqueness form, convenient when a downstream construction
chooses the competing limit as its left-hand representative. -/
theorem allLabelPointwiseHeat_equiv_of_converges_symm
    {w x : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (other : CReal)
    (other_converges :
      CReal.ConvergesTo
        (fun N =>
          CReal.ofQ' (pointwiseHeatPartial w x N))
        other) :
    CReal.Equiv
      other
      (allLabelPointwiseHeat
        w x hw0 hw hxLower hxUpper) :=
  CReal.Equiv.symm
    (allLabelPointwiseHeat_equiv_of_converges
      hw0 hw hxLower hxUpper other other_converges)

end YMGap.Continuum.SU2AllLabelPointwiseHeatLimitBridge

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.SU2AllLabelPointwiseHeatLimitBridge.pointwiseHeatPartials_converge
#print axioms YMGap.Continuum.SU2AllLabelPointwiseHeatLimitBridge.allLabelPointwiseHeat_completedCorridor
#print axioms YMGap.Continuum.SU2AllLabelPointwiseHeatLimitBridge.allLabelPointwiseHeat_limitCertificate
#print axioms YMGap.Continuum.SU2AllLabelPointwiseHeatLimitBridge.allLabelPointwiseHeat_equiv_of_converges
#print axioms YMGap.Continuum.SU2AllLabelPointwiseHeatLimitBridge.allLabelPointwiseHeat_equiv_of_converges_symm
