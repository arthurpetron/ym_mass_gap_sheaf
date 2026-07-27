/-
# Completed SU(2) retained heat Harnack after conditional integration

This module composes two proved layers:

* `BF4CompletedSU2PointwiseRetainedHarnack` constructs the literal product of
  23 completed SU(2) pointwise heat factors and gives it the exact retained
  pathwise spread `(3489/1055)^23`;
* `BF4CompletedRetainedConditionalOrder` proves that multiplication by a
  common nonnegative rational interior-potential product and finite
  integration over retained paths preserve a completed pathwise Harnack
  order.

The resulting conditional Feynman--Kac kernel therefore has exactly
`bf4KineticSpread`; there is no completion loss and no
`potentialSpread ^ path.length` loss.

Honest scope: the theorem is polymorphic in the source carrier, so finite
matrix-index/source pairs may be used as sources and the same entrywise
statement follows.  It does not claim that entrywise order is Loewner/CP
order for arbitrary signed matrix coefficients.  The literal 23-factor
completed class kernel is also not identified here with the interacting BF4
spin-foam Gram kernel, and the hypothesis `w ≤ 1/2` is not the
asymptotically-free `w → 1` trajectory.

## Axiom gate

Only composition of the two imported constructive theorems is used.  There
is no `Classical.*`, `Real`, choice, `native_decide`, `sorry`, custom axiom,
or noncomputable declaration.
-/

import YMGap.Continuum.BF4CompletedSU2PointwiseRetainedHarnack
import YMGap.Continuum.BF4CompletedRetainedConditionalOrder

namespace YMGap.Continuum.BF4CompletedSU2ConditionalHarnack

open YMGap.Constructive
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.BF4CompletedHeatRetainedConsumer
open YMGap.Continuum.BF4CompletedRetainedConditionalOrder
open YMGap.Continuum.BF4CompletedSU2PointwiseRetainedHarnack
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor

/-! ## 1. The literal completed conditional kernel is nonnegative -/

/-- Finite conditional integration of the literal completed 23-factor
SU(2) retained kernel against a nonnegative rational path potential stays in
the constructive-real nonnegative cone. -/
theorem completedSU2ConditionalPathKernel_nonnegative
    {Source Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (w x :
      Source → Target → List State → Factor → Q')
    (w_nonnegative :
      ∀ source target path factor,
        (0 : Q') ≤ w source target path factor)
    (w_le_half :
      ∀ source target path factor,
        w source target path factor ≤ half)
    (x_lower :
      ∀ source target path factor,
        (-(1 : Q')) ≤ x source target path factor)
    (x_upper :
      ∀ source target path factor,
        x source target path factor ≤ (1 : Q'))
    (potential : State → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (sources : List Source) (targets : List Target)
    (source : Source) (hsource : source ∈ sources)
    (target : Target) (htarget : target ∈ targets) :
    ExpPos.geRat
      (completedConditionalPathPushforward
        paths
        (completedPointwiseRetainedKinetic
          factors w x
          w_nonnegative w_le_half x_lower x_upper)
        potential source target)
      0 := by
  let harnack :=
    completedPointwiseRetainedHarnack
      paths factors factor_count w x
      w_nonnegative w_le_half x_lower x_upper
      sources targets
  exact completedConditionalPathPushforward_nonnegative
    paths
    (completedPointwiseRetainedKinetic
      factors w x
      w_nonnegative w_le_half x_lower x_upper)
    potential potential_nonnegative source target
    (fun path hpath =>
      harnack.kinetic_nonnegative
        source hsource target htarget path hpath)

/-! ## 2. Exact spread after the conditional Feynman--Kac pushforward -/

/-- **Literal completed SU(2) conditional Harnack theorem.**  For any two
selected source rows and target column, every nonnegative rational interior
path potential survives finite path integration with exactly the BF4 kinetic
spread `(3489/1055)^23`. -/
theorem completedSU2ConditionalPathHarnack
    {Source Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (w x :
      Source → Target → List State → Factor → Q')
    (w_nonnegative :
      ∀ source target path factor,
        (0 : Q') ≤ w source target path factor)
    (w_le_half :
      ∀ source target path factor,
        w source target path factor ≤ half)
    (x_lower :
      ∀ source target path factor,
        (-(1 : Q')) ≤ x source target path factor)
    (x_upper :
      ∀ source target path factor,
        x source target path factor ≤ (1 : Q'))
    (potential : State → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (sources : List Source) (targets : List Target)
    (first : Source) (hfirst : first ∈ sources)
    (second : Source) (hsecond : second ∈ sources)
    (target : Target) (htarget : target ∈ targets) :
    CReal.leEv
      (completedConditionalPathPushforward
        paths
        (completedPointwiseRetainedKinetic
          factors w x
          w_nonnegative w_le_half x_lower x_upper)
        potential first target)
      (CReal.mul
        (CReal.ofQ' bf4KineticSpread)
        (completedConditionalPathPushforward
          paths
          (completedPointwiseRetainedKinetic
            factors w x
            w_nonnegative w_le_half x_lower x_upper)
          potential second target)) := by
  let harnack :=
    completedPointwiseRetainedHarnack
      paths factors factor_count w x
      w_nonnegative w_le_half x_lower x_upper
      sources targets
  exact completedConditionalPathPushforward_domination
    paths
    (completedPointwiseRetainedKinetic
      factors w x
      w_nonnegative w_le_half x_lower x_upper)
    potential potential_nonnegative
    sources targets harnack
    first hfirst second hsecond target htarget

/-- The scalar appearing in the literal conditional theorem is definitionally
the exact completed retained datum spread, recording that conditional
integration introduces no additional factor. -/
theorem completedSU2ConditionalPathHarnack_spread
    {Source Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (w x :
      Source → Target → List State → Factor → Q')
    (w_nonnegative :
      ∀ source target path factor,
        (0 : Q') ≤ w source target path factor)
    (w_le_half :
      ∀ source target path factor,
        w source target path factor ≤ half)
    (x_lower :
      ∀ source target path factor,
        (-(1 : Q')) ≤ x source target path factor)
    (x_upper :
      ∀ source target path factor,
        x source target path factor ≤ (1 : Q'))
    (sources : List Source) (targets : List Target) :
    (completedPointwiseRetainedHarnack
      paths factors factor_count w x
      w_nonnegative w_le_half x_lower x_upper
      sources targets).spread =
        bf4KineticSpread :=
  rfl

end YMGap.Continuum.BF4CompletedSU2ConditionalHarnack

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4CompletedSU2ConditionalHarnack.completedSU2ConditionalPathKernel_nonnegative
#print axioms YMGap.Continuum.BF4CompletedSU2ConditionalHarnack.completedSU2ConditionalPathHarnack
#print axioms YMGap.Continuum.BF4CompletedSU2ConditionalHarnack.completedSU2ConditionalPathHarnack_spread
