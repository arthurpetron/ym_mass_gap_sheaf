/-
# Completed SU(2) pointwise heat factors give retained BF4 Harnack order

`SU2AllLabelPointwiseHeatCompletion` constructs the genuine all-character
central SU(2) class kernel as a `CReal` for every rational

    0 <= w <= 1/2,    -1 <= x <= 1,

and proves the sound corridor

    1055/2272 <= K_w(x) <= 3489/2272.

`BF4CompletedHeatRetainedConsumer` proves that any literal product of 23
completed factors in this corridor has the BF4 projective spread

    (3489/1055)^23.

This file performs the exact composition.  The local retained weight is now
the completed SU(2) pointwise heat kernel itself, not an abstract `CReal`
carrying assumed bounds.

Honest scope: the result concerns a literal 23-factor product on a supplied
retained carrier.  It does not identify that product with the interacting
finite BF4 spin-foam Gram kernel, whose rank-one amplitudes can have signed
off-diagonal products.  Nor does the strong-coupling window `w <= 1/2`
contain the asymptotically-free continuum trajectory `w -> 1`.

## Axiom gate

Only the two imported constructive layers and exact finite-list data are
used.  There is no `Classical.*`, `Real`, `native_decide`, `sorry`, custom
axiom, or noncomputable declaration.
-/

import YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion
import YMGap.Continuum.BF4CompletedHeatRetainedConsumer

namespace YMGap.Continuum.BF4CompletedSU2PointwiseRetainedHarnack

open YMGap.Constructive
open YMGap.Continuum.BF4CompletedHeatRetainedConsumer
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.BF4RetainedKineticWindow
open YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor

/-! ## 1. The literal completed local factor and retained product -/

/-- A supplied retained class coordinate evaluated by the genuine completed
SU(2) pointwise heat series. -/
def completedPointwiseLocalHeat
    {Source Target State Factor : Type}
    (w x : Source → Target → List State → Factor → Q')
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
    (source : Source) (target : Target)
    (path : List State) (factor : Factor) : CReal :=
  allLabelPointwiseHeat
    (w source target path factor)
    (x source target path factor)
    (w_nonnegative source target path factor)
    (w_le_half source target path factor)
    (x_lower source target path factor)
    (x_upper source target path factor)

/-- Product of the completed local heat factors on the supplied retained
factor list. -/
def completedPointwiseRetainedKinetic
    {Source Target State Factor : Type}
    (factors : List Factor)
    (w x : Source → Target → List State → Factor → Q')
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
    (source : Source) (target : Target)
    (path : List State) : CReal :=
  completedFactorProduct
    (completedPointwiseLocalHeat
      w x w_nonnegative w_le_half x_lower x_upper
      source target path)
    factors

/-! ## 2. Exact completed BF4 Harnack composition -/

/-- Every literal completed local SU(2) heat factor carries the exact
one-factor corridor consumed by the completed-product theorem. -/
def completedPointwiseLocalHeatCorridor
    {Source Target State Factor : Type}
    (w x : Source → Target → List State → Factor → Q')
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
    (source : Source) (target : Target)
    (path : List State) (factor : Factor) :
    CompletedOneFactorHeatCorridor
      (completedPointwiseLocalHeat
        w x w_nonnegative w_le_half x_lower x_upper
        source target path factor) where
  lower :=
    allLabelPointwiseHeat_ge_floor
      (w_nonnegative source target path factor)
      (w_le_half source target path factor)
      (x_lower source target path factor)
      (x_upper source target path factor)
  upper :=
    allLabelPointwiseHeat_le_ceiling
      (w_nonnegative source target path factor)
      (w_le_half source target path factor)
      (x_lower source target path factor)
      (x_upper source target path factor)

/-- **Completed all-label retained BF4 Harnack theorem.**  A literal list of
23 completed pointwise SU(2) heat factors has the exact BF4 floor, ceiling,
and pathwise eventual-order spread `(3489/1055)^23`. -/
def completedPointwiseRetainedHarnack
    {Source Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (w x : Source → Target → List State → Factor → Q')
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
    CompletedRetainedKineticHarnackData
      paths
      (completedPointwiseRetainedKinetic
        factors w x
        w_nonnegative w_le_half x_lower x_upper)
      sources targets := by
  exact completedBF4RetainedKineticHarnack
    paths factors factor_count
    (completedPointwiseLocalHeat
      w x w_nonnegative w_le_half x_lower x_upper)
    sources targets
    (fun _source _hsource _target _htarget
      _path _hpath factor _hfactor =>
        completedPointwiseLocalHeatCorridor
          w x w_nonnegative w_le_half x_lower x_upper
          _source _target _path factor)

/-- The composed all-label retained datum has exactly the finite BF4 spread;
completion introduces no additional factor. -/
theorem completedPointwiseRetainedHarnack_spread
    {Source Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (w x : Source → Target → List State → Factor → Q')
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

end YMGap.Continuum.BF4CompletedSU2PointwiseRetainedHarnack

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4CompletedSU2PointwiseRetainedHarnack.completedPointwiseLocalHeat
#print axioms YMGap.Continuum.BF4CompletedSU2PointwiseRetainedHarnack.completedPointwiseLocalHeatCorridor
#print axioms YMGap.Continuum.BF4CompletedSU2PointwiseRetainedHarnack.completedPointwiseRetainedHarnack
#print axioms YMGap.Continuum.BF4CompletedSU2PointwiseRetainedHarnack.completedPointwiseRetainedHarnack_spread
