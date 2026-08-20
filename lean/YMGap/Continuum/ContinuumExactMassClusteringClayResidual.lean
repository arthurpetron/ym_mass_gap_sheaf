/-
M4w -- factor the remaining legacy Clay-target obligations after the exact
mass/clustering endpoint has fixed the shared OS/Wilson carrier.

`ContinuumExactMassClusteringTarget` already selects one continuum measure,
one full `ContinuumYMExistence` datum, the measure-linked reconstruction, the
Wilson GNS datum and completion, and a nontrivial clustering channel with a
positive exact logarithmic physical mass.  The older
`Rubric.ClayTargetPinned`, however, uses the distinct dimensionless transfer
margin `1 - separator` as its mass currency and asks for a separate legacy
continuum-limit carrier.

This module makes that comparison precise.  Once a target `T` is fixed, all
shared-stack objects and identity pins of `ClayTargetPinned` are canonical.
The residual below carries only the still-unbuilt legacy analytic data:

* continuum existence/tightness in the scorecard's older formulation;
* its volume/spacing limit datum, with continuum mass pinned to the legacy
  transfer margin of `T`'s reconstruction; and
* the scorecard's uniform-in-coupling clause.

The fixed-spacing scorecard line is already proved and is filled
unconditionally.  This does not identify the exact physical mass
`-log(separator)` with `1 - separator`, and it does not construct any residual
field.  Full same-action O(4) covariance remains stronger than the weak O(4)
slot inside the legacy limit datum.
-/

import YMGap.Continuum.ContinuumExactMassClusteringTarget
import YMGap.Rubric.ClayTargetPinned

namespace YMGap.Continuum.ContinuumExactMassClusteringClayResidual

open YMGap.Continuum.ContinuumExactMassClusteringTarget
open YMGap.Continuum.ContinuumExactMassClusteringTarget.ContinuumExactMassClusteringTarget
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.ContinuumYMStack
open YMGap.Continuum.OSAxioms
open YMGap.Continuum.OSReconstruction
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff
open YMGap.Rubric
open YMGap.Rubric.ClayTargetPinned

/-- Exactly the legacy analytic data not supplied by a fixed exact
mass/clustering target.  This structure is deliberately uninhabited. -/
structure LegacyClayPinnedExtensionResidual
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumExactMassClusteringTarget mu) : Type 2 where
  /-- The old scorecard's continuum construction and tightness package. -/
  continuumExistence : ClayScorecard.ClayContinuumExistence
  /-- The old continuum-limit package, on the OS2 proposition of `T`'s own
  bundle.  Its Euclidean-invariance parameter remains the weak legacy slot. -/
  limitData : ContinuumLimitData
    (IsOS2ReflectionPositivity T.existence.os_axioms.t
      T.existence.os_axioms.ht)
    ClayScorecard.RubricO4Restoration
  /-- The legacy continuum mass is pinned to the reconstruction margin.  This
  is intentionally not an equality with `T.canonicalPositiveMass`. -/
  massPinned : limitData.continuumMass =
    reconGapCReal T.wilson.reconstruction
  /-- The old scorecard's coupling-uniform floor. -/
  uniformInCoupling : ClayScorecard.RubricUniformInCoupling

namespace LegacyClayPinnedExtensionResidual

/-- Fill every shared-carrier and identity field of the legacy pinned target
from `T`; only the explicitly named residual analytic data are consumed. -/
def toClayTargetPinned
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumExactMassClusteringTarget mu)
    (R : LegacyClayPinnedExtensionResidual T) :
    ClayTargetPinned mu where
  bundle := T.existence.os_axioms
  recon := T.wilson.reconstruction
  wilson := T.wilson.wilson
  gnsData := T.wilson.wilson.toGNSData
  gns := T.wilson.wilson.toGNSData.gnsComplete
  fixedSpacing := ClayScorecard.clay_fixed_spacing_met
  ePinned := T.wilson.expectationPinned
  specPinned := rfl
  gnsPinned := rfl
  massGap :=
    ⟨reconGapCReal T.wilson.reconstruction,
      reconGapCReal_isPositive T.wilson.reconstruction⟩
  massGapPinned := rfl
  hasGap := T.wilson.reconstruction.hasGap
  continuumExistence := R.continuumExistence
  limitData := R.limitData
  massPinned := R.massPinned
  uniformInCoupling := R.uniformInCoupling

/-- The extension preserves the exact target's reconstruction definitionally. -/
theorem toClayTargetPinned_recon
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumExactMassClusteringTarget mu)
    (R : LegacyClayPinnedExtensionResidual T) :
    (R.toClayTargetPinned T).recon = T.wilson.reconstruction :=
  rfl

/-- The extension preserves the exact target's Wilson datum definitionally. -/
theorem toClayTargetPinned_wilson
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumExactMassClusteringTarget mu)
    (R : LegacyClayPinnedExtensionResidual T) :
    (R.toClayTargetPinned T).wilson = T.wilson.wilson :=
  rfl

/-- The resulting pinned target still uses the legacy margin currency. -/
theorem toClayTargetPinned_mass_eq_margin
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (T : ContinuumExactMassClusteringTarget mu)
    (R : LegacyClayPinnedExtensionResidual T) :
    (R.toClayTargetPinned T).massGap.1 =
      reconGapCReal T.wilson.reconstruction :=
  rfl

end LegacyClayPinnedExtensionResidual

end YMGap.Continuum.ContinuumExactMassClusteringClayResidual

#print axioms YMGap.Continuum.ContinuumExactMassClusteringClayResidual.LegacyClayPinnedExtensionResidual.toClayTargetPinned
#print axioms YMGap.Continuum.ContinuumExactMassClusteringClayResidual.LegacyClayPinnedExtensionResidual.toClayTargetPinned_recon
#print axioms YMGap.Continuum.ContinuumExactMassClusteringClayResidual.LegacyClayPinnedExtensionResidual.toClayTargetPinned_wilson
#print axioms YMGap.Continuum.ContinuumExactMassClusteringClayResidual.LegacyClayPinnedExtensionResidual.toClayTargetPinned_mass_eq_margin
