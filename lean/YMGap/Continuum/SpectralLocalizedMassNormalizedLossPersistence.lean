/-
M3m -- spectral-localization control of normalized physical rate loss.

`GradedBondMovingBudget` constructs a genuine `FullModeDefect` from its
`SpectralLocalization` interface: the gap-relevant defect is bounded by the
summable inverse-Casimir-graded bond-moving budget.  This file connects that
already-constructed defect to physical mass persistence.

The only new field is the same-object analytic comparison

  physical normalized logarithmic rate loss <= localized gap defect.

Thus neither spectral localization nor the physical/RG identification is
silently claimed.  Once both are supplied, the inverse-square budget and the
positive mass floor are constructive consequences.
-/

import YMGap.Continuum.AFQuadraticMassNormalizedLossPersistence
import YMGap.Continuum.GradedBondMovingBudget

namespace YMGap.Continuum.SpectralLocalizedMassNormalizedLossPersistence

open YMGap.Constructive
open YMGap.Continuum.AFQuadraticMassNormalizedLossPersistence
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.GradedBondMovingBudget
open YMGap.Continuum.MassNormalizedLossPersistence
open YMGap.Continuum.SummableInverseSquare

/-- A physical normalized-loss flow controlled by the gap-relevant defect of
one graded spectral-localization package.  `rateLoss_le_gapDefect` is the
remaining same-object bridge; the inverse-square estimate is already proved by
the graded bond-moving development. -/
structure SpectralLocalizedRateLossControl
    (flow : MassNormalizedLossFlow) : Type where
  afRate : AFRateModulus
  modeCutoff : Nat
  localization : SpectralLocalization afRate modeCutoff
  rateLoss_le_gapDefect : forall k : Nat,
    flow.rateLoss k <= localization.gapDefect k

namespace SpectralLocalizedRateLossControl

/-- Package the constructed spectral-localization defect in the generic AF
quadratic normalized-loss interface. -/
def toAFQuadraticControl {flow : MassNormalizedLossFlow}
    (control : SpectralLocalizedRateLossControl flow) :
    AFQuadraticRateLossControl flow where
  afRate := control.afRate
  defect := spectralLocalization_defect
    control.afRate control.modeCutoff control.localization
  rateLoss_le_defect := control.rateLoss_le_gapDefect

/-- The physical rate loss is consequently bounded by the explicit graded
bond-moving budget. -/
theorem rateLoss_le_gradedBudget {flow : MassNormalizedLossFlow}
    (control : SpectralLocalizedRateLossControl flow) (k : Nat) :
    flow.rateLoss k <=
      gradedBudget (control.afRate.w k) control.modeCutoff
        (control.localization.traj.hZ k) :=
  Q'.le_trans' _ _ _ (control.rateLoss_le_gapDefect k)
    (control.localization.hlocalize k)

/-- The localized control constructs the complete normalized-loss budget. -/
def lossBudget {flow : MassNormalizedLossFlow}
    (control : SpectralLocalizedRateLossControl flow) :=
  control.toAFQuadraticControl.lossBudget

@[simp] theorem lossBudget_cap {flow : MassNormalizedLossFlow}
    (control : SpectralLocalizedRateLossControl flow) :
    control.lossBudget.cap =
      fmAconst control.afRate
          (spectralLocalization_defect
            control.afRate control.modeCutoff control.localization) *
        pot 2 (by decide) 0 := rfl

/-- An anchor larger than the explicit inverse-square cap yields a uniformly
positive physical mass floor. -/
def persistence {flow : MassNormalizedLossFlow}
    (control : SpectralLocalizedRateLossControl flow)
    (anchorDominates :
      fmAconst control.afRate
          (spectralLocalization_defect
            control.afRate control.modeCutoff control.localization) *
        pot 2 (by decide) 0 < flow.mass 0) :
    MassNormalizedLossPersistence flow :=
  control.toAFQuadraticControl.persistence anchorDominates

@[simp] theorem persistence_floorWitness {flow : MassNormalizedLossFlow}
    (control : SpectralLocalizedRateLossControl flow)
    (anchorDominates :
      fmAconst control.afRate
          (spectralLocalization_defect
            control.afRate control.modeCutoff control.localization) *
        pot 2 (by decide) 0 < flow.mass 0) :
    (control.persistence anchorDominates).floorWitness =
      flow.mass 0 +
        -(fmAconst control.afRate
            (spectralLocalization_defect
              control.afRate control.modeCutoff control.localization) *
          pot 2 (by decide) 0) := rfl

theorem persistent_floor_pos {flow : MassNormalizedLossFlow}
    (control : SpectralLocalizedRateLossControl flow)
    (anchorDominates :
      fmAconst control.afRate
          (spectralLocalization_defect
            control.afRate control.modeCutoff control.localization) *
        pot 2 (by decide) 0 < flow.mass 0) :
    (0 : Q') < (control.persistence anchorDominates).floorWitness :=
  control.toAFQuadraticControl.persistent_floor_pos anchorDominates

theorem persistent_floor_le_mass {flow : MassNormalizedLossFlow}
    (control : SpectralLocalizedRateLossControl flow)
    (anchorDominates :
      fmAconst control.afRate
          (spectralLocalization_defect
            control.afRate control.modeCutoff control.localization) *
        pot 2 (by decide) 0 < flow.mass 0)
    (k : Nat) :
    (control.persistence anchorDominates).floorWitness <= flow.mass k :=
  control.toAFQuadraticControl.persistent_floor_le_mass anchorDominates k

end SpectralLocalizedRateLossControl

end YMGap.Continuum.SpectralLocalizedMassNormalizedLossPersistence

#print axioms YMGap.Continuum.SpectralLocalizedMassNormalizedLossPersistence.SpectralLocalizedRateLossControl.toAFQuadraticControl
#print axioms YMGap.Continuum.SpectralLocalizedMassNormalizedLossPersistence.SpectralLocalizedRateLossControl.rateLoss_le_gradedBudget
#print axioms YMGap.Continuum.SpectralLocalizedMassNormalizedLossPersistence.SpectralLocalizedRateLossControl.lossBudget
#print axioms YMGap.Continuum.SpectralLocalizedMassNormalizedLossPersistence.SpectralLocalizedRateLossControl.persistence
#print axioms YMGap.Continuum.SpectralLocalizedMassNormalizedLossPersistence.SpectralLocalizedRateLossControl.persistent_floor_pos
#print axioms YMGap.Continuum.SpectralLocalizedMassNormalizedLossPersistence.SpectralLocalizedRateLossControl.persistent_floor_le_mass
