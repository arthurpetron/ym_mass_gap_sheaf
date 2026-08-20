/-
M3k -- AF quadratic full-mode defect to normalized mass persistence.

`FullModeAssembly` already proves that a nonnegative defect quadratic in the
asymptotic-freedom margin is bounded by an inverse-square stream.  The physical
mass-persistence path, however, consumes the normalized logarithmic rate loss.
This file records the precise remaining comparison between those two streams:

  physical rateLoss k <= full-mode defect d k.

Once supplied, all later steps are derived: inverse-square control, a complete
constructive summability budget, and a positive persistent mass floor when the
anchor exceeds the explicit defect cap.

The comparison and the genuine four-dimensional `FullModeDefect` inhabitant
remain analytic inputs.  No actual Yang--Mills flow is constructed here.
-/

import YMGap.Continuum.FullModeAssembly
import YMGap.Continuum.InverseSquareMassNormalizedLossPersistence

namespace YMGap.Continuum.AFQuadraticMassNormalizedLossPersistence

open YMGap.Constructive
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.InverseSquareMassNormalizedLossPersistence
open YMGap.Continuum.MassNormalizedLossPersistence
open YMGap.Continuum.SummableInverseSquare

/-- A normalized physical-loss flow controlled pointwise by one AF full-mode
defect stream.  `rateLoss_le_defect` is the same-object analytic bridge; the
quadratic and AF data live in `defect`. -/
structure AFQuadraticRateLossControl
    (flow : MassNormalizedLossFlow) : Type where
  afRate : AFRateModulus
  defect : FullModeDefect afRate
  rateLoss_le_defect : forall k : Nat,
    flow.rateLoss k <= defect.d k

namespace AFQuadraticRateLossControl

/-- The existing full-mode inverse-square theorem turns the same-object defect
comparison into the exact local control consumed by the summability adapter. -/
def toInverseSquareControl {flow : MassNormalizedLossFlow}
    (control : AFQuadraticRateLossControl flow) :
    InverseSquareRateLossControl flow where
  offset := 2
  offset_at_least_two := by decide
  coefficient := fmAconst control.afRate control.defect
  coefficient_nonnegative :=
    fmAconst_nonneg control.afRate control.defect
  rateLoss_le := fun k =>
    Q'.le_trans' _ _ _ (control.rateLoss_le_defect k)
      (fmDefect_invSq control.afRate control.defect k)

@[simp] theorem inverseSquare_offset {flow : MassNormalizedLossFlow}
    (control : AFQuadraticRateLossControl flow) :
    control.toInverseSquareControl.offset = 2 := rfl

@[simp] theorem inverseSquare_coefficient {flow : MassNormalizedLossFlow}
    (control : AFQuadraticRateLossControl flow) :
    control.toInverseSquareControl.coefficient =
      fmAconst control.afRate control.defect := rfl

/-- The AF quadratic control constructs the complete normalized-loss budget. -/
def lossBudget {flow : MassNormalizedLossFlow}
    (control : AFQuadraticRateLossControl flow) :=
  control.toInverseSquareControl.lossBudget

@[simp] theorem lossBudget_cap {flow : MassNormalizedLossFlow}
    (control : AFQuadraticRateLossControl flow) :
    control.lossBudget.cap =
      fmAconst control.afRate control.defect * pot 2 (by decide) 0 := rfl

/-- If the initial rational mass exceeds the explicit AF defect cap, the
direction-neutral physical mass persists uniformly. -/
def persistence {flow : MassNormalizedLossFlow}
    (control : AFQuadraticRateLossControl flow)
    (anchorDominates :
      fmAconst control.afRate control.defect * pot 2 (by decide) 0 <
        flow.mass 0) :
    MassNormalizedLossPersistence flow :=
  control.toInverseSquareControl.persistence anchorDominates

@[simp] theorem persistence_floorWitness {flow : MassNormalizedLossFlow}
    (control : AFQuadraticRateLossControl flow)
    (anchorDominates :
      fmAconst control.afRate control.defect * pot 2 (by decide) 0 <
        flow.mass 0) :
    (control.persistence anchorDominates).floorWitness =
      flow.mass 0 +
        -(fmAconst control.afRate control.defect * pot 2 (by decide) 0) := rfl

theorem persistent_floor_pos {flow : MassNormalizedLossFlow}
    (control : AFQuadraticRateLossControl flow)
    (anchorDominates :
      fmAconst control.afRate control.defect * pot 2 (by decide) 0 <
        flow.mass 0) :
    (0 : Q') < (control.persistence anchorDominates).floorWitness :=
  control.toInverseSquareControl.persistent_floor_pos anchorDominates

theorem persistent_floor_le_mass {flow : MassNormalizedLossFlow}
    (control : AFQuadraticRateLossControl flow)
    (anchorDominates :
      fmAconst control.afRate control.defect * pot 2 (by decide) 0 <
        flow.mass 0)
    (k : Nat) :
    (control.persistence anchorDominates).floorWitness <= flow.mass k :=
  control.toInverseSquareControl.persistent_floor_le_mass
    anchorDominates k

end AFQuadraticRateLossControl

end YMGap.Continuum.AFQuadraticMassNormalizedLossPersistence

#print axioms YMGap.Continuum.AFQuadraticMassNormalizedLossPersistence.AFQuadraticRateLossControl.toInverseSquareControl
#print axioms YMGap.Continuum.AFQuadraticMassNormalizedLossPersistence.AFQuadraticRateLossControl.lossBudget
#print axioms YMGap.Continuum.AFQuadraticMassNormalizedLossPersistence.AFQuadraticRateLossControl.persistence
#print axioms YMGap.Continuum.AFQuadraticMassNormalizedLossPersistence.AFQuadraticRateLossControl.persistent_floor_pos
#print axioms YMGap.Continuum.AFQuadraticMassNormalizedLossPersistence.AFQuadraticRateLossControl.persistent_floor_le_mass
