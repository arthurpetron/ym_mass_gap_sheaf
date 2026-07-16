/-
# Cofinal schedule alignment for strict-cylinder time translation

The canonical target approximant at base `base + shift` and stage `stage`
uses exactly the same support radius and centered box as the source chart at
base `base` and stage `stage + shift`.  Their derived cutoff precisions are
different, so this file gives them one explicit common refinement and records
the two standard dyadic cutoff-tail estimates.

This is only cofinal bookkeeping.  It does not identify the two cylinder
events, compare their probabilities, or assert a reflection-form
contraction.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationSemanticDescent

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationScheduleAlignment

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.Z4CouplingParametricCutoffTail
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationSemanticDescent
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Exact radius and volume alignment -/

/-- Target stage `stage` is the same radius as source stage
`stage + shift`. -/
theorem strictJointTimeTranslation_scheduleRadius_eq
    (base shift stage : Nat) :
    strictQueryBase (base + shift) + stage =
      strictQueryBase base + (stage + shift) := by
  rw [strictQueryBase_add_shift]
  omega

theorem strictJointTimeTranslation_scheduleCenteredBox_eq
    (base shift stage : Nat) :
    centeredBoxBase (strictQueryBase (base + shift) + stage) =
      centeredBoxBase (strictQueryBase base + (stage + shift)) := by
  rw [strictJointTimeTranslation_scheduleRadius_eq]

theorem strictJointTimeTranslation_scheduleCentralExtent_eq
    (base shift stage : Nat) :
    centralExtent (strictQueryBase (base + shift) + stage) =
      centralExtent (strictQueryBase base + (stage + shift)) := by
  rw [strictJointTimeTranslation_scheduleRadius_eq]

/-! ## 2. One common refinement of the two derived cutoffs -/

def strictJointTimeTranslationScheduleCommonCutoff
    (base shift stage : Nat) : Nat :=
  centralStrictJointCenteredStageCutoff (base + shift) stage +
    centralStrictJointCenteredStageCutoff base (stage + shift)

theorem strictJointTimeTranslation_targetCutoff_le_common
    (base shift stage : Nat) :
    centralStrictJointCenteredStageCutoff (base + shift) stage ≤
      strictJointTimeTranslationScheduleCommonCutoff base shift stage := by
  unfold strictJointTimeTranslationScheduleCommonCutoff
  omega

theorem strictJointTimeTranslation_sourceCutoff_le_common
    (base shift stage : Nat) :
    centralStrictJointCenteredStageCutoff base (stage + shift) ≤
      strictJointTimeTranslationScheduleCommonCutoff base shift stage := by
  unfold strictJointTimeTranslationScheduleCommonCutoff
  omega

/-- The radius identity and the two cutoff dominations, packaged as one
cofinal-schedule certificate. -/
theorem strictJointTimeTranslation_schedules_have_common_refinement
    (base shift stage : Nat) :
    strictQueryBase (base + shift) + stage =
        strictQueryBase base + (stage + shift) ∧
      centralStrictJointCenteredStageCutoff (base + shift) stage ≤
        strictJointTimeTranslationScheduleCommonCutoff base shift stage ∧
      centralStrictJointCenteredStageCutoff base (stage + shift) ≤
        strictJointTimeTranslationScheduleCommonCutoff base shift stage :=
  ⟨strictJointTimeTranslation_scheduleRadius_eq base shift stage,
    strictJointTimeTranslation_targetCutoff_le_common base shift stage,
    strictJointTimeTranslation_sourceCutoff_le_common base shift stage⟩

/-! ## 3. Exact cofinal cutoff-tail bounds -/

theorem couplingParametricStrictJoint_targetCutoff_to_common_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (base shift stage : Nat)
    (event : List (List Nat) → Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling
            (strictJointTimeTranslationScheduleCommonCutoff
              base shift stage)
            (centeredBoxBase
              (strictQueryBase (base + shift) + stage)) event -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling
            (centralStrictJointCenteredStageCutoff
              (base + shift) stage)
            (centeredBoxBase
              (strictQueryBase (base + shift) + stage)) event) ≤
      HalfPow.half ^ stage := by
  exact
    couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
      hcoupling hle event
      (strictJointTimeTranslation_targetCutoff_le_common
        base shift stage)

theorem couplingParametricStrictJoint_sourceCutoff_to_common_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (base shift stage : Nat)
    (event : List (List Nat) → Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling
            (strictJointTimeTranslationScheduleCommonCutoff
              base shift stage)
            (centeredBoxBase
              (strictQueryBase base + (stage + shift))) event -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling
            (centralStrictJointCenteredStageCutoff
              base (stage + shift))
            (centeredBoxBase
              (strictQueryBase base + (stage + shift))) event) ≤
      HalfPow.half ^ (stage + shift) := by
  exact
    couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
      hcoupling hle event
      (strictJointTimeTranslation_sourceCutoff_le_common
        base shift stage)

/-- A common `2^-stage` envelope for the source cutoff tail. -/
theorem couplingParametricStrictJoint_sourceCutoff_to_common_abs_le_stage
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (base shift stage : Nat)
    (event : List (List Nat) → Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling
            (strictJointTimeTranslationScheduleCommonCutoff
              base shift stage)
            (centeredBoxBase
              (strictQueryBase base + (stage + shift))) event -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling
            (centralStrictJointCenteredStageCutoff
              base (stage + shift))
            (centeredBoxBase
              (strictQueryBase base + (stage + shift))) event) ≤
      HalfPow.half ^ stage := by
  have hraw :=
    couplingParametricStrictJoint_sourceCutoff_to_common_abs_le
      hcoupling hle base shift stage event
  exact Q'.le_trans' _ _ _ hraw
    (ExpNeg.pow_half_antitone stage shift)

#print axioms strictJointTimeTranslation_scheduleRadius_eq
#print axioms strictJointTimeTranslation_scheduleCenteredBox_eq
#print axioms strictJointTimeTranslation_schedules_have_common_refinement
#print axioms couplingParametricStrictJoint_targetCutoff_to_common_abs_le
#print axioms couplingParametricStrictJoint_sourceCutoff_to_common_abs_le
#print axioms couplingParametricStrictJoint_sourceCutoff_to_common_abs_le_stage

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationScheduleAlignment
