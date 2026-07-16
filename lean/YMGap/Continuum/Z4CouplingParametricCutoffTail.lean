/-
# Coupling-parametric scheduled cutoff tails

The fixed-box coupling-parametric cutoff sequence has the same anchor-dominated
one-step modulus.  Telescoping it gives a finite extension estimate, and the
existing coefficient-paying schedule absorbs the box-dependent coefficient
into any requested dyadic precision.  This is the cutoff half of the joint
cutoff/volume diagonal below the anchor.
-/

import YMGap.Continuum.Z4CouplingParametricCutoffEventCofinal
import YMGap.Continuum.Z4SpinSummedCutoffTail

namespace YMGap.Continuum.Z4CouplingParametricCutoffTail

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4AdjacentCutoffDyadicSchedule
open YMGap.Continuum.Z4CouplingParametricCutoffEventCofinal
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4SpinSummedCutoffTail
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

theorem couplingParametricCutoffEventProbabilitySequence_extension_abs_le_geoTail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (n : Nat) (event : EdgeLabelling → Bool)
    (stage depth : Nat) :
    Q'.abs
        (couplingParametricCutoffEventProbabilitySequence
            coupling hcoupling n event (stage + depth) -
          couplingParametricCutoffEventProbabilitySequence
            coupling hcoupling n event stage) ≤
      geoTail (anchorParametricCutoffProbabilityStepConstant n) stage := by
  let sequence := couplingParametricCutoffEventProbabilitySequence
    coupling hcoupling n event
  let coefficient := anchorParametricCutoffProbabilityStepConstant n
  have hcoefficient : (0 : Q') ≤ coefficient :=
    anchorParametricCutoffProbabilityStepConstant_nonnegative n
  have hsum := geoTail_series_le coefficient hcoefficient stage depth
  have hupRaw := telescope_up sequence (geoIncr coefficient)
    (couplingParametricCutoffEventProbabilitySequence_step_upper
      hcoupling hle n event) stage depth
  have hloRaw := telescope_lo sequence (geoIncr coefficient)
    (couplingParametricCutoffEventProbabilitySequence_step_lower
      hcoupling hle n event) stage depth
  have hup : sequence (stage + depth) ≤
      sequence stage + geoTail coefficient stage :=
    Q'.le_trans' _ _ _ hupRaw
      (Q'.add_le_add_left _ _ _ hsum)
  have hlo : sequence stage ≤
      sequence (stage + depth) + geoTail coefficient stage :=
    Q'.le_trans' _ _ _ hloRaw
      (Q'.add_le_add_left _ _ _ hsum)
  exact CReal.abs_sub_le_of_bounds hup hlo

theorem couplingParametricKCompatibleEventProbability_scheduledCutoff_extension_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (n : Nat) (event : List (List Nat) → Bool)
    (stage depth : Nat) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling
            (interactingAdjacentCutoff (stage + depth) n) n event -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling
            (interactingAdjacentCutoff stage n) n event) ≤
      geoTail (anchorParametricCutoffProbabilityStepConstant n) stage := by
  have hraw :=
    couplingParametricCutoffEventProbabilitySequence_extension_abs_le_geoTail
      hcoupling hle n (cutoffOneLiftedFamilyEvent n event) stage depth
  have hstart :
      couplingParametricCutoffEventProbabilitySequence coupling hcoupling n
          (cutoffOneLiftedFamilyEvent n event) stage ≈
        couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling (interactingAdjacentCutoff stage n) n event := by
    change couplingKFamilyEventProbability coupling hcoupling
        (interactingAdjacentCutoff stage n) n event ≈ _
    exact couplingKFamilyEventProbability_eqv_compatible
      coupling hcoupling _ n event
  have hend :
      couplingParametricCutoffEventProbabilitySequence coupling hcoupling n
          (cutoffOneLiftedFamilyEvent n event) (stage + depth) ≈
        couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling
          (interactingAdjacentCutoff (stage + depth) n) n event := by
    change couplingKFamilyEventProbability coupling hcoupling
        (interactingAdjacentCutoff (stage + depth) n) n event ≈ _
    exact couplingKFamilyEventProbability_eqv_compatible
      coupling hcoupling _ n event
  have hdiff :
      couplingParametricCutoffEventProbabilitySequence coupling hcoupling n
            (cutoffOneLiftedFamilyEvent n event) (stage + depth) -
          couplingParametricCutoffEventProbabilitySequence coupling hcoupling n
            (cutoffOneLiftedFamilyEvent n event) stage ≈
        couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling
            (interactingAdjacentCutoff (stage + depth) n) n event -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling
            (interactingAdjacentCutoff stage n) n event :=
    Q'.add_eqv_congr' hend (Q'.neg_eqv_congr _ _ hstart)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.abs_eqv_congr hdiff))) hraw

theorem couplingParametricKCompatibleEventProbability_cutoff_extension_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {n stage targetCutoff : Nat}
    (event : List (List Nat) → Bool)
    (hcutoff : interactingAdjacentCutoff stage n ≤ targetCutoff) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling targetCutoff n event -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling
            (interactingAdjacentCutoff stage n) n event) ≤
      geoTail (anchorParametricCutoffProbabilityStepConstant n) stage := by
  let depth := targetCutoff - interactingAdjacentCutoff stage n
  have hend : interactingAdjacentCutoff (stage + depth) n =
      targetCutoff := by
    dsimp only [depth]
    unfold interactingAdjacentCutoff at hcutoff ⊢
    omega
  have hraw :=
    couplingParametricKCompatibleEventProbability_scheduledCutoff_extension_abs_le
      hcoupling hle n event stage depth
  rw [hend] at hraw
  exact hraw

theorem couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {precision n targetCutoff : Nat}
    (event : List (List Nat) → Bool)
    (hcutoff : spinSummedJointCutoff precision n ≤ targetCutoff) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling targetCutoff n event -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling
            (spinSummedJointCutoff precision n) n event) ≤
      HalfPow.half ^ precision := by
  have hraw :=
    couplingParametricKCompatibleEventProbability_cutoff_extension_abs_le
      hcoupling hle event hcutoff
  exact Q'.le_trans' _ _ _ hraw
    (geoTail_jointCutoffStage_le_half_pow precision n)

#print axioms couplingParametricCutoffEventProbabilitySequence_extension_abs_le_geoTail
#print axioms couplingParametricKCompatibleEventProbability_cutoff_extension_abs_le
#print axioms couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le

end YMGap.Continuum.Z4CouplingParametricCutoffTail
