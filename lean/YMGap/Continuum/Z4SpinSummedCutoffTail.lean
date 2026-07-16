/-
# Uniformly scheduled cutoff tails for compatible-family events

The fixed-box cutoff-cofinal probability sequence has a geometric one-step
modulus with a derived, box-dependent coefficient.  This module telescopes
that modulus, transfers it through the arbitrary-cutoff event bridge, and
chooses an explicit cutoff stage that absorbs the coefficient into a requested
dyadic precision.  The resulting tail estimate is ready for a joint
cutoff/volume diagonal construction.
-/

import YMGap.Continuum.Z4SpinSummedCutoffEventBridge

namespace YMGap.Continuum.Z4SpinSummedCutoffTail

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.Z4AdjacentCutoffDyadicSchedule
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedCutoffEventBridge

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite cutoff extensions -/

theorem anchorParametricCutoffEventProbabilitySequence_extension_abs_le_geoTail
    (n : Nat) (event : EdgeLabelling → Bool)
    (stage depth : Nat) :
    Q'.abs
        (anchorParametricCutoffEventProbabilitySequence n event
            (stage + depth) -
          anchorParametricCutoffEventProbabilitySequence n event stage) ≤
      geoTail (anchorParametricCutoffProbabilityStepConstant n) stage := by
  let sequence := anchorParametricCutoffEventProbabilitySequence n event
  let coefficient := anchorParametricCutoffProbabilityStepConstant n
  have hcoefficient : (0 : Q') ≤ coefficient :=
    anchorParametricCutoffProbabilityStepConstant_nonnegative n
  have hsum := geoTail_series_le coefficient hcoefficient stage depth
  have hupRaw := telescope_up sequence (geoIncr coefficient)
    (anchorParametricCutoffEventProbabilitySequence_step_upper n event)
    stage depth
  have hloRaw := telescope_lo sequence (geoIncr coefficient)
    (anchorParametricCutoffEventProbabilitySequence_step_lower n event)
    stage depth
  have hup : sequence (stage + depth) ≤
      sequence stage + geoTail coefficient stage :=
    Q'.le_trans' _ _ _ hupRaw
      (Q'.add_le_add_left _ _ _ hsum)
  have hlo : sequence stage ≤
      sequence (stage + depth) + geoTail coefficient stage :=
    Q'.le_trans' _ _ _ hloRaw
      (Q'.add_le_add_left _ _ _ hsum)
  exact CReal.abs_sub_le_of_bounds hup hlo

theorem parametricKCompatibleEventProbability_scheduledCutoff_extension_abs_le
    (n : Nat) (event : List (List Nat) → Bool)
    (stage depth : Nat) :
    Q'.abs
        (parametricKCompatibleSupportEventProbability
            (interactingAdjacentCutoff (stage + depth) n) n event -
          parametricKCompatibleSupportEventProbability
            (interactingAdjacentCutoff stage n) n event) ≤
      geoTail (anchorParametricCutoffProbabilityStepConstant n) stage := by
  have hraw :=
    anchorParametricCutoffEventProbabilitySequence_extension_abs_le_geoTail
      n (cutoffOneLiftedFamilyEvent n event) stage depth
  have hstart :=
    anchorParametricCutoffProbabilitySequence_eqv_compatible
      n event stage
  have hend :=
    anchorParametricCutoffProbabilitySequence_eqv_compatible
      n event (stage + depth)
  have hdiff :
      anchorParametricCutoffEventProbabilitySequence n
            (cutoffOneLiftedFamilyEvent n event) (stage + depth) -
          anchorParametricCutoffEventProbabilitySequence n
            (cutoffOneLiftedFamilyEvent n event) stage ≈
        parametricKCompatibleSupportEventProbability
            (interactingAdjacentCutoff (stage + depth) n) n event -
          parametricKCompatibleSupportEventProbability
            (interactingAdjacentCutoff stage n) n event :=
    Q'.add_eqv_congr' hend (Q'.neg_eqv_congr _ _ hstart)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.abs_eqv_congr hdiff))) hraw

theorem parametricKCompatibleEventProbability_cutoff_extension_abs_le
    {n stage targetCutoff : Nat}
    (event : List (List Nat) → Bool)
    (hcutoff : interactingAdjacentCutoff stage n ≤ targetCutoff) :
    Q'.abs
        (parametricKCompatibleSupportEventProbability
            targetCutoff n event -
          parametricKCompatibleSupportEventProbability
            (interactingAdjacentCutoff stage n) n event) ≤
      geoTail (anchorParametricCutoffProbabilityStepConstant n) stage := by
  let depth := targetCutoff - interactingAdjacentCutoff stage n
  have hend : interactingAdjacentCutoff (stage + depth) n =
      targetCutoff := by
    dsimp only [depth]
    unfold interactingAdjacentCutoff at hcutoff ⊢
    omega
  have hraw :=
    parametricKCompatibleEventProbability_scheduledCutoff_extension_abs_le
      n event stage depth
  rw [hend] at hraw
  exact hraw

/-! ## 2. A coefficient-paying cutoff schedule -/

def spinSummedCutoffTailCoefficient (n : Nat) : Q' :=
  Q'.ofNat 2 * anchorParametricCutoffProbabilityStepConstant n

theorem spinSummedCutoffTailCoefficient_nonnegative (n : Nat) :
    (0 : Q') ≤ spinSummedCutoffTailCoefficient n := by
  unfold spinSummedCutoffTailCoefficient
  exact Q'.mul_nonneg _ _ (by decide)
    (anchorParametricCutoffProbabilityStepConstant_nonnegative n)

private theorem half_pow_pos_local :
    ∀ exponent : Nat, (0 : Q') < HalfPow.half ^ exponent
  | 0 => by decide
  | exponent + 1 => by
      change (0 : Q') < HalfPow.half * HalfPow.half ^ exponent
      exact Q'.mul_pos (by decide) (half_pow_pos_local exponent)

def spinSummedCutoffPrecisionTolerance
    (precision n : Nat) : Q' :=
  HalfPow.half ^ precision *
    Q'.invSucc (spinSummedCutoffTailCoefficient n).num.toNat

theorem spinSummedCutoffPrecisionTolerance_pos
    (precision n : Nat) :
    (0 : Q') < spinSummedCutoffPrecisionTolerance precision n := by
  unfold spinSummedCutoffPrecisionTolerance
  exact Q'.mul_pos (half_pow_pos_local precision)
    (Q'.invSucc_pos _)

def spinSummedJointCutoffStage (precision n : Nat) : Nat :=
  (spinSummedCutoffPrecisionTolerance precision n).den

def spinSummedJointCutoff (precision n : Nat) : Nat :=
  interactingAdjacentCutoff (spinSummedJointCutoffStage precision n) n

theorem geoTail_jointCutoffStage_le_half_pow
    (precision n : Nat) :
    geoTail (anchorParametricCutoffProbabilityStepConstant n)
        (spinSummedJointCutoffStage precision n) ≤
      HalfPow.half ^ precision := by
  let coefficient := spinSummedCutoffTailCoefficient n
  let tolerance := spinSummedCutoffPrecisionTolerance precision n
  have hcoefficient : (0 : Q') ≤ coefficient :=
    spinSummedCutoffTailCoefficient_nonnegative n
  have htolerance : (0 : Q') < tolerance :=
    spinSummedCutoffPrecisionTolerance_pos precision n
  have hhalf : HalfPow.half ^ tolerance.den ≤ tolerance :=
    HalfPow.pow_half_le tolerance htolerance
  have hscaledHalf := Q'.mul_le_mul_of_nonneg_left
    (HalfPow.half ^ tolerance.den) tolerance coefficient
    hhalf hcoefficient
  have hscale : coefficient * tolerance ≤
      HalfPow.half ^ precision := by
    dsimp only [coefficient, tolerance,
      spinSummedCutoffPrecisionTolerance]
    exact ExpNeg.mul_le_of_mul_invSucc_toNat
      (spinSummedCutoffTailCoefficient n)
      (HalfPow.half ^ precision)
      (spinSummedCutoffTailCoefficient_nonnegative n)
      (Q'.pow_nonneg HalfPow.half HalfPow.half_nonneg precision)
  change coefficient * HalfPow.half ^ tolerance.den ≤
    HalfPow.half ^ precision
  exact Q'.le_trans' _ _ _ hscaledHalf hscale

/-- Every extension above the derived joint cutoff changes an arbitrary
compatible-family event probability by at most the requested dyadic error. -/
theorem parametricKCompatibleEventProbability_jointCutoff_extension_abs_le
    {precision n targetCutoff : Nat}
    (event : List (List Nat) → Bool)
    (hcutoff : spinSummedJointCutoff precision n ≤ targetCutoff) :
    Q'.abs
        (parametricKCompatibleSupportEventProbability
            targetCutoff n event -
          parametricKCompatibleSupportEventProbability
            (spinSummedJointCutoff precision n) n event) ≤
      HalfPow.half ^ precision := by
  have hraw :=
    parametricKCompatibleEventProbability_cutoff_extension_abs_le
      event hcutoff
  exact Q'.le_trans' _ _ _ hraw
    (geoTail_jointCutoffStage_le_half_pow precision n)

#print axioms anchorParametricCutoffEventProbabilitySequence_extension_abs_le_geoTail
#print axioms parametricKCompatibleEventProbability_cutoff_extension_abs_le
#print axioms geoTail_jointCutoffStage_le_half_pow
#print axioms parametricKCompatibleEventProbability_jointCutoff_extension_abs_le

end YMGap.Continuum.Z4SpinSummedCutoffTail
