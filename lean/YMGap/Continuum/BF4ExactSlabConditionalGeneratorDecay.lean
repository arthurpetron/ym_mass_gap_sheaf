/-
# Actual original-generator energy descent

All inputs to the generic descent argument are discharged for the ORIGINAL
conditional generator. The rational step is 1/(2*(number of links+1)).
Its iteration rate depends on volume; this internal proof rate is not the
volume-independent square-energy margin or a physical mass rate.
-/

import YMGap.Continuum.BF4ExactSlabConditionalGeneratorLowerBound
import YMGap.Continuum.BF4ExactSlabConditionalGeneratorIteration
import YMGap.Continuum.GNSResidualGeneratorDescent
import YMGap.Continuum.GNSResidualGeneratorStepSize

namespace YMGap.Continuum.BF4ExactSlabConditionalGeneratorDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSResidualGeneratorStepSize
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabFullActionScalar
open YMGap.Continuum.BF4ExactSlabConditionalGeneratorLowerBound
open YMGap.Continuum.BF4ExactSlabConditionalGeneratorIteration
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Internal iteration rate; the extent dependence is explicit. -/
def rate {w : Q'} (hd : heatRemainderBound w < 1) (extent : Nat) : Q' :=
  1 + -(stepSize (schedule extent).length * BF4ExactSlabConditionalGeneratorMargin.margin hd)

theorem rate_window {w : Q'} (hw0 : (0 : Q') < w) (hd : heatRemainderBound w < 1)
    (hmargin : (0 : Q') < BF4ExactSlabConditionalGeneratorMargin.margin hd) (extent : Nat) :
    (0 : Q') < rate hd extent ∧ rate hd extent < 1 :=
  step_window (schedule extent).length hmargin
    (BF4ExactSlabConditionalGeneratorMargin.margin_le_one hw0 hd)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hmargin : (0 : Q') < BF4ExactSlabConditionalGeneratorMargin.margin hd)
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "S" => fullScalarData hw0 hw1 K extent hK
local notation "s" => stepSize (List.length (schedule extent))
local notation "gamma" => BF4ExactSlabConditionalGeneratorMargin.margin hd
local notation "E" x => Family.finalEnergy (projections hw0 hw1 K extent hK) (schedule extent) x

include hsmall hmargin in
/-- The actual original one-step reduction, with no unsupplied analytic bound. -/
theorem step_energy_contract (x : GNSCompletionSpace F) :
    RCle (E (step hw0 hw1 K extent hK s x)) (RCscale (rate hd extent) (E x)) :=
  GNSResidualGeneratorDescent.energy_contract S P (schedule extent) s gamma
    (Q'.le_of_lt (stepSize_positive _)) (stepSize_times_length_le_one _)
    (Q'.le_of_lt hmargin)
    (fun y => conditionalGenerator_square_lower hw0 hw1 hsmall hd K extent hK y) x

include hsmall hmargin in
/-- Geometric energy bound for the literal finite iteration, on ALL completed
inputs. Centering is needed only later to remove its norm tail. -/
theorem iterate_energy (x : GNSCompletionSpace F) (n : Nat) :
    RCle (E (iterate hw0 hw1 K extent hK s x n))
      (RCscale ((rate hd extent)^n) (E x)) := by
  induction n with
  | zero =>
      change RCle (E x) (RCscale 1 (E x))
      rw [RCscale_one]
      exact RCle_refl _
  | succ n ih =>
      have hstep := step_energy_contract hw0 hw1 hsmall hd hmargin K extent hK
        (iterate hw0 hw1 K extent hK s x n)
      have hscaled := RCscale_mono
        (Q'.le_of_lt (rate_window hw0 hd hmargin extent).1) ih
      rw [RCscale_RCscale] at hscaled
      exact RCle_trans hstep hscaled

include hsmall hmargin in
/-- The actual step's norm decrement is paid for by its energy decrement,
using half the volume-independent square-energy margin. -/
theorem step_telescope (x : GNSCompletionSpace F) :
    RCle (RCscale (HalfPow.half * gamma)
      (RCsub (normSq x) (normSq (step hw0 hw1 K extent hK s x))))
      (RCsub (E x) (E (step hw0 hw1 K extent hK s x))) :=
  GNSResidualGeneratorDescent.step_telescope S P (schedule extent) s gamma
    (Q'.le_of_lt (stepSize_positive _)) (stepSize_times_length_le_one _)
    (Q'.le_of_lt hmargin)
    (fun y => conditionalGenerator_square_lower hw0 hw1 hsmall hd K extent hK y) x

#print axioms rate
#print axioms rate_window
#print axioms step_energy_contract
#print axioms iterate_energy
#print axioms step_telescope

end YMGap.Continuum.BF4ExactSlabConditionalGeneratorDecay
