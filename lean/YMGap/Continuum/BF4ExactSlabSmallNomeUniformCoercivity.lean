/-
# Volume-uniform coercivity for the original small-nome conditional dynamics

The positive finite-volume baseline is used only to remove the norm tail of
the actual centered generator iteration. The resulting coefficient is half
the proved square-energy margin and has NO extent or late-cutoff argument.
All scalar small-nome hypotheses are discharged at the existing pilot.

This is ordinary original-action GNS conditional-link dynamics, not OS time
translation, a continuum scaling family, or a physical Hamiltonian gap.
-/

import YMGap.Continuum.BF4ExactSlabConditionalGeneratorDecay
import YMGap.Continuum.BF4ExactSlabCompletedFiniteVolumeCoercivity
import YMGap.Continuum.BF4ExactSlabFiniteVolumeReverseEnergy
import YMGap.Continuum.RCDescentCoercivity

namespace YMGap.Continuum.BF4ExactSlabSmallNomeUniformCoercivity

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
open YMGap.Continuum.BF4ExactSlabSweepChebyshev
open YMGap.Continuum.BF4ExactSlabConditionalGeneratorIteration
open YMGap.Continuum.BF4ExactSlabConditionalGeneratorDecay
open YMGap.Continuum.BF4ExactSlabFiniteVolumeReverseEnergy
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Explicit same-original-form coercivity coefficient, depending only on nome. -/
def coefficient {w : Q'} (hd : heatRemainderBound w < 1) : Q' :=
  HalfPow.half * BF4ExactSlabConditionalGeneratorMargin.margin hd

theorem coefficient_positive {w : Q'} (hd : heatRemainderBound w < 1)
    (hmargin : (0 : Q') < BF4ExactSlabConditionalGeneratorMargin.margin hd) :
    (0 : Q') < coefficient hd := Q'.mul_pos (by decide) hmargin

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hmargin : (0 : Q') < BF4ExactSlabConditionalGeneratorMargin.margin hd)
  (extent stage : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "s" => stepSize (List.length (schedule extent))

include hsmall hmargin in
/-- Coercivity on EVERY original completed centered vector, with one coefficient
for all extent and all late heat cutoffs at the stated nome. -/
theorem volume_uniform_centered_coercivity (x : GNSCompletionSpace F)
    (hx : Centered hw0 hw1 K extent hK x) :
    RCle (RCscale (coefficient hd) (normSq x))
      ((P).finalEnergy (schedule extent) x) := by
  let X := iterate hw0 hw1 K extent hK s x
  let V := fun n => normSq (X n)
  let E := fun n => (P).finalEnergy (schedule extent) (X n)
  have hwindow := rate_window hw0 hd hmargin extent
  have hfloor (n : Nat) : RCle
      (RCscale (BF4ExactSlabFiniteVolumeCoercivity.coercivity hw0 hw1 extent) (V n))
      (E n) := by
    have hc := iterate_centered hw0 hw1 K extent hK s x hx n
    exact BF4ExactSlabCompletedFiniteVolumeCoercivity.completed_centered_coercivity
      hw0 hw1 extent stage (X n) hc
  exact RCDescentCoercivity.descent_coercivity V E
    (BF4ExactSlabFiniteVolumeCoercivity.coercivity hw0 hw1 extent)
    (coefficient hd) (rate hd extent)
    (BF4ExactSlabFiniteVolumeCoercivity.coercivity_positive hw0 hw1 extent)
    (Q'.le_of_lt (coefficient_positive hd hmargin)) hwindow.1 hwindow.2
    (fun n => GNSResidualGeneratorStep.energy_nonnegative
      (fullScalarData hw0 hw1 K extent hK) P (schedule extent) (X n))
    (fun n => iterate_energy hw0 hw1 hsmall hd hmargin K extent hK x n)
    hfloor
    (fun n => BF4ExactSlabConditionalGeneratorDecay.step_telescope
      hw0 hw1 hsmall hd hmargin K extent hK (X n))

/-- At the exact pilot, no scalar smallness or analytic coercivity input remains. -/
theorem existingNome_centered_coercivity (extent stage : Nat)
    (x : GNSCompletionSpace (fullData nome_pos nome_lt_one
      (headCutoff nome + stage) extent (Nat.le_add_right _ stage)))
    (hx : Centered nome_pos nome_lt_one (headCutoff nome + stage) extent
      (Nat.le_add_right _ stage) x) :
    (0 : Q') < coefficient existingNome_guards.2 ∧
      RCle (RCscale (coefficient existingNome_guards.2) (normSq x))
        ((projections nome_pos nome_lt_one (headCutoff nome + stage) extent
          (Nat.le_add_right _ stage)).finalEnergy (schedule extent) x) :=
  ⟨coefficient_positive _ BF4ExactSlabConditionalGeneratorMargin.existingNome_margin_positive,
    volume_uniform_centered_coercivity nome_pos nome_lt_one existingNome_guards.1
      existingNome_guards.2 BF4ExactSlabConditionalGeneratorMargin.existingNome_margin_positive
      extent stage x hx⟩

include hsmall hmargin in
/-- The proved uniform coefficient supplies the EXISTING reverse-energy
consumer at the actual balanced conditional output. -/
theorem volume_uniform_reverse_energy (u : GNSCompletionSpace F)
    (hu : Centered hw0 hw1 K extent hK u) :
    RCle (RCscale (2 + geometricCalibration * coefficient hd)
      (normSq ((P).balanced (schedule extent) u)))
      (RCscale 2 (normSq ((P).sweep (schedule extent) u))) := by
  have hz := sweep_centered hw0 hw1 K extent hK (schedule extent).reverse _
    (sweep_centered hw0 hw1 K extent hK (schedule extent) u hu)
  have hc := volume_uniform_centered_coercivity hw0 hw1 hsmall hd hmargin extent stage
    ((P).balanced (schedule extent) u) hz
  exact reverse_energy_of_coercivity_at_balanced hw0 hw1 extent stage (coefficient hd) u hc

/-- Strict reverse-energy coefficient with no extent, cutoff, or support-size cost. -/
theorem reverse_coefficient_gt_two {w : Q'} (hd : heatRemainderBound w < 1)
    (hmargin : (0 : Q') < BF4ExactSlabConditionalGeneratorMargin.margin hd) :
    (2 : Q') < 2 + geometricCalibration * coefficient hd :=
  calibrated_coefficient_gt_two _ (coefficient_positive hd hmargin)

#print axioms coefficient
#print axioms coefficient_positive
#print axioms volume_uniform_centered_coercivity
#print axioms existingNome_centered_coercivity
#print axioms volume_uniform_reverse_energy
#print axioms reverse_coefficient_gt_two

end YMGap.Continuum.BF4ExactSlabSmallNomeUniformCoercivity
