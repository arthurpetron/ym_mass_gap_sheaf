/-
# Uniform original conditional coercivity from physical face patches

The face-patch generator margin is independent of spatial extent and late
heat cutoff. Chronological area coercivity is used only to remove the norm
tail of the actual centered descent. These are conditional-link estimates on
the original completed full-action form, not OS time or a continuum gap.
-/

import YMGap.Continuum.BF4ExactSlabFacePatchGeneratorBound
import YMGap.Continuum.BF4ExactSlabCompletedChronologicalCoercivity
import YMGap.Continuum.BF4ExactSlabConditionalGeneratorIteration
import YMGap.Continuum.BF4ExactSlabFiniteVolumeReverseEnergy
import YMGap.Continuum.GNSResidualGeneratorDescent
import YMGap.Continuum.GNSResidualGeneratorStepSize
import YMGap.Continuum.RCDescentCoercivity

namespace YMGap.Continuum.BF4ExactSlabFacePatchUniformCoercivity

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
open YMGap.Continuum.BF4ExactSlabFiniteVolumeReverseEnergy
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Half the proved face-patch square-energy margin, independent of extent. -/
def coefficient {w : Q'} (hd : heatRemainderBound w < 1) : Q' :=
  HalfPow.half * BF4ExactSlabFacePatchGeneratorBound.margin hd

theorem coefficient_positive {w : Q'} (hd : heatRemainderBound w < 1)
    (hmargin : (0 : Q') < BF4ExactSlabFacePatchGeneratorBound.margin hd) :
    (0 : Q') < coefficient hd := Q'.mul_pos (by decide) hmargin

/-- The face-patch margin fits the rational descent window. -/
theorem margin_le_one {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1) :
    BF4ExactSlabFacePatchGeneratorBound.margin hd ≤ 1 := by
  have he := BF4ExactSlabTwoLinkResidualLowerBound.pairCoefficient_nonnegative hw0 hd
  have h36 : (0 : Q') ≤ 36 * BF4ExactSlabTwoLinkResidualLowerBound.pairCoefficient hd :=
    Q'.mul_nonneg _ _ (by decide) he
  unfold BF4ExactSlabFacePatchGeneratorBound.margin
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left 1 (-(36 * BF4ExactSlabTwoLinkResidualLowerBound.pairCoefficient hd))
      0 (Q'.neg_le_neg h36))
    (by decide)

/-- The rate is internal to the proof and may depend on spatial extent. -/
def rate {w : Q'} (hd : heatRemainderBound w < 1) (extent : Nat) : Q' :=
  1 + -(stepSize (schedule extent).length * BF4ExactSlabFacePatchGeneratorBound.margin hd)

theorem rate_window {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hmargin : (0 : Q') < BF4ExactSlabFacePatchGeneratorBound.margin hd)
    (extent : Nat) : (0 : Q') < rate hd extent ∧ rate hd extent < 1 :=
  step_window (schedule extent).length hmargin (margin_le_one hw0 hd)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hmargin : (0 : Q') < BF4ExactSlabFacePatchGeneratorBound.margin hd)
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "S" => fullScalarData hw0 hw1 K extent hK
local notation "s" => stepSize (List.length (schedule extent))
local notation "gamma" => BF4ExactSlabFacePatchGeneratorBound.margin hd
local notation "E" x => Family.finalEnergy (projections hw0 hw1 K extent hK) (schedule extent) x

include hsmall hmargin in
theorem step_energy_contract (x : GNSCompletionSpace F) :
    RCle (E (step hw0 hw1 K extent hK s x)) (RCscale (rate hd extent) (E x)) :=
  GNSResidualGeneratorDescent.energy_contract S P (schedule extent) s gamma
    (Q'.le_of_lt (stepSize_positive _)) (stepSize_times_length_le_one _)
    (Q'.le_of_lt hmargin)
    (fun y => BF4ExactSlabFacePatchGeneratorBound.generator_square_lower
      hw0 hw1 hsmall hd K extent hK y) x

include hsmall hmargin in
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
theorem step_telescope (x : GNSCompletionSpace F) :
    RCle (RCscale (coefficient hd)
      (RCsub (normSq x) (normSq (step hw0 hw1 K extent hK s x))))
      (RCsub (E x) (E (step hw0 hw1 K extent hK s x))) :=
  GNSResidualGeneratorDescent.step_telescope S P (schedule extent) s gamma
    (Q'.le_of_lt (stepSize_positive _)) (stepSize_times_length_le_one _)
    (Q'.le_of_lt hmargin)
    (fun y => BF4ExactSlabFacePatchGeneratorBound.generator_square_lower
      hw0 hw1 hsmall hd K extent hK y) x

/- The late-cutoff specialization has the same carrier as the original
completed centered sweep and does not add a new Hilbert space. -/
variable (stage : Nat)

local notation "L" => headCutoff w + stage
local notation "hL" => Nat.le_add_right (headCutoff w) stage
local notation "FL" => fullData hw0 hw1 L extent hL
local notation "PL" => projections hw0 hw1 L extent hL
local notation "ss" => stepSize (List.length (schedule extent))

include hsmall hmargin in
theorem volume_uniform_centered_coercivity (x : GNSCompletionSpace FL)
    (hx : Centered hw0 hw1 L extent hL x) :
    RCle (RCscale (coefficient hd) (normSq x))
      ((PL).finalEnergy (schedule extent) x) := by
  let X := iterate hw0 hw1 L extent hL ss x
  let V := fun n => normSq (X n)
  let EE := fun n => (PL).finalEnergy (schedule extent) (X n)
  have hwindow := rate_window hw0 hd hmargin extent
  have hfloor (n : Nat) : RCle
      (RCscale (BF4ExactSlabChronologicalCoercivity.areaCoercivity hw0 hw1 extent) (V n))
      (EE n) := by
    have hc := iterate_centered hw0 hw1 L extent hL ss x hx n
    have hcUnit : (FL).cinnerCompl (X n)
        (embedV FL (BF4ExactSlabConditionalCovariance.unit hw0 hw1 extent stage)) = RCzero := by
      change (FL).cinnerCompl (X n)
        (embedV FL (BF4ExactSlabSweepChebyshev.constant hw0 hw1 L extent hL)) = RCzero at hc
      exact hc
    exact BF4ExactSlabCompletedChronologicalCoercivity.completed_centered_area_coercivity
      hw0 hw1 extent stage (X n) hcUnit
  exact RCDescentCoercivity.descent_coercivity V EE
    (BF4ExactSlabChronologicalCoercivity.areaCoercivity hw0 hw1 extent)
    (coefficient hd) (rate hd extent)
    (BF4ExactSlabChronologicalCoercivity.areaCoercivity_positive hw0 hw1 extent)
    (Q'.le_of_lt (coefficient_positive hd hmargin)) hwindow.1 hwindow.2
    (fun n => GNSResidualGeneratorStep.energy_nonnegative
      (fullScalarData hw0 hw1 L extent hL) PL (schedule extent) (X n))
    (fun n => iterate_energy hw0 hw1 hsmall hd hmargin L extent hL x n)
    hfloor
    (fun n => step_telescope hw0 hw1 hsmall hd hmargin L extent hL (X n))

/-- A fully supplied rational nome outside the previous positive-margin
certificate, still uniform in extent and late heat cutoff. -/
theorem expandedNome_centered_coercivity (extent stage : Nat)
    (x : GNSCompletionSpace (fullData
      BF4ExactSlabFacePatchGeneratorBound.expandedNome_guards.1
      BF4ExactSlabFacePatchGeneratorBound.expandedNome_guards.2.1
      (headCutoff BF4ExactSlabFacePatchGeneratorBound.expandedNome + stage) extent
      (Nat.le_add_right _ stage)))
    (hx : Centered
      BF4ExactSlabFacePatchGeneratorBound.expandedNome_guards.1
      BF4ExactSlabFacePatchGeneratorBound.expandedNome_guards.2.1
      (headCutoff BF4ExactSlabFacePatchGeneratorBound.expandedNome + stage) extent
      (Nat.le_add_right _ stage) x) :
    (0 : Q') < coefficient BF4ExactSlabFacePatchGeneratorBound.expandedNome_guards.2.2.2 ∧
      RCle (RCscale
        (coefficient BF4ExactSlabFacePatchGeneratorBound.expandedNome_guards.2.2.2)
        (normSq x))
        ((projections BF4ExactSlabFacePatchGeneratorBound.expandedNome_guards.1
          BF4ExactSlabFacePatchGeneratorBound.expandedNome_guards.2.1
          (headCutoff BF4ExactSlabFacePatchGeneratorBound.expandedNome + stage) extent
          (Nat.le_add_right _ stage)).finalEnergy (schedule extent) x) :=
  ⟨coefficient_positive _ BF4ExactSlabFacePatchGeneratorBound.expandedNome_margin_separation.1,
    volume_uniform_centered_coercivity
      BF4ExactSlabFacePatchGeneratorBound.expandedNome_guards.1
      BF4ExactSlabFacePatchGeneratorBound.expandedNome_guards.2.1
      BF4ExactSlabFacePatchGeneratorBound.expandedNome_guards.2.2.1
      BF4ExactSlabFacePatchGeneratorBound.expandedNome_guards.2.2.2
      BF4ExactSlabFacePatchGeneratorBound.expandedNome_margin_separation.1
      extent stage x hx⟩

include hsmall hmargin in
/-- The original balanced sweep receives the new uniform coefficient. -/
theorem volume_uniform_reverse_energy (u : GNSCompletionSpace FL)
    (hu : Centered hw0 hw1 L extent hL u) :
    RCle (RCscale (2 + geometricCalibration * coefficient hd)
      (normSq ((PL).balanced (schedule extent) u)))
      (RCscale 2 (normSq ((PL).sweep (schedule extent) u))) := by
  have hz := sweep_centered hw0 hw1 L extent hL (schedule extent).reverse _
    (sweep_centered hw0 hw1 L extent hL (schedule extent) u hu)
  have hc := volume_uniform_centered_coercivity hw0 hw1 hsmall hd hmargin extent stage
    ((PL).balanced (schedule extent) u) hz
  exact reverse_energy_of_coercivity_at_balanced hw0 hw1 extent stage (coefficient hd) u hc

include hsmall hmargin in
/-- The same reverse-energy bound at every actual centered Chebyshev
auxiliary. This is not a bound on OS time translation. -/
theorem coupled_auxiliary_reverse_energy (x : GNSCompletionSpace FL)
    (hx : Centered hw0 hw1 L extent hL x) (n : Nat) :
    let u := (coupled hw0 hw1 L extent hL
      (2 + geometricCalibration * coefficient hd) x n).2
    RCle (RCscale (2 + geometricCalibration * coefficient hd)
      (normSq ((PL).balanced (schedule extent) u)))
      (RCscale 2 (normSq ((PL).sweep (schedule extent) u))) := by
  exact volume_uniform_reverse_energy hw0 hw1 hsmall hd hmargin extent stage _
    (coupled_centered hw0 hw1 L extent hL
      (2 + geometricCalibration * coefficient hd) x hx n).2

#print axioms coefficient
#print axioms coefficient_positive
#print axioms margin_le_one
#print axioms rate_window
#print axioms step_energy_contract
#print axioms iterate_energy
#print axioms step_telescope
#print axioms volume_uniform_centered_coercivity
#print axioms expandedNome_centered_coercivity
#print axioms volume_uniform_reverse_energy
#print axioms coupled_auxiliary_reverse_energy

end YMGap.Continuum.BF4ExactSlabFacePatchUniformCoercivity
