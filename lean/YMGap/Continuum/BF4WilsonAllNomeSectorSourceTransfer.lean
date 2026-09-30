/-
# An original signed energy estimate supplies a controlled domain source

Use ONE original time step, not a changed observable model: the domain point
is exactly (T x,A x). A relative original defect bound E(x)<=c*||x||^2
retains the fraction r=1-2c of the original squared norm, and bounds the
actual derivative form by (c/r)*||T x||^2 when r>0. An original positive
norm floor becomes r times that floor. All constants are rational data.

This is the explicit same-source join between a future signed scaling
estimate and the existing derivative domain. It does not prove that missing
estimate, choose a scaling family, identify physical time or establish
continuum survival. No inverse transfer or log-series identity is used.
-/

import YMGap.Continuum.BF4WilsonAllNomeSectorSmoothingEnergy
import YMGap.Continuum.BF4WilsonAllNomeSectorDerivative

namespace YMGap.Continuum.BF4WilsonAllNomeSectorSourceTransfer

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
  (defect defect_symmetric mixedMoment mixedMoment_split mixedMoment_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist completedDist_symm)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (corePoint)
open YMGap.Continuum.BF4WilsonAllNomeSectorSmoothingEnergy
  (norm_retention derivative_core_upper)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "D" => seminorm hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "E" x => B x (defect hw0 hw1 x)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

def retainedFraction (c : Q') : Q' := 1 + -(2*c)

def energyRatio (c : Q') (hr : (0 : Q') < retainedFraction c) : Q' :=
  Q'.divPos c (retainedFraction c) hr

theorem energyRatio_nonnegative (c : Q') (hc : (0 : Q') ≤ c)
    (hr : (0 : Q') < retainedFraction c) : (0 : Q') ≤ energyRatio c hr :=
  Q'.mul_nonneg _ _ hc (Q'.le_of_lt (Q'.recipPos_pos _ hr))

private theorem cancel_retained (c : Q') (a : RC) :
    RCadd a (RCneg (RCscale (2*c) a)) = RCscale (retainedFraction c) a := by
  refine Quotient.inductionOn a ?_
  intro a
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.mul (.mul (.const 2) (.var 1)) (.var 0))))
      (.mul (.add (.const 1) (.neg (.mul (.const 2) (.var 1)))) (.var 0))
      (by decide) (fun | 0 => a.approx n | _ => c)))

private theorem cancel_added (a b : RC) : RCadd (RCadd a b) (RCneg b) = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro a b
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 1)))
      (.var 0) (by decide) (fun | 0 => a.approx n | _ => b.approx n)))

/-- One-step source replacement costs at most the ORIGINAL defect energy.
This supplies a source-recovery error, not just a norm-retention estimate. -/
theorem smoothing_distance_le_energy (x : V) :
    RCle (completedDist hw0 hw1 (T 1 x) x) (E x) := by
  have h := RCadd_le_add (mixedMoment_nonnegative hw0 hw1 x 1 1)
    (RCle_refl (mixedMoment hw0 hw1 x 0 2))
  have hz : RCadd RCzero (mixedMoment hw0 hw1 x 0 2) =
      mixedMoment hw0 hw1 x 0 2 := by
    refine Quotient.inductionOn (mixedMoment hw0 hw1 x 0 2) ?_
    intro a
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.eqv_of_eq (Q'.zero_add' (a.approx n))))
  rw [hz,← mixedMoment_split] at h
  simp only [mixedMoment,completedTime_zero,
    BF4WilsonAllNomeTimeDefectMoments.defectPower] at h
  rw [← defect_symmetric] at h
  rw [completedDist_symm]
  exact h

/-- The supplied signed relative estimate also controls source replacement. -/
theorem relative_source_error (x : V) (c : Q')
    (h : RCle (E x) (RCscale c (B x x))) :
    RCle (completedDist hw0 hw1 (T 1 x) x) (RCscale c (B x x)) :=
  RCle_trans (smoothing_distance_le_energy hw0 hw1 x) h

/-- Small original energy bounds the loss of norm when entering the domain.
No positivity guard on c is needed for this algebraic implication. -/
theorem relative_norm_retention (x : V) (c : Q')
    (h : RCle (E x) (RCscale c (B x x))) :
    RCle (RCscale (retainedFraction c) (B x x)) (B (T 1 x) (T 1 x)) := by
  have hupper := RCle_trans (norm_retention hw0 hw1 x)
    (RCadd_le_add (RCle_refl (B (T 1 x) (T 1 x)))
      (RCscale_mono (by decide : (0 : Q') ≤ 2) h))
  rw [RCscale_RCscale] at hupper
  have hc := RCadd_le_add hupper (RCle_refl (RCneg (RCscale (2*c) (B x x))))
  rwa [cancel_retained,cancel_added] at hc

/-- The actual core generator form inherits the signed source budget, with
the explicit normalization cost c/(1-2c). -/
theorem relative_derivative_bound (x : V) (c : Q') (hc : (0 : Q') ≤ c)
    (hr : (0 : Q') < retainedFraction c)
    (h : RCle (E x) (RCscale c (B x x))) :
    RCle (B (T 1 x) (A x))
      (RCscale (energyRatio c hr) (B (T 1 x) (T 1 x))) := by
  have hratio := RCscale_mono (energyRatio_nonnegative c hc hr)
    (relative_norm_retention hw0 hw1 x c h)
  have hcancel : Q'.eqv (energyRatio c hr * retainedFraction c) c :=
    Q'.divPos_mul_eqv c (retainedFraction c) hr
  rw [RCscale_RCscale,scale_congr hcancel] at hratio
  exact RCle_trans (derivative_core_upper hw0 hw1 x) (RCle_trans h hratio)

/-- Existing represented source data produce this SAME actual domain point;
the bound is not a statement about an independently chosen operator. -/
theorem corePoint_relative_bound (X : (D).Cauchy) (c : Q') (hc : (0 : Q') ≤ c)
    (hr : (0 : Q') < retainedFraction c)
    (h : RCle (E (Class X)) (RCscale c (B (Class X) (Class X)))) :
    RCle (B (corePoint hw0 hw1 X).input.val (corePoint hw0 hw1 X).output.val)
      (RCscale (energyRatio c hr)
        (B (corePoint hw0 hw1 X).input.val (corePoint hw0 hw1 X).input.val)) :=
  relative_derivative_bound hw0 hw1 (Class X) c hc hr h

/-- An explicit original source floor loses only the computed fraction.
No new independent nontriviality hypothesis on the domain point is needed. -/
theorem corePoint_norm_floor (X : (D).Cauchy) (floor c : Q')
    (hr : (0 : Q') < retainedFraction c)
    (hfloor : RCle (rat floor) (B (Class X) (Class X)))
    (h : RCle (E (Class X)) (RCscale c (B (Class X) (Class X)))) :
    RCle (rat (retainedFraction c * floor))
      (B (corePoint hw0 hw1 X).input.val (corePoint hw0 hw1 X).input.val) :=
  RCle_trans (RCscale_mono (Q'.le_of_lt hr) hfloor)
    (relative_norm_retention hw0 hw1 (Class X) c h)

theorem transferredFloor_positive (floor c : Q') (hf : (0 : Q') < floor)
    (hr : (0 : Q') < retainedFraction c) :
    (0 : Q') < retainedFraction c * floor := Q'.mul_pos hr hf

/-- The original vacuum-complement condition is retained by the same step. -/
theorem corePoint_orthogonal (X : (D).Cauchy)
    (hx : B (unitState hw0 hw1 width) (Class X) = RCzero) :
    B (unitState hw0 hw1 width) (corePoint hw0 hw1 X).input.val = RCzero := by
  change B (unitState hw0 hw1 width) (T 1 (Class X)) = RCzero
  rw [← completedInner_time_balance,completedUnit_fixed]
  exact hx

#print axioms retainedFraction
#print axioms energyRatio
#print axioms energyRatio_nonnegative
#print axioms smoothing_distance_le_energy
#print axioms relative_source_error
#print axioms relative_norm_retention
#print axioms relative_derivative_bound
#print axioms corePoint_relative_bound
#print axioms corePoint_norm_floor
#print axioms transferredFloor_positive
#print axioms corePoint_orthogonal

end YMGap.Continuum.BF4WilsonAllNomeSectorSourceTransfer
