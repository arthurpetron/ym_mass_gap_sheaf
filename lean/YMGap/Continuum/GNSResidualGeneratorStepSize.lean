/-
An explicit rational averaging step for a finite list of residual generators.
The step is positive, at most one half, and its total list-length budget is
at most one. These scalar facts alone do not assert a contraction.
-/

import YMGap.Constructive.RegularCRealArith
import YMGap.Constructive.CRealMul
import YMGap.Constructive.CauchyConv
import YMGap.Continuum.HeatKernelPos

namespace YMGap.Continuum.GNSResidualGeneratorStepSize

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.HKPos

def stepSize (n : Nat) : Q' :=
  Q'.divPos HalfPow.half (Q'.ofNat (n + 1)) (Q'.ofNat_succ_pos n)

theorem stepSize_positive (n : Nat) : (0 : Q') < stepSize n := by
  unfold stepSize
  exact Q'.divPos_pos HalfPow.half (Q'.ofNat (n + 1))
    (Q'.ofNat_succ_pos n) (by decide)

theorem stepSize_le_half (n : Nat) : stepSize n ≤ HalfPow.half := by
  have hden : (1 : Q') ≤ Q'.ofNat (n + 1) :=
    CReal.ofNat_le_ofNat (Nat.succ_le_succ (Nat.zero_le n))
  have hmul : HalfPow.half ≤ HalfPow.half * Q'.ofNat (n + 1) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv HalfPow.half)))
      (Q'.mul_le_mul_of_nonneg_left 1 (Q'.ofNat (n + 1)) HalfPow.half
        hden HalfPow.half_nonneg)
  unfold stepSize
  exact Q'.divPos_le_of_le_mul HalfPow.half (Q'.ofNat (n + 1))
    (Q'.ofNat_succ_pos n) (C := HalfPow.half) hmul

theorem stepSize_times_length_le_one (n : Nat) :
    stepSize n * Q'.ofNat n ≤ (1 : Q') := by
  have hnat : Q'.ofNat n ≤ Q'.ofNat (n + 1) :=
    CReal.ofNat_le_ofNat (Nat.le_succ n)
  have hmul := Q'.mul_le_mul_of_nonneg_left (Q'.ofNat n)
    (Q'.ofNat (n + 1)) (stepSize n) hnat
    (Q'.le_of_lt (stepSize_positive n))
  have hcancel := Q'.divPos_mul_eqv HalfPow.half (Q'.ofNat (n + 1))
    (Q'.ofNat_succ_pos n)
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcancel) (by decide))

private theorem one_sub_lt_one_of_pos {x : Q'} (hx : (0 : Q') < x) :
    (1 : Q') + -x < (1 : Q') := by
  show ((1 : Q') + -x).num * ((1 : Q').den : Int) <
    (1 : Q').num * (((1 : Q') + -x).den : Int)
  have hnum : (0 : Int) < x.num := Q'.num_pos_of_pos hx
  change
    (((1 : Int) * (x.den : Int) + (-x.num) * (1 : Int)) * (1 : Int)) <
      ((1 : Int) * (((1 : Nat) * x.den : Nat) : Int))
  push_cast
  omega

theorem step_window (n : Nat) {gamma : Q'} (hg0 : (0 : Q') < gamma)
    (hg1 : gamma ≤ (1 : Q')) :
    (0 : Q') < 1 + -(stepSize n * gamma) ∧
      1 + -(stepSize n * gamma) < (1 : Q') := by
  have hs := stepSize_positive n
  have hproduct : (0 : Q') < stepSize n * gamma := Q'.mul_pos hs hg0
  have hproduct_le : stepSize n * gamma ≤ stepSize n :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left gamma 1 (stepSize n) hg1 (Q'.le_of_lt hs))
      (Q'.le_of_eqv (Q'.mul_one_eqv (stepSize n)))
  have hs_lt_one : stepSize n < (1 : Q') :=
    Q'.lt_of_le_of_lt (stepSize_le_half n) (by decide)
  have hproduct_lt : stepSize n * gamma < (1 : Q') :=
    Q'.lt_of_le_of_lt hproduct_le hs_lt_one
  exact ⟨HKPos.one_sub_pos hproduct_lt, one_sub_lt_one_of_pos hproduct⟩

end YMGap.Continuum.GNSResidualGeneratorStepSize

#print axioms YMGap.Continuum.GNSResidualGeneratorStepSize.stepSize
#print axioms YMGap.Continuum.GNSResidualGeneratorStepSize.stepSize_positive
#print axioms YMGap.Continuum.GNSResidualGeneratorStepSize.stepSize_le_half
#print axioms YMGap.Continuum.GNSResidualGeneratorStepSize.stepSize_times_length_le_one
#print axioms YMGap.Continuum.GNSResidualGeneratorStepSize.step_window
