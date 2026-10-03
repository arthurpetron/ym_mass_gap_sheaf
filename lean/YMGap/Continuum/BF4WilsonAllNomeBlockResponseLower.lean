/-
# Macroscopic response propagation on the ORIGINAL all-nome completion

Positivity of the actual completed time powers propagates a supplied response
ratio across arbitrary integer blocks, starting at any integer lag. In
particular a ratio between R(s) and R(2*s) controls later macroscopic blocks;
no adjacent-step budget or spectral theorem is required.

This is a conditional consequence on the SAME state and transfer, not a
producer of a uniform ratio, a changing-width map or a physical-time limit.
-/

import YMGap.Continuum.BF4WilsonAllNomeResponseLower

namespace YMGap.Continuum.BF4WilsonAllNomeBlockResponseLower

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "S" => completedSmul hw0 hw1

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem rc_sub_nonnegative_of_le {a b : RC} (h : RCle b a) :
    RCnonneg (RCsub a b) := by
  have h' := RCadd_le_add h (RCle_refl (RCneg b))
  change RCle (RCsub b b) (RCsub a b) at h'
  rwa [rc_sub_self] at h'

private theorem rc_sub_add (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.sub_add_cancel_eqv (A.approx n) (C.approx n)))

private theorem rc_le_of_sub_nonnegative {a b : RC}
    (h : RCnonneg (RCsub a b)) : RCle b a := by
  have h' := RCadd_le_add h (RCle_refl b)
  rwa [rc_zero_add, rc_sub_add] at h'

private theorem rc_scale_sub (rho : Q') (a b : RC) :
    RCscale rho (RCsub a b) =
      RCsub (RCscale rho a) (RCscale rho b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1))
        (.neg (.mul (.var 0) (.var 2))))
      (by decide)
      (fun | 0 => rho | 1 => A.approx n | _ => C.approx n)))

/-- The positive form of `T(n)` on `T(step)x-rho*x` controls the
second difference across the actual `step`-block, without a sign premise
on `rho` or a new operator/carrier. -/
theorem response_block_second_difference (x : V) (rho : Q') (step n : Nat) :
    RCle
      (RCscale rho (RCsub (B x (T (n+step) x))
        (RCscale rho (B x (T n x)))))
      (RCsub (B x (T (n+2*step) x))
        (RCscale rho (B x (T (n+step) x)))) := by
  let y := completedSub hw0 hw1 (T step x) (S rho x)
  have h := mixedMoment_nonnegative hw0 hw1 y n 0
  change RCnonneg (B y (T n y)) at h
  dsimp only [y] at h
  rw [completedTime_sub, completedTime_smul,
    ← completedTime_add hw0 hw1 n step x] at h
  simp only [completedInner_sub_left, completedInner_sub_right,
    completedInner_smul_left, completedInner_smul_right,
    completedInner_time_sum] at h
  have h1 : step+n = n+step := by omega
  have h2 : step+(n+step) = n+2*step := by omega
  rw [h2, h1] at h
  simp only [rc_scale_sub] at h ⊢
  exact rc_le_of_sub_nonnegative h

/-- A supplied ratio at `start` propagates to every later full block.
The state and the original completed time map are unchanged. -/
theorem response_shifted_block_step_lower (x : V) (rho : Q')
    (hrho : (0 : Q') ≤ rho) (step start : Nat)
    (hfloor : RCle (RCscale rho (B x (T start x)))
      (B x (T (start+step) x))) : ∀ lag : Nat,
    RCle (RCscale rho (B x (T (start+lag*step) x)))
      (B x (T (start+lag*step+step) x))
  | 0 => by simpa only [Nat.zero_mul, Nat.add_zero] using hfloor
  | lag+1 => by
      have h := RCscale_mono hrho
        (rc_sub_nonnegative_of_le
          (response_shifted_block_step_lower x rho hrho step start hfloor lag))
      rw [RCscale_RCzero] at h
      have hd := response_block_second_difference hw0 hw1 x rho step (start+lag*step)
      have hnext := rc_le_of_sub_nonnegative (RCle_trans h hd)
      have h1 : start+(lag+1)*step = start+lag*step+step := by
        rw [Nat.add_mul]
        omega
      have h2 : start+lag*step+2*step = start+(lag+1)*step+step := by
        rw [h1]
        omega
      rw [h2] at hnext
      simpa only [h1] using hnext

/-- A single supplied block ratio gives an explicit geometric floor at
every later block, with no adjacent-step estimate or division. -/
theorem response_shifted_block_geometric_lower (x : V) (rho : Q')
    (hrho : (0 : Q') ≤ rho) (step start : Nat)
    (hfloor : RCle (RCscale rho (B x (T start x)))
      (B x (T (start+step) x))) : ∀ lag : Nat,
    RCle (RCscale (rho^lag) (B x (T start x)))
      (B x (T (start+lag*step) x))
  | 0 => by
      rw [Q'.pow_zero, RCscale_one, Nat.zero_mul, Nat.add_zero]
      exact RCle_refl _
  | lag+1 => by
      have h := RCle_trans
        (RCscale_mono hrho
          (response_shifted_block_geometric_lower x rho hrho step start hfloor lag))
        (response_shifted_block_step_lower hw0 hw1 x rho hrho step start hfloor lag)
      rw [RCscale_RCscale] at h
      have h1 : start+(lag+1)*step = start+lag*step+step := by
        rw [Nat.add_mul]
        omega
      simpa only [Q'.pow_succ, h1] using h

#print axioms response_block_second_difference
#print axioms response_shifted_block_step_lower
#print axioms response_shifted_block_geometric_lower

end YMGap.Continuum.BF4WilsonAllNomeBlockResponseLower
