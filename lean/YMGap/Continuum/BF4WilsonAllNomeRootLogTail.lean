/-
# Root-series tail budget on the SAME original Wilson completion

For the actual positive root R at depth d+2, its mixed moments give

  (N/2) B(x,R^(N-1)(I-R)^2 x) <= (8/N) B(x,x), N=2^(d+2).

Both coefficients are exact constructive rationals: N/2 is
ofNat(N)*half, and 8/N is 2*half^d.  This pays the positive root-series
tail in the proposed derivative/log comparison without a spectral theorem
or a sharp scalar binomial ceiling.  The S/F polynomial comparison and
its original-root transport remain open; this does not identify the two
existing operators or supply physical scaling control.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay

namespace YMGap.Continuum.BF4WilsonAllNomeRootLogTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Constructive.SU3CharFactor (ofNat_nonneg ofNat_mul_eqv)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy (half_power_normalizes)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1

/-- Finite time-index monotonicity of the ACTUAL root mixed moment. -/
theorem moment_time_antitone (depth : Nat) (x : V) (l : Nat)
    {i j : Nat} (hij : i ≤ j) :
    RCle (moment hw0 hw1 depth x j l) (moment hw0 hw1 depth x i l) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction n with
  | zero => rw [Nat.add_zero]; exact RCle_refl _
  | succ n ih =>
      exact RCle_trans (moment_time_decreases hw0 hw1 depth x (i+n) l) ih

private theorem weighted_coefficient (d : Nat) :
    Q'.eqv ((2*half^d)*(Q'.ofNat (2^d))^2) (2*Q'.ofNat (2^d)) := by
  have he : Q'.eqv ((2*half^d)*(Q'.ofNat (2^d))^2)
      ((half^d*Q'.ofNat (2^d))*(2*Q'.ofNat (2^d))) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.var 0))
        (.mul (.var 1) (.mul (.var 1) (.const 1))))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.const 2) (.var 1)))
      (by decide) (fun | 0 => half^d | _ => Q'.ofNat (2^d))
  exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (half_power_normalizes d))
    (Q'.one_mul_eqv _))

private theorem root_coefficient (d : Nat) :
    Q'.eqv (Q'.ofNat (2^(d+2))*half) (2*Q'.ofNat (2^d)) := by
  have hN : 2^(d+2) = 2^d*4 := by
    rw [show d+2 = (d+1)+1 by omega, Nat.pow_succ, Nat.pow_succ]
    simp only [Nat.mul_assoc]
  rw [hN]
  refine Q'.eqv_trans _ ((Q'.ofNat (2^d)*4)*half) _
    (Q'.mul_eqv_congr_right _ _ _ (ofNat_mul_eqv (2^d) 4)) ?_
  refine Q'.eqv_trans _ (Q'.ofNat (2^d)*(4*half)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  exact Q'.eqv_trans _ (Q'.ofNat (2^d)*2) _
    (Q'.mul_eqv_congr_left _ _ _ (by decide)) (Q'.mul_comm_eqv _ _)

/-- A computed O(1/N) tail on every state of the EXISTING carrier.
No form comparison or positive norm is supplied by the caller. -/
theorem root_quadratic_tail_bound (d : Nat) (x : V) :
    RCle (RCscale (Q'.ofNat (2^(d+2))*half)
      (moment hw0 hw1 (d+2) x (2^(d+2)-1) 2))
      (RCscale (2*half^d) (B x x)) := by
  have hn : 0 < 2^d := Nat.pow_pos (by decide)
  have hi : 2*2^d ≤ 2^(d+2)-1 := by
    rw [show d+2 = (d+1)+1 by omega, Nat.pow_succ, Nat.pow_succ]
    omega
  have hm := moment_time_antitone hw0 hw1 (d+2) x 2 hi
  have h := RCle_trans
    (RCscale_mono (Q'.pow_nonneg _ (ofNat_nonneg (2^d)) 2) hm)
    (by simpa only [Nat.zero_add] using
      weighted_order hw0 hw1 (d+2) x 0 0 (2^d) 2)
  rw [moment_zero] at h
  have hs := RCscale_mono
    (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2)
      (Q'.pow_nonneg half half_nonneg d)) h
  rw [RCscale_RCscale, scale_congr (weighted_coefficient d),
    ← scale_congr (root_coefficient d)] at hs
  exact hs

#print axioms moment_time_antitone
#print axioms root_quadratic_tail_bound

end YMGap.Continuum.BF4WilsonAllNomeRootLogTail
