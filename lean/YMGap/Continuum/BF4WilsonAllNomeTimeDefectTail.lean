/-
# Physical-time decay on the range of the ORIGINAL time defect

For D=I-T on the existing all-nome Wilson completion,
||T^n D x||^2 <= ||x||^2/(n+1)^2. This transposes the mixed-moment
telescoping argument for D^n T x; n now counts actual lattice-time steps.
The estimate is uniform in nome and width, with an explicit relative modulus.

The right side uses the supplied preimage x, NOT the norm of D x.
This is polynomial decay on the defect range, not exponential decay on
every vacuum-complement state or a positive continuum mass gap.
-/

import YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail

namespace YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "M" => mixedMoment hw0 hw1

private theorem add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem add_assoc (a b c : RC) :
    RCadd (RCadd a b) c = RCadd a (RCadd b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B' C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_assoc_eqv (A.approx n) (B'.approx n) (C.approx n)))

private theorem scale_nat_succ (n : Nat) (a : RC) :
    RCscale (Q'.ofNat (n+1)) a = RCadd (RCscale (Q'.ofNat n) a) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun j =>
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv n 1))
      (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv (A.approx j))))))

private theorem split_commuted (x : V) (k l : Nat) :
    M x k l = RCadd (M x k (l+1)) (M x (k+1) l) := by
  rw [mixedMoment_split]
  generalize M x (k+1) l = a, M x k (l+1) = b
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B' => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_comm_eqv (A.approx n) (B'.approx n)))

/-- Actual mixed moments decrease when physical time increases. -/
theorem mixedMoment_time_decreasing (x : V) (k l : Nat) :
    RCle (M x (k+1) l) (M x k l) := by
  have h := RCadd_le_add (RCle_refl (M x (k+1) l))
    (mixedMoment_nonnegative hw0 hw1 x k (l+1))
  rw [add_zero, ← mixedMoment_split] at h
  exact h

/-- Telescoping in actual time, with the positive last term retained. -/
theorem mixedMoment_time_budget (x : V) (k l n : Nat) :
    RCle (RCadd (RCscale (Q'.ofNat (n+1)) (M x (k+n) (l+1)))
      (M x (k+n+1) l)) (M x k l) := by
  induction n with
  | zero =>
      simp only [Nat.add_zero, show Q'.ofNat (0+1) = (1 : Q') from rfl,
        RCscale_one, ← split_commuted]
      exact RCle_refl _
  | succ n ih =>
      rw [show k+(n+1)=k+n+1 by omega, scale_nat_succ (n+1), add_assoc,
        ← split_commuted hw0 hw1 x (k+n+1) l]
      exact RCle_trans (RCadd_le_add
        (RCscale_mono (Q'.ofNat_nonneg (n+1))
          (mixedMoment_time_decreasing hw0 hw1 x (k+n) (l+1)))
        (RCle_refl _)) ih

theorem mixedMoment_column_bound (x : V) (k l n : Nat) :
    RCle (M x (k+n) (l+1)) (RCscale (Q'.invSucc n) (M x k l)) := by
  have h := RCadd_le_add
    (RCle_refl (RCscale (Q'.ofNat (n+1)) (M x (k+n) (l+1))))
    (mixedMoment_nonnegative hw0 hw1 x (k+n+1) l)
  rw [add_zero] at h
  have hb := RCscale_mono (Q'.invSucc_nonneg n)
    (RCle_trans h (mixedMoment_time_budget hw0 hw1 x k l n))
  have hi : Q'.eqv (Q'.invSucc n * Q'.ofNat (n+1)) 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.ofNat_succ_mul_invSucc n)
  rw [RCscale_RCscale, RCSignedPairBudget.scale_congr hi, RCscale_one] at hb
  exact hb

theorem mixedMoment_two_defect_bound (x : V) (n : Nat) :
    RCle (M x (2*n) 2)
      (RCscale (Q'.invSucc n * Q'.invSucc n) (B x x)) := by
  have hfirst := mixedMoment_column_bound hw0 hw1 x 0 0 n
  have hsecond := mixedMoment_column_bound hw0 hw1 x n 1 n
  simp only [Nat.zero_add, mixedMoment_zero] at hfirst
  rw [show n+n=2*n by omega] at hsecond
  have h := RCle_trans hsecond (RCscale_mono (Q'.invSucc_nonneg n) hfirst)
  rw [RCscale_RCscale] at h
  exact h

/-- No change of carrier or operator: this is the actual physical-time orbit. -/
theorem timeDefect_norm_pin (n : Nat) (x : V) :
    B (T n (defect hw0 hw1 x)) (T n (defect hw0 hw1 x)) = M x (2*n) 2 := by
  rw [completedInner_time_sum]
  rw [defect_symmetric, defect_time]
  change B x (T (n+n) (defectPower hw0 hw1 2 x)) = _
  rw [show n+n=2*n by omega]
  rfl

/-- Uniform in nome and width, relative to the supplied original preimage.
The inverse-square rate is polynomial, not a mass-gap rate. -/
theorem timeDefect_bound (n : Nat) (x : V) :
    RCle (B (T n (defect hw0 hw1 x)) (T n (defect hw0 hw1 x)))
      (RCscale (Q'.invSucc n * Q'.invSucc n) (B x x)) := by
  rw [timeDefect_norm_pin]
  exact mixedMoment_two_defect_bound hw0 hw1 x n

/-- Reuses the explicit rational cutoff epsilon.den; no preimage selection. -/
theorem timeDefect_small (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : relativeTailModulus epsilon ≤ n) (x : V) :
    RCle (B (T n (defect hw0 hw1 x)) (T n (defect hw0 hw1 x)))
      (RCscale epsilon (B x x)) :=
  RCle_trans (timeDefect_bound hw0 hw1 n x)
    (RCscale_scalar_mono (tailRate_small epsilon he n hn)
      (completedInner_nonnegative hw0 hw1 x))

#print axioms mixedMoment_time_decreasing
#print axioms mixedMoment_time_budget
#print axioms mixedMoment_column_bound
#print axioms mixedMoment_two_defect_bound
#print axioms timeDefect_norm_pin
#print axioms timeDefect_bound
#print axioms timeDefect_small

end YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail
