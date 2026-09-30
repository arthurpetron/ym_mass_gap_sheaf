/-
# Explicit low-transfer filtering on the ORIGINAL positive-time range

For D=I-T on the existing all-nome Wilson completion, the actual positive
mixed moments give ||D^n T x||^2 <= ||x||^2/(n+1)^2. The coefficient is
independent of nome, width, and x; its rational tolerance cutoff is data.
This is a polynomial approximation estimate, not a positive mass bound.

The input is the original x, not a selected preimage or a replacement
carrier. In particular this does not assert D^n x -> 0 for every x:
the proved positive-norm boundary kernel forbids that assertion.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
import YMGap.Continuum.ContinuousTransferCalculus
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "M" => mixedMoment hw0 hw1

private theorem zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

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

/-- Increasing the defect power decreases each actual mixed moment. -/
theorem mixedMoment_defect_decreasing (x : V) (k l : Nat) :
    RCle (M x k (l+1)) (M x k l) := by
  have h := RCadd_le_add (mixedMoment_nonnegative hw0 hw1 x (k+1) l)
    (RCle_refl (M x k (l+1)))
  rw [zero_add, ← mixedMoment_split] at h
  exact h

/-- A finite telescoping bound, retaining the last nonnegative term. -/
theorem mixedMoment_telescoping_budget (x : V) (k l n : Nat) :
    RCle (RCadd (RCscale (Q'.ofNat (n+1)) (M x (k+1) (l+n)))
      (M x k (l+n+1))) (M x k l) := by
  induction n with
  | zero =>
      simp only [Nat.add_zero, show Q'.ofNat (0+1) = (1 : Q') from rfl,
        RCscale_one, ← mixedMoment_split]
      exact RCle_refl _
  | succ n ih =>
      rw [show l+(n+1)=l+n+1 by omega, scale_nat_succ (n+1), add_assoc,
        ← mixedMoment_split hw0 hw1 x k (l+n+1)]
      exact RCle_trans (RCadd_le_add
        (RCscale_mono (Q'.ofNat_nonneg (n+1))
          (mixedMoment_defect_decreasing hw0 hw1 x (k+1) (l+n)))
        (RCle_refl _)) ih

/-- One retained time factor yields an inverse-linear bound after n defects. -/
theorem mixedMoment_row_bound (x : V) (k l n : Nat) :
    RCle (M x (k+1) (l+n)) (RCscale (Q'.invSucc n) (M x k l)) := by
  have h := RCadd_le_add
    (RCle_refl (RCscale (Q'.ofNat (n+1)) (M x (k+1) (l+n))))
    (mixedMoment_nonnegative hw0 hw1 x k (l+n+1))
  rw [add_zero] at h
  have hb := RCscale_mono (Q'.invSucc_nonneg n)
    (RCle_trans h (mixedMoment_telescoping_budget hw0 hw1 x k l n))
  have hi : Q'.eqv (Q'.invSucc n * Q'.ofNat (n+1)) 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.ofNat_succ_mul_invSucc n)
  rw [RCscale_RCscale, RCSignedPairBudget.scale_congr hi, RCscale_one] at hb
  exact hb

/-- Two applications of the same telescoping argument give the squared rate. -/
theorem mixedMoment_two_time_bound (x : V) (n : Nat) :
    RCle (M x 2 (2*n))
      (RCscale (Q'.invSucc n * Q'.invSucc n) (B x x)) := by
  have hfirst := mixedMoment_row_bound hw0 hw1 x 0 0 n
  have hsecond := mixedMoment_row_bound hw0 hw1 x 1 n n
  simp only [Nat.zero_add, mixedMoment_zero] at hfirst
  rw [show n+n=2*n by omega] at hsecond
  have h := RCle_trans hsecond (RCscale_mono (Q'.invSucc_nonneg n) hfirst)
  rw [RCscale_RCscale] at h
  exact h

/-- This is the actual polynomial filter on an actual one-step image. -/
def positiveTimeTail (n : Nat) (x : V) : V :=
  defectPower hw0 hw1 n (T 1 x)

theorem positiveTimeTail_norm_pin (n : Nat) (x : V) :
    B (positiveTimeTail hw0 hw1 n x) (positiveTimeTail hw0 hw1 n x) =
      M x 2 (2*n) := by
  unfold positiveTimeTail
  rw [defectPower_symmetric, ← defectPower_add, ← time_defectPower,
    completedInner_time_sum]
  rw [show n+n=2*n by omega]
  rfl

/-- Uniform in all 0<w<1, widths, and completed vectors; NOT spectral decay
in physical time. Here n counts polynomial filter iterations. -/
theorem positiveTimeTail_bound (n : Nat) (x : V) :
    RCle (B (positiveTimeTail hw0 hw1 n x) (positiveTimeTail hw0 hw1 n x))
      (RCscale (Q'.invSucc n * Q'.invSucc n) (B x x)) := by
  rw [positiveTimeTail_norm_pin]
  exact mixedMoment_two_time_bound hw0 hw1 x n

/-- A computable relative squared-norm tolerance cutoff, not a quotient choice. -/
def relativeTailModulus (epsilon : Q') : Nat := epsilon.den

theorem tailRate_small (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : relativeTailModulus epsilon ≤ n) :
    Q'.invSucc n * Q'.invSucc n ≤ epsilon := by
  have hi : Q'.invSucc n ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le (Nat.zero_le n)) (by decide)
  have hs : Q'.invSucc n * Q'.invSucc n ≤ Q'.invSucc n :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hi (Q'.invSucc_nonneg n))
      (Q'.le_of_eqv (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ hs (Q'.le_trans' _ _ _
    (ExpNeg.invSucc_le_of_le hn) (HalfPow.invSucc_den_le epsilon he))

theorem positiveTimeTail_small (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : relativeTailModulus epsilon ≤ n) (x : V) :
    RCle (B (positiveTimeTail hw0 hw1 n x) (positiveTimeTail hw0 hw1 n x))
      (RCscale epsilon (B x x)) :=
  RCle_trans (positiveTimeTail_bound hw0 hw1 n x)
    (RCscale_scalar_mono (tailRate_small epsilon he n hn)
      (completedInner_nonnegative hw0 hw1 x))

#print axioms mixedMoment_defect_decreasing
#print axioms mixedMoment_telescoping_budget
#print axioms mixedMoment_row_bound
#print axioms mixedMoment_two_time_bound
#print axioms positiveTimeTail
#print axioms positiveTimeTail_norm_pin
#print axioms positiveTimeTail_bound
#print axioms relativeTailModulus
#print axioms tailRate_small
#print axioms positiveTimeTail_small

end YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail
