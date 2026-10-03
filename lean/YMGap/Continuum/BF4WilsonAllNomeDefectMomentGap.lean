/-
# Actual kinetic coercivity of original Wilson defect moments

On the existing vacuum complement, every moment of D=I-T has the SAME
kinetic floor/cap margin. Even powers use the one-step margin; odd powers
retain the square of (D-rI)y. No spectral calculus or comparison premise is
used. The margin depends on the original nome and width: these statements
do not provide a uniform physical rate or a changing-family estimate.
-/

import YMGap.Continuum.BF4WilsonAllNomeOneStepGap
import YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments

namespace YMGap.Continuum.BF4WilsonAllNomeDefectMomentGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RCSignedPairBudget (scale_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixFraction mixFraction_positive)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
  (completedInner_sub_left completedInner_sub_right)
open YMGap.Continuum.BF4WilsonAllNomeOneStepGap
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n))))

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem sub_nonnegative_of_le {a b : RC} (h : RCle a b) :
    RCnonneg (RCsub b a) := by
  have h' := RCadd_le_add h (RCle_refl (RCneg a))
  change RCle (RCsub a a) (RCsub b a) at h'
  rwa [rc_sub_self] at h'

private theorem le_of_sub_nonnegative {a b : RC}
    (h : RCnonneg (RCsub b a)) : RCle a b := by
  have h' := RCadd_le_add (RCle_refl a) h
  have he : RCadd a (RCsub b a) = b := by
    refine Quotient.inductionOn₂ a b ?_
    exact fun A B' => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.var 0) (.add (.var 1) (.neg (.var 0))))
        (.var 1) (by decide)
        (fun | 0 => A.approx n | _ => B'.approx n)))
  rwa [rc_add_zero, he] at h'

private theorem square_remainder_identity (s : Q') (a b c : RC) :
    RCadd
      (RCsub (RCsub c (RCscale s a))
        (RCscale s (RCsub a (RCscale s b))))
      (RCscale s (RCsub a (RCscale s b))) =
      RCsub c (RCscale s a) := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B' C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add
        (.add (.add (.var 2) (.neg (.mul (.var 3) (.var 0))))
          (.neg (.mul (.var 3)
            (.add (.var 0) (.neg (.mul (.var 3) (.var 1)))))))
        (.mul (.var 3) (.add (.var 0) (.neg (.mul (.var 3) (.var 1))))))
      (.add (.var 2) (.neg (.mul (.var 3) (.var 0)))) (by decide)
      (fun
        | 0 => A.approx n
        | 1 => B'.approx n
        | 2 => C.approx n
        | _ => s)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "D" => defect hw0 hw1
local notation "DP" => defectPower hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "r" => mixFraction hw0 hw1 width

/-- Powers of the literal time defect preserve the original vacuum complement. -/
theorem defectPower_vacuum_orthogonal (x : V) (hx : B x U = RCzero) (k : Nat) :
    B (DP k x) U = RCzero := by
  induction k with
  | zero => exact hx
  | succ k ih =>
      change B (D (DP k x)) U = RCzero
      rw [defect, completedInner_sub_left,
        completedInner_time_balance hw0 hw1 1 (DP k x) U,
        completedUnit_fixed, ih, rc_sub_self]

private theorem first_margin (y : V) (hy : B y U = RCzero) :
    RCle (RCscale r (B y y)) (B y (D y)) := by
  have h := completed_oneStep_defect_margin hw0 hw1 y hy
  rw [defect, completedInner_sub_right]
  exact h

private theorem odd_margin (y : V) (hy : B y U = RCzero) :
    RCle (RCscale r (B y (D y))) (B (D y) (D y)) := by
  let e := completedSub hw0 hw1 (D y) (completedSmul hw0 hw1 r y)
  have he : RCnonneg (B y e) := by
    dsimp only [e]
    rw [completedInner_sub_right, completedInner_smul_right]
    exact sub_nonnegative_of_le (first_margin hw0 hw1 y hy)
  have hscaled := RCscale_mono (Q'.le_of_lt (mixFraction_positive hw0 hw1 width)) he
  rw [RCscale_RCzero] at hscaled
  have hsum := RCadd_le_add (completedInner_nonnegative hw0 hw1 e) hscaled
  rw [rc_add_zero] at hsum
  have hidentity : RCadd (B e e) (RCscale r (B y e)) =
      RCsub (B (D y) (D y)) (RCscale r (B y (D y))) := by
    dsimp only [e]
    rw [completedInner_sub_left, completedInner_smul_left]
    simp only [completedInner_sub_right, completedInner_smul_right,
      completedInner_symm hw0 hw1 (D y) y]
    exact square_remainder_identity r (B y (D y)) (B y y) (B (D y) (D y))
  rw [hidentity] at hsum
  exact le_of_sub_nonnegative hsum

private theorem defect_pair_pin (x : V) (m n : Nat) :
    B (DP m x) (DP n x) = B x (DP (m+n) x) := by
  rw [defectPower_symmetric, ← defectPower_add]

private theorem even_step (x : V) (hx : B x U = RCzero) (m : Nat) :
    RCle (RCscale r (B x (DP (2*m) x))) (B x (DP (2*m+1) x)) := by
  have h := first_margin hw0 hw1 (DP m x)
    (defectPower_vacuum_orthogonal hw0 hw1 x hx m)
  change RCle (RCscale r (B (DP m x) (DP m x)))
    (B (DP m x) (DP (m+1) x)) at h
  rw [defect_pair_pin, defect_pair_pin,
    show m+m=2*m by omega, show m+(m+1)=2*m+1 by omega] at h
  exact h

private theorem odd_step (x : V) (hx : B x U = RCzero) (m : Nat) :
    RCle (RCscale r (B x (DP (2*m+1) x))) (B x (DP ((2*m+1)+1) x)) := by
  have h := odd_margin hw0 hw1 (DP m x)
    (defectPower_vacuum_orthogonal hw0 hw1 x hx m)
  change RCle (RCscale r (B (DP m x) (DP (m+1) x)))
    (B (DP (m+1) x) (DP (m+1) x)) at h
  rw [defect_pair_pin, defect_pair_pin,
    show m+(m+1)=2*m+1 by omega,
    show (m+1)+(m+1)=(2*m+1)+1 by omega] at h
  exact h

/-- Every adjacent defect moment has the actual kinetic floor/cap margin.
The odd case keeps a nonnegative remainder square rather than assuming a
spectral measure or a scalar functional-calculus comparison. -/
theorem defect_moment_step_gap (x : V) (hx : B x U = RCzero) (k : Nat) :
    RCle (RCscale r (B x (DP k x))) (B x (DP (k+1) x)) := by
  rcases Nat.mod_two_eq_zero_or_one k with he | ho
  · have hk : 2*(k/2)=k := by
      simpa only [he, Nat.zero_add] using Nat.mod_add_div k 2
    have h := even_step hw0 hw1 x hx (k/2)
    rwa [hk] at h
  · have hk : 2*(k/2)+1=k := by
      simpa only [ho, Nat.add_comm] using Nat.mod_add_div k 2
    have h := odd_step hw0 hw1 x hx (k/2)
    rwa [hk] at h

/-- The original defect moments dominate r^k times the original norm.
This is a fixed-parameter bound, not a scale-uniform Hamiltonian claim. -/
theorem defect_moment_geometric_lower (x : V) (hx : B x U = RCzero) (k : Nat) :
    RCle (RCscale (r^k) (B x x)) (B x (DP k x)) := by
  induction k with
  | zero =>
      simp only [Q'.pow_zero, defectPower, RCscale_one]
      exact RCle_refl _
  | succ k ih =>
      have h := RCle_trans
        (RCscale_mono (Q'.le_of_lt (mixFraction_positive hw0 hw1 width)) ih)
        (defect_moment_step_gap hw0 hw1 x hx k)
      rw [RCscale_RCscale, ← Q'.pow_succ] at h
      exact h

#print axioms defectPower_vacuum_orthogonal
#print axioms defect_moment_step_gap
#print axioms defect_moment_geometric_lower

end YMGap.Continuum.BF4WilsonAllNomeDefectMomentGap
