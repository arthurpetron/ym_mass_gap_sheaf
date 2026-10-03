/-
# Exact one-step form rate on the ORIGINAL all-nome Wilson completion

The existing squared norm rate is literally q*q, with q=mixRate. Expanding
the nonnegative norm of q*x-T*x gives the one-step form bound with q itself,
not (1+q*q)/2. The zero-rate branch uses the SAME completed positive-definite
pairing; no scalar square root, spectral theorem or positive norm premise is
needed. Translation gives a RELATIVE bound at every even response horizon.

This sharpens a fixed-nome, fixed-width estimate. The resulting defect margin
is the actual kinetic floor/cap fraction. It does not produce a changing
family, spatially uniform rate, physical calibration or continuum mass gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
import YMGap.Continuum.BF4WilsonAllNomeGeometry
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4WilsonAllNomeOneStepGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RCSignedPairBudget (scale_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixRate mixRate_nonnegative mixFraction)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap (twoStepRate)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
  (completedInner_sub_left completedInner_sub_right)

local infix:50 " ≈ " => Q'.eqv

private theorem add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n))))

private theorem midpoint_cancel (a b c : RC) :
    RCadd (RCadd b b) (RCsub (RCsub a b) (RCsub b c)) = RCadd a c := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 1) (.var 1))
        (.add (.add (.var 0) (.neg (.var 1)))
          (.neg (.add (.var 1) (.neg (.var 2))))))
      (.add (.var 0) (.var 2)) (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

private theorem double_scale (c : Q') (a : RC) :
    RCadd (RCscale c a) (RCscale c a) = RCscale (2*c) a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.const 2) (.var 0)) (.var 1)) (by decide)
      (fun | 0 => c | _ => A.approx n)))

private theorem zero_scale (a : RC) : RCscale 0 a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (A.approx n)))

private theorem defect_margin (q : Q') (a b : RC)
    (h : RCle b (RCscale q a)) : RCle (RCscale (1 + -q) a) (RCsub a b) := by
  have hneg := RCadd_le_add (RCle_refl a) (RCSignedPairBudget.neg_mono h)
  have he : RCsub a (RCscale q a) = RCscale (1 + -q) a := by
    refine Quotient.inductionOn a ?_
    exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.var 0) (.neg (.mul (.var 1) (.var 0))))
        (.mul (.add (.const 1) (.neg (.var 1))) (.var 0)) (by decide)
        (fun | 0 => A.approx n | _ => q)))
  change RCle (RCsub a (RCscale q a)) (RCsub a b) at hneg
  rwa [he] at hneg

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "q" => mixRate hw0 hw1 width

/-- The exact rational one-step rate follows from the squared norm rate.
This holds on EVERY state of the existing completed vacuum complement. -/
theorem completed_oneStep_form_gap (x : V) (hx : B x U = RCzero) :
    RCle (B x (T 1 x)) (RCscale q (B x x)) := by
  have hnorm := completed_oneStep_norm_gap hw0 hw1 width 0 x hx
  simp only [completedTime_zero, Nat.zero_add, twoStepRate] at hnorm
  by_cases hq : (0 : Q') < q
  · have hpos := completedInner_nonnegative hw0 hw1
      (completedSub hw0 hw1 (S q x) (T 1 x))
    rw [completedInner_sub_left, completedInner_sub_right,
      completedInner_sub_right] at hpos
    simp only [completedInner_smul_left, completedInner_smul_right,
      RCscale_RCscale, completedInner_symm hw0 hw1 (T 1 x) x] at hpos
    have h := RCadd_le_add
      (RCle_refl (RCadd (RCscale q (B x (T 1 x)))
        (RCscale q (B x (T 1 x))))) hpos
    rw [add_zero, midpoint_cancel] at h
    have hdouble := RCle_trans h
      (RCadd_le_add (RCle_refl (RCscale (q*q) (B x x))) hnorm)
    rw [double_scale, double_scale] at hdouble
    let r := Q'.recipPos (2*q) (Q'.mul_pos (by decide : (0 : Q') < 2) hq)
    have hr : (0 : Q') < r := Q'.recipPos_pos (2*q)
      (Q'.mul_pos (by decide : (0 : Q') < 2) hq)
    have hs := RCscale_mono (Q'.le_of_lt hr) hdouble
    change RCle (RCscale r (RCscale (2*q) (B x (T 1 x))))
      (RCscale r (RCscale (2*(q*q)) (B x x))) at hs
    have hi : r*(2*q) ≈ 1 :=
      Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)
    have hiq : r*(2*(q*q)) ≈ q :=
      Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.const 2) (.mul (.var 1) (.var 1))))
          (.mul (.mul (.var 0) (.mul (.const 2) (.var 1))) (.var 1))
          (by decide) (fun | 0 => r | _ => q))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ q hi) (Q'.one_mul_eqv q))
    rwa [RCscale_RCscale, RCscale_RCscale, scale_congr hi,
      scale_congr hiq, RCscale_one] at hs
  · have hqle : q ≤ (0 : Q') := by
      show (q).num * ((0 : Q').den : Int) ≤ (0 : Q').num * ((q).den : Int)
      exact Int.not_lt.mp hq
    have hqzero : q ≈ 0 := ExpNeg.eqv_of_le_le hqle (mixRate_nonnegative hw0 hw1 width)
    have hqqzero : q*q ≈ 0 := Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ q hqzero) (Q'.zero_mul_eqv q)
    rw [scale_congr hqqzero, zero_scale] at hnorm
    have hz : B (T 1 x) (T 1 x) = RCzero :=
      RCle_antisymm hnorm (completedInner_nonnegative hw0 hw1 (T 1 x))
    have ht : T 1 x = completedZero hw0 hw1 width :=
      (BF4WilsonAllNomeGeometry.completedInner_posdef hw0 hw1 width (T 1 x)).mp hz
    rw [ht, completedInner_zero_right, scale_congr hqzero, zero_scale]
    exact RCle_refl _

/-- Translation is on the original completed state, not a new or fractional
carrier. Both responses retain the SAME vector and normalization. -/
theorem completed_even_filtered_form_gap (x : V) (hx : B x U = RCzero) (t : Nat) :
    RCle (B x (T (2*t+1) x)) (RCscale q (B x (T (2*t) x))) := by
  have hx' : B U x = RCzero := (completedInner_symm hw0 hw1 U x).trans hx
  have horth' := completedTime_preserves_vacuumComplement hw0 hw1 t x hx'
  have horth : B (T t x) U = RCzero :=
    (completedInner_symm hw0 hw1 (T t x) U).trans horth'
  have h := completed_oneStep_form_gap hw0 hw1 (T t x) horth
  rw [← completedTime_add hw0 hw1 1 t x,
    completedInner_time_sum hw0 hw1 t (1+t) x x,
    show t+(1+t)=2*t+1 by omega,
    ← completedInner_even_diagonal hw0 hw1 width t x] at h
  exact h

/-- The actual one-step time loss has the EXACT kinetic floor/cap margin. -/
theorem completed_oneStep_defect_margin (x : V) (hx : B x U = RCzero) :
    RCle (RCscale (mixFraction hw0 hw1 width) (B x x))
      (RCsub (B x x) (B x (T 1 x))) := by
  have h := defect_margin q (B x x) (B x (T 1 x))
    (completed_oneStep_form_gap hw0 hw1 x hx)
  have he : 1 + -q ≈ mixFraction hw0 hw1 width :=
    poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
      (.var 0) (by decide) (fun _ => mixFraction hw0 hw1 width)
  rwa [scale_congr he] at h

#print axioms completed_oneStep_form_gap
#print axioms completed_even_filtered_form_gap
#print axioms completed_oneStep_defect_margin

end YMGap.Continuum.BF4WilsonAllNomeOneStepGap
