/-
# Fixed-parameter geometric decay of original mixed time/defect moments

The original kinetic floor/cap gap applies at each even physical-time slice
of a vacuum-orthogonal state. This gives geometric decay for EVERY defect
degree on the same completed Wilson carrier. The rate retains its nome and
width dependence; no changing-family or continuum estimate follows.
-/

import YMGap.Continuum.BF4WilsonAllNomeDefectMomentGap
import YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail

namespace YMGap.Continuum.BF4WilsonAllNomeTimeDefectGeometric

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixFraction mixRate mixRate_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail
  (mixedMoment_time_decreasing)
open YMGap.Continuum.BF4WilsonAllNomeDefectMomentGap
  (defect_moment_step_gap)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "M" => mixedMoment hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "r" => mixFraction hw0 hw1 width
local notation "q" => mixRate hw0 hw1 width

private theorem add_sub_last (a b : RC) : RCsub (RCadd a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 1)))
      (.var 0) (by decide) (fun
        | 0 => A.approx n
        | _ => B'.approx n)))

private theorem sub_scaled_self (s : Q') (a : RC) :
    RCsub a (RCscale s a) = RCscale (1 + -s) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.mul (.var 1) (.var 0))))
      (.mul (.add (.const 1) (.neg (.var 1))) (.var 0))
      (by decide) (fun | 0 => A.approx n | _ => s)))

/-- Both sides use the original time map and the same completed state. -/
theorem mixedMoment_evenTime_shift (x : V) (t l : Nat) :
    M x (2*t) l = M (T t x) 0 l := by
  calc
    M x (2*t) l = B x (T (t+t) (defectPower hw0 hw1 l x)) := by
      rw [show 2*t=t+t by omega]
      rfl
    _ = B (T t x) (T t (defectPower hw0 hw1 l x)) :=
      (completedInner_time_sum hw0 hw1 t t x (defectPower hw0 hw1 l x)).symm
    _ = M (T t x) 0 l := by
      rw [time_defectPower hw0 hw1 l t x]
      simp only [mixedMoment, completedTime_zero]

private theorem mixedMoment_evenTime_defect_gap (x : V) (hx : B x U = RCzero)
    (t l : Nat) : RCle (RCscale r (M x (2*t) l)) (M x (2*t) (l+1)) := by
  have hx' : B U x = RCzero := (completedInner_symm hw0 hw1 U x).trans hx
  have htime := completedTime_preserves_vacuumComplement hw0 hw1 t x hx'
  have horth : B (T t x) U = RCzero :=
    (completedInner_symm hw0 hw1 (T t x) U).trans htime
  have h : RCle (RCscale r (M (T t x) 0 l)) (M (T t x) 0 (l+1)) := by
    simpa only [mixedMoment, completedTime_zero] using
      (defect_moment_step_gap hw0 hw1 (T t x) horth l)
  rw [← mixedMoment_evenTime_shift hw0 hw1 x t l,
    ← mixedMoment_evenTime_shift hw0 hw1 x t (l+1)] at h
  exact h

/-- One two-step time contraction for every original defect degree. -/
theorem mixedMoment_evenTime_step (x : V) (hx : B x U = RCzero)
    (t l : Nat) :
    RCle (M x (2*(t+1)) l) (RCscale q (M x (2*t) l)) := by
  let a := M x (2*t) l
  let b := M x (2*t+1) l
  let c := M x (2*t) (l+1)
  have hs : a = RCadd b c := mixedMoment_split hw0 hw1 x (2*t) l
  have hg : RCle (RCscale r a) c :=
    mixedMoment_evenTime_defect_gap hw0 hw1 x hx t l
  have hbc : RCle (RCadd b (RCscale r a)) a := by
    exact RCle_trans (RCadd_le_add (RCle_refl b) hg)
      (by rw [← hs]; exact RCle_refl a)
  have hsub := RCadd_le_add hbc (RCle_refl (RCneg (RCscale r a)))
  change RCle (RCsub (RCadd b (RCscale r a)) (RCscale r a))
    (RCsub a (RCscale r a)) at hsub
  rw [add_sub_last, sub_scaled_self] at hsub
  have hnext : RCle (M x (2*(t+1)) l) b := by
    have h := mixedMoment_time_decreasing hw0 hw1 x (2*t+1) l
    simpa only [b, show 2*(t+1)=2*t+1+1 by omega] using h
  exact RCle_trans hnext hsub

/-- Fixed nome and width; the zero state and every defect degree are included. -/
theorem mixedMoment_evenTime_geometric (x : V) (hx : B x U = RCzero)
    (t l : Nat) :
    RCle (M x (2*t) l) (RCscale (q^t) (M x 0 l)) := by
  induction t with
  | zero =>
      simpa only [Nat.mul_zero, Q'.pow_zero, RCscale_one] using
        (RCle_refl (M x 0 l))
  | succ t ih =>
      have h := RCle_trans
        (mixedMoment_evenTime_step hw0 hw1 x hx t l)
        (RCscale_mono (mixRate_nonnegative hw0 hw1 width) ih)
      rw [RCscale_RCscale, ← Q'.pow_succ] at h
      exact h

#print axioms mixedMoment_evenTime_shift
#print axioms mixedMoment_evenTime_step
#print axioms mixedMoment_evenTime_geometric

end YMGap.Continuum.BF4WilsonAllNomeTimeDefectGeometric
