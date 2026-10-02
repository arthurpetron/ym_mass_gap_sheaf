/-
# Exact positive curvature gain of the ORIGINAL Wilson time response

For the actual completed T and D=I-T, the mixed-moment split telescopes to
  B(x,T^m x) = B(x,x) - m B(x,Dx) +
    sum_{j=0}^{m-2} (m-1-j) B(Dx,T^j Dx).
The triangular gain is computed from the same mixed moments and is
nonnegative. The literal dyadic UNIT excitation has B(x,x)=1.

This keeps the positive curvature which the linear one-step energy bound
discards. It produces no quantitative lower bound on that gain, no spectral
measure or log identification, and no changing-family survival theorem.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
import YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments

namespace YMGap.Continuum.BF4WilsonAllNomeResponseCurvatureGain

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem eq_sub_of_eq_add {a b c : RC} (h : a = RCadd b c) : b = RCsub a c := by
  rw [h]
  refine Quotient.inductionOn₂ b c ?_
  exact fun B C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.var 0)
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1)))
      (by decide) (fun | 0 => B.approx n | _ => C.approx n)))

private theorem rc_nat_succ_scale (n : Nat) (a : RC) :
    RCscale (Q'.ofNat (n+1)) a = RCadd (RCscale (Q'.ofNat n) a) a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun j =>
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv n 1))
      (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv (A.approx j))))))

private theorem row_step_ring (a b c g : RC) (q : Q') :
    RCadd (RCsub (RCsub a b) (RCscale q (RCsub b c))) g =
      RCadd (RCsub a (RCadd (RCscale q b) b)) (RCadd (RCscale q c) g) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  refine Quotient.inductionOn g ?_
  intro G
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.neg (.var 1)))
        (.neg (.mul (.var 4) (.add (.var 1) (.neg (.var 2)))))) (.var 3))
      (.add (.add (.var 0) (.neg (.add (.mul (.var 4) (.var 1)) (.var 1))))
        (.add (.mul (.var 4) (.var 2)) (.var 3)))
      (by decide) (fun
        | 0 => A.approx n
        | 1 => B.approx n
        | 2 => C.approx n
        | 3 => G.approx n
        | _ => q)))

private theorem complement_ring (a b c : RC) :
    RCadd (RCsub a b) c = RCsub a (RCsub b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 2))
      (.add (.var 0) (.neg (.add (.var 1) (.neg (.var 2)))))
      (by decide) (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

private theorem complement_le (a b c : RC) (h : RCle a (RCsub c b)) :
    RCle b (RCsub c a) := by
  have hh := RCadd_le_add h (RCle_refl (RCsub b a))
  have hl : RCadd a (RCsub b a) = b := by
    refine Quotient.inductionOn₂ a b ?_
    exact fun A B => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq (.add (.var 0) (.add (.var 1) (.neg (.var 0))))
        (.var 1) (by decide) (fun | 0 => A.approx n | _ => B.approx n)))
  have hr : RCadd (RCsub c b) (RCsub b a) = RCsub c a := by
    refine Quotient.inductionOn₃ a b c ?_
    exact fun A B C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 2) (.neg (.var 1))) (.add (.var 1) (.neg (.var 0))))
        (.add (.var 2) (.neg (.var 0))) (by decide)
        (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))
  rwa [hl, hr] at hh

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "M" => mixedMoment hw0 hw1

/-- The actual one-step reflected energy, on this unchanged completion. -/
def responseOneStepLoss (x : V) : RC := M x 0 1

theorem responseOneStepLoss_pin (x : V) :
    responseOneStepLoss hw0 hw1 x = B x (defect hw0 hw1 x) := by
  simp only [responseOneStepLoss, mixedMoment, defectPower, completedTime_zero]

/-- Literal head-recursive triangular sum: weights count,count-1,...,1. -/
def responseCurvatureRow (x : V) : Nat → Nat → RC
  | _, 0 => RCzero
  | start, count+1 => RCadd
      (RCscale (Q'.ofNat (count+1)) (M x start 2))
      (responseCurvatureRow x (start+1) count)

/-- Computed gain at lag m; the empty m=0 and m=1 sums are zero. -/
def responseCurvatureGain (x : V) (lag : Nat) : RC :=
  responseCurvatureRow hw0 hw1 x 0 (lag-1)

theorem responseCurvature_pin (x : V) (j : Nat) :
    M x j 2 = B (defect hw0 hw1 x) (T j (defect hw0 hw1 x)) := by
  rw [defect_symmetric, defect_time]
  rfl

theorem responseCurvatureRow_nonnegative (x : V) : ∀ start count : Nat,
    RCnonneg (responseCurvatureRow hw0 hw1 x start count)
  | _, 0 => RCle_refl _
  | start, count+1 => by
      have hc := RCscale_mono (Q'.ofNat_nonneg (count+1))
        (mixedMoment_nonnegative hw0 hw1 x start 2)
      rw [RCscale_RCzero] at hc
      have h := RCadd_le_add hc (responseCurvatureRow_nonnegative x (start+1) count)
      rw [rc_zero_add] at h
      exact h

theorem responseCurvatureGain_nonnegative (x : V) (lag : Nat) :
    RCnonneg (responseCurvatureGain hw0 hw1 x lag) :=
  responseCurvatureRow_nonnegative hw0 hw1 x 0 (lag-1)

private theorem responseCurvatureRow_identity (x : V) (count : Nat) : ∀ start : Nat,
    M x (start+count+1) 0 =
      RCadd (RCsub (M x start 0) (RCscale (Q'.ofNat (count+1)) (M x start 1)))
        (responseCurvatureRow hw0 hw1 x start count) := by
  induction count with
  | zero =>
      intro start
      have h := eq_sub_of_eq_add (mixedMoment_split hw0 hw1 x start 0)
      simpa only [Nat.add_zero, responseCurvatureRow, RCscale_one,
        show Q'.ofNat (0+1) = (1 : Q') from rfl,
        rc_add_zero] using h
  | succ count ih =>
      intro start
      have hr := eq_sub_of_eq_add (mixedMoment_split hw0 hw1 x start 0)
      have hd := eq_sub_of_eq_add (mixedMoment_split hw0 hw1 x start 1)
      rw [show start+(count+1)+1=(start+1)+count+1 by omega, ih (start+1)]
      rw [hr, hd]
      have hs := row_step_ring (M x start 0) (M x start 1) (M x start 2)
        (responseCurvatureRow hw0 hw1 x (start+1) count) (Q'.ofNat (count+1))
      rw [← rc_nat_succ_scale (count+1)] at hs
      exact hs

/-- Exact complete response: none of its positive curvature is discarded. -/
theorem response_curvature_identity (x : V) (lag : Nat) :
    B x (T lag x) =
      RCadd (RCsub (B x x)
        (RCscale (Q'.ofNat lag) (responseOneStepLoss hw0 hw1 x)))
        (responseCurvatureGain hw0 hw1 x lag) := by
  cases lag with
  | zero =>
      rw [completedTime_zero]
      change B x x = RCadd (RCsub (B x x) (RCscale 0 _)) RCzero
      refine Quotient.inductionOn (B x x) ?_
      intro A
      refine Quotient.inductionOn (responseOneStepLoss hw0 hw1 x) ?_
      intro E
      exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
        poly_identity_of_normal_eq (.var 0)
          (.add (.add (.var 0) (.neg (.mul (.const 0) (.var 1)))) (.const 0))
          (by decide) (fun | 0 => A.approx n | _ => E.approx n)))
  | succ count =>
      have h := responseCurvatureRow_identity hw0 hw1 x count 0
      simpa only [Nat.zero_add, Nat.add_sub_cancel, mixedMoment_zero,
        mixedMoment, defectPower, completedTime_zero,
        responseOneStepLoss, responseCurvatureGain] using h

variable (scale : Nat) (hwidth : side scale < width)

local notation "u" => Subtype.val (dyadicUnitExcitation hw0 hw1 scale width hwidth)

/-- Literal dyadic unit instance on the SAME actual time and defect. -/
theorem dyadicUnit_response_curvature_identity (lag : Nat) :
    B u (T lag u) =
      RCadd (RCsub (Rq 1)
        (RCscale (Q'.ofNat lag) (responseOneStepLoss hw0 hw1 u)))
        (responseCurvatureGain hw0 hw1 u lag) := by
  rw [response_curvature_identity, dyadicUnitExcitation_norm]

/-- Exact scalar equivalence, not a supplied quantitative gain estimate.
A large first loss is permitted when its computed curvature compensates it. -/
theorem dyadicUnit_response_lower_iff (lag : Nat) (gamma : Q') :
    RCle (RCsub (RCscale (Q'.ofNat lag) (responseOneStepLoss hw0 hw1 u))
      (responseCurvatureGain hw0 hw1 u lag)) (Rq (1-gamma)) ↔
    RCle (Rq gamma) (B u (T lag u)) := by
  have hp : Rq (1-gamma) = RCsub (Rq 1) (Rq gamma) := rfl
  have hr := dyadicUnit_response_curvature_identity hw0 hw1 scale hwidth lag
  rw [complement_ring] at hr
  rw [hp, hr]
  exact ⟨fun h => complement_le _ _ _ h, fun h => complement_le _ _ _ h⟩

#print axioms responseOneStepLoss
#print axioms responseOneStepLoss_pin
#print axioms responseCurvatureRow
#print axioms responseCurvatureGain
#print axioms responseCurvature_pin
#print axioms responseCurvatureRow_nonnegative
#print axioms responseCurvatureGain_nonnegative
#print axioms response_curvature_identity
#print axioms dyadicUnit_response_curvature_identity
#print axioms dyadicUnit_response_lower_iff

end YMGap.Continuum.BF4WilsonAllNomeResponseCurvatureGain
