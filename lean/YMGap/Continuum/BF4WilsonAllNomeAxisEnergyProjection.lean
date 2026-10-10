/-
# Energy of the actual spatial-axis sectors

The even and odd averages of the existing spatial swap split both the
completed pairing and its one-step time defect. Positivity of the latter
therefore makes even projection energy-contracting on the SAME original
Wilson completion. This is an unconditional fixed-nome statement, not a
dual-overlap, late-response, or mass-gap estimate.
-/

import YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion
import YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments

namespace YMGap.Continuum.BF4WilsonAllNomeAxisEnergyProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
open YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "U" => completedSwap hw0 hw1
local notation "P" => evenPart hw0 hw1
local notation "O" => oddPart hw0 hw1

private theorem rc_parity_pair (a b : RC) :
    RCadd
      (RCscale HalfPow.half
        (RCadd (RCscale HalfPow.half (RCadd a b))
          (RCscale HalfPow.half (RCadd b a))))
      (RCscale HalfPow.half
        (RCsub (RCscale HalfPow.half (RCsub a b))
          (RCscale HalfPow.half (RCsub b a)))) = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.add
        (.mul (.var 2)
          (.add
            (.mul (.var 2) (.add (.var 0) (.var 1)))
            (.mul (.var 2) (.add (.var 1) (.var 0)))))
        (.mul (.var 2)
          (.add
            (.mul (.var 2) (.add (.var 0) (.neg (.var 1))))
            (.neg (.mul (.var 2)
              (.add (.var 1) (.neg (.var 0))))))))
      (.mul (.mul (.const 4) (.mul (.var 2) (.var 2))) (.var 0))
      (by decide)
      (fun | 0 => A.approx n | 1 => B'.approx n | _ => HalfPow.half))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right
          (Q'.ofInt 4 * (HalfPow.half * HalfPow.half)) 1
          (A.approx n) (by decide))
        (Q'.one_mul_eqv (A.approx n)))))

private theorem rc_sub_pair (a b c d : RC) :
    RCadd (RCsub a b) (RCsub c d) =
      RCsub (RCadd a c) (RCadd b d) := by
  refine Quotient.inductionOn a ?_
  intro A
  refine Quotient.inductionOn b ?_
  intro B'
  refine Quotient.inductionOn c ?_
  intro C
  refine Quotient.inductionOn d ?_
  intro D
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1)))
        (.add (.var 2) (.neg (.var 3))))
      (.add (.add (.var 0) (.var 2))
        (.neg (.add (.var 1) (.var 3))))
      (by decide)
      (fun
        | 0 => A.approx n
        | 1 => B'.approx n
        | 2 => C.approx n
        | _ => D.approx n)))

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n))))

/-- Orthogonal polarization of the two actual swap-sector projections. -/
theorem sector_pairing_split (x y : V) :
    RCadd (B (P x) (P y)) (B (O x) (O y)) = B x y := by
  have heven : B (P x) (P y) =
      RCscale HalfPow.half
        (RCadd (RCscale HalfPow.half (RCadd (B x y) (B x (U y))))
          (RCscale HalfPow.half (RCadd (B x (U y)) (B x y)))) := by
    unfold evenPart
    rw [completedInner_smul_left, completedInner_add_left,
      completedInner_smul_right, completedInner_smul_right,
      completedInner_add_right, completedInner_add_right,
      completedInner_swap_balance hw0 hw1 x y,
      completedInner_swap hw0 hw1 x y]
  have hodd : B (O x) (O y) =
      RCscale HalfPow.half
        (RCsub (RCscale HalfPow.half (RCsub (B x y) (B x (U y))))
          (RCscale HalfPow.half (RCsub (B x (U y)) (B x y)))) := by
    unfold oddPart
    rw [completedInner_smul_left, completedInner_sub_left,
      completedInner_smul_right, completedInner_smul_right,
      completedInner_sub_right, completedInner_sub_right,
      completedInner_swap_balance hw0 hw1 x y,
      completedInner_swap hw0 hw1 x y]
  rw [heven, hodd]
  exact rc_parity_pair (B x y) (B x (U y))

/-- The one-step defect energy splits without changing its time operator. -/
theorem sector_energy_split (v : V) :
    RCadd (B (P v) (defect hw0 hw1 (P v)))
      (B (O v) (defect hw0 hw1 (O v))) =
        B v (defect hw0 hw1 v) := by
  have he : B (P v) (defect hw0 hw1 (P v)) =
      RCsub (B (P v) (P v)) (B (P v) (P (T 1 v))) := by
    rw [defect, completedInner_sub_right,
      ← evenPart_time hw0 hw1 1 v]
  have ho : B (O v) (defect hw0 hw1 (O v)) =
      RCsub (B (O v) (O v)) (B (O v) (O (T 1 v))) := by
    rw [defect, completedInner_sub_right,
      ← oddPart_time hw0 hw1 1 v]
  rw [he, ho, rc_sub_pair, sector_pairing_split hw0 hw1 v v,
    sector_pairing_split hw0 hw1 v (T 1 v)]
  exact (completedInner_sub_right hw0 hw1 v v (T 1 v)).symm

/-- Even projection cannot increase actual one-step energy. -/
theorem evenPart_energy_le (v : V) :
    RCle (B (P v) (defect hw0 hw1 (P v)))
      (B v (defect hw0 hw1 v)) := by
  have h := RCadd_le_add
    (RCle_refl (B (P v) (defect hw0 hw1 (P v))))
    (defect_nonnegative hw0 hw1 (O v))
  rw [rc_add_zero, sector_energy_split hw0 hw1 v] at h
  exact h

#print axioms sector_pairing_split
#print axioms sector_energy_split
#print axioms evenPart_energy_le

end YMGap.Continuum.BF4WilsonAllNomeAxisEnergyProjection
