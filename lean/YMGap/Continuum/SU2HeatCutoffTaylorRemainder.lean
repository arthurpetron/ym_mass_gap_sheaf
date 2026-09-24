/-
Quadratic remainder for the actual truncated SU(2) heat attenuation.

Below the cutoff this is the ordinary rational-power Taylor remainder.  Above
the cutoff the attenuation vanishes; the existing omitted-Casimir guard makes
the linear scale at least one, which still bounds the resulting remainder by
its square.  This is a finite scalar statement, not a scaling-limit claim.
-/

import YMGap.Continuum.BondMovingQuadratic
import YMGap.Continuum.RingNormaliser
import YMGap.Continuum.SU2HeatCutoffCasimirBound

namespace YMGap.Continuum.SU2HeatCutoffTaylorRemainder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.SU2HeatCutoffCasimirBound

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.neg_den, neg_num_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.natCast_mul, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.zero_mul, Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- First-order remainder for the actual finite-cutoff attenuation in harmonic
degree `d`. -/
def cutoffRemainder (w : Q') (K d : Nat) : Q' :=
  (attenuation w K d - (1 : Q')) +
    ((1 : Q') - w) * Q'.ofNat (d * (d + 2))

/-- The truncated attenuation remainder is nonnegative whenever the usual
linear cutoff/Casimir defect estimate is available. -/
theorem cutoffRemainder_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (K d : Nat)
    (hguard : (1 : Q') ≤
      ((1 : Q') - w) * Q'.ofNat ((K + 1) * (K + 3))) :
    (0 : Q') ≤ cutoffRemainder w K d := by
  have hdefect := one_sub_attenuation_le hw0 hw1 K d hguard
  have hcanonical :
      (0 : Q') ≤
        (((1 : Q') - w) * Q'.ofNat (d * (d + 2)) -
          ((1 : Q') - attenuation w K d)) :=
    Q'.sub_nonneg_of_le hdefect
  exact Q'.le_trans' _ _ _ hcanonical (Q'.le_of_eqv (by
    unfold cutoffRemainder
    exact RingNormaliser.poly_identity_of_normal_eq
      (.add (.mul (.var 1) (.var 2))
        (.neg (.add (.const 1) (.neg (.var 0)))))
      (.add (.add (.var 0) (.neg (.const 1)))
        (.mul (.var 1) (.var 2)))
      (by decide)
      (fun
        | 0 => attenuation w K d
        | 1 => (1 : Q') - w
        | _ => Q'.ofNat (d * (d + 2)))))

/-- The truncated attenuation has the same loose quadratic Taylor envelope in
every degree, including degrees omitted by the finite cutoff. -/
theorem cutoffRemainder_le_square {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (K d : Nat)
    (hguard : (1 : Q') ≤
      ((1 : Q') - w) * Q'.ofNat ((K + 1) * (K + 3))) :
    cutoffRemainder w K d ≤
      (((1 : Q') - w) * ((1 : Q') - w)) *
        Q'.ofNat ((d * (d + 2)) * (d * (d + 2))) := by
  let n := d * (d + 2)
  let x := ((1 : Q') - w) * Q'.ofNat n
  by_cases hd : d ≤ K
  · have hpower := secondOrder_qpow hw0 hw1 n
    have hleft : cutoffRemainder w K d ≈
        (Q'.ofNat n * ((1 : Q') - w)) - ((1 : Q') - qpow w n) := by
      unfold cutoffRemainder attenuation n
      rw [if_pos hd]
      exact RingNormaliser.poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.const 1)))
          (.mul (.var 1) (.var 2)))
        (.add (.mul (.var 2) (.var 1))
          (.neg (.add (.const 1) (.neg (.var 0)))))
        (by decide)
        (fun
          | 0 => qpow w (d * (d + 2))
          | 1 => (1 : Q') - w
          | _ => Q'.ofNat (d * (d + 2)))
    have hright :
        ((Q'.ofNat n * Q'.ofNat n) *
            (((1 : Q') - w) * ((1 : Q') - w))) ≈
          (((1 : Q') - w) * ((1 : Q') - w)) *
            Q'.ofNat ((d * (d + 2)) * (d * (d + 2))) := by
      have hcoefficient :
          (Q'.ofNat n * Q'.ofNat n).eqv (Q'.ofNat (n * n)) :=
        Q'.eqv_symm (ofNat_mul_eqv n n)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hcoefficient) ?_
      unfold n
      ring_qeqv
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hpower (Q'.le_of_eqv hright))
  · have hdefect := one_sub_attenuation_le hw0 hw1 K d hguard
    have hx : (1 : Q') ≤ x := by
      unfold attenuation at hdefect
      rw [if_neg hd] at hdefect
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (by decide : (1 : Q') ≈ (1 : Q') - 0)) hdefect
    have hx0 : (0 : Q') ≤ x := Q'.le_trans' _ _ _ (by decide) hx
    have hxx : x ≤ x * x := by
      have hmul := Q'.mul_le_mul_of_nonneg_right (1 : Q') x x hx hx0
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv x))) hmul
    have hdrop : x + (-(1 : Q')) ≤ x := by
      have hadd := Q'.add_le_add_left x (-(1 : Q')) 0 (by decide)
      simpa only [Q'.add_zero'] using hadd
    have hleft : cutoffRemainder w K d ≈ x + (-(1 : Q')) := by
      unfold cutoffRemainder attenuation x n
      rw [if_neg hd]
      exact RingNormaliser.poly_identity_of_normal_eq
        (.add (.add (.const 0) (.neg (.const 1)))
          (.mul (.var 0) (.var 1)))
        (.add (.mul (.var 0) (.var 1)) (.neg (.const 1)))
        (by decide)
        (fun
          | 0 => (1 : Q') - w
          | _ => Q'.ofNat (d * (d + 2)))
    have hright :
        (x * x).eqv
          ((((1 : Q') - w) * ((1 : Q') - w)) *
            Q'.ofNat ((d * (d + 2)) * (d * (d + 2)))) := by
      unfold x n
      have hreorder :
          ((((1 : Q') - w) * Q'.ofNat (d * (d + 2))) *
              (((1 : Q') - w) * Q'.ofNat (d * (d + 2)))).eqv
            ((((1 : Q') - w) * ((1 : Q') - w)) *
              (Q'.ofNat (d * (d + 2)) * Q'.ofNat (d * (d + 2)))) := by
        ring_qeqv
      refine Q'.eqv_trans _ _ _ hreorder ?_
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (ofNat_mul_eqv (d * (d + 2)) (d * (d + 2))))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hdrop
        (Q'.le_trans' _ _ _ hxx (Q'.le_of_eqv hright)))

/-- Computed-cutoff specialization, requiring no separate omitted-mode guard. -/
theorem cutoffRemainder_bounds_of_sufficientCutoff {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) {K : Nat}
    (hK : sufficientCutoff w ≤ K) (d : Nat) :
    (0 : Q') ≤ cutoffRemainder w K d ∧
      cutoffRemainder w K d ≤
        (((1 : Q') - w) * ((1 : Q') - w)) *
          Q'.ofNat ((d * (d + 2)) * (d * (d + 2))) := by
  have hguard := cutoff_guard_of_le hw1 hK
  exact ⟨cutoffRemainder_nonnegative hw0 (Q'.le_of_lt hw1) K d hguard,
    cutoffRemainder_le_square hw0 (Q'.le_of_lt hw1) K d hguard⟩

end YMGap.Continuum.SU2HeatCutoffTaylorRemainder

#print axioms YMGap.Continuum.SU2HeatCutoffTaylorRemainder.cutoffRemainder_nonnegative
#print axioms YMGap.Continuum.SU2HeatCutoffTaylorRemainder.cutoffRemainder_le_square
#print axioms YMGap.Continuum.SU2HeatCutoffTaylorRemainder.cutoffRemainder_bounds_of_sufficientCutoff
