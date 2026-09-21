/-
# SU(2) dimension-weighted neighboring heat convexity

For a rational heat ratio in `[0,1]`, the adjacent SU(2) dimension weights
satisfy the elementary convexity inequality used to align neighboring
Casimir labels.  The proof is constructive induction on the label.  Its gap
recurrence is an exact polynomial identity, and every increment is exhibited
as a product of nonnegative rational factors.

This is only the arithmetic neighboring-label ingredient.  It is not a gap,
a pointwise heat-kernel order theorem, or a removal of endpoint truncation
errors in a finite character sum.
-/

import YMGap.Constructive.CauchyConv
import YMGap.Constructive.SumOfSquares
import YMGap.Continuum.HeatKernelPos
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2HeatNeighborConvexity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private def gap (x : Q') (j : Nat) : Q' :=
  Q'.ofNat j + Q'.ofNat (j + 2) * x ^ (2 * j + 2) +
    -(2 * Q'.ofNat (j + 1) * x ^ (j + 2))

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem add_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ ha)
    (Q'.add_eqv_congr_left _ _ _ hb)

private theorem pow_add_two (x : Q') (n : Nat) :
    x ^ (n + 2) ≈ (x * x) * x ^ n := by
  rw [show n + 2 = (n + 1) + 1 by omega, Q'.pow_succ, Q'.pow_succ]
  exact Q'.eqv_symm (Q'.mul_assoc_eqv x x (x ^ n))

private theorem pow_add (x : Q') (a : Nat) : ∀ b : Nat,
    x ^ (a + b) ≈ x ^ a * x ^ b
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv (x ^ a))
  | b + 1 => by
      rw [show a + (b + 1) = (a + b) + 1 by omega,
        Q'.pow_succ, Q'.pow_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left x _ _ (pow_add x a b)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv x (x ^ a) (x ^ b))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (x ^ b) (Q'.mul_comm_eqv x (x ^ a))) ?_
      exact Q'.mul_assoc_eqv (x ^ a) x (x ^ b)

private theorem gap_step_algebra (J x p q : Q') :
    (J + 1) + ((J + 2) * ((x * x) * q) + p * p) +
        -(2 * (J + 2) * (x * p)) ≈
      (x * x) * (J + (J + 2) * q + -(2 * (J + 1) * p)) +
        (x + -p) * (x + -p) +
        (J + 1) * ((1 + -x) * (1 + x + -(2 * (x * p)))) := by
  exact poly_identity_of_normal_eq
    (.add
      (.add (.add (.var 0) (.const 1))
        (.add
          (.mul (.add (.var 0) (.const 2))
            (.mul (.mul (.var 1) (.var 1)) (.var 3)))
          (.mul (.var 2) (.var 2))))
      (.neg (.mul (.mul (.const 2) (.add (.var 0) (.const 2)))
        (.mul (.var 1) (.var 2)))))
    (.add
      (.add
        (.mul (.mul (.var 1) (.var 1))
          (.add
            (.add (.var 0) (.mul (.add (.var 0) (.const 2)) (.var 3)))
            (.neg (.mul (.mul (.const 2) (.add (.var 0) (.const 1))) (.var 2)))))
        (.mul (.add (.var 1) (.neg (.var 2)))
          (.add (.var 1) (.neg (.var 2)))))
      (.mul (.add (.var 0) (.const 1))
        (.mul (.add (.const 1) (.neg (.var 1)))
          (.add (.add (.const 1) (.var 1))
            (.neg (.mul (.const 2) (.mul (.var 1) (.var 2))))))))
    (by decide) (fun | 0 => J | 1 => x | 2 => p | _ => q)

private theorem gap_step (x : Q') (j : Nat) :
    gap x (j + 1) ≈
      (x * x) * gap x j +
        (x + -(x ^ (j + 2))) * (x + -(x ^ (j + 2))) +
        Q'.ofNat (j + 1) *
          ((1 + -x) * (1 + x + -(2 * x ^ (j + 3)))) := by
  let J := Q'.ofNat j
  let p := x ^ (j + 2)
  let q := x ^ (2 * j + 2)
  have hJ1 : Q'.ofNat (j + 1) ≈ J + 1 := by
    exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv j 1)
      (Q'.add_eqv_congr_left _ _ _ (by decide))
  have hJ2 : Q'.ofNat (j + 2) ≈ J + 2 := by
    exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv j 2)
      (Q'.add_eqv_congr_left _ _ _ (by decide))
  have hJ3 : Q'.ofNat (j + 3) ≈ J + 3 := by
    exact Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv j 3)
      (Q'.add_eqv_congr_left _ _ _ (by decide))
  have hp : x ^ (j + 3) ≈ x * p := by
    dsimp only [p]
    rw [show j + 3 = (j + 2) + 1 by omega, Q'.pow_succ]
    exact Q'.eqv_refl _
  have hq : x ^ (2 * (j + 1) + 2) ≈ (x * x) * q := by
    dsimp only [q]
    rw [show 2 * (j + 1) + 2 = (2 * j + 2) + 2 by omega]
    exact pow_add_two x (2 * j + 2)
  have hpp : x ^ (2 * (j + 1) + 2) ≈ p * p := by
    dsimp only [p]
    rw [show 2 * (j + 1) + 2 = (j + 2) + (j + 2) by omega]
    exact pow_add x (j + 2) (j + 2)
  have hweighted :
      Q'.ofNat ((j + 1) + 2) * x ^ (2 * (j + 1) + 2) ≈
        (J + 2) * ((x * x) * q) + p * p := by
    have hsplit :
        (J + 3) * x ^ (2 * (j + 1) + 2) ≈
          (J + 2) * x ^ (2 * (j + 1) + 2) + x ^ (2 * (j + 1) + 2) :=
      poly_identity_of_normal_eq
        (.mul (.add (.var 0) (.const 3)) (.var 1))
        (.add (.mul (.add (.var 0) (.const 2)) (.var 1)) (.var 1))
        (by decide) (fun | 0 => J | _ => x ^ (2 * (j + 1) + 2))
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hJ3)
      (Q'.eqv_trans _ _ _ hsplit
        (add_congr (mul_congr (Q'.eqv_refl _) hq) hpp))
  have hleft : gap x (j + 1) ≈
      (J + 1) + ((J + 2) * ((x * x) * q) + p * p) +
        -(2 * (J + 2) * (x * p)) := by
    unfold gap
    exact add_congr
      (add_congr hJ1 hweighted)
      (Q'.neg_eqv_congr _ _
        (mul_congr (mul_congr (Q'.eqv_refl 2) hJ2) hp))
  have hgapmodel :
      J + (J + 2) * q + -(2 * (J + 1) * p) ≈ gap x j := by
    unfold gap
    exact add_congr
      (add_congr (Q'.eqv_refl _)
        (mul_congr (Q'.eqv_symm hJ2) (Q'.eqv_refl _)))
      (Q'.neg_eqv_congr _ _
        (mul_congr
          (mul_congr (Q'.eqv_refl 2) (Q'.eqv_symm hJ1))
          (Q'.eqv_refl _)))
  have hright :
      (x * x) * (J + (J + 2) * q + -(2 * (J + 1) * p)) +
          (x + -p) * (x + -p) +
          (J + 1) * ((1 + -x) * (1 + x + -(2 * (x * p)))) ≈
        (x * x) * gap x j +
          (x + -(x ^ (j + 2))) * (x + -(x ^ (j + 2))) +
          Q'.ofNat (j + 1) *
            ((1 + -x) * (1 + x + -(2 * x ^ (j + 3)))) := by
    dsimp only [J, p, q]
    exact add_congr
      (add_congr
        (mul_congr (Q'.eqv_refl _) hgapmodel)
        (Q'.eqv_refl _))
      (mul_congr (Q'.eqv_symm hJ1)
        (mul_congr (Q'.eqv_refl _)
          (add_congr (Q'.eqv_refl _)
            (Q'.neg_eqv_congr _ _
              (mul_congr (Q'.eqv_refl 2) (Q'.eqv_symm hp))))))
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ (gap_step_algebra J x p q) hright)

private theorem gap_zero (x : Q') : gap x 0 ≈ 0 := by
  unfold gap
  simp only [Q'.pow_succ, Q'.pow_zero]
  exact poly_identity_of_normal_eq
    (.add
      (.add (.const 0)
        (.mul (.const 2) (.mul (.var 0) (.mul (.var 0) (.const 1)))))
      (.neg (.mul (.mul (.const 2) (.const 1))
        (.mul (.var 0) (.mul (.var 0) (.const 1))))))
    (.const 0) (by decide) (fun _ => x)

private theorem gap_nonnegative {x : Q'} (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    ∀ j : Nat, (0 : Q') ≤ gap x j := by
  intro j
  induction j with
  | zero => exact Q'.le_of_eqv (Q'.eqv_symm (gap_zero x))
  | succ j ih =>
      let p := x ^ (j + 2)
      let r := x ^ (j + 3)
      have hxx : (0 : Q') ≤ x * x := SumOfSquares.q_mul_self_nonneg x
      have hfirst : (0 : Q') ≤ (x * x) * gap x j :=
        Q'.mul_nonneg _ _ hxx ih
      have hsquare : (0 : Q') ≤ (x + -p) * (x + -p) :=
        SumOfSquares.q_mul_self_nonneg (x + -p)
      have hrx : r ≤ x := by
        dsimp only [r]
        exact HKPos.pow_succ_le_self hx0 hx1 (j + 2)
      have hr1 : r ≤ (1 : Q') := Q'.le_trans' _ _ _ hrx hx1
      have htwor : 2 * r ≤ 1 + x := by
        have hadd : r + r ≤ 1 + x := Q'.add_le_add hr1 hrx
        have he : 2 * r ≈ r + r :=
          poly_identity_of_normal_eq (.mul (.const 2) (.var 0))
            (.add (.var 0) (.var 0)) (by decide) (fun _ => r)
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hadd
      have hlastFactor : (0 : Q') ≤ 1 + x + -(2 * r) :=
        Q'.sub_nonneg_of_le htwor
      have hthird : (0 : Q') ≤
          Q'.ofNat (j + 1) * ((1 + -x) * (1 + x + -(2 * r))) :=
        Q'.mul_nonneg _ _ (Q'.le_of_lt (Q'.ofNat_succ_pos j))
          (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hx1) hlastFactor)
      have hsum : (0 : Q') ≤
          (x * x) * gap x j + (x + -p) * (x + -p) +
            Q'.ofNat (j + 1) * ((1 + -x) * (1 + x + -(2 * r))) :=
        Q'.zero_le_add _ _ (Q'.zero_le_add _ _ hfirst hsquare) hthird
      exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv (gap_step x j))

/-- SU(2) dimension-weighted adjacent-Casimir convexity on the rational unit
interval.  Endpoint errors from truncating a label sum are not part of this
inequality and must remain explicit in its consumers. -/
theorem dimension_weighted_neighbor_convexity {x : Q'}
    (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (j : Nat) :
    2 * Q'.ofNat (j + 1) * x ^ (j + 2) ≤
      Q'.ofNat j + Q'.ofNat (j + 2) * x ^ (2 * j + 2) :=
  Q'.le_of_sub_nonneg (gap_nonnegative hx0 hx1 j)

end YMGap.Continuum.SU2HeatNeighborConvexity

#print axioms YMGap.Continuum.SU2HeatNeighborConvexity.dimension_weighted_neighbor_convexity
