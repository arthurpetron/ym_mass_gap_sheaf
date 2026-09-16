/-
# Differences and midpoint order for the actual intrinsic reflected pairing

Subtraction retains the original finite signed natural-distance schedules.
The checked bilinear laws give its four-pairing expansion; actual reflected
positivity of this difference gives the midpoint inequality. Nome, spatial
width and heat stage are unchanged throughout.

These are algebra and order laws for the existing original-action scalar
pairing. No time-shift identity, norm contraction, completed operator,
one-step transfer positivity or continuum statement is assumed or claimed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm

/-- Literal subtraction in the same signed natural-distance presentation. -/
def difference (xs ys : DistanceSpan) : DistanceSpan :=
  xs ++ scaleSpan (-1) ys

theorem physical_difference {width : Nat} {xs ys : DistanceSpan}
    (hx : Physical width xs) (hy : Physical width ys) :
    Physical width (difference xs ys) :=
  physical_append hx (physical_scale (-1) hy)

theorem radius_difference (xs ys : DistanceSpan) :
    radius (difference xs ys) = max (radius xs) (radius ys) := by
  rw [difference, radius_append, radius_scale]

private theorem negative_one_mul (A : CReal) :
    Equiv (mul (ofQ' (-1)) A) (neg A) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (A.approx n))
    (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (A.approx n)))

private theorem sub_congr {a b c d : CReal} (ha : Equiv a b) (hc : Equiv c d) :
    Equiv (sub a c) (sub b d) :=
  Equiv_add ha (CReal.neg_congr hc)

private theorem sub_self (A : CReal) : Equiv (sub A A) (ofQ' 0) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv (A.approx n))

/-- Subtraction in the first argument, without a physical-face premise. -/
theorem pairing_difference_left {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (xs ys zs : DistanceSpan) (stage : Nat) :
    Equiv (pairing hw0 hw1 width (difference xs ys) zs stage)
      (sub (pairing hw0 hw1 width xs zs stage) (pairing hw0 hw1 width ys zs stage)) :=
  Equiv.trans (pairing_add_left hw0 hw1 width xs (scaleSpan (-1) ys) zs stage)
    (Equiv_add (Equiv.refl _) (Equiv.trans
      (pairing_smul_left hw0 hw1 width (-1) ys zs stage) (negative_one_mul _)))

/-- Subtraction in the second argument, with all three spans ordered explicitly. -/
theorem pairing_difference_right {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (xs ys zs : DistanceSpan) (stage : Nat) :
    Equiv (pairing hw0 hw1 width xs (difference ys zs) stage)
      (sub (pairing hw0 hw1 width xs ys stage) (pairing hw0 hw1 width xs zs stage)) :=
  Equiv.trans (pairing_add_right hw0 hw1 width xs ys (scaleSpan (-1) zs) stage)
    (Equiv_add (Equiv.refl _) (Equiv.trans
      (pairing_smul_right hw0 hw1 width (-1) xs zs stage) (negative_one_mul _)))

/-- The exact four-pairing squared-difference expansion; symmetry is not needed. -/
theorem pairing_difference_diagonal {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (xs ys : DistanceSpan) (stage : Nat) :
    Equiv (pairing hw0 hw1 width (difference xs ys) (difference xs ys) stage)
      (sub (sub (pairing hw0 hw1 width xs xs stage) (pairing hw0 hw1 width xs ys stage))
        (sub (pairing hw0 hw1 width ys xs stage) (pairing hw0 hw1 width ys ys stage))) :=
  Equiv.trans (pairing_difference_left hw0 hw1 width xs ys (difference xs ys) stage)
    (sub_congr (pairing_difference_right hw0 hw1 width xs xs ys stage)
      (pairing_difference_right hw0 hw1 width ys xs ys stage))

theorem pairing_difference_self_left {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (xs ys : DistanceSpan) (stage : Nat) :
    Equiv (pairing hw0 hw1 width (difference xs xs) ys stage) (ofQ' 0) :=
  Equiv.trans (pairing_difference_left hw0 hw1 width xs xs ys stage) (sub_self _)

theorem pairing_difference_self_right {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (xs ys : DistanceSpan) (stage : Nat) :
    Equiv (pairing hw0 hw1 width xs (difference ys ys) stage) (ofQ' 0) :=
  Equiv.trans (pairing_difference_right hw0 hw1 width xs ys ys stage) (sub_self _)

private theorem diagonal_reverse (a b c d : CReal) :
    Equiv (sub (sub a b) (sub c d)) (sub (sub d c) (sub b a)) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 2) (.neg (.var 3)))))
    (.add (.add (.var 3) (.neg (.var 2))) (.neg (.add (.var 1) (.neg (.var 0)))))
    (by decide)
    (fun
      | 0 => a.approx n
      | 1 => b.approx n
      | 2 => c.approx n
      | _ => d.approx n)

/-- Reversing a difference leaves its actual reflected diagonal unchanged. -/
theorem pairing_difference_reverse {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (xs ys : DistanceSpan) (stage : Nat) :
    Equiv (pairing hw0 hw1 width (difference xs ys) (difference xs ys) stage)
      (pairing hw0 hw1 width (difference ys xs) (difference ys xs) stage) :=
  Equiv.trans (pairing_difference_diagonal hw0 hw1 width xs ys stage)
    (Equiv.trans (diagonal_reverse _ _ _ _)
      (Equiv.symm (pairing_difference_diagonal hw0 hw1 width ys xs stage)))

private theorem midpoint_cancel (a b c : CReal) :
    Equiv (add (mul (ofQ' 2) b) (sub (sub a b) (sub b c))) (add a c) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.mul (.const 2) (.var 1))
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 1) (.neg (.var 2))))))
    (.add (.var 0) (.var 2)) (by decide)
    (fun
      | 0 => a.approx n
      | 1 => b.approx n
      | _ => c.approx n)

/-- Positivity of the SAME original reflected difference gives midpoint order.
This is the scalar input for a later time-balance/doubling contraction proof. -/
theorem pairing_midpoint_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (xs zs : DistanceSpan)
    (hxs : Physical width xs) (hzs : Physical width zs) (stage : Nat) :
    leEv (mul (ofQ' 2) (pairing hw0 hw1 width xs zs stage))
      (add (pairing hw0 hw1 width xs xs stage) (pairing hw0 hw1 width zs zs stage)) := by
  have hdiag := Equiv.trans (pairing_difference_diagonal hw0 hw1 width xs zs stage)
    (sub_congr (Equiv.refl _)
      (CReal.sub_congr_left (pairing_symm hw0 hw1 width zs xs hzs hxs stage)))
  have hpos := leEv_trans
    (pairing_self_nonnegative hw0 hw1 width (difference xs zs) (physical_difference hxs hzs) stage)
    (leEv_of_equiv hdiag)
  have hsum := leEv_add (leEv_refl (mul (ofQ' 2) (pairing hw0 hw1 width xs zs stage))) hpos
  have hzero : Equiv
      (add (mul (ofQ' 2) (pairing hw0 hw1 width xs zs stage)) (ofQ' 0))
      (mul (ofQ' 2) (pairing hw0 hw1 width xs zs stage)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => QPoly.q_add_zero_eqv _)
  exact leEv_trans (leEv_of_equiv (Equiv.symm hzero))
    (leEv_trans hsum (leEv_of_equiv (midpoint_cancel _ _ _)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference.difference
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference.physical_difference
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference.radius_difference
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference.pairing_difference_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference.pairing_difference_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference.pairing_difference_diagonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference.pairing_difference_self_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference.pairing_difference_self_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference.pairing_difference_reverse
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference.pairing_midpoint_bound
