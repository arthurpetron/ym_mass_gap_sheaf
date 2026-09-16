/-
# The original intrinsic reflected squared seminorm

The carrier consists of finite signed natural-distance presentations with
their actual physical spatial-face guards. Squared distance is exactly the
existing reflected pairing of their literal difference. Its triangle law
comes from reflected midpoint order, and zero-distance replacement comes
from the proved radical annihilation of the SAME pairing.

This constructs the existing explicit-modulus completion machinery's input,
not a replacement inner product. No physical time-shift bound, completed
inner product, transfer positivity, spectral gap or continuum claim is made.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference
import YMGap.Continuum.CRealSeminormCompletion

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference

/-- The face guard is retained on every original intrinsic presentation. -/
abbrev PhysicalSpan (width : Nat) := {xs : DistanceSpan // Physical width xs}

/-- The actual reflected diagonal of the signed difference, at fixed heat stage. -/
def distSq {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (x y : PhysicalSpan width) : CReal :=
  pairing hw0 hw1 width (difference x.val y.val) (difference x.val y.val) stage

private theorem sub_congr {a b c d : CReal} (ha : Equiv a b) (hc : Equiv c d) :
    Equiv (sub a c) (sub b d) :=
  Equiv_add ha (CReal.neg_congr hc)

private theorem sub_add_sub (a b c : CReal) :
    Equiv (add (sub a b) (sub b c)) (sub a c) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
    (.add (.var 0) (.neg (.var 2))) (by decide)
    (fun
      | 0 => a.approx n
      | 1 => b.approx n
      | _ => c.approx n)

/-- Consecutive differences telescope inside the original pairing, without
identifying their different finite-list presentations. -/
theorem pairing_difference_chain_left {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (xs ys zs ts : DistanceSpan) (stage : Nat) :
    Equiv (pairing hw0 hw1 width (difference xs ys ++ difference ys zs) ts stage)
      (pairing hw0 hw1 width (difference xs zs) ts stage) :=
  Equiv.trans (pairing_add_left hw0 hw1 width (difference xs ys) (difference ys zs) ts stage)
    (Equiv.trans (Equiv_add (pairing_difference_left hw0 hw1 width xs ys ts stage)
      (pairing_difference_left hw0 hw1 width ys zs ts stage))
      (Equiv.trans (sub_add_sub _ _ _)
        (Equiv.symm (pairing_difference_left hw0 hw1 width xs zs ts stage))))

private theorem sum_square_bound {a b c : CReal}
    (h : leEv (mul (ofQ' 2) b) (add a c)) :
    leEv (add (add a b) (add b c)) (add (add a a) (add c c)) := by
  have hleft : Equiv (add (add a b) (add b c))
      (add (mul (ofQ' 2) b) (add a c)) := by
    apply SumOfSquares.Equiv_of_approx_eqv
    intro n
    exact RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.add (.var 1) (.var 2)))
      (.add (.mul (.const 2) (.var 1)) (.add (.var 0) (.var 2))) (by decide)
      (fun
        | 0 => a.approx n
        | 1 => b.approx n
        | _ => c.approx n)
  have hright : Equiv (add (add a c) (add a c)) (add (add a a) (add c c)) := by
    apply SumOfSquares.Equiv_of_approx_eqv
    intro n
    exact RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
      (.add (.add (.var 0) (.var 0)) (.add (.var 1) (.var 1))) (by decide)
      (fun
        | 0 => a.approx n
        | _ => c.approx n)
  exact leEv_trans (leEv_of_equiv hleft)
    (leEv_trans (leEv_add h (leEv_refl (add a c))) (leEv_of_equiv hright))

/-- The sqrt-free sum bound is derived from the proved physical midpoint
inequality, not supplied as a seminorm premise. -/
theorem pairing_add_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (xs ys : DistanceSpan)
    (hx : Physical width xs) (hy : Physical width ys) (stage : Nat) :
    leEv (pairing hw0 hw1 width (xs++ys) (xs++ys) stage)
      (add (add (pairing hw0 hw1 width xs xs stage) (pairing hw0 hw1 width xs xs stage))
        (add (pairing hw0 hw1 width ys ys stage) (pairing hw0 hw1 width ys ys stage))) := by
  have hdiag := Equiv.trans (pairing_add_left hw0 hw1 width xs ys (xs++ys) stage)
    (Equiv_add (pairing_add_right hw0 hw1 width xs xs ys stage)
      (Equiv.trans (pairing_add_right hw0 hw1 width ys xs ys stage)
        (Equiv_add (pairing_symm hw0 hw1 width ys xs hy hx stage) (Equiv.refl _))))
  exact leEv_trans (leEv_of_equiv hdiag)
    (sum_square_bound (pairing_midpoint_bound hw0 hw1 width xs ys hx hy stage))

theorem distSq_refl {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (x : PhysicalSpan width) : Equiv (distSq hw0 hw1 width stage x x) czero :=
  pairing_difference_self_left hw0 hw1 width x.val (difference x.val x.val) stage

theorem distSq_symm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (x y : PhysicalSpan width) :
    Equiv (distSq hw0 hw1 width stage x y) (distSq hw0 hw1 width stage y x) :=
  pairing_difference_reverse hw0 hw1 width x.val y.val stage

theorem distSq_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (x y : PhysicalSpan width) : leEv czero (distSq hw0 hw1 width stage x y) :=
  pairing_self_nonnegative hw0 hw1 width (difference x.val y.val)
    (physical_difference x.property y.property) stage

theorem distSq_triangle {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (x y z : PhysicalSpan width) :
    leEv (distSq hw0 hw1 width stage x z)
      (add (add (distSq hw0 hw1 width stage x y) (distSq hw0 hw1 width stage x y))
        (add (distSq hw0 hw1 width stage y z) (distSq hw0 hw1 width stage y z))) := by
  let a := difference x.val y.val
  let b := difference y.val z.val
  let d := difference x.val z.val
  have ha : Physical width a := physical_difference x.property y.property
  have hb : Physical width b := physical_difference y.property z.property
  have hd : Physical width d := physical_difference x.property z.property
  have hpin : Equiv (pairing hw0 hw1 width (a++b) (a++b) stage)
      (pairing hw0 hw1 width d d stage) :=
    Equiv.trans (pairing_difference_chain_left hw0 hw1 width x.val y.val z.val (a++b) stage)
      (Equiv.trans (pairing_symm hw0 hw1 width d (a++b) hd (physical_append ha hb) stage)
        (pairing_difference_chain_left hw0 hw1 width x.val y.val z.val d stage))
  exact leEv_trans (leEv_of_equiv (Equiv.symm hpin))
    (pairing_add_bound hw0 hw1 width a b ha hb stage)

private theorem equiv_of_sub_zero {a b : CReal} (h : Equiv (sub a b) czero) : Equiv a b := by
  have hcancel : Equiv (add (sub a b) b) a :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.sub_add_cancel_eqv (a.approx n) (b.approx n))
  have hzero : Equiv (add czero b) b :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_of_eq (Q'.zero_add' (b.approx n)))
  exact Equiv.trans (Equiv.symm hcancel) (Equiv.trans (Equiv_add h (Equiv.refl b)) hzero)

/-- A null original difference has zero pairing with every physical span. -/
theorem pairing_null_left {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) {x x' : PhysicalSpan width}
    (hx : Equiv (distSq hw0 hw1 width stage x x') czero) (y : PhysicalSpan width) :
    Equiv (pairing hw0 hw1 width x.val y.val stage) (pairing hw0 hw1 width x'.val y.val stage) := by
  have hz := pairing_radical_zero hw0 hw1 width (difference x.val x'.val) y.val
    (physical_difference x.property x'.property) y.property stage hx
  exact equiv_of_sub_zero (Equiv.trans
    (Equiv.symm (pairing_difference_left hw0 hw1 width x.val x'.val y.val stage)) hz)

theorem pairing_null_congr {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) {x x' y y' : PhysicalSpan width}
    (hx : Equiv (distSq hw0 hw1 width stage x x') czero)
    (hy : Equiv (distSq hw0 hw1 width stage y y') czero) :
    Equiv (pairing hw0 hw1 width x.val y.val stage) (pairing hw0 hw1 width x'.val y'.val stage) :=
  Equiv.trans (pairing_null_left hw0 hw1 width stage hx y)
    (Equiv.trans (pairing_symm hw0 hw1 width x'.val y.val x'.property y.property stage)
      (Equiv.trans (pairing_null_left hw0 hw1 width stage hy x')
        (pairing_symm hw0 hw1 width y'.val x'.val y'.property x'.property stage)))

/-- Zero-distance replacement preserves the SAME distance representative up
to constructive-real equivalence, by the actual radical theorem. -/
theorem distSq_null_congr {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) {x x' y y' : PhysicalSpan width}
    (hx : Equiv (distSq hw0 hw1 width stage x x') czero)
    (hy : Equiv (distSq hw0 hw1 width stage y y') czero) :
    Equiv (distSq hw0 hw1 width stage x y) (distSq hw0 hw1 width stage x' y') :=
  Equiv.trans (pairing_difference_diagonal hw0 hw1 width x.val y.val stage)
    (Equiv.trans
      (sub_congr
        (sub_congr (pairing_null_congr hw0 hw1 width stage hx hx)
          (pairing_null_congr hw0 hw1 width stage hx hy))
        (sub_congr (pairing_null_congr hw0 hw1 width stage hy hx)
          (pairing_null_congr hw0 hw1 width stage hy hy)))
      (Equiv.symm (pairing_difference_diagonal hw0 hw1 width x'.val y'.val stage)))

/-- All squared-seminorm fields are proved for the original reflected form. -/
def seminorm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) : SquaredSeminorm where
  Carrier := PhysicalSpan width
  distSq := distSq hw0 hw1 width stage
  distSq_refl := distSq_refl hw0 hw1 width stage
  distSq_symm := distSq_symm hw0 hw1 width stage
  distSq_nonneg := distSq_nonnegative hw0 hw1 width stage
  distSq_triangle := distSq_triangle hw0 hw1 width stage
  null_congr := distSq_null_congr hw0 hw1 width stage

end YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm.PhysicalSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm.distSq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm.pairing_difference_chain_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm.pairing_add_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm.distSq_refl
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm.distSq_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm.distSq_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm.distSq_triangle
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm.pairing_null_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm.pairing_null_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm.distSq_null_congr
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm.seminorm
