/-
# Same-object original-time balance on the intrinsic Wilson form

The finite mixed-product identity is passed through original-action window
stationarity at one explicit common horizon. This proves sum-of-times for
the already constructed reflected form, with no operator law supplied as a
hypothesis. Reflection positivity of the literal difference then gives the
midpoint estimate used by the separate bounded-doubling contraction proof.

The radius-tagged unit is fixed in the actual seminorm, not literally as an
expression. These results concern the existing small-nome SU(2) fixed-spacing
limit. A strict vacuum-complement bound and continuum QFT remain open.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity
import YMGap.Constructive.CRealAlg

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

private theorem sub_congr {a b c d : CReal} (ha : Equiv a b) (hc : Equiv c d) :
    Equiv (sub a c) (sub b d) := Equiv_add ha (neg_congr hc)

private theorem midpoint_cancel (a b c : CReal) :
    Equiv (add (mul (ofQ' 2) b) (sub (sub a b) (sub b c))) (add a c) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.mul (.const 2) (.var 1))
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 1) (.neg (.var 2))))))
    (.add (.var 0) (.var 2)) (by decide)
    (fun | 0 => a.approx n | 1 => b.approx n | _ => c.approx n)

attribute [local irreducible] intrinsicForm

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base)

local notation "F" => intrinsicForm hw0 hw1 hsmall hd hs hb
local notation "u" => unit base

/-- Both operands and their total-time product use the SAME original action. -/
theorem intrinsicForm_time_sum (m n : Nat) (x y : IntrinsicExpression base) :
    Equiv (F (advance m x) (advance n y)) (F x (advance (m+n) y)) := by
  let H := x.radius+y.radius+m+n
  have hx : x.radius+m ≤ H := by omega
  have hy : y.radius+(m+n) ≤ H := by omega
  have hx0 : x.radius ≤ H := by omega
  have hyn : y.radius+n ≤ H := by omega
  have hm : m ≤ 2*H := by omega
  have hl := intrinsicForm_chart hw0 hw1 hsmall hd hs hb
    (advance m x) (advance n y) H hx hyn
  have hr := intrinsicForm_chart hw0 hw1 hsmall hd hs hb
    x (advance (m+n) y) H hx0 hy
  have ht := spatialLimit_shift_within hw0 hw1 hsmall hd hs hb H (2*H-m) m
    (.mul (mirror H (chart H x)) (chart H (advance (m+n) y)))
    (mixed_advance_source_within H m n x y hx hy) (by omega)
  have hform : Equiv
      (form hw0 hw1 hsmall hd hs hb H (chart H (advance m x)) (chart H (advance n y))
        (chart_within H (advance m x) hx) (chart_within H (advance n y) hyn))
      (form hw0 hw1 hsmall hd hs hb H (chart H x) (chart H (advance (m+n) y))
        (chart_within H x hx0) (chart_within H (advance (m+n) y) hy)) := by
    simpa only [form, mixed_advance H m n x y hx hy] using ht
  exact hl.trans (hform.trans hr.symm)

theorem intrinsicForm_time_balance (n : Nat) (x y : IntrinsicExpression base) :
    Equiv (F (advance n x) y) (F x (advance n y)) := by
  simpa only [advance_zero, Nat.add_zero] using
    intrinsicForm_time_sum hw0 hw1 hsmall hd hs hb n 0 x y

/-- Positivity of an actual signed difference, not an assumed norm inequality. -/
theorem intrinsicForm_midpoint_bound (x y : IntrinsicExpression base) :
    leEv (mul (ofQ' 2) (F x y)) (add (F x x) (F y y)) := by
  have hdiag := (intrinsicForm_difference_diagonal hw0 hw1 hsmall hd hs hb x y).trans
    (sub_congr (Equiv.refl _)
      (sub_congr (intrinsicForm_symm hw0 hw1 hsmall hd hs hb y x) (Equiv.refl _)))
  have hp := leEv_trans (intrinsicForm_nonnegative hw0 hw1 hsmall hd hs hb (difference x y))
    (leEv_of_equiv hdiag)
  have hsum := leEv_add (leEv_refl (mul (ofQ' 2) (F x y))) hp
  have hz : Equiv (add (mul (ofQ' 2) (F x y)) (ofQ' 0)) (mul (ofQ' 2) (F x y)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => QPoly.q_add_zero_eqv _)
  exact leEv_trans (leEv_of_equiv hz.symm)
    (leEv_trans hsum (leEv_of_equiv (midpoint_cancel _ _ _)))

/-- Equality of the literal unit charts removes its changed radius tag. -/
theorem intrinsicForm_advanced_unit_right (n : Nat) (x : IntrinsicExpression base) :
    Equiv (F x (advance n u)) (F x u) := by
  let H := x.radius+n
  have hx : x.radius ≤ H := by omega
  have hun : (advance n u).radius ≤ H := by change 0+n ≤ H; omega
  have hu : (unit base).radius ≤ H := Nat.zero_le _
  have hl := intrinsicForm_chart hw0 hw1 hsmall hd hs hb x (advance n u) H hx hun
  have hr := intrinsicForm_chart hw0 hw1 hsmall hd hs hb x u H hx hu
  exact hl.trans (by simpa only [chart_advance_unit, chart_unit] using hr.symm)

theorem intrinsicForm_advanced_unit_left (n : Nat) (x : IntrinsicExpression base) :
    Equiv (F (advance n u) x) (F u x) :=
  (intrinsicForm_symm hw0 hw1 hsmall hd hs hb (advance n u) x).trans
    ((intrinsicForm_advanced_unit_right hw0 hw1 hsmall hd hs hb n x).trans
      (intrinsicForm_symm hw0 hw1 hsmall hd hs hb x u))

theorem intrinsicForm_unit_invariant (n : Nat) (x : IntrinsicExpression base) :
    Equiv (F (advance n x) u) (F x u) :=
  (intrinsicForm_time_balance hw0 hw1 hsmall hd hs hb n x u).trans
    (intrinsicForm_advanced_unit_right hw0 hw1 hsmall hd hs hb n x)

/-- The advanced unit is the SAME completion class although its radius differs. -/
theorem advance_unit_null (n : Nat) :
    (seminorm hw0 hw1 hsmall hd hs hb).Null (advance n u) u := by
  change Equiv (distSq hw0 hw1 hsmall hd hs hb (advance n u) u) czero
  have haa := (intrinsicForm_advanced_unit_left hw0 hw1 hsmall hd hs hb n (advance n u)).trans
    (intrinsicForm_advanced_unit_right hw0 hw1 hsmall hd hs hb n u)
  have hau := intrinsicForm_advanced_unit_left hw0 hw1 hsmall hd hs hb n u
  have hua := intrinsicForm_advanced_unit_right hw0 hw1 hsmall hd hs hb n u
  exact (distSq_diagonal hw0 hw1 hsmall hd hs hb (advance n u) u).trans
    ((sub_congr (sub_congr haa hau) (sub_congr hua (Equiv.refl _))).trans
      (sub_self_eqv_zero _))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm.intrinsicForm_time_sum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm.intrinsicForm_time_balance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm.intrinsicForm_midpoint_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm.intrinsicForm_advanced_unit_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm.intrinsicForm_advanced_unit_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm.intrinsicForm_unit_invariant
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm.advance_unit_null
