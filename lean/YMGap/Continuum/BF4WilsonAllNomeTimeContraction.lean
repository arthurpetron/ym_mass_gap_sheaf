/-
# Literal-width all-nome Wilson time contraction

The actual original finite expectations have a placement-independent interval
cap.  Passing that cap through the witnessed joint Cauchy sequence bounds every
time translate of the literal-width all-nome reflected form.  Exact time
balance and reflection positivity then give the midpoint-doubling argument and
nonexpansiveness of physical time on the same intrinsic Wilson carrier.

This is a fixed-nome, fixed-width statement.  It does not assert a strict gap,
continuum scaling, or an identification with the separate face-span carrier.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeForm
import YMGap.Continuum.BF4WilsonAllNomeSeminorm
import YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds
import YMGap.Continuum.BoundedMidpointDoublingEventual

namespace YMGap.Continuum.BF4WilsonAllNomeTimeContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabSpatialWilsonControl
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart chart_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
  (difference)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
open YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
open YMGap.Continuum.BF4WilsonAllNomeFormLaws
open YMGap.Continuum.BF4WilsonAllNomeSeminorm
open YMGap.Continuum.BF4WilsonAllNomeTimeForm

/-- A purely algebraic cap on an intrinsic expression.  It contains no radius,
time, cutoff, or nome. -/
def intrinsicCap {width : Nat} (x : IntrinsicExpression width) : Q' :=
  windowCap x.expression

theorem intrinsicCap_nonnegative {width : Nat} (x : IntrinsicExpression width) :
    (0 : Q') ≤ intrinsicCap x :=
  (placed_interval (Nat.le_add_right width x.radius)
    (by omega : 0+x.radius ≤ width+x.radius) x.expression x.within).nonnegative

theorem chart_cap {width : Nat} (H : Nat) (x : IntrinsicExpression width) :
    windowCap (chart H x) = intrinsicCap x :=
  windowCap_mapOffsets (fun offset => offset+(H-x.radius)) x.expression

theorem intrinsicCap_advance {width : Nat} (n : Nat) (x : IntrinsicExpression width) :
    intrinsicCap (advance n x) = intrinsicCap x := rfl

/-- Every actual finite scalar used by the joint limit retains the interval cap. -/
theorem originalWindowScalar_abs_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (he : Within L e)
    (stage m n : Nat) :
    Q'.abs (originalWindowScalar hw0 hw1 L e stage m n) ≤ windowCap e := by
  unfold originalWindowScalar
  exact finiteValue_abs_bound w hw0 hw1 _ _ _ _ _
    (placed_interval (Nat.le_add_right _ _) (by omega) e he) stage

/-- The cap holds at every canonical approximation of the actual joint limit. -/
theorem originalJointLimit_approx_abs_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : Nat) (e : WindowExpression width) (he : Within L e)
    (k : Nat) :
    Q'.abs ((originalJointLimit hw0 hw1 L e he).approx k) ≤ windowCap e := by
  let c := originalJointCauchy hw0 hw1 L e he
  exact originalWindowScalar_abs_bound hw0 hw1 L e he
    (QMhat _ c k) (QMhat _ c k) (QMhat _ c k)

attribute [local irreducible] intrinsicForm

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

local notation "F" => intrinsicForm hw0 hw1
local notation "D" => distSq hw0 hw1

/-- Each intrinsic operand contributes only its expression cap. -/
theorem intrinsicForm_approx_abs_bound {width : Nat}
    (x y : IntrinsicExpression width) (k : Nat) :
    Q'.abs ((F x y).approx k) ≤ intrinsicCap x*intrinsicCap y := by
  let H := max x.radius y.radius
  have h := originalJointLimit_approx_abs_bound hw0 hw1 (2*H)
    (.mul (mirror H (chart H x)) (chart H y))
    ⟨mirror_within H (chart H x), within_mono (by omega : H ≤ 2*H) _
      (chart_within H y (Nat.le_max_right _ _))⟩ k
  unfold intrinsicForm commonForm
  simpa only [windowCap, windowCap_mirror, chart_cap] using h

theorem intrinsicForm_upper_bound {width : Nat} (x y : IntrinsicExpression width) :
    leEv (F x y) (ofQ' (intrinsicCap x*intrinsicCap y)) :=
  leEv_le_ofQ'_of_approx_le (fun k =>
    Q'.le_trans' _ _ _ (Q'.le_abs_self _) (intrinsicForm_approx_abs_bound hw0 hw1 x y k))

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

/-- Positivity of the literal difference gives the midpoint inequality. -/
theorem intrinsicForm_midpoint_bound {width : Nat} (x y : IntrinsicExpression width) :
    leEv (mul (ofQ' 2) (F x y)) (add (F x x) (F y y)) := by
  have hdiag := (intrinsicForm_difference_diagonal hw0 hw1 x y).trans
    (sub_congr (Equiv.refl _)
      (sub_congr (intrinsicForm_symm hw0 hw1 y x) (Equiv.refl _)))
  have hp := leEv_trans (intrinsicForm_nonnegative hw0 hw1 (difference x y))
    (leEv_of_equiv hdiag)
  have hsum := leEv_add (leEv_refl (mul (ofQ' 2) (F x y))) hp
  have hz : Equiv (add (mul (ofQ' 2) (F x y)) (ofQ' 0)) (mul (ofQ' 2) (F x y)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => QPoly.q_add_zero_eqv _)
  exact leEv_trans (leEv_of_equiv hz.symm)
    (leEv_trans hsum (leEv_of_equiv (midpoint_cancel _ _ _)))

/-- Diagonal form along the actual physical-time orbit. -/
def timeNorm {width : Nat} (n : Nat) (x : IntrinsicExpression width) : CReal :=
  F (advance n x) (advance n x)

theorem timeNorm_nonnegative {width : Nat} (n : Nat) (x : IntrinsicExpression width) :
    leEv (ofQ' 0) (timeNorm hw0 hw1 n x) :=
  intrinsicForm_nonnegative hw0 hw1 (advance n x)

theorem timeNorm_bounded {width : Nat} (n : Nat) (x : IntrinsicExpression width) :
    leEv (timeNorm hw0 hw1 n x) (ofQ' (intrinsicCap x*intrinsicCap x)) := by
  simpa only [timeNorm, intrinsicCap_advance] using
    intrinsicForm_upper_bound hw0 hw1 (advance n x) (advance n x)

theorem timeNorm_midpoint {width : Nat} (n : Nat) (x : IntrinsicExpression width) :
    leEv (mul (ofQ' 2) (timeNorm hw0 hw1 n x))
      (add (timeNorm hw0 hw1 0 x) (timeNorm hw0 hw1 (2*n) x)) := by
  have hm : Equiv (timeNorm hw0 hw1 n x) (F x (advance (2*n) x)) := by
    simpa only [timeNorm, Nat.two_mul] using
      intrinsicForm_time_sum hw0 hw1 n n x x
  have hmid := intrinsicForm_midpoint_bound hw0 hw1 x (advance (2*n) x)
  exact leEv_trans (leEv_of_equiv (TrigSignedAdd.mul_congr_right hm))
    (by simpa only [timeNorm, advance_zero] using hmid)

theorem timeNorm_le_anchor {width : Nat} (n : Nat) (x : IntrinsicExpression width) :
    leEv (timeNorm hw0 hw1 n x) (timeNorm hw0 hw1 0 x) :=
  BoundedMidpointDoublingEventual.bounded_midpointDoubling_leEv_anchor
    (fun k => timeNorm hw0 hw1 k x) (intrinsicCap x*intrinsicCap x)
    (fun k => timeNorm_bounded hw0 hw1 k x)
    (timeNorm_nonnegative hw0 hw1 0 x)
    (fun k => timeNorm_midpoint hw0 hw1 k x) n

/-- Actual physical time is nonexpansive for the literal-width all-nome form. -/
theorem intrinsicForm_advance_contraction {width : Nat}
    (n : Nat) (x : IntrinsicExpression width) :
    leEv (F (advance n x) (advance n x)) (F x x) := by
  simpa only [timeNorm, advance_zero] using timeNorm_le_anchor hw0 hw1 n x

/-- Squared-distance contraction on the same intrinsic Wilson carrier. -/
theorem distSq_advance_contraction {width : Nat}
    (n : Nat) (x y : IntrinsicExpression width) :
    leEv (D (advance n x) (advance n y)) (D x y) := by
  simpa only [distSq, advance_difference] using
    intrinsicForm_advance_contraction hw0 hw1 n (difference x y)

end YMGap.Continuum.BF4WilsonAllNomeTimeContraction

#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeContraction.intrinsicCap
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeContraction.originalWindowScalar_abs_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeContraction.originalJointLimit_approx_abs_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeContraction.intrinsicForm_upper_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeContraction.intrinsicForm_midpoint_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeContraction.timeNorm_le_anchor
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeContraction.intrinsicForm_advance_contraction
#print axioms YMGap.Continuum.BF4WilsonAllNomeTimeContraction.distSq_advance_contraction
