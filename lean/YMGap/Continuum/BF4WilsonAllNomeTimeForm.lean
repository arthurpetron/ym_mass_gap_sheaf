/-
# All-nome time balance on the literal-width Wilson form

The existing intrinsic time advance is balanced directly in the fixed-width
all-nome reflected form.  The proof uses the literal mixed-window identity
and padding/stationarity of the same original joint limit; no small-nome
spatial limit or replacement completion is introduced.  The odd-window
certificate also gives positivity of the actual one-step quadratic.

This supplies form laws only.  It does not construct a bounded completed time
operator, a contraction, a strict rate, or a changing-spacing limit.
-/

import YMGap.Continuum.BF4WilsonAllNomeReflectedForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimePositive

namespace YMGap.Continuum.BF4WilsonAllNomeTimeForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
  (originalJointLimit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart chart_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
  (advance mixed_advance mixed_advance_source_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow
  (oddPair oddPair_within oneStep_chart_source)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimePositive
  (originalJoint_odd_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity
  (originalJoint_padding originalJoint_shift_within_window)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm

attribute [local irreducible] originalJointLimit

/-- Both operands and their total-time product retain the same original
fixed-width action. -/
theorem intrinsicForm_time_sum {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (m n : Nat) (x y : IntrinsicExpression width) :
    Equiv (intrinsicForm hw0 hw1 (advance m x) (advance n y))
      (intrinsicForm hw0 hw1 x (advance (m+n) y)) := by
  let H := x.radius+y.radius+m+n
  have hx : x.radius+m ≤ H := by omega
  have hy : y.radius+(m+n) ≤ H := by omega
  have hx0 : x.radius ≤ H := by omega
  have hyn : y.radius+n ≤ H := by omega
  have hl := intrinsicForm_chart hw0 hw1
    (advance m x) (advance n y) H hx hyn
  have hr := intrinsicForm_chart hw0 hw1
    x (advance (m+n) y) H hx0 hy
  have ht := originalJoint_shift_within_window hw0 hw1 (2*H-m) (2*H) m
    (.mul (mirror H (chart H x)) (chart H (advance (m+n) y)))
    (mixed_advance_source_within H m n x y hx hy) (by omega)
  have hform : Equiv
      (commonForm hw0 hw1 H (chart H (advance m x)) (chart H (advance n y))
        (chart_within H (advance m x) hx) (chart_within H (advance n y) hyn))
      (commonForm hw0 hw1 H (chart H x) (chart H (advance (m+n) y))
        (chart_within H x hx0) (chart_within H (advance (m+n) y) hy)) := by
    simpa only [commonForm, mixed_advance H m n x y hx hy] using ht
  exact hl.trans (hform.trans hr.symm)

theorem intrinsicForm_time_balance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (n : Nat) (x y : IntrinsicExpression width) :
    Equiv (intrinsicForm hw0 hw1 (advance n x) y) (intrinsicForm hw0 hw1 x (advance n y)) := by
  simpa only [BF4ExactSlabFixedSpatialWilsonPhysicalTime.advance_zero, Nat.add_zero] using
    intrinsicForm_time_sum hw0 hw1 n 0 x y

/-- The one-step all-nome form is exactly the already-positive odd original
joint window, after one harmless unit of exterior padding. -/
theorem intrinsicForm_oneStep_oddPair {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (x : IntrinsicExpression width) :
    Equiv (intrinsicForm hw0 hw1 x (advance 1 x))
      (originalJointLimit hw0 hw1 (2*x.radius+1)
        (oddPair x.radius x.expression) (oddPair_within x.radius x.expression x.within)) := by
  let H := x.radius+1
  have hx : x.radius ≤ H := by omega
  have hxa : (advance 1 x).radius ≤ H := by change x.radius+1 ≤ H; exact Nat.le_refl _
  have hc := intrinsicForm_chart hw0 hw1 x (advance 1 x) H hx hxa
  have hp := originalJoint_padding hw0 hw1 (2*x.radius+1) 0 1
    (oddPair x.radius x.expression) (oddPair_within x.radius x.expression x.within)
  have hcommon : Equiv
      (commonForm hw0 hw1 H (chart H x) (chart H (advance 1 x))
        (chart_within H x hx) (chart_within H (advance 1 x) hxa))
      (originalJointLimit hw0 hw1 (2*x.radius+1)
        (oddPair x.radius x.expression) (oddPair_within x.radius x.expression x.within)) := by
    simpa only [commonForm, H, oneStep_chart_source x,
      show 2*H = (2*x.radius+1)+0+1 by omega, shift_zero] using hp
  exact hc.trans hcommon

/-- Positivity of the actual one-step quadratic at every strict nome. -/
theorem intrinsicForm_oneStep_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (x : IntrinsicExpression width) :
    leEv (ofQ' 0) (intrinsicForm hw0 hw1 x (advance 1 x)) :=
  leEv_trans (originalJoint_odd_nonnegative hw0 hw1 x.radius x.expression x.within)
    (leEv_of_equiv (intrinsicForm_oneStep_oddPair hw0 hw1 x).symm)

#print axioms intrinsicForm_time_sum
#print axioms intrinsicForm_time_balance
#print axioms intrinsicForm_oneStep_oddPair
#print axioms intrinsicForm_oneStep_nonnegative

end YMGap.Continuum.BF4WilsonAllNomeTimeForm
