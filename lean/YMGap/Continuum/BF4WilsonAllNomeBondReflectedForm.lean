/-
# The mixed original bond-reflected Wilson form

Two signed intrinsic expressions are placed in one common chart. Their
one-step reflected product fits in the balanced odd window, and the original
joint-limit padding theorem identifies its limit with the already constructed
one-step time form. This is a fixed-width, fixed-nome physical window pin,
not a new carrier, an ambient-kernel quotient, or a continuum OS root.
-/

import YMGap.Continuum.BF4WilsonAllNomeCompletedTime
import YMGap.Continuum.BF4WilsonAllNomeTimeForm

namespace YMGap.Continuum.BF4WilsonAllNomeBondReflectedForm

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
  (advance mirror_chart_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow
  (oddPair oneStep_chart_source)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity
  (originalJoint_padding)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
  (intrinsicForm intrinsicForm_chart commonForm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (embed completedInner completedInner_embed)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedTime_embed)

/-- The actual signed cross-source across one bond. The upper operand comes
first, as in the original reflected form. The common radius retains the
source support of both operands rather than choosing a new observable. -/
def crossOdd {width : Nat} (x y : IntrinsicExpression width) :
    WindowExpression width :=
  let R := max x.radius y.radius
  .mul (mirror (R+1) (chart (R+1) x))
    (chart (R+1) (advance 1 y))

/-- The central bond separates the upper reflected copy from the lower copy.
The original source fits in `2*R+1`, one slice shorter than its chart. -/
theorem crossOdd_within {width : Nat} (x y : IntrinsicExpression width) :
    Within (2*(max x.radius y.radius)+1) (crossOdd x y) := by
  let R := max x.radius y.radius
  have hx : x.radius ≤ R := Nat.le_max_left _ _
  have hy : y.radius ≤ R := Nat.le_max_right _ _
  change Within (2*R+1)
    (.mul (mirror (R+1) (chart (R+1) x))
      (chart (R+1) (advance 1 y)))
  constructor
  · exact within_mono (by omega : R+1+x.radius ≤ 2*R+1) _
      (mirror_chart_within (R+1) x)
  · exact within_mono (by omega : R+1 ≤ 2*R+1) _
      (chart_within (R+1) (advance 1 y) (by change y.radius+1 ≤ R+1; omega))

/-- The mixed bond source is pinned to the SAME original joint limit.
Padding is used at the limit, not as a false finite symmetric-depth identity. -/
theorem crossOdd_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (x y : IntrinsicExpression width) :
    Equiv (intrinsicForm hw0 hw1 x (advance 1 y))
      (originalJointLimit hw0 hw1 (2*(max x.radius y.radius)+1)
        (crossOdd x y) (crossOdd_within x y)) := by
  let R := max x.radius y.radius
  have hx : x.radius ≤ R+1 := by dsimp [R]; omega
  have hy : (advance 1 y).radius ≤ R+1 := by
    change y.radius+1 ≤ R+1
    dsimp [R]
    omega
  have hc := intrinsicForm_chart hw0 hw1 x (advance 1 y) (R+1) hx hy
  have hp := originalJoint_padding hw0 hw1 (2*R+1) 0 1
    (crossOdd x y) (crossOdd_within x y)
  have hcommon : Equiv
      (commonForm hw0 hw1 (R+1) (chart (R+1) x)
        (chart (R+1) (advance 1 y))
        (chart_within (R+1) x hx)
        (chart_within (R+1) (advance 1 y) hy))
      (originalJointLimit hw0 hw1 (2*R+1)
        (crossOdd x y) (crossOdd_within x y)) := by
    simpa only [commonForm, crossOdd,
      show 2*(R+1)=(2*R+1)+0+1 by omega, shift_zero] using hp
  exact hc.trans hcommon

/-- On the diagonal this source is exactly the established odd pair, with no
change of Wilson word order or signed coefficients. -/
theorem crossOdd_self {width : Nat} (x : IntrinsicExpression width) :
    crossOdd x x = oddPair x.radius x.expression := by
  simpa only [crossOdd, Nat.max_self] using oneStep_chart_source x

/-- Dense completed Gram pin for the original one-step bond reflection. -/
theorem completed_crossOdd_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (x y : IntrinsicExpression width) :
    completedInner hw0 hw1 (embed hw0 hw1 x)
      (completedTime hw0 hw1 1 (embed hw0 hw1 y)) =
      Quotient.mk crealSetoid
        (originalJointLimit hw0 hw1 (2*(max x.radius y.radius)+1)
          (crossOdd x y) (crossOdd_within x y)) := by
  rw [completedTime_embed, completedInner_embed]
  exact Quotient.sound (crossOdd_pin hw0 hw1 x y)

#print axioms crossOdd
#print axioms crossOdd_within
#print axioms crossOdd_pin
#print axioms crossOdd_self
#print axioms completed_crossOdd_pin

end YMGap.Continuum.BF4WilsonAllNomeBondReflectedForm
