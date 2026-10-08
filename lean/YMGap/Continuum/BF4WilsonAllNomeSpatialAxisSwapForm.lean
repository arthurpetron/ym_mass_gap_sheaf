/-
# SAME-width original reflected forms under the spatial axis swap

The literal finite Wilson-window swap identity passes to the already chosen
original joint limit. Radius tags, temporal charts and time advances are
preserved, and so are the existing common, intrinsic and odd bond forms.
Every ordered loop, spin and signed term remains in the original action.

This is the finite-source reflected-form isometry at fixed width and nome.
It does not construct a completed spatial operator, continuous rotations,
spatial scaling, continuum covariance or a physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabSpatialAxisSwapWilsonWindow
import YMGap.Continuum.BF4WilsonAllNomeBondOSRealization

namespace YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
  (originalJointLimit originalJoint_diagonal_converges)
open YMGap.Continuum.BF4ExactSlabSpatialAxisSwapWilsonWindow
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (commonForm intrinsicForm)
open YMGap.Continuum.BF4WilsonAllNomeBondReflectedForm (crossOdd crossOdd_within)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization (bondForm)

/-- The SAME original diagonal sequence, not a newly chosen limit. -/
theorem originalJointLimit_swap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}
    (L : Nat) (e : WindowExpression width) (he : Within L e) :
    Equiv (originalJointLimit hw0 hw1 L (swapExpression e) ((within_swap e).mpr he))
      (originalJointLimit hw0 hw1 L e he) :=
  Equiv_of_limit_of_equal
    (fun stage => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      originalWindowScalar_swap hw0 hw1 L e stage stage stage))
    (originalJoint_diagonal_converges hw0 hw1 L (swapExpression e)
      ((within_swap e).mpr he))
    (originalJoint_diagonal_converges hw0 hw1 L e he)

/-- The spatial swap does not alter distance from the temporal plane. -/
def swapIntrinsic {width : Nat} (x : IntrinsicExpression width) :
    IntrinsicExpression width where
  radius := x.radius
  expression := swapExpression x.expression
  within := (within_swap x.expression).mpr x.within

theorem swapIntrinsic_radius {width : Nat} (x : IntrinsicExpression width) :
    (swapIntrinsic x).radius = x.radius := rfl

theorem swapIntrinsic_expression {width : Nat} (x : IntrinsicExpression width) :
    (swapIntrinsic x).expression = swapExpression x.expression := rfl

/-- Exact syntax, including offsets even before a semantic chart guard. -/
theorem swap_chart {width : Nat} (H : Nat) (x : IntrinsicExpression width) :
    swapExpression (chart H x) = chart H (swapIntrinsic x) :=
  swap_mapOffsets _ x.expression

theorem swap_advance {width : Nat} (n : Nat) (x : IntrinsicExpression width) :
    swapIntrinsic (advance n x) = advance n (swapIntrinsic x) := rfl

/-- Both operands move on the SAME original doubled window. -/
theorem commonForm_swap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}
    (H : Nat) (e f : WindowExpression width) (he : Within H e) (hf : Within H f) :
    Equiv (commonForm hw0 hw1 H (swapExpression e) (swapExpression f)
      ((within_swap e).mpr he) ((within_swap f).mpr hf))
      (commonForm hw0 hw1 H e f he hf) := by
  have h := originalJointLimit_swap hw0 hw1 (2*H) (.mul (mirror H e) f)
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) f hf⟩
  simpa only [commonForm, swapExpression, swap_mirror] using h

/-- Isometry of the existing all-nome intrinsic reflected form. -/
theorem intrinsicForm_swap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}
    (x y : IntrinsicExpression width) :
    Equiv (intrinsicForm hw0 hw1 (swapIntrinsic x) (swapIntrinsic y))
      (intrinsicForm hw0 hw1 x y) := by
  have h := commonForm_swap hw0 hw1 (max x.radius y.radius)
    (chart (max x.radius y.radius) x) (chart (max x.radius y.radius) y)
    (BF4ExactSlabFixedSpatialWilsonIntrinsicForm.chart_within _ x
      (Nat.le_max_left _ _))
    (BF4ExactSlabFixedSpatialWilsonIntrinsicForm.chart_within _ y
      (Nat.le_max_right _ _))
  simpa only [intrinsicForm, swapIntrinsic_radius, swap_chart] using h

/-- Literal odd reflected source, with its one-sided time advance unchanged. -/
theorem swap_crossOdd {width : Nat} (x y : IntrinsicExpression width) :
    swapExpression (crossOdd x y) = crossOdd (swapIntrinsic x) (swapIntrinsic y) := by
  change WindowExpression.mul
      (swapExpression (mirror (max x.radius y.radius+1)
        (chart (max x.radius y.radius+1) x)))
      (swapExpression (chart (max x.radius y.radius+1) (advance 1 y))) =
    WindowExpression.mul
      (mirror (max x.radius y.radius+1)
        (chart (max x.radius y.radius+1) (swapIntrinsic x)))
      (chart (max x.radius y.radius+1) (advance 1 (swapIntrinsic y)))
  rw [swap_mirror, swap_chart, swap_chart, swap_advance]

/-- Equality in the existing real quotient of the ORIGINAL bond form.
No spatial operator or new physical pairing is declared. -/
theorem bondForm_swap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}
    (x y : IntrinsicExpression width) :
    bondForm hw0 hw1 (swapIntrinsic x) (swapIntrinsic y) = bondForm hw0 hw1 x y := by
  apply Quotient.sound
  have h := originalJointLimit_swap hw0 hw1 (2*(max x.radius y.radius)+1)
    (crossOdd x y) (crossOdd_within x y)
  simpa only [bondForm, swapIntrinsic_radius, swap_crossOdd] using h

end YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapForm

#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapForm.originalJointLimit_swap
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapForm.swapIntrinsic
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapForm.swapIntrinsic_radius
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapForm.swapIntrinsic_expression
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapForm.swap_chart
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapForm.swap_advance
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapForm.commonForm_swap
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapForm.intrinsicForm_swap
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapForm.swap_crossOdd
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapForm.bondForm_swap
