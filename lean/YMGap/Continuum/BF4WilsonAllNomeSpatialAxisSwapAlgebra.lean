/-
# Constructive spatial-swap algebra on the SAME all-nome carrier

The concrete loop swap is involutive. Its intrinsic action preserves the
actual common-radius sum/difference syntax, rational scaling and the unit.
The checked original reflected-form identity therefore gives equality of
the existing squared distances and a nonexpansive map on that seminorm.
No new form, physical carrier, completed operator or continuum action is
declared here.
-/

import YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapForm

namespace YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry
open YMGap.Continuum.BF4ExactSlabSpatialAxisSwapWilsonLoop
open YMGap.Continuum.BF4ExactSlabSpatialAxisSwapWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (WindowExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
  (sum difference)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra
  (smul zero)
open YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapForm
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (distSq seminorm)

private theorem sourceLoop_ext {width : Nat} (x y : SourceLoop width)
    (hs : x.start = y.start) (he : x.edges = y.edges) : x = y := by
  cases x
  cases y
  cases hs
  cases he
  rfl

theorem swapSourceLoop_involutive {width : Nat} (loop : SourceLoop width) :
    swapSourceLoop (swapSourceLoop loop) = loop := by
  apply sourceLoop_ext
  · exact swapVertex_involutive loop.start
  · change (loop.edges.map swapEntry).map swapEntry = loop.edges
    simp only [List.map_map, Function.comp_def, swapEntry_involutive]
    exact List.map_id _

theorem swapExpression_involutive {width : Nat} :
    ∀ e : WindowExpression width, swapExpression (swapExpression e) = e
  | .one => rfl
  | .loop offset value spin => by
      change WindowExpression.loop offset (swapSourceLoop (swapSourceLoop value)) spin =
        WindowExpression.loop offset value spin
      rw [swapSourceLoop_involutive]
  | .add e f => by
      change WindowExpression.add (swapExpression (swapExpression e))
        (swapExpression (swapExpression f)) = WindowExpression.add e f
      rw [swapExpression_involutive e, swapExpression_involutive f]
  | .mul e f => by
      change WindowExpression.mul (swapExpression (swapExpression e))
        (swapExpression (swapExpression f)) = WindowExpression.mul e f
      rw [swapExpression_involutive e, swapExpression_involutive f]
  | .smul c e => by
      change WindowExpression.smul c (swapExpression (swapExpression e)) =
        WindowExpression.smul c e
      rw [swapExpression_involutive e]

private theorem intrinsic_ext {width : Nat} (x y : IntrinsicExpression width)
    (hr : x.radius = y.radius) (he : x.expression = y.expression) : x = y := by
  cases x
  cases y
  cases hr
  cases he
  rfl

theorem swapIntrinsic_involutive {width : Nat} (x : IntrinsicExpression width) :
    swapIntrinsic (swapIntrinsic x) = x := by
  apply intrinsic_ext
  · rfl
  · exact swapExpression_involutive x.expression

theorem swapIntrinsic_unit (width : Nat) :
    swapIntrinsic (unit width) = unit width := rfl

/-- Both source operands keep their literal common-radius charts. -/
theorem swapIntrinsic_sum {width : Nat} (x y : IntrinsicExpression width) :
    swapIntrinsic (sum x y) = sum (swapIntrinsic x) (swapIntrinsic y) := by
  apply intrinsic_ext
  · rfl
  · change WindowExpression.add
      (swapExpression (chart (max x.radius y.radius) x))
      (swapExpression (chart (max x.radius y.radius) y)) =
      WindowExpression.add (chart (max x.radius y.radius) (swapIntrinsic x))
        (chart (max x.radius y.radius) (swapIntrinsic y))
    rw [swap_chart, swap_chart]

theorem swapIntrinsic_difference {width : Nat} (x y : IntrinsicExpression width) :
    swapIntrinsic (difference x y) =
      difference (swapIntrinsic x) (swapIntrinsic y) := by
  apply intrinsic_ext
  · rfl
  · change WindowExpression.add
      (swapExpression (chart (max x.radius y.radius) x))
      (WindowExpression.smul (-1) (swapExpression (chart (max x.radius y.radius) y))) =
      WindowExpression.add (chart (max x.radius y.radius) (swapIntrinsic x))
        (WindowExpression.smul (-1) (chart (max x.radius y.radius) (swapIntrinsic y)))
    rw [swap_chart, swap_chart]

theorem swapIntrinsic_smul {width : Nat} (c : Q') (x : IntrinsicExpression width) :
    swapIntrinsic (smul c x) = smul c (swapIntrinsic x) := rfl

theorem swapIntrinsic_zero (width : Nat) :
    swapIntrinsic (zero width) = zero width := rfl

/-- Equality of the actual all-nome distance, not of a substituted norm. -/
theorem distSq_swap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (x y : IntrinsicExpression width) :
    Equiv (distSq hw0 hw1 (swapIntrinsic x) (swapIntrinsic y))
      (distSq hw0 hw1 x y) := by
  unfold distSq
  simpa only [swapIntrinsic_difference] using
    intrinsicForm_swap hw0 hw1 (difference x y) (difference x y)

/-- Constructed contraction data for the existing fixed-width seminorm. -/
def swapNonexpansive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} : (seminorm hw0 hw1 (width := width)).Nonexpansive where
  toFun := swapIntrinsic
  contraction := fun x y => leEv_of_equiv (distSq_swap hw0 hw1 x y)

end YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapAlgebra

#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapAlgebra.swapSourceLoop_involutive
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapAlgebra.swapExpression_involutive
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapAlgebra.swapIntrinsic_involutive
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapAlgebra.swapIntrinsic_unit
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapAlgebra.swapIntrinsic_sum
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapAlgebra.swapIntrinsic_difference
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapAlgebra.swapIntrinsic_smul
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapAlgebra.swapIntrinsic_zero
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapAlgebra.distSq_swap
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapAlgebra.swapNonexpansive
