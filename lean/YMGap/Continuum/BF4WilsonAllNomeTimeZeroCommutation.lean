/-
# Equal-time Wilson multipliers commute on the literal-width all-nome carrier

The source-polynomial identity is descended through the original all-nome
window pins, then through the same completed pairing.  This proves
commutativity of the actual completed multiplication operators and symmetry
of their product, at fixed width and nome.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeZeroOperator
import YMGap.Continuum.BF4WilsonAllNomeWindowPins
import YMGap.Continuum.BF4WilsonAllNomeLinear
import YMGap.Continuum.BF4WilsonAllNomeBilinearTime

namespace YMGap.Continuum.BF4WilsonAllNomeTimeZeroCommutation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeTimeZeroOperator
open YMGap.Continuum.BF4WilsonAllNomeWindowPins
  (embedWindow embedWindow_eq_of_source_identity)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completion_eq_of_pointwise)
open YMGap.Continuum.BF4WilsonTimeZeroIntrinsicMultiplier
  (multiply)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "M" => completedMultiply hw0 hw1
local notation "C" => multiplyCauchy hw0 hw1

private theorem polynomial_left_comm (a b e : RatPoly) :
    RatPolyCoeffEqv (polyMul a (polyMul b e)) (polyMul b (polyMul a e)) :=
  (RatPolyCoeffEqv.mul_assoc a b e).symm.trans
    (((RatPolyCoeffEqv.mul_comm a b).mul_right e).trans
      (RatPolyCoeffEqv.mul_assoc b a e))

private theorem embedded_multipliers_comm (L R : SourceLoop width) (i j : Nat)
    (x : IntrinsicExpression width) :
    embed hw0 hw1 (multiply L i (multiply R j x)) =
      embed hw0 hw1 (multiply R j (multiply L i x)) := by
  let H := x.radius
  let e : WindowExpression width :=
    .mul (.loop H L i) (.mul (.loop H R j) x.expression)
  let f : WindowExpression width :=
    .mul (.loop H R j) (.mul (.loop H L i) x.expression)
  have he : Within H e := ⟨Nat.le_refl _, ⟨Nat.le_refl _, x.within⟩⟩
  have hf : Within H f := ⟨Nat.le_refl _, ⟨Nat.le_refl _, x.within⟩⟩
  have hp : RatPolyCoeffEqv (sourcePolynomial e) (sourcePolynomial f) := by
    change RatPolyCoeffEqv
      (polyMul (sourcePolynomial (.loop H L i))
        (polyMul (sourcePolynomial (.loop H R j)) (sourcePolynomial x.expression)))
      (polyMul (sourcePolynomial (.loop H R j))
        (polyMul (sourcePolynomial (.loop H L i)) (sourcePolynomial x.expression)))
    exact polynomial_left_comm _ _ _
  have h := embedWindow_eq_of_source_identity hw0 hw1 H e f he hf hp
  change embed hw0 hw1 (multiply L i (multiply R j x)) =
    embed hw0 hw1 (multiply R j (multiply L i x)) at h
  exact h

private theorem intrinsicForm_multiplier_comm (L R : SourceLoop width) (i j : Nat)
    (x y : IntrinsicExpression width) :
    Equiv (intrinsicForm hw0 hw1 (multiply L i (multiply R j x)) y)
      (intrinsicForm hw0 hw1 (multiply R j (multiply L i x)) y) := by
  have h := embedded_multipliers_comm hw0 hw1 L R i j x
  have hpair := congrArg (fun z => completedInner hw0 hw1 z (embed hw0 hw1 y)) h
  exact Quotient.exact (by simpa only [completedInner_embed] using hpair)

private theorem multiplyCauchy_comm (L R : SourceLoop width) (i j : Nat)
    (X : (D).Cauchy) :
    Quotient.mk (D).completionSetoid (C L i (C R j X)) =
      Quotient.mk (D).completionSetoid (C R j (C L i X)) := by
  apply completion_eq_of_pointwise hw0 hw1
  intro n z
  exact intrinsicForm_multiplier_comm hw0 hw1 L R i j (X.seq n) z

/-- The actual completed equal-time multiplication operators commute. -/
theorem completedMultiply_comm (L R : SourceLoop width) (i j : Nat) (x : V) :
    M L i (M R j x) = M R j (M L i x) := by
  refine Quotient.inductionOn x ?_
  intro X
  change Quotient.mk (D).completionSetoid (C L i (C R j X)) =
    Quotient.mk (D).completionSetoid (C R j (C L i X))
  exact multiplyCauchy_comm hw0 hw1 L R i j X

/-- Their product is symmetric in the same all-nome completed pairing. -/
theorem completedInner_multiplier_product_balance
    (L R : SourceLoop width) (i j : Nat) (x y : V) :
    B (M L i (M R j x)) y = B x (M L i (M R j y)) := by
  rw [completedInner_multiplier_balance, completedInner_multiplier_balance,
    completedMultiply_comm hw0 hw1 R L j i y]

#print axioms embedded_multipliers_comm
#print axioms intrinsicForm_multiplier_comm
#print axioms multiplyCauchy_comm
#print axioms completedMultiply_comm
#print axioms completedInner_multiplier_product_balance

end YMGap.Continuum.BF4WilsonAllNomeTimeZeroCommutation
