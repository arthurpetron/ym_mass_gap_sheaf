/-
# Algebra for summable rational step variation

This module supplies the elementary closure operations needed to split one
large cutoff-dependent rational debt into independently estimable pieces.

* pointwise `Q'.eqv` transports an existing variation certificate;
* multiplication by a fixed positive rational preserves summable variation;
* two summable variation streams may be added; and
* two nonnegative streams with positive uniform ceilings may be multiplied.

The product compiler uses the explicit one-step budget
`rightCeiling * leftVariation + leftCeiling * rightVariation`.  Thus two
analytic producers can work independently and meet at one lossless algebraic
consumer.  No physical estimate is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Constructive.ExpNeg
import YMGap.Continuum.SummableRationalSquareStepVariation

namespace YMGap.Continuum.SummableRationalStepVariationAlgebra

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalSquareStepVariation
open YMGap.Continuum.SummableRationalStepVariation

local infix:50 " ≈ " => Q'.eqv

private theorem add_le_add_local
    {a b c d : Q'} (hab : a <= b) (hcd : c <= d) :
    a + c <= b + d :=
  Q'.le_trans' _ _ _
    (Q'.add_le_add_right a b c hab)
    (Q'.add_le_add_left b c d hcd)

private theorem add_quad_rearrange_local (a b c d : Q') :
    (a + b) + (c + d) ≈ (a + c) + (b + d) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a b (c + d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a (b + (c + d)) ((b + c) + d)
      (Q'.eqv_symm (Q'.add_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a ((b + c) + d) ((c + b) + d)
      (Q'.add_eqv_congr_right (b + c) (c + b) d
        (Q'.add_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a ((c + b) + d) (c + (b + d))
      (Q'.add_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv a c (b + d))

/-! ## 1. Tail-control addition -/

/-- Two antitone summable tails combine by asking each summand for half the
tolerance and taking the maximum of the two resulting stages. -/
def addAntitoneTailControl
    {leftVariation rightVariation : Nat -> Q'}
    (left : AntitoneTailControl leftVariation)
    (right : AntitoneTailControl rightVariation) :
    AntitoneTailControl
      (fun scale => leftVariation scale + rightVariation scale) where
  tailRate := fun epsilon =>
    max
      (left.tailRate (HalfPow.half * epsilon))
      (right.tailRate (HalfPow.half * epsilon))
  tailRate_antitone := by
    intro epsilon delta delta_pos delta_le_epsilon
    have half_delta_pos : (0 : Q') < HalfPow.half * delta :=
      Q'.mul_pos (by decide) delta_pos
    have half_le : HalfPow.half * delta <= HalfPow.half * epsilon :=
      Q'.mul_le_mul_of_nonneg_left delta epsilon HalfPow.half
        delta_le_epsilon HalfPow.half_nonneg
    apply Nat.max_le.mpr
    exact
      ⟨Nat.le_trans
          (left.tailRate_antitone
            (HalfPow.half * epsilon) (HalfPow.half * delta)
            half_delta_pos half_le)
          (Nat.le_max_left _ _),
        Nat.le_trans
          (right.tailRate_antitone
            (HalfPow.half * epsilon) (HalfPow.half * delta)
            half_delta_pos half_le)
          (Nat.le_max_right _ _)⟩
  tailBound := by
    intro epsilon epsilon_pos start start_bound length
    have half_epsilon_pos : (0 : Q') < HalfPow.half * epsilon :=
      Q'.mul_pos (by decide) epsilon_pos
    have left_start :
        left.tailRate (HalfPow.half * epsilon) <= start :=
      Nat.le_trans (Nat.le_max_left _ _) start_bound
    have right_start :
        right.tailRate (HalfPow.half * epsilon) <= start :=
      Nat.le_trans (Nat.le_max_right _ _) start_bound
    have left_bound := left.tailBound
      (HalfPow.half * epsilon) half_epsilon_pos
      start left_start length
    have right_bound := right.tailBound
      (HalfPow.half * epsilon) half_epsilon_pos
      start right_start length
    have combined_bound :
        finSum (fun offset => leftVariation (start + offset)) length +
            finSum (fun offset => rightVariation (start + offset)) length <=
          HalfPow.half * epsilon + HalfPow.half * epsilon :=
      add_le_add_local left_bound right_bound
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (RationalTail.finSum_add
          (fun offset => leftVariation (start + offset))
          (fun offset => rightVariation (start + offset)) length))
      (Q'.le_trans' _ _ _ combined_bound
        (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))

/-! ## 2. Setoid transport, scaling, and addition -/

/-- Transport a summable variation certificate along pointwise rational
setoid equality.  The variation stream and its tail modulus are unchanged. -/
def ofPointwiseEqv
    {leftStream rightStream : Nat -> Q'}
    (data : SummableRationalStepVariation leftStream)
    (pointwise : forall scale, leftStream scale ≈ rightStream scale) :
    SummableRationalStepVariation rightStream where
  variation := data.variation
  variation_nonnegative := data.variation_nonnegative
  tailControl := data.tailControl
  stepBound := by
    intro scale
    have forward := (data.stepBound scale).1
    have backward := (data.stepBound scale).2
    exact
      ⟨Q'.le_trans' _ _ _
          (Q'.ge_of_eqv (pointwise (scale + 1)))
          (Q'.le_trans' _ _ _ forward
            (Q'.add_le_add_right _ _ _
              (Q'.le_of_eqv (pointwise scale)))),
        Q'.le_trans' _ _ _
          (Q'.ge_of_eqv (pointwise scale))
          (Q'.le_trans' _ _ _ backward
            (Q'.add_le_add_right _ _ _
              (Q'.le_of_eqv (pointwise (scale + 1)))))⟩

/-- Multiplication by one fixed positive rational preserves summable
two-sided step variation. -/
def scale
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream)
    (multiplier : Q') (multiplier_pos : (0 : Q') < multiplier) :
    SummableRationalStepVariation
      (fun scale => multiplier * stream scale) where
  variation := fun scale => multiplier * data.variation scale
  variation_nonnegative := fun scale =>
    Q'.mul_nonneg _ _ (Q'.le_of_lt multiplier_pos)
      (data.variation_nonnegative scale)
  tailControl := scaledAntitoneTailControl data.tailControl
    multiplier multiplier_pos
  stepBound := by
    intro scale
    have forward := Q'.mul_le_mul_of_nonneg_left _ _ multiplier
      (data.stepBound scale).1 (Q'.le_of_lt multiplier_pos)
    have backward := Q'.mul_le_mul_of_nonneg_left _ _ multiplier
      (data.stepBound scale).2 (Q'.le_of_lt multiplier_pos)
    exact
      ⟨Q'.le_trans' _ _ _ forward
          (Q'.le_of_eqv
            (Q'.mul_add_eqv multiplier (stream scale)
              (data.variation scale))),
        Q'.le_trans' _ _ _ backward
          (Q'.le_of_eqv
            (Q'.mul_add_eqv multiplier (stream (scale + 1))
              (data.variation scale)))⟩

/-- Pointwise addition preserves summable two-sided step variation. -/
def add
    {leftStream rightStream : Nat -> Q'}
    (left : SummableRationalStepVariation leftStream)
    (right : SummableRationalStepVariation rightStream) :
    SummableRationalStepVariation
      (fun scale => leftStream scale + rightStream scale) where
  variation := fun scale => left.variation scale + right.variation scale
  variation_nonnegative := fun scale =>
    Q'.zero_le_add _ _
      (left.variation_nonnegative scale)
      (right.variation_nonnegative scale)
  tailControl := addAntitoneTailControl
    left.tailControl right.tailControl
  stepBound := by
    intro scale
    have forward := add_le_add_local
      (left.stepBound scale).1 (right.stepBound scale).1
    have backward := add_le_add_local
      (left.stepBound scale).2 (right.stepBound scale).2
    exact
      ⟨Q'.le_trans' _ _ _ forward
          (Q'.le_of_eqv
            (add_quad_rearrange_local
              (leftStream scale) (left.variation scale)
              (rightStream scale) (right.variation scale))),
        Q'.le_trans' _ _ _ backward
          (Q'.le_of_eqv
            (add_quad_rearrange_local
              (leftStream (scale + 1)) (left.variation scale)
              (rightStream (scale + 1)) (right.variation scale)))⟩

/-! ## 3. Bounded products -/

/-- One bounded product step.  The left and right streams may have different
ceilings and different step budgets. -/
theorem product_step_le
    (leftCurrent leftNext rightCurrent rightNext
      leftVariation rightVariation leftCeiling rightCeiling : Q')
    (leftCurrent_nonnegative : (0 : Q') <= leftCurrent)
    (rightNext_nonnegative : (0 : Q') <= rightNext)
    (leftVariation_nonnegative : (0 : Q') <= leftVariation)
    (rightVariation_nonnegative : (0 : Q') <= rightVariation)
    (leftCurrent_le : leftCurrent <= leftCeiling)
    (rightNext_le : rightNext <= rightCeiling)
    (leftStep : leftNext <= leftCurrent + leftVariation)
    (rightStep : rightNext <= rightCurrent + rightVariation) :
    leftNext * rightNext <=
      leftCurrent * rightCurrent +
        (rightCeiling * leftVariation + leftCeiling * rightVariation) := by
  have replaceLeft : leftNext * rightNext <=
      (leftCurrent + leftVariation) * rightNext :=
    Q'.mul_le_mul_of_nonneg_right _ _ rightNext leftStep
      rightNext_nonnegative
  have expandLeft : leftNext * rightNext <=
      leftCurrent * rightNext + leftVariation * rightNext :=
    Q'.le_trans' _ _ _ replaceLeft
      (Q'.le_of_eqv
        (Q'.add_mul_eqv leftCurrent leftVariation rightNext))
  have replaceRight : leftCurrent * rightNext <=
      leftCurrent * (rightCurrent + rightVariation) :=
    Q'.mul_le_mul_of_nonneg_left _ _ leftCurrent rightStep
      leftCurrent_nonnegative
  have expandRight : leftCurrent * rightNext <=
      leftCurrent * rightCurrent + leftCurrent * rightVariation :=
    Q'.le_trans' _ _ _ replaceRight
      (Q'.le_of_eqv
        (Q'.mul_add_eqv leftCurrent rightCurrent rightVariation))
  have insertRight :
      leftCurrent * rightNext + leftVariation * rightNext <=
        (leftCurrent * rightCurrent + leftCurrent * rightVariation) +
          leftVariation * rightNext :=
    Q'.add_le_add_right _ _ _ expandRight
  have boundLeftVariation : leftVariation * rightNext <=
      rightCeiling * leftVariation := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ leftVariation
        rightNext_le leftVariation_nonnegative)
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv leftVariation rightCeiling))
  have boundRightVariation : leftCurrent * rightVariation <=
      leftCeiling * rightVariation :=
    Q'.mul_le_mul_of_nonneg_right _ _ rightVariation
      leftCurrent_le rightVariation_nonnegative
  have insertRightVariation :
      (leftCurrent * rightCurrent + leftCurrent * rightVariation) +
          leftVariation * rightNext <=
        (leftCurrent * rightCurrent + leftCeiling * rightVariation) +
          leftVariation * rightNext :=
    Q'.add_le_add_right _ _ _
      (Q'.add_le_add_left _ _ _ boundRightVariation)
  have insertLeftVariation :
      (leftCurrent * rightCurrent + leftCeiling * rightVariation) +
          leftVariation * rightNext <=
        (leftCurrent * rightCurrent + leftCeiling * rightVariation) +
          rightCeiling * leftVariation :=
    Q'.add_le_add_left _ _ _ boundLeftVariation
  have collect :
      (leftCurrent * rightCurrent + leftCeiling * rightVariation) +
          rightCeiling * leftVariation ≈
        leftCurrent * rightCurrent +
          (rightCeiling * leftVariation + leftCeiling * rightVariation) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv
        (leftCurrent * rightCurrent)
        (leftCeiling * rightVariation)
        (rightCeiling * leftVariation)) ?_
    exact Q'.add_eqv_congr_left (leftCurrent * rightCurrent) _ _
      (Q'.add_comm_eqv
        (leftCeiling * rightVariation)
        (rightCeiling * leftVariation))
  exact Q'.le_trans' _ _ _ expandLeft
    (Q'.le_trans' _ _ _ insertRight
      (Q'.le_trans' _ _ _ insertRightVariation
        (Q'.le_trans' _ _ _ insertLeftVariation
          (Q'.le_of_eqv collect))))

/-- The product of two nonnegative streams with positive uniform ceilings
has summable variation.  The two source certificates remain independent
inputs to this compiler. -/
def mulOfCeilings
    {leftStream rightStream : Nat -> Q'}
    (left : SummableRationalStepVariation leftStream)
    (right : SummableRationalStepVariation rightStream)
    (leftCeiling rightCeiling : Q')
    (leftCeiling_pos : (0 : Q') < leftCeiling)
    (rightCeiling_pos : (0 : Q') < rightCeiling)
    (left_nonnegative : forall scale, (0 : Q') <= leftStream scale)
    (right_nonnegative : forall scale, (0 : Q') <= rightStream scale)
    (left_le : forall scale, leftStream scale <= leftCeiling)
    (right_le : forall scale, rightStream scale <= rightCeiling) :
    SummableRationalStepVariation
      (fun scale => leftStream scale * rightStream scale) where
  variation := fun scale =>
    rightCeiling * left.variation scale +
      leftCeiling * right.variation scale
  variation_nonnegative := fun scale =>
    Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (Q'.le_of_lt rightCeiling_pos)
        (left.variation_nonnegative scale))
      (Q'.mul_nonneg _ _ (Q'.le_of_lt leftCeiling_pos)
        (right.variation_nonnegative scale))
  tailControl := addAntitoneTailControl
    (scaledAntitoneTailControl left.tailControl
      rightCeiling rightCeiling_pos)
    (scaledAntitoneTailControl right.tailControl
      leftCeiling leftCeiling_pos)
  stepBound := by
    intro scale
    exact
      ⟨product_step_le
          (leftStream scale) (leftStream (scale + 1))
          (rightStream scale) (rightStream (scale + 1))
          (left.variation scale) (right.variation scale)
          leftCeiling rightCeiling
          (left_nonnegative scale)
          (right_nonnegative (scale + 1))
          (left.variation_nonnegative scale)
          (right.variation_nonnegative scale)
          (left_le scale)
          (right_le (scale + 1))
          (left.stepBound scale).1 (right.stepBound scale).1,
        product_step_le
          (leftStream (scale + 1)) (leftStream scale)
          (rightStream (scale + 1)) (rightStream scale)
          (left.variation scale) (right.variation scale)
          leftCeiling rightCeiling
          (left_nonnegative (scale + 1))
          (right_nonnegative scale)
          (left.variation_nonnegative scale)
          (right.variation_nonnegative scale)
          (left_le (scale + 1))
          (right_le scale)
          (left.stepBound scale).2 (right.stepBound scale).2⟩

end YMGap.Continuum.SummableRationalStepVariationAlgebra

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.SummableRationalStepVariationAlgebra.addAntitoneTailControl
#print axioms
  YMGap.Continuum.SummableRationalStepVariationAlgebra.ofPointwiseEqv
#print axioms
  YMGap.Continuum.SummableRationalStepVariationAlgebra.scale
#print axioms
  YMGap.Continuum.SummableRationalStepVariationAlgebra.add
#print axioms
  YMGap.Continuum.SummableRationalStepVariationAlgebra.product_step_le
#print axioms
  YMGap.Continuum.SummableRationalStepVariationAlgebra.mulOfCeilings
