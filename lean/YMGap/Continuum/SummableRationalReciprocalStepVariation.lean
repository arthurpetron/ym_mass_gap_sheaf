/-
# Summable variation of positive rational reciprocals

A positive rational stream with summable two-sided step variation need not
have summable reciprocal variation if it approaches zero.  This module states
and proves the exact constructive missing condition: one positive rational
floor below every stream value.

For `floor <= stream k`, the reciprocal map is Lipschitz with constant
`1 / floor^2`.  Thus the original one-step variation, scaled by the explicit
positive rational `(recipPos floor)^2`, is a summable two-sided variation for
the reciprocal stream.  No independent reciprocal-variation or ceiling
certificate is required.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.SummableRationalStepVariationAlgebra

namespace YMGap.Continuum.SummableRationalReciprocalStepVariation

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SummableRationalSquareStepVariation
open YMGap.Continuum.SummableRationalStepVariation

local infix:50 " ≈ " => Q'.eqv

private theorem recipPos_antitone_local
    {larger smaller : Q'}
    (larger_pos : (0 : Q') < larger)
    (smaller_pos : (0 : Q') < smaller)
    (smaller_le : smaller <= larger) :
    Q'.recipPos larger larger_pos <=
      Q'.recipPos smaller smaller_pos := by
  show (Q'.recipPos larger larger_pos).num *
      ((Q'.recipPos smaller smaller_pos).den : Int) <=
    (Q'.recipPos smaller smaller_pos).num *
      ((Q'.recipPos larger larger_pos).den : Int)
  rw [Q'.recipPos_num, Q'.recipPos_den,
    Q'.recipPos_num, Q'.recipPos_den]
  have cross : smaller.num * (larger.den : Int) <=
      larger.num * (smaller.den : Int) := smaller_le
  simpa only [Int.mul_comm] using cross

private theorem reciprocal_budget_times_left_ge
    (left right variation floor : Q')
    (right_pos : (0 : Q') < right)
    (floor_pos : (0 : Q') < floor)
    (variation_nonnegative : (0 : Q') <= variation)
    (floor_le_left : floor <= left)
    (floor_le_right : floor <= right) :
    Q'.recipPos right right_pos * variation <=
      ((Q'.recipPos floor floor_pos * Q'.recipPos floor floor_pos) *
          variation) * left := by
  let reciprocalFloor := Q'.recipPos floor floor_pos
  let reciprocalRight := Q'.recipPos right right_pos
  have reciprocalRight_le : reciprocalRight <= reciprocalFloor :=
    recipPos_antitone_local right_pos floor_pos floor_le_right
  have first_bound : reciprocalRight * variation <=
      reciprocalFloor * variation :=
    Q'.mul_le_mul_of_nonneg_right _ _ variation
      reciprocalRight_le variation_nonnegative
  have reciprocalFloor_nonnegative : (0 : Q') <= reciprocalFloor :=
    Q'.le_of_lt (Q'.recipPos_pos floor floor_pos)
  have reciprocalFloorVariation_nonnegative : (0 : Q') <=
      reciprocalFloor * variation :=
    Q'.mul_nonneg _ _ reciprocalFloor_nonnegative
      variation_nonnegative
  have floor_scaled : reciprocalFloor * floor <=
      reciprocalFloor * left :=
    Q'.mul_le_mul_of_nonneg_left _ _ reciprocalFloor
      floor_le_left reciprocalFloor_nonnegative
  have cancellation : reciprocalFloor * floor ≈ (1 : Q') := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv reciprocalFloor floor) ?_
    exact Q'.mul_recipPos_eqv floor floor_pos
  have one_le_scaled : (1 : Q') <= reciprocalFloor * left :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv cancellation) floor_scaled
  have multiply_one :
      (reciprocalFloor * variation) * 1 <=
        (reciprocalFloor * variation) *
          (reciprocalFloor * left) :=
    Q'.mul_le_mul_of_nonneg_left _ _
      (reciprocalFloor * variation)
      one_le_scaled reciprocalFloorVariation_nonnegative
  have second_bound : reciprocalFloor * variation <=
      (reciprocalFloor * variation) *
        (reciprocalFloor * left) :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (Q'.mul_one_eqv (reciprocalFloor * variation)))
      multiply_one
  have rearrange :
      (reciprocalFloor * variation) *
          (reciprocalFloor * left) ≈
        ((reciprocalFloor * reciprocalFloor) * variation) * left := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (reciprocalFloor * variation) reciprocalFloor left)) ?_
    refine Q'.mul_eqv_congr_right _ _ left ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv reciprocalFloor variation reciprocalFloor) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left reciprocalFloor _ _
        (Q'.mul_comm_eqv variation reciprocalFloor)) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv reciprocalFloor reciprocalFloor variation)
  exact Q'.le_trans' _ _ _ first_bound
    (Q'.le_trans' _ _ _ second_bound
      (Q'.le_of_eqv rearrange))

/-- One reciprocal step.  If `right <= left + variation`, then
`1/left <= 1/right + variation/floor^2`. -/
theorem reciprocal_step_le
    (left right variation floor : Q')
    (left_pos : (0 : Q') < left)
    (right_pos : (0 : Q') < right)
    (floor_pos : (0 : Q') < floor)
    (variation_nonnegative : (0 : Q') <= variation)
    (floor_le_left : floor <= left)
    (floor_le_right : floor <= right)
    (step : right <= left + variation) :
    Q'.recipPos left left_pos <=
      Q'.recipPos right right_pos +
        (Q'.recipPos floor floor_pos * Q'.recipPos floor floor_pos) *
          variation := by
  let reciprocalLeft := Q'.recipPos left left_pos
  let reciprocalRight := Q'.recipPos right right_pos
  let budget :=
    (Q'.recipPos floor floor_pos * Q'.recipPos floor floor_pos) *
      variation
  have reciprocalRight_nonnegative : (0 : Q') <= reciprocalRight :=
    Q'.le_of_lt (Q'.recipPos_pos right right_pos)
  have step_scaled : reciprocalRight * right <=
      reciprocalRight * (left + variation) :=
    Q'.mul_le_mul_of_nonneg_left _ _ reciprocalRight
      step reciprocalRight_nonnegative
  have right_cancellation : reciprocalRight * right ≈ (1 : Q') := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv reciprocalRight right) ?_
    exact Q'.mul_recipPos_eqv right right_pos
  have one_le_expanded : (1 : Q') <=
      reciprocalRight * left + reciprocalRight * variation :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv right_cancellation)
      (Q'.le_trans' _ _ _ step_scaled
        (Q'.le_of_eqv
          (Q'.mul_add_eqv reciprocalRight left variation)))
  have reciprocal_budget_bound : reciprocalRight * variation <=
      budget * left := by
    exact reciprocal_budget_times_left_ge
      left right variation floor
      right_pos floor_pos variation_nonnegative
      floor_le_left floor_le_right
  have one_le_budgeted : (1 : Q') <=
      reciprocalRight * left + budget * left :=
    Q'.le_trans' _ _ _ one_le_expanded
      (Q'.add_le_add_left _ _ _ reciprocal_budget_bound)
  have one_le_factored : (1 : Q') <=
      (reciprocalRight + budget) * left :=
    Q'.le_trans' _ _ _ one_le_budgeted
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.add_mul_eqv reciprocalRight budget left)))
  have quotient_bound : Q'.divPos 1 left left_pos <=
      reciprocalRight + budget :=
    Q'.divPos_le_of_le_mul 1 left left_pos one_le_factored
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv reciprocalLeft))
    quotient_bound

/-- Summable two-sided variation transfers through `recipPos` when one
positive rational floor stays below the entire stream. -/
def reciprocal
    {stream : Nat -> Q'}
    (stream_pos : forall scale, (0 : Q') < stream scale)
    (data : SummableRationalStepVariation stream)
    (floor : Q') (floor_pos : (0 : Q') < floor)
    (floor_le : forall scale, floor <= stream scale) :
    SummableRationalStepVariation
      (fun scale => Q'.recipPos (stream scale) (stream_pos scale)) where
  variation := fun scale =>
    (Q'.recipPos floor floor_pos * Q'.recipPos floor floor_pos) *
      data.variation scale
  variation_nonnegative := fun scale =>
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.le_of_lt (Q'.recipPos_pos floor floor_pos))
        (Q'.le_of_lt (Q'.recipPos_pos floor floor_pos)))
      (data.variation_nonnegative scale)
  tailControl := scaledAntitoneTailControl data.tailControl
    (Q'.recipPos floor floor_pos * Q'.recipPos floor floor_pos)
    (Q'.mul_pos
      (Q'.recipPos_pos floor floor_pos)
      (Q'.recipPos_pos floor floor_pos))
  stepBound := fun scale =>
    ⟨reciprocal_step_le
        (stream (scale + 1)) (stream scale)
        (data.variation scale) floor
        (stream_pos (scale + 1)) (stream_pos scale)
        floor_pos (data.variation_nonnegative scale)
        (floor_le (scale + 1)) (floor_le scale)
        (data.stepBound scale).2,
      reciprocal_step_le
        (stream scale) (stream (scale + 1))
        (data.variation scale) floor
        (stream_pos scale) (stream_pos (scale + 1))
        floor_pos (data.variation_nonnegative scale)
        (floor_le scale) (floor_le (scale + 1))
        (data.stepBound scale).1⟩

end YMGap.Continuum.SummableRationalReciprocalStepVariation

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.SummableRationalReciprocalStepVariation.reciprocal_step_le
#print axioms
  YMGap.Continuum.SummableRationalReciprocalStepVariation.reciprocal
