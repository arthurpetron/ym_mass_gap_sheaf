/-
# Nome-defect ceiling for the retained heat-head floor

The computable retained heat floor is bounded above by a quadratic nome
defect.  This is a scalar limitation of the particular Euler-product floor;
it is not an upper bound on an actual variance, response, or transfer
eigenvalue.
-/

import YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.BF4ExactSlabHeadFloorNomeCeiling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.GaussQBinomEulerNormalization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison

local infix:50 " ≈ " => Q'.eqv

/-- The first Euler factor already bounds the retained infinite-product
floor by the nome defect. -/
theorem eulerFloor_le_nome_defect {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    EulerProductStrictFloor.floor w ≤ 1 + -w := by
  have h := EulerProductStrictFloor.floor_le_euler hw0 hw1 1
  have he : euler w 1 ≈ 1 + -w := by
    change (1 * (1 + -(w ^ 1))) ≈ 1 + -w
    exact poly_identity_of_normal_eq
      (.mul (.const 1) (.add (.const 1) (.neg (.mul (.var 0) (.const 1)))))
      (.add (.const 1) (.neg (.var 0))) (by decide) (fun _ => w)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv he)

/-- The pointwise SU(2) heat floor inherits the square of the Euler defect;
the explicit quarter normalization is only discarded upward. -/
theorem heatFloor_le_nome_defect_square {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    SU2PointwiseHeatStrictFloor.floor w ≤ (1 + -w) * (1 + -w) := by
  have hd0 : (0 : Q') ≤ 1 + -w := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have he0 : (0 : Q') ≤ EulerProductStrictFloor.floor w :=
    Q'.le_of_lt (EulerProductStrictFloor.floor_pos hw0 hw1)
  have he := eulerFloor_le_nome_defect hw0 hw1
  have ht : ThetaProductStrictFloor.floor w ≤ (1 + -w) * (1 + -w) := by
    unfold ThetaProductStrictFloor.floor
    exact HKConv.mul_le_mul' he0 hd0 he he
  have hquarter : HalfPow.half * HalfPow.half ≤ (1 : Q') := by decide
  have htheta0 : (0 : Q') ≤ ThetaProductStrictFloor.floor w :=
    Q'.le_of_lt (ThetaProductStrictFloor.floor_pos hw0 hw1)
  have hs : SU2PointwiseHeatStrictFloor.floor w ≤ ThetaProductStrictFloor.floor w := by
    unfold SU2PointwiseHeatStrictFloor.floor
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hquarter htheta0)
      (Q'.le_of_eqv (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ hs ht

/-- The extra half normalization in `headFloor` preserves the same quadratic
nome-defect ceiling. -/
theorem headFloor_le_nome_defect_square {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    headFloor w ≤ (1 + -w) * (1 + -w) := by
  have hh : HalfPow.half ≤ (1 : Q') := by decide
  have hf0 : (0 : Q') ≤ SU2PointwiseHeatStrictFloor.floor w :=
    Q'.le_of_lt (SU2PointwiseHeatStrictFloor.floor_pos hw0 hw1)
  have hhead : headFloor w ≤ SU2PointwiseHeatStrictFloor.floor w := by
    unfold headFloor
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hh hf0)
      (Q'.le_of_eqv (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ hhead (heatFloor_le_nome_defect_square hw0 hw1)

#print axioms eulerFloor_le_nome_defect
#print axioms heatFloor_le_nome_defect_square
#print axioms headFloor_le_nome_defect_square

end YMGap.Continuum.BF4ExactSlabHeadFloorNomeCeiling
