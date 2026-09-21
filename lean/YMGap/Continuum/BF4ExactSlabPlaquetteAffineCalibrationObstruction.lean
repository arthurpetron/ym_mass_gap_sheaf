/-
# The affine variance witness cannot pay the existing nome loss budget

The new selected-action coefficient floor is positive at every fixed nome.
It is nevertheless at most `(1-w)^48/600`: the actual Euler-product floor
lies below its first factor, and the twenty-four-face absolute window squares
that loss before taking its twenty-fourth power. Dividing the existing
single-plaquette loss budget `192*(1-w)` by THIS floor gives at least 115200.

These are bounds on computed certificate numbers, NOT an upper bound on
actual variance or a lower bound on actual time loss. They rule out direct
subtraction/linear-spacing calibration using this pair of certificates.
They do not refute physical survival or any Yang--Mills theory. The new
completed-family nontriviality theorem remains valid and unchanged.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity
import YMGap.Continuum.BF4ExactSlabHeadFloorNomeCeiling
import YMGap.Continuum.PhysicalSeparatorLinearTail

namespace YMGap.Continuum.BF4ExactSlabPlaquetteAffineCalibrationObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity
open YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryWindow
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabHeadFloorNomeCeiling
open YMGap.Continuum.PhysicalSeparatorLogRate (PhysicalSpacing)
open YMGap.Continuum.PhysicalSeparatorLinearTail (SpacingToZero)

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

include hw0 hw1

/-- This is a ceiling on the particular lower-window NUMBER, not on heat
or variance. The right side is the forty-eighth power of the nome defect. -/
theorem boundary_lower_le_defect_power :
    lower w ≤ ((1 + -w)*(1 + -w))^24 :=
  HKConv.pow_le_pow_base (Q'.le_of_lt (localFloor_positive hw0 hw1))
    (Q'.le_trans' _ _ _ Q'.min_le_left (headFloor_le_nome_defect_square hw0 hw1)) 24

omit hw1 in
private theorem one_le_upper : (1 : Q') ≤ upper w := by
  have h := HKConv.pow_le_pow_base Q'.zero_le_one (one_le_localCap hw0) 24
  exact Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ (1 : Q')^24) h

/-- Cancel the exact positive denominator; no asymptotic estimate or
replacement for the already constructed floor is introduced. -/
theorem sixHundred_floor_le_boundary_lower :
    600 * varianceFloor w hw0 ≤ lower w := by
  let L := lower w
  let U := upper w
  let r := Q'.recipPos (600*U) (varianceDenominator_positive hw0)
  have hpin : (600*(L*r))*U ≈ L :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.const 600) (.mul (.var 0) (.var 1))) (.var 2))
        (.mul (.var 0) (.mul (.mul (.const 600) (.var 2)) (.var 1)))
        (by decide) (fun | 0 => L | 1 => r | _ => U))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_recipPos_eqv (600*U) (varianceDenominator_positive hw0)))
        (Q'.mul_one_eqv _))
  have h := Q'.mul_le_mul_of_nonneg_left _ _ (600*varianceFloor w hw0)
    (one_le_upper hw0) (Q'.mul_nonneg _ _ (by decide)
      (Q'.le_of_lt (varianceFloor_positive hw0 hw1)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hpin))

/-- A nome-explicit ceiling on THIS floor: `600*floor <= (1-w)^48`. -/
theorem sixHundred_floor_le_defect_power :
    600 * varianceFloor w hw0 ≤ ((1 + -w)*(1 + -w))^24 :=
  Q'.le_trans' _ _ _ (sixHundred_floor_le_boundary_lower hw0 hw1)
    (boundary_lower_le_defect_power hw0 hw1)

/-- Weaken the power ceiling only for the subsequent sharp-direction test. -/
theorem sixHundred_floor_le_defect :
    600 * varianceFloor w hw0 ≤ 1 + -w := by
  let d := 1 + -w
  have hd0 : (0 : Q') ≤ d := Q'.le_of_lt (HKPos.one_sub_pos hw1)
  have hd1 : d ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (Q'.le_of_lt hw0)))
    (Q'.le_of_eqv (by decide : (1 : Q') + -0 ≈ 1))
  have hsq : d*d ≤ d := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hd1 hd0) (Q'.le_of_eqv (Q'.mul_one_eqv _))
  have hp := HKPos.pow_succ_le_self (Q'.mul_nonneg _ _ hd0 hd0)
    (Q'.le_trans' _ _ _ hsq hd1) 23
  exact Q'.le_trans' _ _ _ (sixHundred_floor_le_defect_power hw0 hw1)
    (Q'.le_trans' _ _ _ hp hsq)

/-- The exact rational quotient of the AVAILABLE single-plaquette loss
upper budget by the AVAILABLE affine norm lower witness. This is not the
actual relative loss. -/
def computedLossRatio : Q' :=
  (192*(1 + -w)) * Q'.recipPos (varianceFloor w hw0) (varianceFloor_positive hw0 hw1)

/-- The bound-to-bound quotient is never small, at ANY strict nome. -/
theorem computedLossRatio_ge : (115200 : Q') ≤ computedLossRatio hw0 hw1 := by
  let f := varianceFloor w hw0
  let r := Q'.recipPos f (varianceFloor_positive hw0 hw1)
  have h := Q'.mul_le_mul_of_nonneg_left _ _ 192
    (sixHundred_floor_le_defect hw0 hw1) (by decide)
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ r h
    (Q'.le_of_lt (Q'.recipPos_pos f (varianceFloor_positive hw0 hw1)))
  have he : (192*(600*f))*r ≈ 115200 :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.const 192) (.mul (.const 600) (.var 0))) (.var 1))
      (.mul (.const 115200) (.mul (.var 0) (.var 1))) (by decide)
      (fun | 0 => f | _ => r))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_recipPos_eqv f (varianceFloor_positive hw0 hw1))) (Q'.mul_one_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hs

/-- Directly subtracting the existing `192*(1-w)` one-step loss budget
from THIS norm floor never certifies a positive response. Actual response
may be positive and much larger than this computed lower number. -/
theorem subtraction_floor_nonpositive :
    varianceFloor w hw0 + -(192*(1 + -w)) ≤ (0 : Q') := by
  have hf : varianceFloor w hw0 ≤ 600*varianceFloor w hw0 :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
      (Q'.mul_le_mul_of_nonneg_right 1 600 _ (by decide)
        (Q'.le_of_lt (varianceFloor_positive hw0 hw1)))
  have hd : 1 + -w ≤ 192*(1 + -w) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
      (Q'.mul_le_mul_of_nonneg_right 1 192 _ (by decide)
        (Q'.le_of_lt (HKPos.one_sub_pos hw1)))
  have h := Q'.le_trans' _ _ _ hf
    (Q'.le_trans' _ _ _ (sixHundred_floor_le_defect hw0 hw1) hd)
  exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ h)
    (Q'.le_of_eqv (Q'.add_neg_self_eqv _))

/-- An explicit scale refutes linear-spacing smallness of THIS quotient,
even when a new strict nome is chosen at every index. It does not refute
linear control of the actual normalized time loss. -/
theorem computedLossRatio_no_linear_scaling
    (A : PhysicalSpacing) (Z : SpacingToZero A) (M : Q') (hM : (0 : Q') < M)
    (j : Nat) (hj : Z.modulus (Q'.divPos 1 M hM) ≤ j) :
    ¬ computedLossRatio hw0 hw1 ≤ M*A.spacing j := by
  intro h
  have hm : M*A.spacing j ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ M
        (Z.spacing_le _ (Q'.divPos_pos _ _ hM (by decide)) j hj) (Q'.le_of_lt hM))
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
        (Q'.divPos_mul_eqv 1 M hM)))
  exact (by decide : ¬ (115200 : Q') ≤ (1 : Q'))
    (Q'.le_trans' _ _ _ (computedLossRatio_ge hw0 hw1) (Q'.le_trans' _ _ _ h hm))

end YMGap.Continuum.BF4ExactSlabPlaquetteAffineCalibrationObstruction

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffineCalibrationObstruction.boundary_lower_le_defect_power
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffineCalibrationObstruction.sixHundred_floor_le_boundary_lower
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffineCalibrationObstruction.sixHundred_floor_le_defect_power
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffineCalibrationObstruction.sixHundred_floor_le_defect
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffineCalibrationObstruction.computedLossRatio_ge
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffineCalibrationObstruction.subtraction_floor_nonpositive
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteAffineCalibrationObstruction.computedLossRatio_no_linear_scaling
