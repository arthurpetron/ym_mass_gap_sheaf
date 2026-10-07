/-
# Nome-defect lower obstruction for the constructed log-curvature cap

The literal zeroth heat-tail term forces both prefix budgets above one.
The actual second-derivative cap is consequently at least 4096+128.
Combining its head-floor reciprocal with the existing quadratic nome-defect
ceiling gives the cleared lower bound 4224 <= (1-w)^2*logCurvatureCap.

This diagnoses the nome dependence of THIS constructed entrywise cap.
It is not a lower bound on actual curvature, a refutation of an improved
joint score estimate, or a Yang--Mills mass-gap obstruction. Tensorization
does not turn this cap into an AF-uniform analytic producer.
-/

import YMGap.Continuum.BF4ExactSlabHeadFloorNomeCeiling
import YMGap.Continuum.SU2HeatPolynomialPrefixBound
import YMGap.Continuum.SU2QuaternionHeatLogCurvature

namespace YMGap.Continuum.SU2QuaternionLogCurvatureCapObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BondMovingScaledNorm (tailTerm)
open YMGap.Continuum.SU2HeatPolynomialPrefixBound
open YMGap.Continuum.QuaternionHaarHeatSecondAngularDerivative
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound (relativeCap)
open YMGap.Continuum.SU2QuaternionHeatLogCurvature
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive)
open YMGap.Continuum.BF4ExactSlabHeadFloorNomeCeiling

local infix:50 " ≈ " => Q'.eqv

/-- The actual zeroth tail term, not a substituted positive budget. -/
theorem prefixBudget_one_le {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (m : Nat) : (1 : Q') ≤ prefixBudget w m := by
  have hzero : finSum (tailTerm w m) 1 ≈ (1 : Q') := by
    change (0 + Q'.ofNat (1^m)*1) ≈ (1 : Q')
    rw [Nat.one_pow]
    decide
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hzero) (prefix_bound hw0 hw1 m 1)

/-- Literal derivative cap at the original relative-quaternion parameters. -/
theorem heatSecondDerivativeCap_ge_4224 {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (4224 : Q') ≤ heatSecondDerivativeCap w 32 32 64 := by
  have h := Q'.add_le_add
    (Q'.mul_le_mul_of_nonneg_left _ _ (4*32*32)
      (prefixBudget_one_le hw0 hw1 6) (by decide))
    (Q'.mul_le_mul_of_nonneg_left _ _ (2*64)
      (prefixBudget_one_le hw0 hw1 4) (by decide))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by decide : (4224 : Q') ≈ (4*32*32)*1+(2*64)*1)) h

/-- Conservative inverse-quadratic nome-defect growth of the SAME computed
entrywise cap. No lower bound on an actual response is inferred. -/
theorem logCurvatureCap_nome_defect_square_lower {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (4224 : Q') ≤ (1 + -w)*(1 + -w)*logCurvatureCap w hw0 hw1 := by
  let H := headFloor w
  let C := heatSecondDerivativeCap w 32 32 64
  let r := Q'.recipPos H (headFloor_positive hw0 hw1)
  have hC : (0 : Q') ≤ C := Q'.le_trans' _ _ _ (by decide)
    (heatSecondDerivativeCap_ge_4224 hw0 hw1)
  have hH : (0 : Q') ≤ H := Q'.le_of_lt (headFloor_positive hw0 hw1)
  have hr : (0 : Q') ≤ r := Q'.le_of_lt (Q'.recipPos_pos H _)
  have hsecond : (0 : Q') ≤ secondRelativeCap w hw0 hw1 := Q'.mul_nonneg C r hC hr
  have hlog : (0 : Q') ≤ logCurvatureCap w hw0 hw1 :=
    Q'.zero_le_add _ _ hsecond (SumOfSquares.q_mul_self_nonneg (relativeCap w 32))
  have hpin : H*secondRelativeCap w hw0 hw1 ≈ C :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
        (fun | 0 => H | 1 => C | _ => r))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left C _ _
          (Q'.mul_recipPos_eqv H (headFloor_positive hw0 hw1))) (Q'.mul_one_eqv C))
  have hpart : secondRelativeCap w hw0 hw1 ≤ logCurvatureCap w hw0 hw1 :=
    Q'.add_le_self_of_nonneg _ _ (SumOfSquares.q_mul_self_nonneg (relativeCap w 32))
  have hfirst : (4224 : Q') ≤ H*logCurvatureCap w hw0 hw1 :=
    Q'.le_trans' _ _ _ (heatSecondDerivativeCap_ge_4224 hw0 hw1)
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpin)
        (Q'.mul_le_mul_of_nonneg_left _ _ H hpart hH))
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (headFloor_le_nome_defect_square hw0 hw1) hlog)

end YMGap.Continuum.SU2QuaternionLogCurvatureCapObstruction

#print axioms YMGap.Continuum.SU2QuaternionLogCurvatureCapObstruction.prefixBudget_one_le
#print axioms YMGap.Continuum.SU2QuaternionLogCurvatureCapObstruction.heatSecondDerivativeCap_ge_4224
#print axioms YMGap.Continuum.SU2QuaternionLogCurvatureCapObstruction.logCurvatureCap_nome_defect_square_lower
