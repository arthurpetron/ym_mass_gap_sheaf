/-
# Nonnegative bulk coefficients in the ORIGINAL SU(2) heat fusion residual

The dimension factors j+1 and Casimir exponents j*(j+2) reduce the adjacent
coefficient inequality to an explicit rational weighted-power inequality.
Thus every positive-spin coefficient in heat_fusion_residual is nonnegative.
The two finite-cutoff boundary terms are NOT removed by this result.

The consumer is quadratic positivity of a relative-character kernel with
the SAME endpoint source on both sides. This is not pointwise positivity
of the character residual, nor positivity under arbitrary signed insertions.
-/

import YMGap.Continuum.SU2HeatNeighborConvexity
import YMGap.Continuum.SU2QuaternionHeatFusionResidual
import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
import YMGap.Continuum.FiveHolonomyPerronCutoff

namespace YMGap.Continuum.SU2HeatFusionCoefficientPositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RGTransport (dimQ c4)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.SU2HeatNeighborConvexity
open YMGap.Continuum.SU2QuaternionHeatFusionResidual
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion (qpow_eqv_pow)
open YMGap.Continuum.FiveHolonomyPerronCutoff (pow_mul_eqv)

local infix:50 " ≈ " => Q'.eqv

private theorem native_coeff (w : Q') (j : Nat) :
    coeffW w j ≈ Q'.ofNat (j+1) * w^(j*(j+2)) :=
  Q'.mul_eqv_congr_left _ _ _ (qpow_eqv_pow w (c4 j))

private theorem scaled_power (w c : Q') (a b : Nat) :
    (c*(w^2)^a)*w^b ≈ c*w^(2*a+b) :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (pow_mul_eqv w 2 a)))
    (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.pow_add_eqv w (2*a) b))))

/-- The original adjacent-spin inequality, including its dimension factors. -/
theorem adjacent_heat_coefficients {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (k : Nat) :
    coeffW w 1 * coeffW w (k+1) ≤ coeffW w k + coeffW w (k+2) := by
  have hx0 : (0 : Q') ≤ w^2 := Q'.pow_nonneg w hw0 2
  have hx1 : w^2 ≤ (1 : Q') := YMGap.Continuum.HKPos.pow_le_one hw0 hw1 2
  have h := Q'.mul_le_mul_of_nonneg_right _ _ (w^(k*(k+2)))
    (dimension_weighted_neighbor_convexity hx0 hx1 (k+1)) (Q'.pow_nonneg w hw0 _)
  have e1 : 2*(k+3)+k*(k+2) = 3+(k+1)*(k+3) := by
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  have e2 : 2*(2*(k+1)+2)+k*(k+2) = (k+2)*(k+4) := by
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  have hl : coeffW w 1 * coeffW w (k+1) ≈
      ((2 : Q')*Q'.ofNat (k+2)*(w^2)^(k+3))*w^(k*(k+2)) := by
    have hp := Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (native_coeff w 1))
      (Q'.mul_eqv_congr_left _ _ _ (native_coeff w (k+1)))
    have hn : ((2 : Q')*w^3)*(Q'.ofNat (k+2)*w^((k+1)*(k+3))) ≈
        ((2 : Q')*Q'.ofNat (k+2))*w^(3+(k+1)*(k+3)) :=
      Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.mul (.const 2) (.var 0)) (.mul (.var 1) (.var 2)))
          (.mul (.mul (.const 2) (.var 1)) (.mul (.var 0) (.var 2)))
          (by decide) (fun | 0 => w^3 | 1 => Q'.ofNat (k+2) | _ => w^((k+1)*(k+3))))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.pow_add_eqv w 3 _)))
    exact Q'.eqv_trans _ _ _ hp (Q'.eqv_trans _ _ _ hn
      (Q'.eqv_symm (by simpa only [e1] using scaled_power w ((2 : Q')*Q'.ofNat (k+2)) (k+3) (k*(k+2)))))
  have hr : (Q'.ofNat (k+1)+Q'.ofNat (k+3)*(w^2)^(2*(k+1)+2))*w^(k*(k+2)) ≈
      coeffW w k + coeffW w (k+2) :=
    Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_symm (native_coeff w k))
        (Q'.eqv_trans _ _ _
          (by simpa only [e2] using scaled_power w (Q'.ofNat (k+3)) (2*(k+1)+2) (k*(k+2)))
          (Q'.eqv_symm (native_coeff w (k+2)))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hr))

/-- Genuine bulk positivity; finite-boundary terms remain explicit elsewhere. -/
theorem fusionCoeff_nonnegative {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (k : Nat) :
    (0 : Q') ≤ fusionCoeff w (k+1) := by
  simp only [fusionCoeff, Nat.add_sub_cancel]
  exact Q'.sub_nonneg_of_le (adjacent_heat_coefficients hw0 hw1 k)

#print axioms adjacent_heat_coefficients
#print axioms fusionCoeff_nonnegative

end YMGap.Continuum.SU2HeatFusionCoefficientPositive
