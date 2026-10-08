/-
# Nome scaling of the selected THREE-paired prefix curvature envelope

For the literal selected prefixCurvatureCost, the Taylor nome-defect
prefactor leaves a coefficient at least nine. Its excess above nine is
at most 9*(1-w), with an exact rational formula below.

This screens THIS fixed envelope, not the sharper adaptive certificate,
the complete signed score payment, its noise/weight derivatives or Taylor
remainders. It does not refute improved certificates, scaling or Yang--Mills.
-/

import YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature

namespace YMGap.Continuum.SU2QuaternionPairedPrefixCostScaling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.JacobiHeatTransverseCurvature (transverseCap)
open YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature (prefixCurvatureCost)

local infix:50 " ≈ " => Q'.eqv

/-- The selected curvature payment in THREE paired directions, after the
literal nome-defect prefactor. No cutoff or source datum is changed. -/
def normalizedPairedPrefixCost (w : Q') : Q' :=
  3*(1 + -w)*prefixCurvatureCost w

private theorem plus_nome_positive {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') < 1+w :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.add_le_self_of_nonneg 1 w (Q'.le_of_lt hw0))

private theorem nome_square_lt_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : w*w < (1 : Q') :=
  HKPos.q_lt_of_le_of_lt
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right w 1 w (Q'.le_of_lt hw1) (Q'.le_of_lt hw0))
      (Q'.le_of_eqv (Q'.one_mul_eqv w))) hw1

private theorem cost_denominator_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    prefixCurvatureCost w*(1 + -(w*w)) ≈
      (w+w+4)+2*(1 + -(w*w)) := by
  let D := 1 + -(w*w)
  let t := HKConv.divPos 1 D
  have hD : (0 : Q') < D := HKPos.one_sub_pos (nome_square_lt_one hw0 hw1)
  have ht : t*D ≈ (1 : Q') := HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hD)
  have hform : prefixCurvatureCost w*D ≈ (w+w+4)*(t*D)+2*D := by
    change (((w+w)*1)*t+(4*1)*t+1+1)*D ≈ (w+w+4)*(t*D)+2*D
    exact poly_identity_of_normal_eq
      (.mul (.add (.add (.add
        (.mul (.mul (.add (.var 0) (.var 0)) (.const 1)) (.var 1))
        (.mul (.mul (.const 4) (.const 1)) (.var 1))) (.const 1)) (.const 1)) (.var 2))
      (.add (.mul (.add (.add (.var 0) (.var 0)) (.const 4))
        (.mul (.var 1) (.var 2))) (.mul (.const 2) (.var 2)))
      (by decide) (fun
        | 0 => w
        | 1 => t
        | _ => D)
  exact Q'.eqv_trans _ _ _ hform
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left _ _ _ ht))
      (Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv _)))

/-- Exact cleared excess, on the SAME literal selected envelope. -/
theorem normalizedPairedPrefixCost_excess_cleared_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (1+w)*(normalizedPairedPrefixCost w + -9) ≈
      3*(1 + -w)*(2*w+3) := by
  have hfactor : (1+w)*(normalizedPairedPrefixCost w + -9) ≈
      3*(prefixCurvatureCost w*(1 + -(w*w))) + -(9*(1+w)) := by
    exact poly_identity_of_normal_eq
      (.mul (.add (.const 1) (.var 0))
        (.add (.mul (.mul (.const 3) (.add (.const 1) (.neg (.var 0)))) (.var 1))
          (.neg (.const 9))))
      (.add (.mul (.const 3) (.mul (.var 1)
        (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))))
        (.neg (.mul (.const 9) (.add (.const 1) (.var 0)))))
      (by decide) (fun
        | 0 => w
        | _ => prefixCurvatureCost w)
  exact Q'.eqv_trans _ _ _ hfactor
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (cost_denominator_pin hw0 hw1)))
      (poly_identity_of_normal_eq
        (.add (.mul (.const 3) (.add (.add (.add (.var 0) (.var 0)) (.const 4))
          (.mul (.const 2) (.add (.const 1) (.neg (.mul (.var 0) (.var 0)))))))
          (.neg (.mul (.const 9) (.add (.const 1) (.var 0)))))
        (.mul (.mul (.const 3) (.add (.const 1) (.neg (.var 0))))
          (.add (.mul (.const 2) (.var 0)) (.const 3)))
        (by decide) (fun _ => w)))

/-- The explicit rational formula H=9+3*(1-w)*(2w+3)/(1+w).
The denominator is positive at every strict nome. -/
theorem normalizedPairedPrefixCost_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    normalizedPairedPrefixCost w ≈
      9+3*(1 + -w)*HKConv.divPos (2*w+3) (1+w) := by
  let H := normalizedPairedPrefixCost w
  let t := HKConv.divPos (2*w+3) (1+w)
  have ht : t*(1+w) ≈ 2*w+3 :=
    HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (plus_nome_positive hw0))
  have ha : (1+w)*H ≈ (1+w)*(9+3*(1 + -w)*t) := by
    have hleft : (1+w)*H ≈ (1+w)*(H + -9)+9*(1+w) :=
      poly_identity_of_normal_eq
        (.mul (.add (.const 1) (.var 0)) (.var 1))
        (.add (.mul (.add (.const 1) (.var 0)) (.add (.var 1) (.neg (.const 9))))
          (.mul (.const 9) (.add (.const 1) (.var 0))))
        (by decide) (fun
          | 0 => w
          | _ => H)
    have hright : (1+w)*(9+3*(1 + -w)*t) ≈
        3*(1 + -w)*(t*(1+w))+9*(1+w) :=
      poly_identity_of_normal_eq
        (.mul (.add (.const 1) (.var 0)) (.add (.const 9)
          (.mul (.mul (.const 3) (.add (.const 1) (.neg (.var 0)))) (.var 1))))
        (.add (.mul (.mul (.const 3) (.add (.const 1) (.neg (.var 0))))
          (.mul (.var 1) (.add (.const 1) (.var 0))))
          (.mul (.const 9) (.add (.const 1) (.var 0))))
        (by decide) (fun
          | 0 => w
          | _ => t)
    exact Q'.eqv_trans _ _ _ hleft
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (normalizedPairedPrefixCost_excess_cleared_pin hw0 hw1))
        (Q'.eqv_symm (Q'.eqv_trans _ _ _ hright
          (Q'.add_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left _ _ _ ht)))))
  exact Int.le_antisymm
    (HKConvGen.mul_le_mul_left_cancel (plus_nome_positive hw0) (Q'.le_of_eqv ha))
    (HKConvGen.mul_le_mul_left_cancel (plus_nome_positive hw0) (Q'.ge_of_eqv ha))

/-- Quantitative screen: the selected coefficient has excess in [0,9*(1-w)]. -/
theorem normalizedPairedPrefixCost_excess_bounds {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') ≤ normalizedPairedPrefixCost w + -9 ∧
    normalizedPairedPrefixCost w + -9 ≤ 9*(1 + -w) := by
  have hd : (0 : Q') ≤ 1 + -w := Q'.le_of_lt (HKPos.one_sub_pos hw1)
  have hw : (0 : Q') ≤ w := Q'.le_of_lt hw0
  have hscale : (0 : Q') ≤ 3*(1 + -w) := Q'.mul_nonneg _ _ (by decide) hd
  have hnum : 2*w+3 ≤ 3*(1+w) := by
    have hp : (2*w+3)+w ≈ 3*(1+w) :=
      poly_identity_of_normal_eq
        (.add (.add (.mul (.const 2) (.var 0)) (.const 3)) (.var 0))
        (.mul (.const 3) (.add (.const 1) (.var 0))) (by decide) (fun _ => w)
    exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hw) (Q'.le_of_eqv hp)
  have hpin := normalizedPairedPrefixCost_excess_cleared_pin hw0 hw1
  constructor
  · apply HKConvGen.mul_le_mul_left_cancel (plus_nome_positive hw0)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv _))
      (Q'.le_trans' _ _ _
        (Q'.mul_nonneg _ _ hscale
          (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (by decide) hw) (by decide)))
        (Q'.ge_of_eqv hpin))
  · apply HKConvGen.mul_le_mul_left_cancel (plus_nome_positive hw0)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hnum hscale)
        (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.mul (.mul (.const 3) (.add (.const 1) (.neg (.var 0))))
            (.mul (.const 3) (.add (.const 1) (.var 0))))
          (.mul (.add (.const 1) (.var 0))
            (.mul (.const 9) (.add (.const 1) (.neg (.var 0)))))
          (by decide) (fun _ => w))))

/-- The nome-defect prefactor alone cannot make THIS selected cost small. -/
theorem normalizedPairedPrefixCost_lower {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (9 : Q') ≤ normalizedPairedPrefixCost w :=
  Q'.le_of_sub_nonneg (normalizedPairedPrefixCost_excess_bounds hw0 hw1).1

end YMGap.Continuum.SU2QuaternionPairedPrefixCostScaling

#print axioms YMGap.Continuum.SU2QuaternionPairedPrefixCostScaling.normalizedPairedPrefixCost
#print axioms YMGap.Continuum.SU2QuaternionPairedPrefixCostScaling.normalizedPairedPrefixCost_excess_cleared_pin
#print axioms YMGap.Continuum.SU2QuaternionPairedPrefixCostScaling.normalizedPairedPrefixCost_pin
#print axioms YMGap.Continuum.SU2QuaternionPairedPrefixCostScaling.normalizedPairedPrefixCost_excess_bounds
#print axioms YMGap.Continuum.SU2QuaternionPairedPrefixCostScaling.normalizedPairedPrefixCost_lower
