/-
The computed Fisher curvature COST of the literal odd marginal has a
non-vanishing first-order nome-defect coefficient.  This prunes only the
proposal to pay a small temporal budget with this existing upper-bound
constant alone.  It is not a lower bound for the actual energy or operator
cost, a no-go theorem for signed cancellations, or a Yang--Mills gap claim.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalCurvature

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFisherCalibrationObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalCurvature
  (marginalCurvatureCost)

local infix:50 " ≈ " => Q'.eqv

/-- Exact expression of the already-computed six-face/two-terminal marginal
curvature cost.  The quotient is `HKConv.divPos`, not a new inverse premise. -/
theorem marginalCurvatureCost_formula (w : Q') :
    marginalCurvatureCost w ≈
      32 + 8 * HKConv.divPos 1 (1 + -(w*w)) := by
  let t := HKConv.divPos 1 (1 + -(w*w))
  change (6 * (((1+t)+2)+1) + (((1+t)+2)+1)) + (((1+t)+2)+1) ≈
    32 + 8*t
  exact poly_identity_of_normal_eq
    (.add
      (.add (.mul (.const 6)
        (.add (.add (.add (.const 1) (.var 0)) (.const 2)) (.const 1)))
        (.add (.add (.add (.const 1) (.var 0)) (.const 2)) (.const 1)))
      (.add (.add (.add (.const 1) (.var 0)) (.const 2)) (.const 1)))
    (.add (.const 32) (.mul (.const 8) (.var 0)))
    (by decide) (fun _ => t)

private theorem nome_square_lt_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : w*w < (1 : Q') :=
  HKPos.q_lt_of_le_of_lt
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right w 1 w (Q'.le_of_lt hw1) (Q'.le_of_lt hw0))
      (Q'.le_of_eqv (Q'.one_mul_eqv w))) hw1

/-- Multiplication by the actual positive difference-of-squares denominator
clears the reciprocal in the marginal cost. -/
theorem marginalCurvatureCost_denominator_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    marginalCurvatureCost w * (1 + -(w*w)) ≈
      32*(1 + -(w*w)) + 8 := by
  let D := 1 + -(w*w)
  let t := HKConv.divPos 1 D
  have hD : (0 : Q') < D := HKPos.one_sub_pos (nome_square_lt_one hw0 hw1)
  have ht : t*D ≈ (1 : Q') :=
    HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hD)
  have hform : marginalCurvatureCost w * D ≈
      32*D + 8*(t*D) := by
    have h := Q'.mul_eqv_congr_right
      (marginalCurvatureCost w) (32+8*t) D (marginalCurvatureCost_formula w)
    exact Q'.eqv_trans _ _ _ h
      (poly_identity_of_normal_eq
        (.mul (.add (.const 32) (.mul (.const 8) (.var 0))) (.var 1))
        (.add (.mul (.const 32) (.var 1))
          (.mul (.const 8) (.mul (.var 0) (.var 1))))
        (by decide) (fun | 0 => t | _ => D))
  exact Q'.eqv_trans _ _ _ hform
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (32*D) _ _
        (Q'.mul_eqv_congr_left 8 _ _ ht))
      (Q'.add_eqv_congr_left (32*D) _ _ (Q'.mul_one_eqv 8)))

/-- The first-order defect times THIS computed upper-bound constant is never
below four on the strict-nome interval.  This says nothing about the optimal
energy coefficient after signed cancellation. -/
theorem marginalCurvatureCost_nome_defect_lower {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (4 : Q') ≤ (1 + -w)*marginalCurvatureCost w := by
  let D := 1 + -(w*w)
  have hplus : (0 : Q') < 1+w :=
    Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.add_le_self_of_nonneg 1 w (Q'.le_of_lt hw0))
  have hD : (0 : Q') < D := HKPos.one_sub_pos (nome_square_lt_one hw0 hw1)
  have hfactor : (1+w)*((1 + -w)*marginalCurvatureCost w) ≈
      marginalCurvatureCost w * D :=
    poly_identity_of_normal_eq
      (.mul (.add (.const 1) (.var 0))
        (.mul (.add (.const 1) (.neg (.var 0))) (.var 1)))
      (.mul (.var 1) (.add (.const 1) (.neg (.mul (.var 0) (.var 0)))))
      (by decide) (fun | 0 => w | _ => marginalCurvatureCost w)
  have hcleared : (1+w)*((1 + -w)*marginalCurvatureCost w) ≈
      32*D+8 := Q'.eqv_trans _ _ _ hfactor
        (marginalCurvatureCost_denominator_pin hw0 hw1)
  have hplus_le_two : 1+w ≤ (2 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_left 1 _ _ (Q'.le_of_lt hw1))
      (Q'.le_of_eqv (by decide : (1 : Q')+1 ≈ 2))
  have hleft : 4*(1+w) ≤ (8 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hplus_le_two (by decide))
      (Q'.le_of_eqv (by decide : (4 : Q')*2 ≈ 8))
  have hright : (8 : Q') ≤ 32*D+8 := by
    have h32 : (0 : Q') ≤ 32*D :=
      Q'.mul_nonneg _ _ (by decide) (Q'.le_of_lt hD)
    exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 8 (32*D) h32)
      (Q'.le_of_eqv (Q'.add_comm_eqv 8 (32*D)))
  apply HKConvGen.mul_le_mul_left_cancel hplus
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv (1+w) 4))
    (Q'.le_trans' _ _ _ hleft
      (Q'.le_trans' _ _ _ hright (Q'.ge_of_eqv hcleared)))

/-- A target strictly below four cannot be certified merely by replacing
the temporal first-order coefficient with this particular curvature cost. -/
theorem marginalCurvatureCost_not_below_target {w epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hepsilon : epsilon < (4 : Q')) :
    ¬ ((1 + -w)*marginalCurvatureCost w ≤ epsilon) := by
  intro hcost
  have hbad : (4 : Q') < 4 := HKPos.q_lt_of_le_of_lt
    (marginalCurvatureCost_nome_defect_lower hw0 hw1)
    (HKPos.q_lt_of_le_of_lt hcost hepsilon)
  exact (by decide : ¬ ((4 : Q') < 4)) hbad

end YMGap.Continuum.BF4ExactSlabFixedSpatialFisherCalibrationObstruction

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFisherCalibrationObstruction.marginalCurvatureCost_formula
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFisherCalibrationObstruction.marginalCurvatureCost_denominator_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFisherCalibrationObstruction.marginalCurvatureCost_nome_defect_lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFisherCalibrationObstruction.marginalCurvatureCost_not_below_target
