/-
# Explicit polynomial nome budget for the original prediction coefficient

The actual relative score satisfies C(w)*(1-w)^3 <= 24582. This is a
denominator-cleared rational estimate, not a physical spacing calibration.
It exposes the near-one cost without using the global heat-product minimum.
-/

import YMGap.Continuum.BF4ExactSlabRelativePredictionError

namespace YMGap.Continuum.BF4RelativePredictionNomeBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.JacobiShiftedRelativeSlope
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.BF4ExactSlabRelativePredictionError

local infix:50 " ≈ " => Q'.eqv

def cubicDeficit (w : Q') : Q' := ((1 + -w)*(1 + -w))*(1 + -w)

private theorem sub_one_le_one {a : Q'} (ha : (0 : Q') ≤ a) : 1 + -a ≤ 1 := by
  have he : (1 : Q') + -(1 + -a) ≈ a :=
    poly_identity_of_normal_eq (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 0)))))
      (.var 0) (by decide) (fun _ => a)
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ ha (Q'.ge_of_eqv he))

private theorem mul_le_one {a b : Q'} (ha0 : (0 : Q') ≤ a)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) : a*b ≤ 1 :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ a hb1 ha0)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv a)) ha1)

theorem cubicDeficit_positive {w : Q'} (hw1 : w < (1 : Q')) :
    (0 : Q') < cubicDeficit w :=
  Q'.mul_pos (HKPos.factorLB_pos hw1) (HKPos.one_sub_pos hw1)

theorem cubicDeficit_le_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    cubicDeficit w ≤ 1 := by
  have hd0 := Q'.le_of_lt (HKPos.one_sub_pos hw1)
  have hd1 := sub_one_le_one (Q'.le_of_lt hw0)
  exact mul_le_one (Q'.mul_nonneg _ _ hd0 hd0) (mul_le_one hd0 hd1 hd1) hd1

private theorem square_lt_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    w*w < (1 : Q') := by
  have h : w*w ≤ w := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ w (Q'.le_of_lt hw1) (Q'.le_of_lt hw0))
    (Q'.le_of_eqv (Q'.one_mul_eqv w))
  exact HKPos.q_lt_of_le_of_lt h hw1

def slopeDenominator (w : Q') : Q' := HKPos.factorLB w * (1 + -(w*w))

/-- Exact cancellation in the actual Jacobi relative-slope budget. -/
theorem budget_denominator_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    budget w * slopeDenominator w ≈ w+w := by
  let d := HKPos.factorLB w
  let e := 1 + -(w*w)
  let c := HKConv.Cstar w
  let h := HKConv.divPos 1 e
  have hc : c*d ≈ w+w := HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (HKPos.factorLB_pos hw1))
  have hh : h*e ≈ 1 := HKConv.divPos_mul_eqv
    (CReal.num_pos_of_pos (HKPos.one_sub_pos (square_lt_one hw0 hw1)))
  change ((c*1)*h)*(d*e) ≈ w+w
  exact Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.mul (.mul (.mul (.var 0) (.const 1)) (.var 1)) (.mul (.var 2) (.var 3)))
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
    (by decide) (fun | 0 => c | 1 => h | 2 => d | _ => e))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hc)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hh) (Q'.mul_one_eqv _)))

theorem denominator_ge_cubic {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    cubicDeficit w ≤ slopeDenominator w := by
  have he : slopeDenominator w ≈ cubicDeficit w * (1+w) := by
    let d : PolyExpr := .add (.const 1) (.neg (.var 0))
    exact poly_identity_of_normal_eq
      (.mul (.mul d d) (.add (.const 1) (.neg (.mul (.var 0) (.var 0)))))
      (.mul (.mul (.mul d d) d) (.add (.const 1) (.var 0))) (by decide) (fun _ => w)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (cubicDeficit w)
        (Q'.add_le_self_of_nonneg 1 w (Q'.le_of_lt hw0))
        (Q'.le_of_lt (cubicDeficit_positive hw1))) (Q'.ge_of_eqv he))

theorem denominator_le_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    slopeDenominator w ≤ 1 := by
  have hd0 := Q'.le_of_lt (HKPos.one_sub_pos hw1)
  have hd1 := sub_one_le_one (Q'.le_of_lt hw0)
  exact mul_le_one (Q'.mul_nonneg _ _ hd0 hd0) (mul_le_one hd0 hd1 hd1)
    (sub_one_le_one (Q'.mul_nonneg _ _ (Q'.le_of_lt hw0) (Q'.le_of_lt hw0)))

/-- The large constant is explicit and independent of nome; all nome cost
is displayed in the cubic deficit on the left. -/
theorem relativeCap_cubic_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    relativeCap w 2048 * cubicDeficit w ≤ 4097 := by
  have hpin : relativeCap w 2048 * slopeDenominator w ≈
      4096*w + slopeDenominator w := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.add (.mul (.const 2048) (.var 0)) (.const 1)) (.var 1))
      (.add (.mul (.const 2048) (.mul (.var 0) (.var 1))) (.var 1))
      (by decide) (fun | 0 => budget w | _ => slopeDenominator w))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left 2048 _ _ (budget_denominator_pin hw0 hw1)) (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.mul (.const 2048) (.add (.var 0) (.var 0))) (.var 1))
        (.add (.mul (.const 4096) (.var 0)) (.var 1)) (by decide)
        (fun | 0 => w | _ => slopeDenominator w)))
  have hc : 4096*w ≤ 4096 := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ 4096 (Q'.le_of_lt hw1) (by decide))
    (Q'.le_of_eqv (Q'.mul_one_eqv _))
  have hs := Q'.add_le_add hc (denominator_le_one hw0 hw1)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ (relativeCap w 2048)
      (denominator_ge_cubic hw0 hw1) (Q'.le_of_lt (relativeCap_positive hw0 (by decide))))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
      (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (by decide))))

theorem selectedScore_cubic_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    selectedScoreCap w * cubicDeficit w ≤ 24582 := by
  have h := Q'.mul_le_mul_of_nonneg_left _ _ 6
    (relativeCap_cubic_bound hw0 hw1) (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by decide)))

#print axioms cubicDeficit_positive
#print axioms cubicDeficit_le_one
#print axioms budget_denominator_pin
#print axioms denominator_ge_cubic
#print axioms denominator_le_one
#print axioms relativeCap_cubic_bound
#print axioms selectedScore_cubic_bound

end YMGap.Continuum.BF4RelativePredictionNomeBudget
