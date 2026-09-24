/-
# The six-face star-ratio witness cannot pay a nome-linear loss budget

The existing six-face local-star variance witness is a computed certificate
number.  The head-floor ceiling makes it at most `(1-w)^12`, hence at most
`1-w`.  Therefore subtracting any coefficient at least one times the
nome-linear absolute loss budget is nonpositive.

These are bounds on certificate numbers only.  They are not an upper bound on
an actual variance, nor a lower bound on actual time loss, and do not refute
physical survival or any Yang--Mills theory.
-/

import YMGap.Continuum.BF4ExactSlabHeadFloorNomeCeiling
import YMGap.Continuum.BF4ExactSlabLocalStarComparison

namespace YMGap.Continuum.BF4ExactSlabStarVarianceLossObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabHeadFloorNomeCeiling
open YMGap.Continuum.BF4ExactSlabLocalStarComparison

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

include hw0 hw1

/-- The six-face numerator is bounded by the sixth power of the quadratic
nome-defect ceiling.  This is a bound on the computed star-ratio numerator. -/
theorem starRatio_numerator_le_defect_power :
    lowerFactor w ≤ ((1 + -w) * (1 + -w)) ^ 6 := by
  exact HKConv.pow_le_pow_base (Q'.le_of_lt (localFloor_positive hw0 hw1))
    (Q'.le_trans' _ _ _ Q'.min_le_left (headFloor_le_nome_defect_square hw0 hw1)) 6

/-- The denominator is at least one, so the star ratio inherits the numerator
ceiling. -/
theorem starRatio_le_defect_power :
    starRatio w ≤ ((1 + -w) * (1 + -w)) ^ 6 := by
  apply HKConv.divPos_le_of_le (CReal.num_pos_of_pos (upperFactor_positive hw0))
  have hnum := starRatio_numerator_le_defect_power hw0 hw1
  have hden : (1 : Q') ≤ upperFactor w := by
    have h := HKConv.pow_le_pow_base Q'.zero_le_one (one_le_localCap hw0) 6
    exact Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ (1 : Q')^6) h
  have hd0 : (0 : Q') ≤ ((1 + -w) * (1 + -w)) ^ 6 :=
    Q'.pow_nonneg _
      (Q'.mul_nonneg _ _ (Q'.le_of_lt (HKPos.one_sub_pos hw1))
        (Q'.le_of_lt (HKPos.one_sub_pos hw1))) 6
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ _ hden hd0
  exact Q'.le_trans' _ _ _ hnum
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _)) hmul)

/-- The quadratic defect power is no larger than the nome defect itself. -/
theorem starRatio_le_nome_defect :
    starRatio w ≤ 1 + -w := by
  let d : Q' := 1 + -w
  have hd0 : (0 : Q') ≤ d := Q'.le_of_lt (HKPos.one_sub_pos hw1)
  have hd1 : d ≤ (1 : Q') := by
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (Q'.le_of_lt hw0)))
      (Q'.le_of_eqv (by decide : Q'.eqv ((1 : Q') + -0) 1))
  have hsq : d * d ≤ d := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hd1 hd0)
      (Q'.le_of_eqv (Q'.mul_one_eqv _))
  have hpow_mono : (d * d) ^ 6 ≤ d ^ 6 := by
    exact HKConv.pow_le_pow_base (Q'.mul_nonneg _ _ hd0 hd0) hsq 6
  have hpow : d ^ 6 ≤ d := by
    simpa only [show 6 = 5 + 1 by omega] using
      (HKPos.pow_succ_le_self hd0 hd1 5)
  have hdef : ((1 + -w) * (1 + -w)) ^ 6 ≤ d ^ 6 := by
    simpa only [d] using hpow_mono
  exact Q'.le_trans' _ _ _ (starRatio_le_defect_power hw0 hw1)
    (Q'.le_trans' _ _ _ hdef hpow)

/-- A coefficient at least one cannot turn this certificate pair into a
positive response by subtracting the nome-linear loss budget. -/
theorem starRatio_sub_mul_nome_defect_nonpositive {C : Q'} (hC : (1 : Q') ≤ C) :
    starRatio w + -(C * (1 + -w)) ≤ (0 : Q') := by
  have hd : (0 : Q') ≤ 1 + -w := Q'.le_of_lt (HKPos.one_sub_pos hw1)
  have hmul : 1 + -w ≤ C * (1 + -w) := by
    have h := Q'.mul_le_mul_of_nonneg_right _ _ _ hC hd
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _)) h
  have hsub : starRatio w ≤ C * (1 + -w) :=
    Q'.le_trans' _ _ _ (starRatio_le_nome_defect hw0 hw1) hmul
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ _ hsub)
    (Q'.le_of_eqv (Q'.add_neg_self_eqv _))

/-- For a four-edge plaquette, half the one-step increment budget is
192*(1-w). Subtracting that AVAILABLE upper budget from this AVAILABLE norm
floor never certifies a positive response. Actual response may be positive. -/
theorem plaquette_budget_nonpositive :
    starRatio w + -((192 : Q') * (1 + -w)) ≤ (0 : Q') :=
  starRatio_sub_mul_nome_defect_nonpositive hw0 hw1 (by decide)

end YMGap.Continuum.BF4ExactSlabStarVarianceLossObstruction

#print axioms YMGap.Continuum.BF4ExactSlabStarVarianceLossObstruction.starRatio_numerator_le_defect_power
#print axioms YMGap.Continuum.BF4ExactSlabStarVarianceLossObstruction.starRatio_le_defect_power
#print axioms YMGap.Continuum.BF4ExactSlabStarVarianceLossObstruction.starRatio_le_nome_defect
#print axioms YMGap.Continuum.BF4ExactSlabStarVarianceLossObstruction.starRatio_sub_mul_nome_defect_nonpositive
#print axioms YMGap.Continuum.BF4ExactSlabStarVarianceLossObstruction.plaquette_budget_nonpositive
