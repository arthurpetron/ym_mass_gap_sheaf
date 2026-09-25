import YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction
import YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTwoStepRateWidthObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialRateWidthObstruction
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap

local infix:50 " ≈ " => Q'.eqv

private theorem lt_of_add_neg_pos {a b : Q'} (h : (0 : Q') < a + -b) : b < a := by
  apply Int.lt_of_not_ge
  intro hba
  have hneg : -b ≤ -a := Q'.neg_le_neg hba
  have hsum : a + -b ≤ a + -a := Q'.add_le_add_left a (-b) (-a) hneg
  have hzero : a + -a ≤ (0 : Q') :=
    Q'.le_of_eqv (Q'.add_neg_self_eqv a)
  exact Int.not_lt.mpr (Q'.le_trans' _ _ _ hsum hzero) h

private theorem add_one_lt_two {q : Q'} (hq : q < (1 : Q')) :
    (1 : Q') + q < (2 : Q') := by
  show ((1 : Q') + q).num * ((2 : Q').den : Int) <
    (2 : Q').num * (((1 : Q') + q).den : Int)
  rw [Q'.add_den_cast]
  change ((1 : Int) * (q.den : Int) + q.num * (1 : Int)) * (1 : Int) <
    (2 : Int) * ((1 : Int) * (q.den : Int))
  simp only [Int.one_mul, Int.mul_one]
  have hq0 : q.num * (1 : Int) < (1 : Int) * (q.den : Int) := hq
  have hq' : q.num < (q.den : Int) := by simpa using hq0
  omega

private theorem midpoint_lt_one {q : Q'} (hq : q < (1 : Q')) :
    HalfPow.half * ((1 : Q') + q) < (1 : Q') := by
  have hmid : HalfPow.half * ((1 : Q') + q) <
      HalfPow.half * (2 : Q') :=
    Q'.mul_lt_mul_of_pos_left (by decide) (add_one_lt_two hq)
  exact ClusteringImpliesGap.lt_of_lt_of_le hmid
    (Q'.le_of_eqv (Q'.eqv_symm (by decide :
      (HalfPow.half * (2 : Q')).eqv (1 : Q'))))

private theorem midpoint_sq_gt {q : Q'}
    (hq1 : q < (1 : Q')) :
    q < (HalfPow.half * ((1 : Q') + q)) *
      (HalfPow.half * ((1 : Q') + q)) := by
  let lhs : RingNormaliser.PolyExpr :=
    .mul (.add (.const 1) (.var 0)) (.add (.const 1) (.var 0))
  let rhs : RingNormaliser.PolyExpr :=
    .add
      (.mul (.add (.const 1) (.neg (.var 0)))
        (.add (.const 1) (.neg (.var 0))))
      (.mul (.const 4) (.var 0))
  have hpoly := RingNormaliser.poly_identity_of_normal_eq lhs rhs (by decide)
    (fun _ => q)
  change (((1 : Q') + q) * ((1 : Q') + q)).eqv
      (((1 : Q') + -q) * ((1 : Q') + -q) + (4 : Q') * q) at hpoly
  have hh4 : ((HalfPow.half * HalfPow.half) * (4 : Q')).eqv 1 := by decide
  have hsq :
      ((HalfPow.half * ((1 : Q') + q)) *
        (HalfPow.half * ((1 : Q') + q))).eqv
      ((HalfPow.half * HalfPow.half) *
        (((1 : Q') + q) * ((1 : Q') + q))) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left HalfPow.half _ _
        (ClusteringImpliesGap.mul_comm_assoc _ _ _)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  have hdecomp0 :
      ((HalfPow.half * HalfPow.half) *
        (((1 : Q') + q) * ((1 : Q') + q))).eqv
      ((HalfPow.half * HalfPow.half) *
        (((1 : Q') + -q) * ((1 : Q') + -q) + (4 : Q') * q)) :=
    Q'.mul_eqv_congr_left (HalfPow.half * HalfPow.half) _ _ hpoly
  have hsplit :
      (((HalfPow.half * HalfPow.half) *
        (((1 : Q') + -q) * ((1 : Q') + -q) + (4 : Q') * q))).eqv
      (((HalfPow.half * HalfPow.half) *
        ((1 : Q') + -q) * ((1 : Q') + -q)) + q) := by
    have hfourq :
        ((HalfPow.half * HalfPow.half) * ((4 : Q') * q)).eqv q := by
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (HalfPow.half * HalfPow.half * (4 : Q'))
          1 q hh4) ?_
      exact Q'.one_mul_eqv q
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _) ?_
    exact ClusteringImpliesGap.add_eqv_both
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) hfourq
  have hdecomp :
      ((HalfPow.half * ((1 : Q') + q)) *
        (HalfPow.half * ((1 : Q') + q)) + -q).eqv
      ((HalfPow.half * HalfPow.half) *
        ((1 : Q') + -q) * ((1 : Q') + -q)) := by
    have hsqAdd := Q'.add_eqv_congr_right _ _ (-q) hsq
    have hdecomp0Add := Q'.add_eqv_congr_right _ _ (-q) hdecomp0
    have hsplitAdd := Q'.add_eqv_congr_right _ _ (-q) hsplit
    have hcancel :
        (((HalfPow.half * HalfPow.half) *
          ((1 : Q') + -q) * ((1 : Q') + -q) + q) + -q).eqv
          ((HalfPow.half * HalfPow.half) *
            ((1 : Q') + -q) * ((1 : Q') + -q)) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv q)) ?_
      rw [Q'.add_zero']
      exact Q'.eqv_refl _
    refine Q'.eqv_trans _ _ _ hsqAdd ?_
    refine Q'.eqv_trans _ _ _ hdecomp0Add ?_
    exact Q'.eqv_trans _ _ _ hsplitAdd hcancel
  have hdiff : (0 : Q') < (1 : Q') + -q :=
    ClusteringImpliesGap.sub_pos_of_lt hq1
  have hpositive : (0 : Q') <
      (HalfPow.half * HalfPow.half) *
        ((1 : Q') + -q) * ((1 : Q') + -q) := by
    exact Q'.mul_pos (Q'.mul_pos (Q'.mul_pos (by decide) (by decide)) hdiff) hdiff
  have hgap : (0 : Q') <
      (HalfPow.half * ((1 : Q') + q)) *
        (HalfPow.half * ((1 : Q') + q)) + -q :=
    ClusteringImpliesGap.lt_of_lt_of_le hpositive (Q'.ge_of_eqv hdecomp)
  exact lt_of_add_neg_pos hgap

/-- The computed two-step rate has no positive width-uniform contraction
constant below one.  This only obstructs promotion of the existing
`mixRate^2` certificate; it is not a statement about the actual transfer
operator or about Yang--Mills itself. -/
theorem no_width_uniform_computed_twoStepRate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (q : Q') (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q')) :
    ¬ (∀ width, 0 < width → twoStepRate hw0 hw1 width ≤ q) := by
  intro hbound
  let r : Q' := HalfPow.half * ((1 : Q') + q)
  have hr1 : r < (1 : Q') := by
    exact midpoint_lt_one hq1
  have hrpos : (0 : Q') < r := by
    exact Q'.mul_pos (by decide) (Q'.pos_add_nonneg (by decide) hq0)
  have hmix : r < mixRate hw0 hw1 (violatingWidth r) := by
    apply Int.lt_of_not_ge
    exact rate_not_le_at_violatingWidth hw0 hw1 r hr1
  have hmixpos : (0 : Q') < mixRate hw0 hw1 (violatingWidth r) :=
    ClusteringImpliesGap.lt_of_lt_of_le hrpos (Q'.le_of_lt hmix)
  have hrr : q < r * r := by
    exact midpoint_sq_gt hq1
  have hleft : r * r <
      mixRate hw0 hw1 (violatingWidth r) * r :=
    ClusteringImpliesGap.mul_lt_mul_of_pos_right hrpos hmix
  have hright :
      mixRate hw0 hw1 (violatingWidth r) * r <
        mixRate hw0 hw1 (violatingWidth r) *
          mixRate hw0 hw1 (violatingWidth r) :=
    Q'.mul_lt_mul_of_pos_left hmixpos hmix
  have htwo : q < twoStepRate hw0 hw1 (violatingWidth r) := by
    have hsq : r * r < twoStepRate hw0 hw1 (violatingWidth r) := by
      exact ClusteringImpliesGap.lt_of_lt_of_le hleft (Q'.le_of_lt hright)
    exact ClusteringImpliesGap.lt_of_lt_of_le hrr (Q'.le_of_lt hsq)
  exact Int.not_lt.mpr
    (hbound (violatingWidth r) (Nat.succ_pos _)) htwo

end YMGap.Continuum.BF4ExactSlabFixedSpatialTwoStepRateWidthObstruction

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTwoStepRateWidthObstruction.no_width_uniform_computed_twoStepRate
