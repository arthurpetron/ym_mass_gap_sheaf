/-
# The existing shared-face absolute window cannot close a degree-two budget

For at least one common face, the current retained-head floor is at most
1/32 and the absolute prefix cap is at least one. Consequently the ratio
obtained solely by multiplying these pointwise windows is at most 1/32.
Even the improved formal two-block coefficient (1-ratio)/2 therefore
cannot meet the signed-neighbor budget at degree two or above.

This is an obstruction to this PARTICULAR floor-based scalar producer,
not a lower bound on the actual original conditional influence, a claim
about an SU(2)-specific cancellation, or a Yang--Mills no-go theorem.
-/

import YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound

namespace YMGap.Continuum.BF4ExactSlabSharedFloorBudgetObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
open YMGap.Continuum.BF4ExactSlabStarRateObstruction

private theorem cap_power_ge_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    ∀ s : Nat, (1 : Q') ≤ (prefixCap w)^s
  | 0 => Q'.le_refl' _
  | s + 1 => by
      have ih := cap_power_ge_one hw0 hw1 s
      have hc := prefixCap_ge_one hw0 hw1
      change (1 : Q') ≤ prefixCap w * (prefixCap w)^s
      have hstep : (1 : Q') * (prefixCap w)^s ≤
          prefixCap w * (prefixCap w)^s :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hc
          (Q'.pow_nonneg _ (Q'.le_trans' _ _ _ Q'.zero_le_one hc) s)
      exact Q'.le_trans' _ _ _ ih
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _)) hstep)

/-- The ratio of the ACTUAL named one-face floor/cap powers, with its
positive denominator retained as constructive data. -/
def sharedFloorRatio {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (sharedCount : Nat) : Q' :=
  Q'.divPos ((headFloor w)^sharedCount) ((prefixCap w)^sharedCount)
    (HKPos.pow_pos
      (Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
        (prefixCap_ge_one hw0 hw1)) sharedCount)

/-- One or more shared faces already force the floor-only ratio below 1/32.
This says nothing about the exact shared interaction or its cancellations. -/
theorem sharedFloorRatio_le_oneThirtySecond {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (sharedCount : Nat) (hshared : 1 ≤ sharedCount) :
    sharedFloorRatio hw0 hw1 sharedCount ≤ Q'.mkPos 1 32 (by decide) := by
  have hfloor0 : (0 : Q') ≤ headFloor w :=
    Q'.le_of_lt (headFloor_positive hw0 hw1)
  have hfloor1 : headFloor w ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (headFloor_le_oneThirtySecond hw0 hw1) (by decide)
  have hpow : (headFloor w)^sharedCount ≤ headFloor w := by
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hshared
    have h := HKConvGen.pow_base_antitone hfloor0 hfloor1
      (show 1 ≤ 1 + extra from Nat.le_add_right 1 extra)
    change (headFloor w)^(1+extra) ≤ headFloor w * 1 at h
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_one_eqv _))
  have hnum : (headFloor w)^sharedCount ≤ Q'.mkPos 1 32 (by decide) :=
    Q'.le_trans' _ _ _ hpow (headFloor_le_oneThirtySecond hw0 hw1)
  have hcap : (1 : Q') ≤ (prefixCap w)^sharedCount :=
    cap_power_ge_one hw0 hw1 sharedCount
  have hden : Q'.mkPos 1 32 (by decide) ≤
      Q'.mkPos 1 32 (by decide) * (prefixCap w)^sharedCount :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.mul_one_eqv _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hcap (by decide))
  unfold sharedFloorRatio
  exact Q'.divPos_le_of_le_mul _ _ _
    (Q'.le_trans' _ _ _ hnum hden)

/-- The scalar coefficient appearing after the proposed product-reference
two-block Efron--Stein comparison: `2*degree*eta` for
`eta=(1-sharedFloorRatio)/2`. This definition does NOT assert that the
corresponding original-action block estimate has been proved. -/
def degreeBudget {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (sharedCount degree : Nat) : Q' :=
  Q'.ofNat degree * (1 + -sharedFloorRatio hw0 hw1 sharedCount)

/-- With at least one shared face, the existing floor/cap constants make
the proposed signed-neighbor scalar margin nonpositive for degree >= 2. -/
theorem not_degreeBudget_lt_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (sharedCount degree : Nat) (hshared : 1 ≤ sharedCount)
    (hdegree : 2 ≤ degree) :
    ¬ (degreeBudget hw0 hw1 sharedCount degree < (1 : Q')) := by
  have hr := sharedFloorRatio_le_oneThirtySecond hw0 hw1 sharedCount hshared
  have hrem : Q'.mkPos 31 32 (by decide) ≤
      (1 : Q') + -sharedFloorRatio hw0 hw1 sharedCount :=
    Q'.le_trans' _ _ _ (by decide)
      (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hr))
  have hd : (2 : Q') ≤ Q'.ofNat degree := CReal.ofNat_le_ofNat hdegree
  have hd0 : (0 : Q') ≤ Q'.ofNat degree :=
    Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 2) hd
  have hbudget : (1 : Q') ≤ degreeBudget hw0 hw1 sharedCount degree := by
    unfold degreeBudget
    exact Q'.le_trans' _ _ _
      (by decide : (1 : Q') ≤ (2 : Q') * Q'.mkPos 31 32 (by decide))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hd (by decide))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hrem hd0))
  exact Int.not_lt.mpr hbudget

#print axioms sharedFloorRatio
#print axioms sharedFloorRatio_le_oneThirtySecond
#print axioms degreeBudget
#print axioms not_degreeBudget_lt_one

end YMGap.Continuum.BF4ExactSlabSharedFloorBudgetObstruction
