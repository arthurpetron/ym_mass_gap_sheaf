/-
# The existing response collar cost cannot absorb a cubic activity per core face

The literal incidence budget grows by 24 collar faces per added anchor.
Its two OLD and two NEW partition floors therefore lose 96 powers of
headFloor(w). We keep the reciprocals exact and clear them before comparison.
For w >= 1/32, even an additional w^3 per anchor cannot make this displayed
termwise scalar bound decrease.

This is an obstruction to that proposed MAJORANT, not a lower bound on any
original coefficient, a divergence theorem for the signed response, or a
Yang--Mills counterexample. The existing response_activity extracts only one
global w^3; it does not prove the hypothetical per-anchor coefficient bound.
Sharper normalization or cancellations across terms are not ruled out.
-/

import YMGap.Continuum.BF4ExactSlabResponseCollarNormalization

namespace YMGap.Continuum.BF4ExactSlabResponseCollarCostObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabResponseCollarNormalization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.ClusterCount4DProgress

local infix:50 " ≈ " => Q'.eqv
local instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h k := Q'.eqv_trans _ _ _ h k

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

/-- Exact exponent in the existing four-partition floor. -/
theorem collarFloor_power (w : Q') (count : Nat) :
    collarFloor w count ≈ (headFloor w)^(4*count+2) := by
  let h := headFloor w
  calc
    collarFloor w count ≈ h^(count+count)*h^((count+1)+(count+1)) :=
      qmul (Q'.eqv_symm (Q'.pow_add_eqv h count count))
        (Q'.eqv_symm (Q'.pow_add_eqv h (count+1) (count+1)))
    _ ≈ h^((count+count)+((count+1)+(count+1))) :=
      Q'.eqv_symm (Q'.pow_add_eqv h _ _)
    _ ≈ h^(4*count+2) := by
      rw [show (count+count)+((count+1)+(count+1)) = 4*count+2 by omega]
      exact Q'.eqv_refl _

theorem collarCount_cons (roots : List Z4Link) (anchor : List Nat) (id : Nat) :
    collarCount roots (id::anchor) = collarCount roots anchor + 24 := by
  unfold collarCount
  simp only [List.length_cons]
  omega

/-- This step is the cost actually charged by the bounded incidence budget. -/
theorem collarFloor_step (w : Q') (count : Nat) :
    collarFloor w (count+24) ≈ collarFloor w count * (headFloor w)^96 := by
  calc
    collarFloor w (count+24) ≈ (headFloor w)^(4*(count+24)+2) := collarFloor_power w _
    _ ≈ (headFloor w)^((4*count+2)+96) := by
      rw [show 4*(count+24)+2 = (4*count+2)+96 by omega]
      exact Q'.eqv_refl _
    _ ≈ (headFloor w)^(4*count+2)*(headFloor w)^96 := Q'.pow_add_eqv _ _ _
    _ ≈ collarFloor w count * (headFloor w)^96 :=
      Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (collarFloor_power w count))

/-- The old cost times the next floor cancels to exactly h^96. -/
theorem oldCost_nextFloor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (count : Nat) :
    collarCost w hw0 hw1 count * collarFloor w (count+24) ≈ (headFloor w)^96 := by
  calc
    _ ≈ collarCost w hw0 hw1 count * (collarFloor w count * (headFloor w)^96) :=
      Q'.mul_eqv_congr_left _ _ _ (collarFloor_step w count)
    _ ≈ (collarCost w hw0 hw1 count * collarFloor w count) * (headFloor w)^96 :=
      Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    _ ≈ (1 : Q') * (headFloor w)^96 :=
      Q'.mul_eqv_congr_right _ _ _ (collarCost_cancellation hw0 hw1 count)
    _ ≈ (headFloor w)^96 := Q'.one_mul_eqv _

/-- Any proposed nonincreasing one-anchor scalar estimate must pay h^96.
No claim that the coefficient of the original response equals a is made. -/
theorem activity_le_floor_of_nonincrease {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (count : Nat) (a : Q')
    (h : a * collarCost w hw0 hw1 (count+24) ≤ collarCost w hw0 hw1 count) :
    a ≤ (headFloor w)^96 := by
  have he : (a * collarCost w hw0 hw1 (count+24))*collarFloor w (count+24) ≈ a :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (collarCost_cancellation hw0 hw1 _))
        (Q'.mul_one_eqv a))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ h (Q'.le_of_lt (collarFloor_positive hw0 hw1 _)))
      (Q'.le_of_eqv (oldCost_nextFloor hw0 hw1 count)))

private theorem pow_mono {x y : Q'} (hx : (0 : Q') ≤ x) (hxy : x ≤ y) :
    ∀ n : Nat, x^n ≤ y^n
  | 0 => Q'.le_refl' 1
  | n+1 => Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hxy (Q'.pow_nonneg x hx n))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (pow_mono hx hxy n)
        (Q'.le_trans' _ _ _ hx hxy))

/-- A small fixed rational check suffices; h^96 itself is never expanded. -/
theorem no_cubic_cost_nonincrease {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hw : Q'.mkPos 1 32 (by decide) ≤ w) (count : Nat) :
    ¬ (w^3 * collarCost w hw0 hw1 (count+24) ≤ collarCost w hw0 hw1 count) := by
  intro h
  let s : Q' := Q'.mkPos 1 32 (by decide)
  have hs : headFloor w ≤ s := headFloor_le_oneThirtySecond hw0 hw1
  have h0 := Q'.le_of_lt (headFloor_positive hw0 hw1)
  have hh : (headFloor w)^96 ≤ s^4 :=
    Q'.le_trans' _ _ _ (HKConvGen.pow_base_antitone h0
      (Q'.le_trans' _ _ _ hs (by decide : s ≤ (1 : Q'))) (by decide : 4 ≤ 96))
      (pow_mono h0 hs 4)
  have hbad : s^3 ≤ s^4 := Q'.le_trans' _ _ _ (pow_mono (by decide : (0 : Q') ≤ s) hw 3)
    (Q'.le_trans' _ _ _ (activity_le_floor_of_nonincrease hw0 hw1 count (w^3) h) hh)
  exact (by decide : ¬ (s^3 ≤ s^4)) hbad

/-- Specialization to the literal root/core incidence formula. -/
theorem no_cubic_anchor_cost_nonincrease {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hw : Q'.mkPos 1 32 (by decide) ≤ w)
    (roots : List Z4Link) (anchor : List Nat) (id : Nat) :
    ¬ (w^3 * collarCost w hw0 hw1 (collarCount roots (id::anchor)) ≤
      collarCost w hw0 hw1 (collarCount roots anchor)) := by
  rw [collarCount_cons]
  exact no_cubic_cost_nonincrease hw0 hw1 hw _

end YMGap.Continuum.BF4ExactSlabResponseCollarCostObstruction

#print axioms YMGap.Continuum.BF4ExactSlabResponseCollarCostObstruction.collarFloor_power
#print axioms YMGap.Continuum.BF4ExactSlabResponseCollarCostObstruction.collarCount_cons
#print axioms YMGap.Continuum.BF4ExactSlabResponseCollarCostObstruction.collarFloor_step
#print axioms YMGap.Continuum.BF4ExactSlabResponseCollarCostObstruction.oldCost_nextFloor
#print axioms YMGap.Continuum.BF4ExactSlabResponseCollarCostObstruction.activity_le_floor_of_nonincrease
#print axioms YMGap.Continuum.BF4ExactSlabResponseCollarCostObstruction.no_cubic_cost_nonincrease
#print axioms YMGap.Continuum.BF4ExactSlabResponseCollarCostObstruction.no_cubic_anchor_cost_nonincrease
