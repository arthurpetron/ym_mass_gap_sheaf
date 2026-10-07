/-
An explicit rational upper fourth root for an RG two-step norm factor.

For `0 ≤ α ≤ 1`, `explicitRate α = (3+α)/4` satisfies `α ≤ explicitRate α ^ 4`
and has the exact margin `(1-α)/4`. This supplies a usable contraction rate
without selecting an exact rational root. It does not construct an RG map,
an AF estimate, or the older rate relation with the opposite fourth-power
inequality.
-/

import YMGap.Continuum.BF4WilsonAllNomeExprStepRatioWindowSurvival

namespace YMGap.Continuum.RGExplicitRationalRate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeExprStepRatioWindowSurvival (bernoulli_pow)

local infix:50 " ≈ " => Q'.eqv

/-- The exact rational `1/4`. -/
def quarter : Q' := ⟨1, 3⟩

theorem quarter_nonnegative : (0 : Q') ≤ quarter := by decide

theorem four_mul_quarter : (4 : Q') * quarter ≈ (1 : Q') := by decide

/-- A rational upper fourth root with a controlled margin. -/
def explicitRate (α : Q') : Q' := quarter * ((3 : Q') + α)

theorem rate_nonnegative (α : Q') (h0 : (0 : Q') ≤ α) :
    (0 : Q') ≤ explicitRate α := by
  have hs : (0 : Q') ≤ (3 : Q') + α :=
    Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ (3 : Q') + 0)
      (Q'.add_le_add_left 3 0 α h0)
  exact Q'.mul_nonneg _ _ quarter_nonnegative hs

theorem rate_le_one (α : Q') (h1 : α ≤ (1 : Q')) : explicitRate α ≤ 1 := by
  have hs : (3 : Q') + α ≤ (4 : Q') :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_left 3 α 1 h1) (by decide)
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ quarter hs quarter_nonnegative
  exact Q'.le_trans' _ _ _ hm (by decide : quarter * (4 : Q') ≤ 1)

theorem rate_lt_one (α : Q') (h1 : α < (1 : Q')) : explicitRate α < 1 := by
  have hn : α.num < (α.den : Int) := by
    have h : α.num * (1 : Int) < (1 : Int) * (α.den : Int) := h1
    simpa only [Int.mul_one, Int.one_mul] using h
  have hs : (3 : Q') + α < (4 : Q') := by
    have hd : (((3 : Q') + α).den : Int) = (α.den : Int) := by
      exact (Q'.add_den_cast (3 : Q') α).trans (Int.one_mul (α.den : Int))
    change ((3 : Q') + α).num * (1 : Int) < (4 : Int) * (((3 : Q') + α).den : Int)
    rw [hd]
    change ((3 : Int) * (α.den : Int) + α.num * 1) * 1 < 4 * (α.den : Int)
    simp only [Int.mul_one]
    omega
  have hm : explicitRate α < quarter * (4 : Q') :=
    Q'.mul_lt_mul_of_pos_left (by decide : (0 : Q') < quarter) hs
  exact YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le hm
    (by decide : quarter * (4 : Q') ≤ 1)

theorem rate_margin_positive (α : Q') (h1 : α < (1 : Q')) :
    (0 : Q') < (1 : Q') - explicitRate α :=
  YMGap.Continuum.HKPos.one_sub_pos (rate_lt_one α h1)

theorem four_mul_rate (α : Q') : (4 : Q') * explicitRate α ≈ (3 : Q') + α := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv 4 quarter (3 + α)))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (3 + α) four_mul_quarter)
      (Q'.one_mul_eqv (3 + α)))

/-- The exact margin; the reciprocal is a concrete rational, not a polynomial
normalizer assumption about an arbitrary variable. -/
theorem rate_margin (α : Q') :
    (1 : Q') - explicitRate α ≈ quarter * ((1 : Q') - α) := by
  have he : (1 : Q') - explicitRate α ≈
      ((1 : Q') - 4 * quarter) + quarter * ((1 : Q') - α) :=
    poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.mul (.var 0) (.add (.const 3) (.var 1)))))
      (.add (.add (.const 1) (.neg (.mul (.const 4) (.var 0))))
        (.mul (.var 0) (.add (.const 1) (.neg (.var 1)))))
      (by decide) (fun | 0 => quarter | _ => α)
  have hz : (1 : Q') - 4 * quarter ≈ (0 : Q') := by decide
  exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (quarter * (1 - α)) hz)
    (by rw [Q'.zero_add']; exact Q'.eqv_refl _))

private theorem bernoulli_left (α : Q') :
    (1 : Q') - Q'.ofNat 4 * ((1 : Q') - explicitRate α) ≈ α := by
  have he : (1 : Q') - Q'.ofNat 4 * ((1 : Q') - explicitRate α) ≈
      4 * explicitRate α + -(3 : Q') :=
    poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.mul (.const 4) (.add (.const 1) (.neg (.var 0))))))
      (.add (.mul (.const 4) (.var 0)) (.neg (.const 3)))
      (by decide) (fun _ => explicitRate α)
  have hc : ((3 : Q') + α) + -(3 : Q') ≈ α :=
    poly_identity_of_normal_eq
      (.add (.add (.const 3) (.var 0)) (.neg (.const 3))) (.var 0)
      (by decide) (fun _ => α)
  exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-3) (four_mul_rate α)) hc)

/-- Bernoulli gives an upper fourth root, in the direction needed to turn a
two-step norm factor into a one-step contraction rate. -/
theorem factor_le_rate_fourth (α : Q') (h0 : (0 : Q') ≤ α) (h1 : α ≤ (1 : Q')) :
    α ≤ explicitRate α * explicitRate α * (explicitRate α * explicitRate α) := by
  have hb := bernoulli_pow (explicitRate α) (rate_nonnegative α h0) (rate_le_one α h1) 4
  have hp : explicitRate α ^ 4 ≈
      explicitRate α * explicitRate α * (explicitRate α * explicitRate α) := by
    change (explicitRate α * (explicitRate α * (explicitRate α * (explicitRate α * 1)))) ≈ _
    exact poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.const 1)))))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0)))
      (by decide) (fun _ => explicitRate α)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (bernoulli_left α))
    (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv hp))

end YMGap.Continuum.RGExplicitRationalRate

#print axioms YMGap.Continuum.RGExplicitRationalRate.rate_nonnegative
#print axioms YMGap.Continuum.RGExplicitRationalRate.rate_le_one
#print axioms YMGap.Continuum.RGExplicitRationalRate.rate_lt_one
#print axioms YMGap.Continuum.RGExplicitRationalRate.rate_margin_positive
#print axioms YMGap.Continuum.RGExplicitRationalRate.rate_margin
#print axioms YMGap.Continuum.RGExplicitRationalRate.factor_le_rate_fourth
