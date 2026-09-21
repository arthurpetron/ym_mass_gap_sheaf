/-
# Cubic scalar budget for SU(2) character derivatives

This is only the rational arithmetic needed by the polynomial interval
consumer.  The two-step recurrence pays the sharp character cap
`2*(n+2)^2` and remains below the explicit cubic budget.  No derivative,
Haar, heat-kernel, or continuum estimate is asserted here.
-/

import YMGap.Continuum.HeatKernelRGStep
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2CharacterDerivativeCubicBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- A deliberately loose cubic cap for the derivative-character recurrence. -/
def cubicBudget (n : Nat) : Q' :=
  2 * (Q'.ofNat (n+1) * Q'.ofNat (n+1) * Q'.ofNat (n+1))

theorem cubicBudget_nonnegative (n : Nat) : (0 : Q') ≤ cubicBudget n := by
  exact Q'.mul_nonneg _ _ (by decide)
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (zero_le_ofNat _) (zero_le_ofNat _))
      (zero_le_ofNat _))

theorem zero_le_cubicBudget_zero : (0 : Q') ≤ cubicBudget 0 :=
  cubicBudget_nonnegative 0

theorem two_le_cubicBudget_one : (2 : Q') ≤ cubicBudget 1 := by
  decide

private theorem square_congr {a b : Q'} (h : a ≈ b) : a*a ≈ b*b :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ h)

private theorem cube_congr {a b : Q'} (h : a ≈ b) : (a*a)*a ≈ (b*b)*b :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (square_congr h))
    (Q'.mul_eqv_congr_left _ _ _ h)

private theorem cubic_step_scalar (a b c : Q') (ha : (0 : Q') ≤ a)
    (hb : b ≈ a+1) (hc : c ≈ a+2) :
    2*(a*a*a) + 2*(b*b) ≤ 2*(c*c*c) := by
  have hb2 : b*b ≈ (a+1)*(a+1) := square_congr hb
  have hc3 : c*c*c ≈ (a+2)*(a+2)*(a+2) := cube_congr hc
  have hleft : 2*(a*a*a) + 2*(b*b) ≈
      2*(a*a*a) + 2*((a+1)*(a+1)) :=
    Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_left 2 _ _ hb2)
  have hright : 2*(c*c*c) ≈ 2*((a+2)*(a+2)*(a+2)) :=
    Q'.mul_eqv_congr_left 2 _ _ hc3
  have hpositive : (0 : Q') ≤ 2*(5*(a*a) + 10*a + 7) := by
    exact Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _
        (Q'.zero_le_add _ _
          (Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ ha ha))
          (Q'.mul_nonneg _ _ (by decide) ha))
        (by decide))
  have hdiff :
      2*((a+2)*(a+2)*(a+2)) +
          -(2*(a*a*a) + 2*((a+1)*(a+1))) ≈
        2*(5*(a*a) + 10*a + 7) := by
    exact poly_identity_of_normal_eq
      (.add
        (.mul (.const 2)
          (.mul
            (.mul (.add (.var 0) (.const 2)) (.add (.var 0) (.const 2)))
            (.add (.var 0) (.const 2))))
        (.neg
          (.add
            (.mul (.const 2) (.mul (.mul (.var 0) (.var 0)) (.var 0)))
            (.mul (.const 2)
              (.mul (.add (.var 0) (.const 1)) (.add (.var 0) (.const 1)))))))
      (.mul (.const 2)
        (.add
          (.add (.mul (.const 5) (.mul (.var 0) (.var 0)))
            (.mul (.const 10) (.var 0)))
          (.const 7)))
      (by decide) (fun _ => a)
  have hmiddle : 2*(a*a*a) + 2*((a+1)*(a+1)) ≤
      2*((a+2)*(a+2)*(a+2)) :=
    Q'.le_of_sub_nonneg
      (Q'.le_trans' _ _ _ hpositive (Q'.ge_of_eqv hdiff))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hmiddle (Q'.ge_of_eqv hright))

/-- The two-step derivative-character payment fits inside the cubic cap. -/
theorem cubicBudget_step (n : Nat) :
    cubicBudget n + 2 * (Q'.ofNat (n+2) * Q'.ofNat (n+2)) ≤
      cubicBudget (n+2) := by
  let a := Q'.ofNat (n+1)
  have hb : Q'.ofNat (n+2) ≈ a+1 := by
    simpa only [a, Nat.add_assoc] using Q'.ofNat_add_eqv (n+1) 1
  have hc : Q'.ofNat (n+2+1) ≈ a+2 := by
    simpa only [a, Nat.add_assoc] using Q'.ofNat_add_eqv (n+1) 2
  exact cubic_step_scalar a (Q'.ofNat (n+2)) (Q'.ofNat (n+2+1))
    (zero_le_ofNat _) hb hc

end YMGap.Continuum.SU2CharacterDerivativeCubicBudget

#print axioms YMGap.Continuum.SU2CharacterDerivativeCubicBudget.cubicBudget
#print axioms YMGap.Continuum.SU2CharacterDerivativeCubicBudget.cubicBudget_nonnegative
#print axioms YMGap.Continuum.SU2CharacterDerivativeCubicBudget.zero_le_cubicBudget_zero
#print axioms YMGap.Continuum.SU2CharacterDerivativeCubicBudget.two_le_cubicBudget_one
#print axioms YMGap.Continuum.SU2CharacterDerivativeCubicBudget.cubicBudget_step
