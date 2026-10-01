/-
The current explicit quartic response BUDGET has an unavoidable quadratic
head. This is a limitation of this upper-bound formula, not a lower bound
on the original heat moment or on any Yang--Mills state.
-/

import YMGap.Continuum.SU2QuaternionHeatQuarticBound
import YMGap.Constructive.CubeRoot

namespace YMGap.Continuum.SU2HeatQuarticBudgetFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.SU2QuaternionHeatQuarticBound (quarticBudget)
open YMGap.Continuum.SU2HeatQuarticBulkCoefficient (relativeBudget)
open YMGap.Continuum.RGTransport (qpow qpow_nonneg)

local infix:50 " ≈ " => Q'.eqv

/-- The explicit head and tail are nonnegative, so optimizing the split
cannot remove the displayed quadratic term from this particular budget. -/
theorem budget_floor {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (S : Nat) :
    296*((1 + -w)*(1 + -w)) ≤ quarticBudget w S := by
  let h := 1 + -w
  let n := Q'.ofNat (S+2)
  let head := 32*((n*n)*(n*n))*((h*h)*(h*h))
  let tail := 80*Q'.ofNat (S^3)*qpow w (S*S)
  have hh : (0 : Q') ≤ h := Q'.sub_nonneg_of_le hw1
  have hn : (0 : Q') ≤ n := Q'.ofNat_nonneg _
  have hnn : (0 : Q') ≤ n*n := Q'.mul_nonneg _ _ hn hn
  have hhh : (0 : Q') ≤ h*h := Q'.mul_nonneg _ _ hh hh
  have hhead : (0 : Q') ≤ head :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hnn hnn))
      (Q'.mul_nonneg _ _ hhh hhh)
  have htail : (0 : Q') ≤ tail :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide) (Q'.ofNat_nonneg _))
      (qpow_nonneg w hw0 _)
  change 296*(h*h) ≤ (head + 296*(h*h)) + tail
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (296*(h*h)) head hhead)
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
    (Q'.add_le_self_of_nonneg _ tail htail)

/-- If C*h < 296 at a positive nome defect h, the displayed quartic
budget cannot obey C*h^3, regardless of the split S. No claim is made
about the true original quartic moment. -/
theorem not_cubic_budget {w C : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hh : (0 : Q') < 1 + -w)
    (hC : C*(1 + -w) < 296) (S : Nat) :
    ¬ quarticBudget w S ≤ C*(((1 + -w)*(1 + -w))*(1 + -w)) := by
  let h := 1 + -w
  have hsq : (0 : Q') < h*h := Q'.mul_pos hh hh
  have hp : C*((h*h)*h) ≈ (h*h)*(C*h) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 1)))
      (.mul (.mul (.var 1) (.var 1)) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => C | _ => h)
  have hs : C*((h*h)*h) < (h*h)*296 :=
    Q'.lt_of_le_of_lt (Q'.le_of_eqv hp)
      (Q'.mul_lt_mul_of_pos_left hsq hC)
  have hf : (h*h)*296 ≤ quarticBudget w S :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (budget_floor hw0 hw1 S)
  intro hb
  exact Int.lt_irrefl _
    (Q'.lt_of_le_of_lt (Q'.le_trans' _ _ _ hf hb) hs)

#print axioms budget_floor
#print axioms not_cubic_budget

end YMGap.Continuum.SU2HeatQuarticBudgetFloor
