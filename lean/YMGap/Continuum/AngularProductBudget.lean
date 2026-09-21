/-
# Scalar budgets for iterated angular product bounds

This file records only the rational recurrences needed to combine finitely
many value and angular-derivative intervals.  It has no polynomial, Haar,
action, or analytic content.
-/

import YMGap.Continuum.HeatKernelRGStep

namespace YMGap.Continuum.AngularProductBudget

set_option autoImplicit false

open YMGap.Constructive

/-- Value cap after multiplying `n` factors of cap `B`. -/
def valueBudget (B : Q') : Nat → Q'
  | 0 => 1
  | n + 1 => B * valueBudget B n

/-- Leibniz cap after multiplying `n` factors, each with value cap `B` and
derivative cap `C`. -/
def derivativeBudget (B C : Q') : Nat → Q'
  | 0 => 0
  | n + 1 => C * valueBudget B n + B * derivativeBudget B C n

private theorem value_nonnegative_of_nonnegative {B : Q'}
    (hB : (0 : Q') ≤ B) : ∀ n, (0 : Q') ≤ valueBudget B n
  | 0 => Q'.zero_le_one
  | n + 1 => Q'.mul_nonneg _ _ hB (value_nonnegative_of_nonnegative hB n)

private theorem derivative_nonnegative_of_nonnegative {B C : Q'}
    (hB : (0 : Q') ≤ B) (hC : (0 : Q') ≤ C) :
    ∀ n, (0 : Q') ≤ derivativeBudget B C n
  | 0 => Q'.le_refl' 0
  | n + 1 =>
      Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ hC (value_nonnegative_of_nonnegative hB n))
        (Q'.mul_nonneg _ _ hB (derivative_nonnegative_of_nonnegative hB hC n))

/-- The value budget is nonnegative under the monotonicity guard `1 ≤ B`. -/
theorem valueBudget_nonnegative {B : Q'} (hB : (1 : Q') ≤ B) (n : Nat) :
    (0 : Q') ≤ valueBudget B n :=
  value_nonnegative_of_nonnegative (Q'.le_trans' _ _ _ Q'.zero_le_one hB) n

/-- The derivative budget is nonnegative under `1 ≤ B` and `0 ≤ C`. -/
theorem derivativeBudget_nonnegative {B C : Q'}
    (hB : (1 : Q') ≤ B) (hC : (0 : Q') ≤ C) (n : Nat) :
    (0 : Q') ≤ derivativeBudget B C n :=
  derivative_nonnegative_of_nonnegative
    (Q'.le_trans' _ _ _ Q'.zero_le_one hB) hC n

private theorem value_step_le {B : Q'} (hB : (1 : Q') ≤ B) (n : Nat) :
    valueBudget B n ≤ valueBudget B (n + 1) := by
  change valueBudget B n ≤ B * valueBudget B n
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv (valueBudget B n)))
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hB (valueBudget_nonnegative hB n))

private theorem derivative_step_le {B C : Q'}
    (hB : (1 : Q') ≤ B) (hC : (0 : Q') ≤ C) (n : Nat) :
    derivativeBudget B C n ≤ derivativeBudget B C (n + 1) := by
  change derivativeBudget B C n ≤
    C * valueBudget B n + B * derivativeBudget B C n
  have hscale : derivativeBudget B C n ≤ B * derivativeBudget B C n :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.one_mul_eqv (derivativeBudget B C n)))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hB
        (derivativeBudget_nonnegative hB hC n))
  have hterm : (0 : Q') ≤ C * valueBudget B n :=
    Q'.mul_nonneg _ _ hC (valueBudget_nonnegative hB n)
  exact Q'.le_trans' _ _ _ hscale
    (Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (B * derivativeBudget B C n)
        (C * valueBudget B n) hterm)
      (Q'.le_of_eqv (Q'.add_comm_eqv
        (B * derivativeBudget B C n) (C * valueBudget B n))))

/-- Value budgets are monotone in the number of factors. -/
theorem value_le {B : Q'} (hB : (1 : Q') ≤ B) {n m : Nat} (hnm : n ≤ m) :
    valueBudget B n ≤ valueBudget B m := by
  induction m generalizing n with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      exact Q'.le_refl' _
  | succ m induction =>
      by_cases hn : n = m + 1
      · subst n
        exact Q'.le_refl' _
      · exact Q'.le_trans' _ _ _ (induction (by omega)) (value_step_le hB m)

/-- Derivative budgets are monotone in the number of factors. -/
theorem derivative_le {B C : Q'}
    (hB : (1 : Q') ≤ B) (hC : (0 : Q') ≤ C)
    {n m : Nat} (hnm : n ≤ m) :
    derivativeBudget B C n ≤ derivativeBudget B C m := by
  induction m generalizing n with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      exact Q'.le_refl' _
  | succ m induction =>
      by_cases hn : n = m + 1
      · subst n
        exact Q'.le_refl' _
      · exact Q'.le_trans' _ _ _ (induction (by omega))
          (derivative_step_le hB hC m)

end YMGap.Continuum.AngularProductBudget

#print axioms YMGap.Continuum.AngularProductBudget.valueBudget
#print axioms YMGap.Continuum.AngularProductBudget.derivativeBudget
#print axioms YMGap.Continuum.AngularProductBudget.valueBudget_nonnegative
#print axioms YMGap.Continuum.AngularProductBudget.derivativeBudget_nonnegative
#print axioms YMGap.Continuum.AngularProductBudget.value_le
#print axioms YMGap.Continuum.AngularProductBudget.derivative_le
