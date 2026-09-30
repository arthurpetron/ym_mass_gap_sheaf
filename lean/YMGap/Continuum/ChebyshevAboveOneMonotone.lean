/-
# Monotonicity of first-kind Chebyshev values above one

The value and its forward difference are compared together.  The forward
difference obeys a positive recurrence on [1, infinity), avoiding any
subtraction of unrelated inequalities.  This is scalar rational algebra;
it supplies no operator estimate.
-/

import YMGap.Continuum.ChebyshevAboveOne

namespace YMGap.Continuum.ChebyshevAboveOneMonotone

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private def forwardDifference (x : Q') (n : Nat) : Q' :=
  Cheb.T (n+1) x + -(Cheb.T n x)

private theorem value_split (x : Q') (n : Nat) :
    Cheb.T (n+1) x ≈ Cheb.T n x + forwardDifference x n := by
  unfold forwardDifference
  exact poly_identity_of_normal_eq
    (.var 0)
    (.add (.var 1) (.add (.var 0) (.neg (.var 1))))
    (by decide) (fun | 0 => Cheb.T (n+1) x | _ => Cheb.T n x)

private theorem difference_step (x : Q') (n : Nat) :
    forwardDifference x (n+1) ≈
      forwardDifference x n +
        ((2 : Q') * (x + -(1 : Q'))) * Cheb.T (n+1) x := by
  unfold forwardDifference
  rw [show n + 1 + 1 = n + 2 from by omega, Cheb.T_succ_succ]
  exact poly_identity_of_normal_eq
    (.add
      (.add (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.neg (.var 2)))
      (.neg (.var 1)))
    (.add
      (.add (.var 1) (.neg (.var 2)))
      (.mul (.mul (.const 2) (.add (.var 0) (.neg (.const 1)))) (.var 1)))
    (by decide) (fun | 0 => x | 1 => Cheb.T (n+1) x | _ => Cheb.T n x)

/-- First-kind Chebyshev evaluation is monotone in its argument on [1, infinity).
The comparison is coefficient-rational, with no analytic or spectral premise. -/
theorem T_mono (x y : Q') (hx : (1 : Q') ≤ x) (hxy : x ≤ y) (n : Nat) :
    Cheb.T n x ≤ Cheb.T n y := by
  have hy : (1 : Q') ≤ y := Q'.le_trans' _ _ _ hx hxy
  have hdiff : x + -(1 : Q') ≤ y + -(1 : Q') :=
    Q'.add_le_add_right x y (-(1 : Q')) hxy
  have hcoef : (2 : Q') * (x + -(1 : Q')) ≤
      (2 : Q') * (y + -(1 : Q')) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdiff (by decide)
  have hcoef_nonneg : (0 : Q') ≤ (2 : Q') * (y + -(1 : Q')) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.sub_nonneg_of_le hy)
  have all : ∀ k : Nat,
      Cheb.T k x ≤ Cheb.T k y ∧
        forwardDifference x k ≤ forwardDifference y k := by
    intro k
    induction k with
    | zero =>
        constructor
        · exact Q'.le_refl' (1 : Q')
        · change x + -(1 : Q') ≤ y + -(1 : Q')
          exact hdiff
    | succ k ih =>
        have hvalue : Cheb.T (k+1) x ≤ Cheb.T (k+1) y := by
          have hsum := Q'.add_le_add ih.1 ih.2
          exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (value_split x k))
            (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv (value_split y k)))
        have hvalue_nonneg : (0 : Q') ≤ Cheb.T (k+1) x :=
          Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1)
            (ChebyshevAboveOne.T_lower_and_step x hx (k+1)).1
        have hproduct :
            ((2 : Q') * (x + -(1 : Q'))) * Cheb.T (k+1) x ≤
              ((2 : Q') * (y + -(1 : Q'))) * Cheb.T (k+1) y := by
          exact Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_right _ _ _ hcoef hvalue_nonneg)
            (Q'.mul_le_mul_of_nonneg_left _ _ _ hvalue hcoef_nonneg)
        have hsum := Q'.add_le_add ih.2 hproduct
        refine ⟨hvalue, ?_⟩
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (difference_step x k))
          (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv (difference_step y k)))
  exact (all n).1

end YMGap.Continuum.ChebyshevAboveOneMonotone

#print axioms YMGap.Continuum.ChebyshevAboveOneMonotone.T_mono
