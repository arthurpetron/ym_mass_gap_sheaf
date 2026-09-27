/-
# Positive first-kind Chebyshev denominators above one

The recurrence itself gives T_n(x)>=1 and consecutive monotonicity for
rational x>=1. This discharges the denominator guard for the constructed
finite-volume rescaling; it assumes no operator or spectral theorem.
-/

import YMGap.Continuum.ChebyshevBound
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.CRealMulMono
import YMGap.Constructive.Soundness
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.ChebyshevAboveOne

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- The scalar recurrence is increasing and stays above one on [1,infinity). -/
theorem T_lower_and_step (x : Q') (hx : (1 : Q') ≤ x) (n : Nat) :
    (1 : Q') ≤ Cheb.T n x ∧ Cheb.T n x ≤ Cheb.T (n+1) x := by
  induction n with
  | zero => exact ⟨Q'.le_refl' _, hx⟩
  | succ n ih =>
      have hnext := Q'.le_trans' _ _ _ ih.1 ih.2
      refine ⟨hnext, Q'.le_of_sub_nonneg ?_⟩
      have hnonneg : (0 : Q') ≤ Cheb.T (n+1) x :=
        Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1) hnext
      have hsum : (0 : Q') ≤
          (2 : Q') * (x + -(1 : Q')) * Cheb.T (n+1) x +
            (Cheb.T (n+1) x + -(Cheb.T n x)) :=
        Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 0 + 0) (Q'.add_le_add
          (Q'.mul_nonneg _ _
            (Q'.mul_nonneg _ _ (by decide) (Q'.sub_nonneg_of_le hx)) hnonneg)
          (Q'.sub_nonneg_of_le ih.2))
      have he : Cheb.T (n+2) x + -(Cheb.T (n+1) x) ≈
          (2 : Q') * (x + -(1 : Q')) * Cheb.T (n+1) x +
            (Cheb.T (n+1) x + -(Cheb.T n x)) := by
        rw [Cheb.T_succ_succ]
        exact poly_identity_of_normal_eq
          (.add (.add (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.neg (.var 2)))
            (.neg (.var 1)))
          (.add (.mul (.mul (.const 2) (.add (.var 0) (.neg (.const 1)))) (.var 1))
            (.add (.var 1) (.neg (.var 2))))
          (by decide) (fun | 0 => x | 1 => Cheb.T (n+1) x | _ => Cheb.T n x)
      exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv he)

theorem T_positive (x : Q') (hx : (1 : Q') ≤ x) (n : Nat) :
    (0 : Q') < Cheb.T n x :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1) (T_lower_and_step x hx n).1

#print axioms T_lower_and_step
#print axioms T_positive

end YMGap.Continuum.ChebyshevAboveOne
