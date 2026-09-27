/-
An elementary near-one upper bound for first-kind Chebyshev polynomials.
This is a scalar estimate only; it supplies no operator or Yang--Mills gap.
-/

import YMGap.Continuum.ChebyshevAboveOne

namespace YMGap.Continuum.ChebyshevNearOneUpper

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

private theorem add_le_add' {a b c d : Q'} (hab : a ≤ b) (hcd : c ≤ d) :
    a + c ≤ b + d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hab)
    (Q'.add_le_add_left _ _ _ hcd)

/-- Chebyshev evaluation respects rational equivalence of its argument. -/
theorem T_congr (a b : Q') (h : Q'.eqv a b) (k : Nat) :
    Q'.eqv (Cheb.T k a) (Cheb.T k b) := by
  have all : ∀ n : Nat,
      Q'.eqv (Cheb.T n a) (Cheb.T n b) ∧
      Q'.eqv (Cheb.T (n + 1) a) (Cheb.T (n + 1) b) := by
    intro n
    induction n with
    | zero => exact ⟨Q'.eqv_refl _, h⟩
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        rw [show n + 1 + 1 = n + 2 from by omega, Cheb.T_succ_succ,
          Cheb.T_succ_succ]
        have htwo : Q'.eqv ((2 : Q') * a) ((2 : Q') * b) :=
          Q'.mul_eqv_congr_left _ _ _ h
        have hprod : Q'.eqv
            (((2 : Q') * a) * Cheb.T (n + 1) a)
            (((2 : Q') * b) * Cheb.T (n + 1) b) :=
          Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _ htwo)
            (Q'.mul_eqv_congr_left _ _ _ ih.2)
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ _ hprod)
          (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ ih.1))
  exact (all k).1

private theorem gap_step (epsilon a b : Q')
    (ha : (1 : Q') ≤ a) (hb : (1 : Q') ≤ b)
    (he : (2 : Q') * epsilon ≤ 1) :
    ((2 : Q') * (1 + epsilon)) * b + -a ≤
      (1 + (3 : Q') * (b + -(1 : Q'))) + (2 : Q') * epsilon := by
  have h1 : (0 : Q') ≤ a + -(1 : Q') := Q'.sub_nonneg_of_le ha
  have h2 : (0 : Q') ≤ 1 + -((2 : Q') * epsilon) :=
    Q'.sub_nonneg_of_le he
  have h3 : (0 : Q') ≤ b + -(1 : Q') := Q'.sub_nonneg_of_le hb
  have hsum : (0 : Q') ≤
      (a + -(1 : Q')) +
        (1 + -((2 : Q') * epsilon)) * (b + -(1 : Q')) :=
    Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 0 + 0)
      (add_le_add' h1 (Q'.mul_nonneg _ _ h2 h3))
  have hid : Q'.eqv
      (((1 + (3 : Q') * (b + -(1 : Q'))) + (2 : Q') * epsilon) +
        -(((2 : Q') * (1 + epsilon)) * b + -a))
      ((a + -(1 : Q')) +
        (1 + -((2 : Q') * epsilon)) * (b + -(1 : Q'))) := by
    exact poly_identity_of_normal_eq
      (.add
        (.add (.add (.const 1)
          (.mul (.const 3) (.add (.var 1) (.neg (.const 1)))))
          (.mul (.const 2) (.var 0)))
        (.neg (.add
          (.mul (.mul (.const 2) (.add (.const 1) (.var 0))) (.var 1))
          (.neg (.var 2)))))
      (.add (.add (.var 2) (.neg (.const 1)))
        (.mul (.add (.const 1) (.neg (.mul (.const 2) (.var 0))))
          (.add (.var 1) (.neg (.const 1)))))
      (by decide) (fun | 0 => epsilon | 1 => b | _ => a)
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hid))

private theorem two_le_four_pow_succ (n : Nat) :
    (2 : Q') ≤ (4 : Q') ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      change (2 : Q') ≤ (4 : Q') * (4 : Q') ^ (n + 1)
      exact Q'.le_trans' _ _ _
        (by decide : (2 : Q') ≤ (4 : Q') * 2)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ ih (by decide))

private theorem four_step (epsilon p : Q')
    (he : (0 : Q') ≤ epsilon) (hp : (2 : Q') ≤ p) :
    (1 + (3 : Q') * (epsilon * p)) + (2 : Q') * epsilon ≤
      1 + epsilon * ((4 : Q') * p) := by
  have hdiff : (0 : Q') ≤ epsilon * (p + -(2 : Q')) :=
    Q'.mul_nonneg _ _ he (Q'.sub_nonneg_of_le hp)
  have hid : Q'.eqv
      ((1 + epsilon * ((4 : Q') * p)) +
        -((1 + (3 : Q') * (epsilon * p)) + (2 : Q') * epsilon))
      (epsilon * (p + -(2 : Q'))) := by
    exact poly_identity_of_normal_eq
      (.add (.add (.const 1) (.mul (.var 0) (.mul (.const 4) (.var 1))))
        (.neg (.add
          (.add (.const 1) (.mul (.const 3) (.mul (.var 0) (.var 1))))
          (.mul (.const 2) (.var 0)))))
      (.mul (.var 0) (.add (.var 1) (.neg (.const 2))))
      (by decide) (fun | 0 => epsilon | _ => p)
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hdiff (Q'.ge_of_eqv hid))

/-- On the rational half-window, growth away from one is at most `epsilon*4^k`. -/
theorem T_near_one_upper_of_two_mul_le_one (epsilon : Q')
    (h0 : (0 : Q') ≤ epsilon) (hhalf : (2 : Q') * epsilon ≤ 1)
    (k : Nat) :
    Cheb.T k (1 + epsilon) ≤ 1 + epsilon * (4 : Q') ^ k := by
  let x : Q' := 1 + epsilon
  have hx : (1 : Q') ≤ x :=
    Q'.add_le_self_of_nonneg 1 epsilon h0
  have all : ∀ n : Nat,
      Cheb.T n x ≤ 1 + epsilon * (4 : Q') ^ n ∧
      Cheb.T (n + 1) x ≤ 1 + epsilon * (4 : Q') ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
        constructor
        · exact Q'.add_le_self_of_nonneg 1 _
            (Q'.mul_nonneg _ _ h0 (Q'.pow_nonneg _ (by decide) 0))
        · have hfour : epsilon ≤ epsilon * (4 : Q') ^ 1 :=
            Q'.le_trans' _ _ _
              (Q'.ge_of_eqv (Q'.mul_one_eqv epsilon))
              (Q'.mul_le_mul_of_nonneg_left _ _ _
                (by decide : (1 : Q') ≤ (4 : Q') ^ 1) h0)
          exact Q'.add_le_add_left 1 _ _ hfour
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        have ha := (ChebyshevAboveOne.T_lower_and_step x hx n).1
        have hb := (ChebyshevAboveOne.T_lower_and_step x hx (n + 1)).1
        have hgap := gap_step epsilon (Cheb.T n x) (Cheb.T (n + 1) x)
          ha hb hhalf
        have hg : Cheb.T (n + 1) x + -(1 : Q') ≤
            epsilon * (4 : Q') ^ (n + 1) :=
          Q'.sub_le_of_le_add ih.2
        have hscaled : (3 : Q') * (Cheb.T (n + 1) x + -(1 : Q')) ≤
            (3 : Q') * (epsilon * (4 : Q') ^ (n + 1)) :=
          Q'.mul_le_mul_of_nonneg_left _ _ _ hg (by decide)
        have hpartial : Cheb.T (n + 2) x ≤
            (1 + (3 : Q') * (epsilon * (4 : Q') ^ (n + 1))) +
              (2 : Q') * epsilon :=
          Q'.le_trans' _ _ _ (by simpa [Cheb.T_succ_succ, x] using hgap)
            (Q'.add_le_add_right _ _ _ (Q'.add_le_add_left _ _ _ hscaled))
        have hfinal := four_step epsilon ((4 : Q') ^ (n + 1)) h0
          (two_le_four_pow_succ n)
        have hpow : (4 : Q') ^ (n + 2) = (4 : Q') * (4 : Q') ^ (n + 1) :=
          Q'.pow_succ 4 (n + 1)
        exact Q'.le_trans' _ _ _ hpartial (by simpa [hpow] using hfinal)
  exact (all k).1

/-- The convenient half-window formulation for downstream scalar calibration. -/
theorem T_near_one_upper (epsilon : Q')
    (h0 : (0 : Q') ≤ epsilon)
    (hhalf : epsilon ≤ Q'.mkPos 1 2 (by decide)) (k : Nat) :
    Cheb.T k (1 + epsilon) ≤ 1 + epsilon * (4 : Q') ^ k := by
  have htwo : (2 : Q') * epsilon ≤ 1 :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hhalf (by decide))
      (by decide : (2 : Q') * Q'.mkPos 1 2 (by decide) ≤ 1)
  exact T_near_one_upper_of_two_mul_le_one epsilon h0 htwo k

#print axioms T_congr
#print axioms T_near_one_upper_of_two_mul_le_one
#print axioms T_near_one_upper

end YMGap.Continuum.ChebyshevNearOneUpper
