/-
An elementary geometric lower bound for Chebyshev denominators above one.
This is scalar arithmetic; it does not supply an operator coercivity estimate.
-/

import YMGap.Continuum.ChebyshevAboveOne

namespace YMGap.Continuum.ChebyshevGeometricLower

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

private theorem positive_of_one_lt {x : Q'} (hx : (1 : Q') < x) :
    (0 : Q') < x :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1) (Q'.le_of_lt hx)

/-- The rational geometric ratio associated with `x > 1`. -/
def rho (x : Q') (hx : (1 : Q') < x) : Q' :=
  Q'.recipPos x (positive_of_one_lt hx)

theorem rho_positive (x : Q') (hx : (1 : Q') < x) :
    (0 : Q') < rho x hx :=
  Q'.recipPos_pos x (positive_of_one_lt hx)

theorem rho_lt_one (x : Q') (hx : (1 : Q') < x) :
    rho x hx < (1 : Q') := by
  have hnum : (x.den : Int) < x.num := by
    have h : (1 : Q').num * (x.den : Int) < x.num * ((1 : Q').den : Int) := hx
    change (1 : Int) * (x.den : Int) < x.num * (1 : Int) at h
    simpa only [Int.one_mul, Int.mul_one] using h
  show (rho x hx).num * ((1 : Q').den : Int) <
    (1 : Q').num * ((rho x hx).den : Int)
  rw [rho, Q'.recipPos_num, Q'.recipPos_den]
  change (x.den : Int) * 1 < 1 * x.num
  simpa only [Int.one_mul, Int.mul_one] using hnum

private theorem next_ge_mul (x : Q') (hx : (1 : Q') ≤ x) (n : Nat) :
    x * Cheb.T (n + 1) x ≤ Cheb.T (n + 2) x := by
  have ht := ChebyshevAboveOne.T_lower_and_step x hx n
  have htnext : (0 : Q') ≤ Cheb.T (n + 1) x :=
    Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ 1)
      (Q'.le_trans' _ _ _ ht.1 ht.2)
  have hone : Cheb.T (n + 1) x ≤ x * Cheb.T (n + 1) x :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.one_mul_eqv _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hx htnext)
  have hprev : Cheb.T n x ≤ x * Cheb.T (n + 1) x :=
    Q'.le_trans' _ _ _ ht.2 hone
  have hdiff : (0 : Q') ≤ x * Cheb.T (n + 1) x + -(Cheb.T n x) :=
    Q'.sub_nonneg_of_le hprev
  apply Q'.le_of_sub_nonneg
  rw [Cheb.T_succ_succ]
  have hring : Q'.eqv
      ((((2 : Q') * x) * Cheb.T (n + 1) x + -(Cheb.T n x)) +
        -(x * Cheb.T (n + 1) x))
      (x * Cheb.T (n + 1) x + -(Cheb.T n x)) := by
    exact poly_identity_of_normal_eq
      (.add (.add (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.neg (.var 2)))
        (.neg (.mul (.var 0) (.var 1))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.var 2)))
      (by decide) (fun | 0 => x | 1 => Cheb.T (n + 1) x | _ => Cheb.T n x)
  exact Q'.le_trans' _ _ _ hdiff (Q'.ge_of_eqv hring)

/-- For `x > 1`, the first-kind Chebyshev denominator dominates `x^n`. -/
theorem pow_le_T (x : Q') (hx : (1 : Q') < x) (n : Nat) :
    x ^ n ≤ Cheb.T n x := by
  have hle : (1 : Q') ≤ x := Q'.le_of_lt hx
  have hnonneg : (0 : Q') ≤ x := Q'.le_of_lt (positive_of_one_lt hx)
  have all : ∀ k : Nat,
      x ^ k ≤ Cheb.T k x ∧ x ^ (k + 1) ≤ Cheb.T (k + 1) x := by
    intro k
    induction k with
    | zero => exact ⟨Q'.le_refl' _, Q'.le_of_eqv (Q'.mul_one_eqv x)⟩
    | succ k ih =>
        refine ⟨ih.2, ?_⟩
        change x * x ^ (k + 1) ≤ Cheb.T (k + 2) x
        exact Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _ ih.2 hnonneg)
          (next_ge_mul x hle k)
  exact (all n).1

private theorem pow_inverse (x : Q') (hx : (1 : Q') < x) (n : Nat) :
    Q'.eqv (x ^ n * (rho x hx) ^ n) 1 := by
  induction n with
  | zero => exact Q'.one_mul_eqv 1
  | succ n ih =>
      change Q'.eqv ((x * x ^ n) * (rho x hx * (rho x hx) ^ n)) 1
      have hring : Q'.eqv
          ((x * x ^ n) * (rho x hx * (rho x hx) ^ n))
          ((x * rho x hx) * (x ^ n * (rho x hx) ^ n)) := by
        exact poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
          (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
          (by decide)
          (fun | 0 => x | 1 => x ^ n | 2 => rho x hx | _ => (rho x hx) ^ n)
      have hprod : Q'.eqv
          ((x * rho x hx) * (x ^ n * (rho x hx) ^ n)) (1 * 1) :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_recipPos_eqv x (positive_of_one_lt hx)))
          (Q'.mul_eqv_congr_left _ _ _ ih)
      exact Q'.eqv_trans _ _ _ hring
        (Q'.eqv_trans _ _ _ hprod (Q'.one_mul_eqv 1))

/-- The inverse Chebyshev denominator is bounded by an explicit geometric rate. -/
theorem reciprocal_T_le_pow (x : Q') (hx : (1 : Q') < x) (n : Nat) :
    Q'.divPos 1 (Cheb.T n x)
      (ChebyshevAboveOne.T_positive x (Q'.le_of_lt hx) n) ≤
        (rho x hx) ^ n := by
  apply Q'.divPos_le_of_le_mul
  have hnonneg : (0 : Q') ≤ rho x hx := Q'.le_of_lt (rho_positive x hx)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
    (pow_le_T x hx n) (Q'.pow_nonneg _ hnonneg n)
  have hcomm : Q'.eqv ((rho x hx) ^ n * x ^ n)
      (x ^ n * (rho x hx) ^ n) := Q'.mul_comm_eqv _ _
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (pow_inverse x hx n)))
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcomm) hscaled)

#print axioms rho
#print axioms rho_positive
#print axioms rho_lt_one
#print axioms pow_le_T
#print axioms reciprocal_T_le_pow

end YMGap.Continuum.ChebyshevGeometricLower
