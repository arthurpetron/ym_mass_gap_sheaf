/-
# Chebyshev evaluation at a rational reciprocal pair

For rational `r*s ≃ 1`, the first-kind polynomial at `(r+s)/2` is the
half-sum of the two powers. This is scalar algebra only: no operator bound,
coercivity, or square-root calibration is asserted.
-/

import YMGap.Continuum.ChebyshevBound
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.HalfPow
import YMGap.Constructive.Sqrt
import YMGap.Constructive.Soundness
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.ChebyshevReciprocalPair

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.Cheb
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

def center (r s : Q') : Q' := HalfPow.half * (r + s)

private theorem two_center (r s : Q') :
    ((2 : Q') * center r s) ≈ r + s := by
  unfold center
  calc
    (2 : Q') * (HalfPow.half * (r + s))
        ≈ ((2 : Q') * HalfPow.half) * (r + s) :=
      (Q'.mul_assoc_eqv _ _ _).symm
    _ ≈ (1 : Q') * (r + s) :=
      Q'.mul_eqv_congr_right _ _ _ (by decide)
    _ ≈ r + s := Q'.one_mul_eqv _

private theorem scaled_step (r s a b : Q') :
    ((r + s) * (HalfPow.half * a) + -(HalfPow.half * b)) ≈
      HalfPow.half * ((r + s) * a + -b) := by
  exact poly_identity_of_normal_eq
    (.add (.mul (.add (.var 0) (.var 1)) (.mul (.var 4) (.var 2)))
      (.neg (.mul (.var 4) (.var 3))))
    (.mul (.var 4)
      (.add (.mul (.add (.var 0) (.var 1)) (.var 2)) (.neg (.var 3))))
    (by decide)
    (fun | 0 => r | 1 => s | 2 => a | 3 => b | _ => HalfPow.half)

private theorem raw_step (r s a b : Q') (hrs : (r * s) ≈ (1 : Q')) :
    ((r + s) * (r * a + s * b) + -(a + b)) ≈
      r * (r * a) + s * (s * b) := by
  have hmul : ((r * s) * (a + b)) ≈ a + b :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hrs) (Q'.one_mul_eqv _)
  calc
    (r + s) * (r * a + s * b) + -(a + b)
        ≈ (r + s) * (r * a + s * b) + -((r * s) * (a + b)) :=
      Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hmul.symm)
    _ ≈ r * (r * a) + s * (s * b) := by
      exact poly_identity_of_normal_eq
        (.add
          (.mul (.add (.var 0) (.var 1))
            (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))))
          (.neg (.mul (.mul (.var 0) (.var 1))
            (.add (.var 2) (.var 3)))))
        (.add (.mul (.var 0) (.mul (.var 0) (.var 2)))
          (.mul (.var 1) (.mul (.var 1) (.var 3))))
        (by decide)
        (fun | 0 => r | 1 => s | 2 => a | _ => b)

/-- Exact reciprocal-pair evaluation of the literal rational `Cheb.T`. -/
theorem T_center (r s : Q') (hrs : (r * s) ≈ (1 : Q')) (n : Nat) :
    Cheb.T n (center r s) ≈ HalfPow.half * (r ^ n + s ^ n) := by
  let P (k : Nat) : Prop :=
    Cheb.T k (center r s) ≈ HalfPow.half * (r ^ k + s ^ k)
  have hzero : P 0 := by
    change (1 : Q') ≈ HalfPow.half * ((1 : Q') + (1 : Q'))
    decide
  have hone : P 1 := by
    change HalfPow.half * (r + s) ≈
      HalfPow.half * ((r * (1 : Q')) + (s * (1 : Q')))
    apply Q'.mul_eqv_congr_left
    exact Cheb.add_eqv_congr _ _ _ _
      (Q'.eqv_symm (Q'.mul_one_eqv r))
      (Q'.eqv_symm (Q'.mul_one_eqv s))
  have hstep (k : Nat) (hk : P k) (hks : P (k + 1)) : P (k + 2) := by
    change Cheb.T (k + 2) (center r s) ≈
      HalfPow.half * (r ^ (k + 2) + s ^ (k + 2))
    rw [Cheb.T_succ_succ]
    calc
      ((2 : Q') * center r s) * Cheb.T (k + 1) (center r s) +
          -(Cheb.T k (center r s))
          ≈ (r + s) * (HalfPow.half * (r ^ (k + 1) + s ^ (k + 1))) +
              -(HalfPow.half * (r ^ k + s ^ k)) :=
        Cheb.add_eqv_congr _ _ _ _
          (Cheb.mul_eqv_congr _ _ _ _ (two_center r s) hks)
          (Q'.neg_eqv_congr _ _ hk)
      _ ≈ HalfPow.half * ((r + s) * (r ^ (k + 1) + s ^ (k + 1)) +
            -(r ^ k + s ^ k)) :=
        scaled_step r s _ _
      _ ≈ HalfPow.half * (r ^ (k + 2) + s ^ (k + 2)) := by
        apply Q'.mul_eqv_congr_left
        change ((r + s) * (r * r ^ k + s * s ^ k) + -(r ^ k + s ^ k)) ≈
          r * (r * r ^ k) + s * (s * s ^ k)
        exact raw_step r s (r ^ k) (s ^ k) hrs
  have hall : ∀ k : Nat, P k ∧ P (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨hzero, hone⟩
    | succ j ih => exact ⟨ih.2, hstep j ih.1 ih.2⟩
  exact (hall n).1

private theorem pow_pos (a : Q') (ha : (0 : Q') < a) :
    ∀ n : Nat, (0 : Q') < a ^ n
  | 0 => by
      change (0 : Q') < (1 : Q')
      decide
  | n + 1 => Q'.mul_pos ha (pow_pos a ha n)

/-- The reciprocal-pair value is strictly positive for positive roots. -/
theorem T_center_pos (r s : Q') (hrs : (r * s) ≈ (1 : Q'))
    (hr : (0 : Q') < r) (hs : (0 : Q') < s) (n : Nat) :
    (0 : Q') < Cheb.T n (center r s) := by
  have hp : (0 : Q') < HalfPow.half * (r ^ n + s ^ n) :=
    Q'.mul_pos (by decide) (Q'.add_pos (pow_pos r hr n) (pow_pos s hs n))
  exact Q'.pos_of_lt_of_le hp (Q'.ge_of_eqv (T_center r s hrs n))

private theorem powers_recip (r s : Q') (hrs : (r * s) ≈ (1 : Q')) :
    ∀ n : Nat, (r ^ n * s ^ n) ≈ (1 : Q')
  | 0 => by
      change ((1 : Q') * 1) ≈ (1 : Q')
      decide
  | n + 1 => by
      change ((r * r ^ n) * (s * s ^ n)) ≈ (1 : Q')
      calc
        (r * r ^ n) * (s * s ^ n)
            ≈ (r * s) * (r ^ n * s ^ n) := by
          exact poly_identity_of_normal_eq
            (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
            (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
            (by decide)
            (fun | 0 => r | 1 => s | 2 => r ^ n | _ => s ^ n)
        _ ≈ (1 : Q') * (1 : Q') :=
          Cheb.mul_eqv_congr _ _ _ _ hrs (powers_recip r s hrs n)
        _ ≈ (1 : Q') := Q'.one_mul_eqv _

private theorem two_half_product (a b : Q') :
    ((2 : Q') * a) * (HalfPow.half * b) ≈ a * b := by
  calc
    ((2 : Q') * a) * (HalfPow.half * b)
        ≈ ((2 : Q') * HalfPow.half) * (a * b) := by
      exact poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (by decide)
        (fun | 0 => (2 : Q') | 1 => a | 2 => HalfPow.half | _ => b)
    _ ≈ (1 : Q') * (a * b) :=
      Q'.mul_eqv_congr_right _ _ _ (by decide)
    _ ≈ a * b := Q'.one_mul_eqv _

/-- The positive Chebyshev denominator has an explicit rational reciprocal
bound. This remains a scalar fact; the decay base `s` need not be below one. -/
theorem T_center_recip_le (r s : Q') (hrs : (r * s) ≈ (1 : Q'))
    (hr : (0 : Q') < r) (hs : (0 : Q') < s) (n : Nat) :
    Q'.recipPos (Cheb.T n (center r s)) (T_center_pos r s hrs hr hs n) ≤
      (2 : Q') * s ^ n := by
  let t := Cheb.T n (center r s)
  let a := r ^ n
  let b := s ^ n
  have hpair : t ≈ HalfPow.half * (a + b) := T_center r s hrs n
  have hscaled : ((2 : Q') * b) * t ≈ b * (a + b) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left ((2 : Q') * b) _ _ hpair)
      (two_half_product b (a + b))
  have hprod : b * (a + b) ≈ (1 : Q') + b * b := by
    calc
      b * (a + b) ≈ b * a + b * b := Q'.mul_add_eqv _ _ _
      _ ≈ a * b + b * b :=
        Q'.add_eqv_congr_right _ _ _ (Q'.mul_comm_eqv b a)
      _ ≈ (1 : Q') + b * b :=
        Q'.add_eqv_congr_right _ _ _ (powers_recip r s hrs n)
  have hbound : (1 : Q') ≤ ((2 : Q') * b) * t :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg 1 (b * b)
        (Q'.mul_nonneg _ _ (Q'.le_of_lt (pow_pos s hs n))
          (Q'.le_of_lt (pow_pos s hs n))))
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hprod) (Q'.ge_of_eqv hscaled))
  have hdiv := Q'.divPos_le_of_le_mul 1 t (T_center_pos r s hrs hr hs n) hbound
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv (Q'.recipPos t (T_center_pos r s hrs hr hs n))))
    hdiv

#print axioms center
#print axioms T_center
#print axioms T_center_pos
#print axioms T_center_recip_le

end YMGap.Continuum.ChebyshevReciprocalPair
