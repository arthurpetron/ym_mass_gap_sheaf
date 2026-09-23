/-
# Finite constructive Cauchy inequality for lists of Q' values.

This is purely finite arithmetic.  The quadratic-discriminant consumer turns
the nonnegative family of tilted sums of squares into the stated bound.
-/

import YMGap.Continuum.RationalQuadraticDiscriminant
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.AbsQ

namespace YMGap.Continuum.RationalListCauchy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.RationalQuadraticDiscriminant

local infix:50 " ≈ " => Q'.eqv

def qsum : List Q' → Q'
  | [] => 0
  | x :: xs => x + qsum xs

def qsumSquares : List Q' → Q'
  | [] => 0
  | x :: xs => x*x + qsumSquares xs

private theorem square_tilt (s t x : Q') :
    (0 : Q') ≤ (s*x + -t) * (s*x + -t) :=
  SumOfSquares.q_mul_self_nonneg _

private theorem tilted_nonnegative : ∀ (xs : List Q') (s t : Q'),
    (0 : Q') ≤ qsum (xs.map (fun x => (s*x + -t) * (s*x + -t)))
  | [], _, _ => by change (0 : Q') ≤ 0; exact Q'.le_refl' 0
  | x :: xs, s, t => by
      exact Q'.zero_le_add _ _ (square_tilt s t x)
        (tilted_nonnegative xs s t)

private theorem tilted_expand : ∀ (xs : List Q') (s t : Q'),
    qsum (xs.map (fun x => (s*x + -t) * (s*x + -t))) ≈
      s*s*qsumSquares xs + -(2*(s*t)*qsum xs) +
        t*t*Q'.ofNat xs.length
  | [], s, t => by
      apply poly_identity_of_normal_eq
        (.const 0) (.add (.add (.mul (.mul (.var 0) (.var 0)) (.const 0))
          (.neg (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.const 0))))
          (.mul (.mul (.var 1) (.var 1)) (.const 0))) (by decide)
        (fun | 0 => s | _ => t)
  | x :: xs, s, t => by
      have ih := tilted_expand xs s t
      have hlen := Q'.ofNat_add_eqv xs.length 1
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          ((s*x + -t) * (s*x + -t))
          (qsum (xs.map (fun y => (s*y + -t) * (s*y + -t)))) _ ih)
        (Q'.eqv_trans _ _ _
          (poly_identity_of_normal_eq
            (.add
              (.mul (.add (.mul (.var 0) (.var 2)) (.neg (.var 1)))
                (.add (.mul (.var 0) (.var 2)) (.neg (.var 1))))
              (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 3))
                (.neg (.mul (.mul (.const 2) (.mul (.var 0) (.var 1))) (.var 4))))
                (.mul (.mul (.var 1) (.var 1)) (.var 5))))
            (.add
              (.add (.mul (.mul (.var 0) (.var 0))
                  (.add (.mul (.var 2) (.var 2)) (.var 3)))
                (.neg (.mul (.mul (.const 2) (.mul (.var 0) (.var 1)))
                    (.add (.var 2) (.var 4)))))
              (.mul (.mul (.var 1) (.var 1))
                (.add (.var 5) (.const 1)))) (by decide)
            (fun
              | 0 => s | 1 => t | 2 => x
              | 3 => qsumSquares xs | 4 => qsum xs
              | _ => Q'.ofNat xs.length))
          (Q'.add_eqv_congr_left _ _ _
            (Q'.mul_eqv_congr_left (t*t) _ _ (Q'.eqv_symm hlen))))

theorem qsum_sq_le_length_mul_qsumSquares (xs : List Q') :
    qsum xs * qsum xs ≤ Q'.ofNat xs.length * qsumSquares xs := by
  have h := nonnegative_quadratic_discriminant
    (qsumSquares xs) (qsum xs) (Q'.ofNat xs.length)
    (fun s t => Q'.le_trans' _ _ _ (tilted_nonnegative xs s t)
      (Q'.le_of_eqv (tilted_expand xs s t)))
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.mul_comm_eqv (qsumSquares xs) (Q'.ofNat xs.length)))

theorem abs_square_eqv (x : Q') :
    Q'.abs x * Q'.abs x ≈ x*x := by
  unfold Q'.abs
  by_cases hx : (0 : Q') ≤ x
  · rw [if_pos hx]
    exact Q'.eqv_refl _
  · rw [if_neg hx]
    exact poly_identity_of_normal_eq
      (.mul (.neg (.var 0)) (.neg (.var 0))) (.mul (.var 0) (.var 0))
      (by decide) (fun _ => x)

#print axioms YMGap.Continuum.RationalListCauchy.qsum_sq_le_length_mul_qsumSquares
#print axioms YMGap.Continuum.RationalListCauchy.abs_square_eqv

end YMGap.Continuum.RationalListCauchy
