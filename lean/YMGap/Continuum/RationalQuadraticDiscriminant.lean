/- A constructive rational quadratic discriminant consumer.

This is a finite Q' arithmetic lemma only: nonnegativity of a quadratic
family implies the usual discriminant inequality. -/

import YMGap.Continuum.OSReconstructionProgress
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.RationalQuadraticDiscriminant

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.RingNormaliser

/- The sharp discriminant conclusion, with the degenerate diagonal handled
   by the integer tilted-family argument already used by the pre-inner-form
   Cauchy--Schwarz proof. -/
theorem nonnegative_quadratic_discriminant (A B C : Q')
    (h : ∀ s t : Q',
      (0 : Q') ≤ s * s * A + -(2 * (s * t) * B) + t * t * C) :
    B * B ≤ A * C := by
  have hA : (0 : Q') ≤ A := by
    have h0 := h 1 0
    exact le_of_le_eqv h0
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.mul (.const 1) (.const 1)) (.var 0))
          (.neg (.mul (.mul (.const 2) (.mul (.const 1) (.const 0))) (.var 1))))
          (.mul (.mul (.const 0) (.const 0)) (.var 2)))
        (.var 0) (by decide) (fun | 0 => A | 1 => B | _ => C))
  have hC : (0 : Q') ≤ C := by
    have h0 := h 0 1
    exact le_of_le_eqv h0
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.mul (.const 0) (.const 0)) (.var 0))
          (.neg (.mul (.mul (.const 2) (.mul (.const 0) (.const 1))) (.var 1))))
          (.mul (.mul (.const 1) (.const 1)) (.var 2)))
        (.var 2) (by decide) (fun | 0 => A | 1 => B | _ => C))
  have ineqA : A * (B * B) ≤ A * (A * C) :=
    q_le_of_sub_nonneg
      (le_of_le_eqv (h B A)
        (poly_identity_of_normal_eq
          (.add (.add (.mul (.mul (.var 1) (.var 1)) (.var 0))
            (.neg (.mul (.mul (.const 2) (.mul (.var 1) (.var 0))) (.var 1))))
            (.mul (.mul (.var 0) (.var 0)) (.var 2)))
          (.add (.mul (.var 0) (.mul (.var 0) (.var 2)))
            (.neg (.mul (.var 0) (.mul (.var 1) (.var 1)))))
          (by decide) (fun | 0 => A | 1 => B | _ => C)))
  have ineqC : C * (B * B) ≤ C * (A * C) :=
    q_le_of_sub_nonneg
      (le_of_le_eqv (h C B)
        (poly_identity_of_normal_eq
          (.add (.add (.mul (.mul (.var 2) (.var 2)) (.var 0))
            (.neg (.mul (.mul (.const 2) (.mul (.var 2) (.var 1))) (.var 1))))
            (.mul (.mul (.var 1) (.var 1)) (.var 2)))
          (.add (.mul (.var 2) (.mul (.var 0) (.var 2)))
            (.neg (.mul (.var 2) (.mul (.var 1) (.var 1)))))
          (by decide) (fun | 0 => A | 1 => B | _ => C)))
  have hdeg : A.eqv 0 → C.eqv 0 → B.eqv 0 := by
    intro hA0 hC0
    have tilted (t : Q') : (2 * t) * B ≤ t * t * A + C := by
      have ht := h t 1
      have eM : (-(2 * (t * 1) * B)).eqv (-((2 * t) * B)) :=
        Q'.neg_eqv_congr (2 * (t * 1) * B) (2 * t * B)
          (Q'.mul_eqv_congr_right (2 * (t * 1)) (2 * t) B
            (Q'.mul_eqv_congr_left 2 (t * 1) t (Q'.mul_one_eqv t)))
      have eC : (1 * 1 * C).eqv C := by
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right (1 * 1) 1 C (by decide)) (Q'.one_mul_eqv C)
      have e : (t * t * A + -(2 * (t * 1) * B) + 1 * 1 * C).eqv
          ((t * t * A + (-((2 * t) * B))) + C) :=
        QPoly.q_add_congr (QPoly.q_add_congr (Q'.eqv_refl (t*t*A)) eM) eC
      exact q_le_of_mid_neg (le_of_le_eqv ht e)
    have ht := tilted (Q'.ofInt B.num)
    have hAA : (Q'.ofInt B.num * Q'.ofInt B.num * A).eqv 0 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofInt B.num * Q'.ofInt B.num) A 0 hA0)
        (QPoly.q_mul_zero _)
    have hR : (Q'.ofInt B.num * Q'.ofInt B.num * A + C).eqv 0 :=
      Q'.eqv_trans _ _ _ (QPoly.q_add_congr hAA hC0) (Q'.eqv_refl 0)
    have hle : (2 * Q'.ofInt B.num) * B ≤ 0 := le_of_le_eqv ht hR
    have hn : ((2 * Q'.ofInt B.num) * B).num ≤ 0 := by
      have hn' : ((2 * Q'.ofInt B.num) * B).num * (1 : Int) ≤
          (0 : Int) * (((2 * Q'.ofInt B.num) * B).den : Int) := hle
      simpa using hn'
    have hn' : (2 * B.num) * B.num ≤ 0 := by simpa using hn
    rw [Int.mul_assoc] at hn'
    have hs : (0 : Int) ≤ B.num * B.num :=
      (Q'.zero_le_iff_num_nonneg (B * B)).mp (SumOfSquares.q_mul_self_nonneg B)
    have hz : B.num * B.num = 0 := by omega
    have hb : B.num = 0 := by
      rcases Int.mul_eq_zero.mp hz with h | h <;> exact h
    show B.num * (1 : Int) = (0 : Int) * (B.den : Int)
    simp [hb]
  exact cs_core A B C hA hC ineqA ineqC hdeg

/-- Cancel exactly the same positive mass in a homogeneous squared bound. -/
theorem normalize_squared_bound (A B lambda Z : Q') (hZ : (0 : Q') < Z)
    (h : B*B ≤ A*(lambda*Z)) :
    let r := Q'.recipPos Z hZ
    (r*B)*(r*B) ≤ lambda*(r*A) := by
  let r := Q'.recipPos Z hZ
  have hr : (r*Z).eqv 1 := Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (Q'.mul_recipPos_eqv Z hZ)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (r*r) h
    (SumOfSquares.q_mul_self_nonneg r)
  have hleft : ((r*B)*(r*B)).eqv ((r*r)*(B*B)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => r | _ => B)
  have hright : ((r*r)*(A*(lambda*Z))).eqv ((lambda*(r*A))*(r*Z)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.mul (.var 2) (.var 3))))
      (.mul (.mul (.var 2) (.mul (.var 0) (.var 1))) (.mul (.var 0) (.var 3)))
      (by decide) (fun | 0 => r | 1 => A | 2 => lambda | _ => Z)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ hright (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hr) (Q'.mul_one_eqv _)))))

end YMGap.Continuum.RationalQuadraticDiscriminant

#print axioms YMGap.Continuum.RationalQuadraticDiscriminant.nonnegative_quadratic_discriminant
#print axioms YMGap.Continuum.RationalQuadraticDiscriminant.normalize_squared_bound
