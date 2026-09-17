/-
# An explicit nonzero rational pair orthogonal to two prescribed scalars

The decidable zero test returns `(1, 0)` when the first scalar is zero
and `(v, -u)` otherwise.  Thus the witness remains nonzero even when both
inputs vanish.  This is finite rational algebra, not a spectral-gap claim.
-/

import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.Soundness
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.RationalOrthogonalPair

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- A computable orthogonal pair, including the zero-input case. -/
def pair (u v : Q') : Q' × Q' :=
  if u ≈ 0 then (1, 0) else (v, -u)

private theorem square_positive {u : Q'} (h : ¬ u ≈ 0) :
    (0 : Q') < u * u := by
  have hn : u.num ≠ 0 := by
    intro hz
    apply h
    change u.num * (1 : Int) = 0 * (u.den : Int)
    simp only [hz, Int.zero_mul]
  change (0 : Int) * ((u * u).den : Int) < (u.num * u.num) * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  by_cases hp : (0 : Int) < u.num
  · exact Int.mul_pos hp hp
  · have hm : (0 : Int) < -u.num := by omega
    have hs := Int.mul_pos hm hm
    simpa only [Int.neg_mul_neg] using hs

/-- The supplied rational coefficients annihilate the prescribed pair. -/
theorem pair_dot_zero (u v : Q') :
    (pair u v).1 * u + (pair u v).2 * v ≈ 0 := by
  by_cases hu : u ≈ 0
  · simp only [pair, if_pos hu]
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.mul (.const 1) (.var 0)) (.mul (.const 0) (.var 1)))
        (.var 0) (by decide) (fun | 0 => u | _ => v)) hu
  · simp only [pair, if_neg hu]
    exact poly_identity_of_normal_eq
      (.add (.mul (.var 1) (.var 0)) (.mul (.neg (.var 0)) (.var 1)))
      (.const 0) (by decide) (fun | 0 => u | _ => v)

/-- The witness has a strictly positive square budget for every input. -/
theorem pair_square_positive (u v : Q') :
    (0 : Q') < (pair u v).1 * (pair u v).1 +
      (pair u v).2 * (pair u v).2 := by
  by_cases hu : u ≈ 0
  · simp only [pair, if_pos hu]
    decide
  · simp only [pair, if_neg hu]
    have he : u * u + v * v ≈ v * v + (-u) * (-u) :=
      poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.add (.mul (.var 1) (.var 1))
          (.mul (.neg (.var 0)) (.neg (.var 0))))
        (by decide) (fun | 0 => u | _ => v)
    exact Q'.pos_of_lt_of_le (square_positive hu)
      (Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg _ _ (SumOfSquares.q_mul_self_nonneg v))
        (Q'.le_of_eqv he))

end YMGap.Continuum.RationalOrthogonalPair

#print axioms YMGap.Continuum.RationalOrthogonalPair.pair
#print axioms YMGap.Continuum.RationalOrthogonalPair.pair_dot_zero
#print axioms YMGap.Continuum.RationalOrthogonalPair.pair_square_positive
