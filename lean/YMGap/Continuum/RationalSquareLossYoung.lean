/-
# Rational Young bounds for an actual squared loss estimate

The constants are explicit rational data. The proof uses a sum of squares
and decidable rational order, with no square roots or reciprocal of a
variance. The only reciprocal is that of the supplied positive tolerance.
-/

import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.Sqrt
import YMGap.Constructive.Soundness
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.RationalSquareLossYoung

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- Kernel-computed rational coefficient, kept as data. -/
def quarter : Q' := Q'.mkPos 1 4 (by decide)

/-- Signed x is bounded without assuming that x or the upper bound is
strictly positive. In particular zero mass causes no division. -/
theorem le_add_of_square_le_four_mul (x u v : Q')
    (hu : (0 : Q') ≤ u) (hv : (0 : Q') ≤ v)
    (hxx : x*x ≤ 4*(u*v)) : x ≤ u+v := by
  let y := u+v
  have hy : (0 : Q') ≤ y := Q'.zero_le_add u v hu hv
  have hs := SumOfSquares.q_mul_self_nonneg (u-v)
  have hfour : 4*(u*v) ≤ y*y := Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (4*(u*v)) ((u-v)*(u-v)) hs)
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.mul (.const 4) (.mul (.var 0) (.var 1)))
        (.mul (.add (.var 0) (.neg (.var 1)))
          (.add (.var 0) (.neg (.var 1)))))
      (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
      (by decide) (fun | 0 => u | _ => v)))
  have hxy : x*x ≤ y*y := Q'.le_trans' _ _ _ hxx hfour
  by_cases hx : (0 : Q') < x
  · have hsum : (0 : Q') < x+y :=
      Q'.pos_of_lt_of_le hx (Q'.add_le_self_of_nonneg x y hy)
    have hscaled : (x+y)*x ≤ (x+y)*y := Q'.le_trans' _ _ _
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.add (.var 0) (.var 1)) (.var 0))
        (.add (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 1)))
        (by decide) (fun | 0 => x | _ => y)))
      (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (x*y) hxy)
        (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.add (.mul (.var 1) (.var 1)) (.mul (.var 0) (.var 1)))
          (.mul (.add (.var 0) (.var 1)) (.var 1))
          (by decide) (fun | 0 => x | _ => y))))
    exact Q'.le_of_mul_le_mul_left hscaled hsum
  · have hx0 : x ≤ 0 := by
      change x.num * (1 : Int) ≤ 0 * (x.den : Int)
      have hn : ¬ (0 : Int) < x.num := by
        intro hn
        apply hx
        change (0 : Int) * (x.den : Int) < x.num * (1 : Int)
        simpa using hn
      simpa using Int.le_of_not_gt hn
    exact Q'.le_trans' _ _ _ hx0 hy

/-- Root-free one-sided Young inequality. Neither A nor L is inverted,
and the sign of the actual defect x is unrestricted. -/
theorem square_loss_young (x A L c epsilon : Q')
    (hA : (0 : Q') ≤ A) (hL : (0 : Q') ≤ L)
    (hc : (0 : Q') ≤ c) (heps : (0 : Q') < epsilon)
    (hxx : x*x ≤ c*L*A) :
    x ≤ epsilon*A+(quarter*c*Q'.recipPos epsilon heps)*L := by
  let r := Q'.recipPos epsilon heps
  have hu : (0 : Q') ≤ epsilon*A :=
    Q'.mul_nonneg epsilon A (Q'.le_of_lt heps) hA
  have hv : (0 : Q') ≤ (quarter*c*r)*L :=
    Q'.mul_nonneg _ L (Q'.mul_nonneg _ r
      (Q'.mul_nonneg quarter c (by decide) hc)
      (Q'.le_of_lt (Q'.recipPos_pos epsilon heps))) hL
  have hfour : 4*((epsilon*A)*((quarter*c*r)*L)) ≈ c*L*A :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.const 4)
        (.mul (.mul (.var 0) (.var 1))
          (.mul (.mul (.mul (.var 2) (.var 3)) (.var 4)) (.var 5))))
      (.mul (.mul (.mul (.const 4) (.var 2)) (.mul (.var 0) (.var 4)))
        (.mul (.mul (.var 3) (.var 5)) (.var 1)))
      (by decide) (fun | 0 => epsilon | 1 => A | 2 => quarter | 3 => c | 4 => r | _ => L))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (c*L*A)
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ (epsilon*r)
              (by decide : 4*quarter ≈ (1 : Q')))
            (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv (epsilon*r))
              (Q'.mul_recipPos_eqv epsilon heps))))
        (Q'.one_mul_eqv (c*L*A)))
  exact le_add_of_square_le_four_mul x (epsilon*A) ((quarter*c*r)*L)
    hu hv (Q'.le_trans' _ _ _ hxx (Q'.ge_of_eqv hfour))

#print axioms quarter
#print axioms le_add_of_square_le_four_mul
#print axioms square_loss_young

end YMGap.Continuum.RationalSquareLossYoung
