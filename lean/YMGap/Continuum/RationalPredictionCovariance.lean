/-
# Rational prediction covariance from a uniform quadratic floor

The finite test coefficient is selected explicitly when its squared cost is
positive.  When the cost is zero, the supplied ordinary Cauchy--Schwarz
bound handles the degenerate case.  This is scalar algebra only; the Wilson
weight, variances, and prediction floor belong to the physical caller.
-/

import YMGap.Continuum.RationalDualTestOptimization
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.RationalPredictionCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem optimized_quadratic_identity
    (A B C t : Q') (ht : t*C ≈ B) :
    ((A + -(2*t*B) + t*t*C)*C) + B*B ≈ A*C := by
  let u := t*C + -B
  have hu : u ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ht (Q'.eqv_refl _))
      (Q'.add_neg_self_eqv B)
  have hsq : u*u ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hu)
      (Q'.mul_zero_eqv u)
  have hpoly :
      ((A + -(2*t*B) + t*t*C)*C) + B*B ≈ A*C + u*u :=
    poly_identity_of_normal_eq
      (.add
        (.mul
          (.add (.add (.var 0)
            (.neg (.mul (.mul (.const 2) (.var 3)) (.var 1))))
            (.mul (.mul (.var 3) (.var 3)) (.var 2)))
          (.var 2))
        (.mul (.var 1) (.var 1)))
      (.add (.mul (.var 0) (.var 2))
        (.mul (.add (.mul (.var 3) (.var 2)) (.neg (.var 1)))
          (.add (.mul (.var 3) (.var 2)) (.neg (.var 1)))))
      (by decide)
      (fun | 0 => A | 1 => B | 2 => C | _ => t)
  exact Q'.eqv_trans _ _ _ hpoly
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hsq)
      (Q'.eqv_of_eq (Q'.add_zero' _)))

private theorem optimized_coefficient (B C : Q') (hC : (0 : Q') < C) :
    (B * Q'.recipPos C hC)*C ≈ B := by
  let r := Q'.recipPos C hC
  have hr : r*C ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv r C)
      (Q'.mul_recipPos_eqv C hC)
  exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv B r C)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hr)
      (Q'.mul_one_eqv B))

/-- Uniform rational prediction loss bounds the covariance by the residual
variance.  `A`, `B`, `C`, and `s` are supplied by the actual finite model;
there is no positivity premise on `A-s` hidden in the conclusion. -/
theorem covariance_budget (A B C s : Q')
    (hC : (0 : Q') ≤ C)
    (hCS : B*B ≤ A*C)
    (hfloor : ∀ t : Q', s ≤ A + -(2*t*B) + t*t*C) :
    B*B ≤ (A + -s)*C := by
  by_cases hCpos : (0 : Q') < C
  · let t := B * Q'.recipPos C hCpos
    let q := A + -(2*t*B) + t*t*C
    have htest : s ≤ q := hfloor t
    have hscaled : s*C ≤ q*C :=
      Q'.mul_le_mul_of_nonneg_right s q C htest hC
    have hsum : s*C + B*B ≤ q*C + B*B :=
      Q'.add_le_add_right _ _ _ hscaled
    have hopt : q*C + B*B ≈ A*C :=
      optimized_quadratic_identity A B C t
        (optimized_coefficient B C hCpos)
    have htotal : s*C + B*B ≤ A*C :=
      Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hopt)
    have hsub : (0 : Q') ≤ A*C + -(s*C + B*B) :=
      Q'.sub_nonneg_of_le htotal
    have hrearrange :
        ((A + -s)*C + -(B*B)) ≈
          A*C + -(s*C + B*B) :=
      poly_identity_of_normal_eq
        (.add (.mul (.add (.var 0) (.neg (.var 3))) (.var 2))
          (.neg (.mul (.var 1) (.var 1))))
        (.add (.mul (.var 0) (.var 2))
          (.neg (.add (.mul (.var 3) (.var 2))
            (.mul (.var 1) (.var 1)))))
        (by decide)
        (fun | 0 => A | 1 => B | 2 => C | _ => s)
    exact Q'.le_of_sub_nonneg
      (Q'.le_trans' _ _ _ hsub (Q'.ge_of_eqv hrearrange))
  · have hnum : C.num ≤ (0 : Int) :=
      Int.not_lt.mp (fun h => hCpos (by
        show (0 : Int) * (C.den : Int) < C.num * (1 : Int)
        simpa only [Int.zero_mul, Int.mul_one] using h))
    have hCle : C ≤ (0 : Q') := by
      change C.num * (1 : Int) ≤ (0 : Int) * (C.den : Int)
      simpa only [Int.mul_one, Int.zero_mul] using hnum
    have hCzero : C ≈ 0 := Q'.eqv_of_le_le hCle hC
    have hACzero : A*C ≈ 0 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hCzero)
        (Q'.mul_zero_eqv A)
    have hRzero : (A + -s)*C ≈ 0 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hCzero)
        (Q'.mul_zero_eqv (A + -s))
    exact Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ hCS (Q'.le_of_eqv hACzero))
      (Q'.ge_of_eqv hRzero)

#print axioms covariance_budget

end YMGap.Continuum.RationalPredictionCovariance
