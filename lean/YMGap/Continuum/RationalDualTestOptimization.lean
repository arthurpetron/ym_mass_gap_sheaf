/-
# Exact optimization of a rational dual test with positive cost

For a pairing A and a strictly positive squared cost C, the finite rational
coefficient A/C maximizes 2*a*A-a²*C and gives the homogeneous gain A²/C.
The null-cost case is intentionally left to the physical caller, which has
the relevant Cauchy--Schwarz proof that its pairing is also null.
-/

import YMGap.Continuum.RationalDualTestNormalization
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.RationalDualTestOptimization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- Exact rational maximizing coefficient when the cost is positive. -/
def coefficient (A C : Q') (hC : (0 : Q') < C) : Q' :=
  Q'.divPos A C hC

/-- The homogeneous rational Rayleigh gain. -/
def gain (A C : Q') (hC : (0 : Q') < C) : Q' :=
  Q'.divPos (A*A) C hC

private theorem reciprocal_correction_zero (C : Q') (hC : (0 : Q') < C) :
    1 + -(Q'.recipPos C hC * C) ≈ 0 :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (Q'.recipPos C hC) C)
          (Q'.mul_recipPos_eqv C hC))))
    (Q'.add_neg_self_eqv _)

/-- The chosen coefficient attains the exact dual quadratic value. -/
theorem value_identity (A C : Q') (hC : (0 : Q') < C) :
    RationalDualTestNormalization.value (coefficient A C hC) A C ≈
      gain A C hC := by
  let r := Q'.recipPos C hC
  have he : RationalDualTestNormalization.value (coefficient A C hC) A C ≈
      gain A C hC + (A*A*r)*(1 + -(r*C)) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.mul (.var 0) (.var 2)) (.var 0))
        (.mul (.mul (.var 0) (.var 2)) (.var 0)))
        (.neg (.mul (.mul (.mul (.var 0) (.var 2))
          (.mul (.var 0) (.var 2))) (.var 1))))
      (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
        (.mul (.mul (.mul (.var 0) (.var 0)) (.var 2))
          (.add (.const 1) (.neg (.mul (.var 2) (.var 1))))))
      (by decide) (fun | 0 => A | 1 => C | _ => r)
  exact Q'.eqv_trans _ _ _ he
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (reciprocal_correction_zero C hC))
          (Q'.mul_zero_eqv _)))
      (Q'.eqv_of_eq (Q'.add_zero' _)))

/-- Positive cost makes the optimized rational gain nonnegative. -/
theorem gain_nonnegative (A C : Q') (hC : (0 : Q') < C) :
    (0 : Q') ≤ gain A C hC :=
  Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg A)
    (Q'.le_of_lt (Q'.recipPos_pos C hC))

/-- Square completion: no other rational coefficient exceeds the exact gain. -/
theorem value_le_gain (A C b : Q') (hC : (0 : Q') < C) :
    RationalDualTestNormalization.value b A C ≤ gain A C hC := by
  let r := Q'.recipPos C hC
  let u := b + -(A*r)
  have hsq : (0 : Q') ≤ C * (u*u) :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt hC) (SumOfSquares.q_mul_self_nonneg u)
  have he : RationalDualTestNormalization.value b A C + C*(u*u) ≈
      gain A C hC +
        (((b*A+b*A) + -(A*A*r)) * (1 + -(r*C))) :=
    poly_identity_of_normal_eq
      (.add
        (.add (.add (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0)))
          (.neg (.mul (.mul (.var 1) (.var 1)) (.var 2))))
        (.mul (.var 2)
          (.mul (.add (.var 1) (.neg (.mul (.var 0) (.var 3))))
            (.add (.var 1) (.neg (.mul (.var 0) (.var 3)))))))
      (.add (.mul (.mul (.var 0) (.var 0)) (.var 3))
        (.mul
          (.add (.add (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0)))
            (.neg (.mul (.mul (.var 0) (.var 0)) (.var 3))))
          (.add (.const 1) (.neg (.mul (.var 3) (.var 2))))))
      (by decide) (fun | 0 => A | 1 => b | 2 => C | _ => r)
  have hzero :
      (((b*A+b*A) + -(A*A*r)) * (1 + -(r*C))) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (reciprocal_correction_zero C hC))
      (Q'.mul_zero_eqv _)
  have hfinal : RationalDualTestNormalization.value b A C + C*(u*u) ≈
      gain A C hC :=
    Q'.eqv_trans _ _ _ he
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) hzero)
        (Q'.eqv_of_eq (Q'.add_zero' _)))
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ hsq)
    (Q'.le_of_eqv hfinal)

#print axioms coefficient
#print axioms gain
#print axioms value_identity
#print axioms gain_nonnegative
#print axioms value_le_gain

end YMGap.Continuum.RationalDualTestOptimization
