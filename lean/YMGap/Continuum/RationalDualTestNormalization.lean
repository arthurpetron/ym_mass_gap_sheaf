/-
# An explicit scalar choice for finite signed dual tests

For pairing A and nonnegative squared norm C choose a=A/(1+C).
Then 2*a*A-a^2*C=A^2/(1+C)+a^2. The guaranteed gain is nonnegative
and is positive when A is positively witnessed. No division by C or by
a possibly null vector norm occurs. Physical pairings and norms must still
be supplied by actual tests; this does not produce uniform coercivity.
-/

import YMGap.Continuum.HamiltonianScalar
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.RationalDualTestNormalization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- Finite rational coefficient; valid even when C is zero. -/
def coefficient (A C : Q') : Q' := A * ExpUBInstance.oneOver1p C

def gain (A C : Q') : Q' := (A*A) * ExpUBInstance.oneOver1p C

def value (a A C : Q') : Q' := (a*A+a*A) + -((a*a)*C)

private theorem correction_zero (C : Q') (hC : (0 : Q') ≤ C) :
    1 + -(ExpUBInstance.oneOver1p C * (1+C)) ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.neg_eqv_congr _ _ (ExpUBInstance.oneOver1p_mul_oneAddX C hC)))
    (Q'.add_neg_self_eqv _)

/-- The normalized value retains the actual cost C, not a supplied coarse cap. -/
theorem value_identity (A C : Q') (hC : (0 : Q') ≤ C) :
    value (coefficient A C) A C ≈
      gain A C + coefficient A C * coefficient A C := by
  let r := ExpUBInstance.oneOver1p C
  have he : value (coefficient A C) A C ≈
      (gain A C + coefficient A C * coefficient A C) +
        (A*A*r)*(1 + -(r*(1+C))) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.mul (.var 0) (.var 2)) (.var 0))
        (.mul (.mul (.var 0) (.var 2)) (.var 0)))
        (.neg (.mul (.mul (.mul (.var 0) (.var 2))
          (.mul (.var 0) (.var 2))) (.var 1))))
      (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 0) (.var 2))))
        (.mul (.mul (.mul (.var 0) (.var 0)) (.var 2))
          (.add (.const 1) (.neg (.mul (.var 2) (.add (.const 1) (.var 1)))))))
      (by decide) (fun | 0 => A | 1 => C | _ => r)
  exact Q'.eqv_trans _ _ _ he
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (correction_zero C hC))
        (Q'.mul_zero_eqv _))) (Q'.eqv_of_eq (Q'.add_zero' _)))

theorem gain_nonnegative (A C : Q') : (0 : Q') ≤ gain A C :=
  Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg A)
    (ExpUBInstance.oneOver1p_nonneg C)

theorem gain_positive (A C : Q') (hA : (0 : Q') < A) :
    (0 : Q') < gain A C :=
  Q'.mul_pos (Q'.mul_pos hA hA) (oneOver1p_pos C)

/-- A computable guaranteed lower gain for the chosen rational coefficient. -/
theorem gain_le_value (A C : Q') (hC : (0 : Q') ≤ C) :
    gain A C ≤ value (coefficient A C) A C :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (SumOfSquares.q_mul_self_nonneg (coefficient A C)))
    (Q'.ge_of_eqv (value_identity A C hC))

#print axioms coefficient
#print axioms value_identity
#print axioms gain_nonnegative
#print axioms gain_positive
#print axioms gain_le_value

end YMGap.Continuum.RationalDualTestNormalization
