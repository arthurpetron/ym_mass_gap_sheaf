/-
# Division-free variance comparison from one explicit centered test

The test is the squared polynomial M*f-b, where M is the positive
reference mass and b its raw first moment. Multiplying its cap bound by
the nonnegative target mass Z leaves the correction square (M*B-Z*b)^2.
Discarding that square and cancelling the positive factor M^2 gives the
target variance determinant bound without constructing either reciprocal.

This is scalar algebra for the original Dirichlet marginal comparison.
It supplies no kernel estimate, physical variance bound or uniform rate.
The actual centered-test bound remains an explicit premise; no sign is
required of the cap U or any of the first or second moments.
-/

import YMGap.Continuum.RationalVarianceComparison
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.RationalVarianceCapComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- Exact correction square for the division-free reference-centered test. -/
theorem centered_test_decomposition (M Z A B b : Q') :
    (M*M)*(Z*A + -(B*B)) + (M*B + -(Z*b))*(M*B + -(Z*b)) ≈
      Z*(M*M*A + -(2*M*b*B) + b*b*Z) :=
  poly_identity_of_normal_eq
    (.add
      (.mul (.mul (.var 0) (.var 0))
        (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 3) (.var 3)))))
      (.mul
        (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 4))))
        (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 4))))))
    (.mul (.var 1)
      (.add
        (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
          (.neg (.mul (.mul (.mul (.const 2) (.var 0)) (.var 4)) (.var 3))))
        (.mul (.mul (.var 4) (.var 4)) (.var 1))))
    (by decide) (fun | 0 => M | 1 => Z | 2 => A | 3 => B | _ => b)

private theorem centered_cap_reorder (M Z b C U : Q') :
    Z*(U*M*(M*M*C + -(2*M*b*b) + b*b*M)) ≈
      (M*M)*(U*Z*(M*C + -(b*b))) :=
  poly_identity_of_normal_eq
    (.mul (.var 1)
      (.mul (.mul (.var 4) (.var 0))
        (.add
          (.add (.mul (.mul (.var 0) (.var 0)) (.var 3))
            (.neg (.mul (.mul (.mul (.const 2) (.var 0)) (.var 2)) (.var 2))))
          (.mul (.mul (.var 2) (.var 2)) (.var 0)))))
    (.mul (.mul (.var 0) (.var 0))
      (.mul (.mul (.var 4) (.var 1))
        (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 2) (.var 2))))))
    (by decide) (fun | 0 => M | 1 => Z | 2 => b | 3 => C | _ => U)

/-- A cap on the single reference-centered squared test bounds the target
variance determinant. Only the two displayed mass signs are needed. -/
theorem variance_cap_of_centered_test (M Z A B b C U : Q')
    (hM : (0 : Q') < M) (hZ : (0 : Q') ≤ Z)
    (htest : M*M*A + -(2*M*b*B) + b*b*Z ≤
      U*M*(M*M*C + -(2*M*b*b) + b*b*M)) :
    Z*A + -(B*B) ≤ U*Z*(M*C + -(b*b)) := by
  have hstart : (M*M)*(Z*A + -(B*B)) ≤
      Z*(M*M*A + -(2*M*b*B) + b*b*Z) :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ _
        (SumOfSquares.q_mul_self_nonneg (M*B + -(Z*b))))
      (Q'.le_of_eqv (centered_test_decomposition M Z A B b))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ Z htest hZ
  have hfinish : (M*M)*(Z*A + -(B*B)) ≤
      (M*M)*(U*Z*(M*C + -(b*b))) :=
    Q'.le_trans' _ _ _ hstart
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (centered_cap_reorder M Z b C U)))
  exact Q'.le_of_mul_le_mul_left hfinish (Q'.mul_pos hM hM)

end YMGap.Continuum.RationalVarianceCapComparison

#print axioms YMGap.Continuum.RationalVarianceCapComparison.centered_test_decomposition
#print axioms YMGap.Continuum.RationalVarianceCapComparison.variance_cap_of_centered_test
