/-
# Rational centering and variance comparison

For raw mass z, first moment a, second moment b and a supplied reciprocal
pin z*s = 1, the normalized squared distance from c is exactly the
normalized variance plus (c-a*s)^2. The explicit normalized mean therefore
minimizes that quadratic, without an existence or minimization oracle.

A comparison of the squared tests at every rational center transfers to
the two endpoint variances by choosing the OLD mean. This is algebra and
order: the comparison of actual original-action moments is a separate
consumer, not an assumed physical contraction or spatial-decay theorem.
-/

import YMGap.Constructive.SumOfSquares
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.RationalVarianceComparison

set_option autoImplicit false

open YMGap.Constructive

local infix:50 " ≈ " => Q'.eqv

/-- Normalized variance from the two raw moments and the SAME reciprocal. -/
def variance (a b s : Q') : Q' := b * s + -((a * s) * (a * s))

/-- Normalized squared test about the explicit rational center c. -/
def quadratic (z a b s c : Q') : Q' := (b + -(2 * c * a) + c * c * z) * s

/-- Completing the square retains the original mass-normalization pin. -/
theorem quadratic_decomposition (z a b s c : Q') (hz : z * s ≈ 1) :
    quadratic z a b s c ≈ variance a b s + (c + -(a * s)) * (c + -(a * s)) := by
  have hfactor : quadratic z a b s c ≈
      (b * s + -(2 * c * (a * s))) + (c * c) * (z * s) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.add (.add (.var 2) (.neg (.mul (.mul (.const 2) (.var 4)) (.var 1))))
        (.mul (.mul (.var 4) (.var 4)) (.var 0))) (.var 3))
      (.add (.add (.mul (.var 2) (.var 3))
        (.neg (.mul (.mul (.const 2) (.var 4)) (.mul (.var 1) (.var 3)))))
        (.mul (.mul (.var 4) (.var 4)) (.mul (.var 0) (.var 3))))
      (by decide) (fun | 0 => z | 1 => a | 2 => b | 3 => s | _ => c)
  have hsquare : (c * c) * (z * s) ≈ c * c :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_one_eqv _)
  have hcomplete : (b * s + -(2 * c * (a * s))) + c * c ≈
      variance a b s + (c + -(a * s)) * (c + -(a * s)) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.mul (.mul (.const 2) (.var 2)) (.var 1))))
        (.mul (.var 2) (.var 2)))
      (.add (.add (.var 0) (.neg (.mul (.var 1) (.var 1))))
        (.mul (.add (.var 2) (.neg (.var 1))) (.add (.var 2) (.neg (.var 1)))))
      (by decide) (fun | 0 => b * s | 1 => a * s | _ => c)
  exact Q'.eqv_trans _ _ _ hfactor
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hsquare) hcomplete)

/-- The explicit rational endpoint mean attains its normalized variance. -/
theorem quadratic_minimizer (z a b s : Q') (hz : z * s ≈ 1) :
    quadratic z a b s (a * s) ≈ variance a b s :=
  Q'.eqv_trans _ _ _ (quadratic_decomposition z a b s (a * s) hz)
    (RingNormaliser.poly_identity_of_normal_eq
      (.add (.var 0) (.mul (.add (.var 1) (.neg (.var 1))) (.add (.var 1) (.neg (.var 1)))))
      (.var 0) (by decide) (fun | 0 => variance a b s | _ => a * s))

/-- Every rational center has squared cost at least the variance. -/
theorem variance_le_quadratic (z a b s c : Q') (hz : z * s ≈ 1) :
    variance a b s ≤ quadratic z a b s c :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (SumOfSquares.q_mul_self_nonneg _))
    (Q'.ge_of_eqv (quadratic_decomposition z a b s c hz))

/-- Compare at the OLD explicit mean, then minimize at the NEW mean.
No positivity of C is needed for this implication. -/
theorem variance_transport (z a b s Z A B S C : Q')
    (hz : z * s ≈ 1) (hZ : Z * S ≈ 1)
    (hcompare : ∀ c : Q', quadratic Z A B S c ≤ C * quadratic z a b s c) :
    variance A B S ≤ C * variance a b s :=
  Q'.le_trans' _ _ _ (variance_le_quadratic Z A B S (a * s) hZ)
    (Q'.le_trans' _ _ _ (hcompare (a * s))
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (quadratic_minimizer z a b s hz))))

end YMGap.Continuum.RationalVarianceComparison

#print axioms YMGap.Continuum.RationalVarianceComparison.variance
#print axioms YMGap.Continuum.RationalVarianceComparison.quadratic
#print axioms YMGap.Continuum.RationalVarianceComparison.quadratic_decomposition
#print axioms YMGap.Continuum.RationalVarianceComparison.quadratic_minimizer
#print axioms YMGap.Continuum.RationalVarianceComparison.variance_le_quadratic
#print axioms YMGap.Continuum.RationalVarianceComparison.variance_transport
