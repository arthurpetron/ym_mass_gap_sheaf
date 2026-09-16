/-
# Rational relative perturbations with both endpoint partitions retained

The changes of numerator and partition are measured relative to the NEW
partition Z, while the original numerator is bounded relative to z.
Expanding the signed determinant before applying the triangle inequality
therefore gives the coefficient 2*c*eta directly against Z*z.

No positive reciprocal, eta-smallness assumption, or volume-dependent
partition floor is used. This is rational local-perturbation algebra, not
a spatial-decay or spectral-gap estimate.
-/

import YMGap.Constructive.CRealExp
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.RationalRelativePerturbation

set_option autoImplicit false

open YMGap.Constructive

local infix:50 " ≈ " => Q'.eqv

/-- Endpoint-relative errors preserve both partitions in the determinant
bound; neither partition is inverted or replaced by an absolute floor. -/
theorem relative_determinant_bound (a A z Z c eta : Q')
    (hc : (0 : Q') ≤ c) (he : (0 : Q') ≤ eta)
    (hz : (0 : Q') ≤ z) (hZ0 : (0 : Q') ≤ Z)
    (ha : Q'.abs a ≤ c * z)
    (hd : Q'.abs (A + -a) ≤ (c * eta) * Z)
    (hZ : Q'.abs (Z + -z) ≤ eta * Z) :
    Q'.abs (A * z + -(a * Z)) ≤ (2 * c * eta) * (Z * z) := by
  have hsplit : A * z + -(a * Z) ≈
      (A + -a) * z + -(a * (Z + -z)) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 0) (.var 3))))
      (.add (.mul (.add (.var 1) (.neg (.var 0))) (.var 2))
        (.neg (.mul (.var 0) (.add (.var 3) (.neg (.var 2))))))
      (by decide) (fun | 0 => a | 1 => A | 2 => z | _ => Z)
  have hfirst : Q'.abs ((A + -a) * z) ≤ ((c * eta) * Z) * z := by
    have h := ExpNeg.abs_mul_le (A + -a) z
    rw [ExpNeg.abs_of_nonneg hz] at h
    exact Q'.le_trans' _ _ _ h
      (Q'.mul_le_mul_of_nonneg hd (Q'.le_refl' z)
        (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hc he) hZ0) hz)
  have hsecond : Q'.abs (-(a * (Z + -z))) ≤ (c * z) * (eta * Z) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _))
      (Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le a (Z + -z))
        (Q'.mul_le_mul_of_nonneg ha hZ (Q'.mul_nonneg _ _ hc hz) (Q'.abs_nonneg _)))
  have hcollect : ((c * eta) * Z) * z + (c * z) * (eta * Z) ≈
      (2 * c * eta) * (Z * z) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
        (.mul (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))))
      (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.mul (.var 2) (.var 3)))
      (by decide) (fun | 0 => c | 1 => eta | 2 => Z | _ => z)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hsplit))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.le_trans' _ _ _ (Q'.add_le_add hfirst hsecond) (Q'.le_of_eqv hcollect)))

end YMGap.Continuum.RationalRelativePerturbation

#print axioms YMGap.Continuum.RationalRelativePerturbation.relative_determinant_bound
