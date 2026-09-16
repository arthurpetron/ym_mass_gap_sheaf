/-
# A positive-partition ratio comparison

The numerator bound A <= c*b and partition comparison z <= c*Z imply
A/Z <= c^2*b/z. Only b and c must be nonnegative; A may be signed.
Both denominators are the supplied positive original quantities.
-/

import YMGap.Constructive.Sqrt
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.RationalPositiveRatioComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- Compare normalized values without assuming a sign for the numerator. -/
theorem ratio_comparison (A b z Z c : Q')
    (hz : (0 : Q') < z) (hZ : (0 : Q') < Z)
    (hc : (0 : Q') ≤ c) (hb : (0 : Q') ≤ b)
    (hA : A ≤ c*b) (hzZ : z ≤ c*Z) :
    A * Q'.recipPos Z hZ ≤ (c*c) * (b * Q'.recipPos z hz) := by
  let rz := Q'.recipPos z hz
  let rZ := Q'.recipPos Z hZ
  have hzpos : (0 : Q') ≤ rz := Q'.le_of_lt (Q'.recipPos_pos z hz)
  have hZpos : (0 : Q') ≤ rZ := Q'.le_of_lt (Q'.recipPos_pos Z hZ)
  have hswap : (c*Z)*rz ≈ Z*(c*rz) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => c | 1 => Z | _ => rz)
  have hrec : rZ ≤ c*rz := by
    refine Q'.le_of_mul_le_mul_left (c := Z) ?_ hZ
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_recipPos_eqv Z hZ))
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_recipPos_eqv z hz))
        (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ rz hzZ hzpos)
          (Q'.le_of_eqv hswap)))
  have hcollect : (c*b)*(c*rz) ≈ (c*c)*(b*rz) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
      (by decide) (fun | 0 => c | 1 => b | _ => rz)
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ rZ hA hZpos)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ (c*b) hrec
      (Q'.mul_nonneg _ _ hc hb)) (Q'.le_of_eqv hcollect))

end YMGap.Continuum.RationalPositiveRatioComparison

#print axioms YMGap.Continuum.RationalPositiveRatioComparison.ratio_comparison
