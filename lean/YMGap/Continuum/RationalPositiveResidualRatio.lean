/-
# Cancellation of a common positive reference scale in rational ratios

The nonnegative partition residual X-l*Y controls the signed numerator
residual A-l*B. Expanding A*Y-B*X before taking absolute values preserves
that common reference scale. The determinant is bounded relative to X*Y,
and the existing positive-partition cancellation theorem removes both
actual denominators exactly.

The residual may vanish; neither it nor the reference scale is inverted.
No smallness of eta, sign of A or B, or absolute partition floor is needed.
This scalar lemma feeds the actual observed-window left-boundary comparison;
it makes no independent transfer, stationary-state, or physical-gap claim.
-/

import YMGap.Continuum.BF4ExactSlabFaceSetBoundaryComparison
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.RationalPositiveResidualRatio

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- A nonnegative relative partition residual gives a normalized signed
ratio error with no surviving reference scale or reciprocal ceiling. -/
theorem ratio_bound (A B X Y l c eta : Q')
    (hX : (0 : Q') < X) (hY : (0 : Q') < Y) (hl : (0 : Q') < l)
    (hc : (0 : Q') ≤ c) (heta : (0 : Q') ≤ eta)
    (hr0 : (0 : Q') ≤ X + -(l * Y))
    (hr : X + -(l * Y) ≤ eta * (l * Y))
    (hA : Q'.abs (A + -(l * B)) ≤ c * (X + -(l * Y)))
    (hB : Q'.abs B ≤ c * Y) :
    Q'.abs (A * Q'.recipPos X hX + -(B * Q'.recipPos Y hY)) ≤
      (c + c) * eta := by
  let r := X + -(l * Y)
  have hY0 : (0 : Q') ≤ Y := Q'.le_of_lt hY
  have hbase : (0 : Q') ≤ l * Y := Q'.le_of_lt (Q'.mul_pos hl hY)
  have hfloor : l * Y ≤ X := Q'.le_of_sub_nonneg hr0
  have hrX : r ≤ eta * X :=
    Q'.le_trans' _ _ _ hr
      (Q'.mul_le_mul_of_nonneg (Q'.le_refl' eta) hfloor heta hbase)
  have hsplit : A * Y + -(B * X) ≈
      (A + -(l * B)) * Y + -(B * r) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 3)) (.neg (.mul (.var 1) (.var 2))))
      (.add (.mul (.add (.var 0) (.neg (.mul (.var 4) (.var 1)))) (.var 3))
        (.neg (.mul (.var 1)
          (.add (.var 2) (.neg (.mul (.var 4) (.var 3)))))))
      (by decide) (fun | 0 => A | 1 => B | 2 => X | 3 => Y | _ => l)
  have hfirst : Q'.abs ((A + -(l * B)) * Y) ≤ (c * r) * Y := by
    have h := ExpNeg.abs_mul_le (A + -(l * B)) Y
    rw [ExpNeg.abs_of_nonneg hY0] at h
    exact Q'.le_trans' _ _ _ h (Q'.mul_le_mul_of_nonneg_right _ _ Y hA hY0)
  have hsecond : Q'.abs (-(B * r)) ≤ (c * Y) * r := by
    have h := ExpNeg.abs_mul_le B r
    rw [ExpNeg.abs_of_nonneg hr0] at h
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _))
      (Q'.le_trans' _ _ _ h (Q'.mul_le_mul_of_nonneg_right _ _ r hB hr0))
  have hcollect : (c * r) * Y + (c * Y) * r ≈ ((c + c) * r) * Y :=
    poly_identity_of_normal_eq
      (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.var 1)))
      (.mul (.mul (.add (.var 0) (.var 0)) (.var 1)) (.var 2))
      (by decide) (fun | 0 => c | 1 => r | _ => Y)
  have hscale : ((c + c) * r) * Y ≤ ((c + c) * (eta * X)) * Y :=
    Q'.mul_le_mul_of_nonneg_right _ _ Y
      (Q'.mul_le_mul_of_nonneg_left _ _ (c + c) hrX (Q'.zero_le_add _ _ hc hc)) hY0
  have hregroup : ((c + c) * (eta * X)) * Y ≈ ((c + c) * eta) * (X * Y) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.add (.var 0) (.var 0)) (.mul (.var 1) (.var 2))) (.var 3))
      (.mul (.mul (.add (.var 0) (.var 0)) (.var 1)) (.mul (.var 2) (.var 3)))
      (by decide) (fun | 0 => c | 1 => eta | 2 => X | _ => Y)
  apply BF4ExactSlabFaceSetBoundaryComparison.ratio_difference_bound A B X Y ((c + c) * eta) hX hY
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hsplit))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.le_trans' _ _ _ (Q'.add_le_add hfirst hsecond)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollect)
          (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hregroup)))))

end YMGap.Continuum.RationalPositiveResidualRatio

#print axioms YMGap.Continuum.RationalPositiveResidualRatio.ratio_bound
