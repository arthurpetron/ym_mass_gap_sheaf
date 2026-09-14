/-
# A linear guard for a finite product ceiling

For d >= 0, (1-n*d)*(1+d)^n <= 1. The induction subtracts the
nonnegative correction (n+1)*d^2 at each step. Thus a small linear
guard, rather than a large rational power computation, certifies (1+d)^n <= 2.
-/

import YMGap.Continuum.TotalMajorantClose
import YMGap.Continuum.RingNormaliser
import YMGap.Continuum.ClusterCount

namespace YMGap.Continuum.RationalLinearPowerCeiling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (PolyExpr poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem step_le (d : Q') (hd : (0 : Q') ≤ d) (n : Nat) :
    (1 + -(Q'.ofNat (n+1)*d))*(1+d) ≤ 1 + -(Q'.ofNat n*d) := by
  have he : (1 + -(Q'.ofNat (n+1)*d))*(1+d) ≈
      (1 + -(Q'.ofNat n*d)) + -((Q'.ofNat n+1)*(d*d)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv n 1))))) ?_
    exact poly_identity_of_normal_eq
      (.mul (.add (.const 1) (.neg (.mul (.add (.var 0) (.const 1)) (.var 1))))
        (.add (.const 1) (.var 1)))
      (.add (.add (.const 1) (.neg (.mul (.var 0) (.var 1))))
        (.neg (.mul (.add (.var 0) (.const 1)) (.mul (.var 1) (.var 1)))))
      (by decide) (fun i => if i=0 then Q'.ofNat n else d)
  have hn := Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ (ClusterCount.ofNat_nonneg n) Q'.zero_le_one) (Q'.mul_nonneg _ _ hd hd)
  have hsub : (1 + -(Q'.ofNat n*d)) + -((Q'.ofNat n+1)*(d*d)) ≤ 1 + -(Q'.ofNat n*d) := by
    apply Q'.le_of_sub_nonneg
    exact Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.var 1) (.add (.var 0) (.neg (.add (.var 0) (.neg (.var 1)))))
      (by decide) (fun i => if i=0 then 1 + -(Q'.ofNat n*d) else (Q'.ofNat n+1)*(d*d))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hsub

/-- No guard on n*d is needed for this invariant. -/
theorem linear_inverse_bound {d : Q'} (hd : (0 : Q') ≤ d) : ∀ n : Nat,
    (1 + -(Q'.ofNat n*d))*(1+d)^n ≤ 1
  | 0 => Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.add (.const 1) (.neg (.mul (.const 0) (.var 0)))) (.const 1))
      (.const 1) (by decide) (fun _ => d))
  | n+1 => by
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (step_le d hd n)
          (Q'.pow_nonneg _ (Q'.zero_le_add _ _ Q'.zero_le_one hd) n))
        (linear_inverse_bound hd n))

theorem power_le_two {d : Q'} (hd : (0 : Q') ≤ d) (n : Nat)
    (hlinear : HalfPow.half ≤ 1 + -(Q'.ofNat n*d)) : (1+d)^n ≤ 2 := by
  have h := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hlinear
      (Q'.pow_nonneg _ (Q'.zero_le_add _ _ Q'.zero_le_one hd) n))
    (linear_inverse_bound hd n)
  exact Q'.le_of_mul_le_mul_left (Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (by decide : Q'.eqv 1 (HalfPow.half*2)))) (by decide)

end YMGap.Continuum.RationalLinearPowerCeiling

#print axioms YMGap.Continuum.RationalLinearPowerCeiling.linear_inverse_bound
#print axioms YMGap.Continuum.RationalLinearPowerCeiling.power_le_two
