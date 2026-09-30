/-
# Rational coercivity from the two signed Ward identities

No square root or fiberwise normalizer is used. The physical caller must
supply the original-weight Ward identities, the relative Young bounds,
the positive-square cross bound, and the plaquette kinematic identity.
The displayed inequalities are finite rational algebra, not a mass gap.
-/

import YMGap.Continuum.QuaternionHaarRelativeAngularYoung

namespace YMGap.Continuum.RationalRelativeWardPrediction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

def predictionFactor (C : Q') : Q' := (5+2*(C*C))*(2+3*(C*C))

theorem predictionFactor_positive (C : Q') : (0 : Q') < predictionFactor C := by
  have hu := SumOfSquares.q_mul_self_nonneg C
  exact Q'.mul_pos
    (Q'.pos_of_lt_of_le (by decide : (0 : Q') < 5)
      (Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hu)))
    (Q'.pos_of_lt_of_le (by decide : (0 : Q') < 2)
      (Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hu)))

/-- The explicit positive rational prediction floor. -/
def predictionFloor (C : Q') : Q' :=
  Q'.recipPos (predictionFactor C) (predictionFactor_positive C)

theorem predictionFloor_positive (C : Q') : (0 : Q') < predictionFloor C :=
  Q'.recipPos_pos _ (predictionFactor_positive C)

private theorem right_of_sum {a b c : Q'} (h : a+b ≈ c) : b ≈ c + -a :=
  Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.var 1)
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
      (by decide) (fun | 0 => a | _ => b))
    (Q'.add_eqv_congr' h (Q'.eqv_refl _))

/-- The uncentered Ward identity prevents the angular energy from vanishing
while the original second moment stays positive. -/
theorem square_le_energy (C E F R : Q') (hC : (0 : Q') < C)
    (hward : E+R ≈ 3*F)
    (hyoung : 2*(2*(C*C))*R ≤ 6*(C*C)*F+(2*(C*C))*(2*(C*C))*E) :
    3*F ≤ 2*(1+C*C)*E := by
  let u := C*C
  have hr := right_of_sum hward
  have hb := Q'.sub_nonneg_of_le hyoung
  have he : (6*u*F+(2*u)*(2*u)*E)+ -(2*(2*u)*R) ≈
      (2*u)*(2*(1+u)*E + -(3*F)) := Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left (2*(2*u)) _ _ hr)))
    (poly_identity_of_normal_eq
      (.add (.add (.mul (.mul (.const 6) (.var 0)) (.var 2))
        (.mul (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0))) (.var 1)))
        (.neg (.mul (.mul (.const 2) (.mul (.const 2) (.var 0)))
          (.add (.mul (.const 3) (.var 2)) (.neg (.var 1))))))
      (.mul (.mul (.const 2) (.var 0))
        (.add (.mul (.mul (.const 2) (.add (.const 1) (.var 0))) (.var 1))
          (.neg (.mul (.const 3) (.var 2)))))
      (by decide) (fun | 0 => u | 1 => E | _ => F))
  exact Q'.le_of_sub_nonneg (Q'.nonneg_of_mul_pos
    (Q'.mul_pos (by decide : (0 : Q') < 2) (Q'.mul_pos hC hC))
    (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv he)))

/-- The predictor Ward identity, relative Young and an ordinary weighted
square control energy by the actual prediction error. All signs remain. -/
theorem energy_le_prediction (C E F A B R : Q')
    (hFE : 3*F ≤ 2*(1+C*C)*E)
    (hward : E+R ≈ 3*B)
    (hyoung : -(2*R) ≤ 6*(C*C)*A+E)
    (hcross : 2*(4*(1+C*C))*B ≤ (4*(1+C*C))*(4*(1+C*C))*A+F) :
    E ≤ (24+36*(C*C))*A := by
  let u := C*C
  let t := 4*(1+u)
  have hu : (0 : Q') ≤ u := SumOfSquares.q_mul_self_nonneg C
  have hS : (0 : Q') < 1+u := Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.add_le_self_of_nonneg 1 u hu)
  have ht : (0 : Q') ≤ t := Q'.mul_nonneg _ _ (by decide) (Q'.le_of_lt hS)
  have hr := right_of_sum hward
  have h1 : (0 : Q') ≤ 6*B+6*u*A + -E := by
    have he : (6*u*A+E)+ -(-(2*R)) ≈ 6*B+6*u*A + -E :=
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.neg_eqv_congr _ _ (Q'.neg_eqv_congr _ _
            (Q'.mul_eqv_congr_left 2 _ _ hr))))
        (poly_identity_of_normal_eq
          (.add (.add (.mul (.mul (.const 6) (.var 0)) (.var 1)) (.var 3))
            (.neg (.neg (.mul (.const 2)
              (.add (.mul (.const 3) (.var 2)) (.neg (.var 3)))))))
          (.add (.add (.mul (.const 6) (.var 2))
            (.mul (.mul (.const 6) (.var 0)) (.var 1))) (.neg (.var 3)))
          (by decide) (fun | 0 => u | 1 => A | 2 => B | _ => E))
    exact Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le hyoung) (Q'.le_of_eqv he)
  have h2 : (0 : Q') ≤ t*t*A+F + -(2*t*B) := Q'.sub_nonneg_of_le hcross
  have h3 : (0 : Q') ≤ 2*(1+u)*E + -(3*F) := Q'.sub_nonneg_of_le hFE
  have hsum := Q'.zero_le_add _ _
    (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ ht h1)
      (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 3) h2)) h3
  have he : (t*(6*B+6*u*A + -E)+3*(t*t*A+F + -(2*t*B)))+
      (2*(1+u)*E + -(3*F)) ≈ (2*(1+u))*((24+36*u)*A + -E) :=
    poly_identity_of_normal_eq
      (.add
        (.add
          (.mul (.mul (.const 4) (.add (.const 1) (.var 0)))
            (.add (.add (.mul (.const 6) (.var 2))
              (.mul (.mul (.const 6) (.var 0)) (.var 1))) (.neg (.var 3))))
          (.mul (.const 3)
            (.add (.add
              (.mul (.mul (.mul (.const 4) (.add (.const 1) (.var 0)))
                (.mul (.const 4) (.add (.const 1) (.var 0)))) (.var 1)) (.var 4))
              (.neg (.mul (.mul (.const 2)
                (.mul (.const 4) (.add (.const 1) (.var 0)))) (.var 2))))))
        (.add (.mul (.mul (.const 2) (.add (.const 1) (.var 0))) (.var 3))
          (.neg (.mul (.const 3) (.var 4)))))
      (.mul (.mul (.const 2) (.add (.const 1) (.var 0)))
        (.add (.mul (.add (.const 24) (.mul (.const 36) (.var 0))) (.var 1))
          (.neg (.var 3))))
      (by decide) (fun | 0 => u | 1 => A | 2 => B | 3 => E | _ => F)
  exact Q'.le_of_sub_nonneg (Q'.nonneg_of_mul_pos
    (Q'.mul_pos (by decide : (0 : Q') < 2) hS)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv he)))

/-- The physical kinematic identity closes the rational prediction budget.
The original mass Z is retained; no mass is inverted in this theorem. -/
theorem prediction_bound (C E F A Z : Q')
    (hFE : 3*F ≤ 2*(1+C*C)*E)
    (hEA : E ≤ (24+36*(C*C))*A)
    (hkin : E+F ≈ 4*Z) : Z ≤ predictionFactor C*A := by
  let u := C*C
  have hu : (0 : Q') ≤ u := SumOfSquares.q_mul_self_nonneg C
  have hcoeff : (0 : Q') ≤ 5+2*u := Q'.zero_le_add _ _ (by decide)
    (Q'.mul_nonneg _ _ (by decide) hu)
  have hsum := Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ hcoeff (Q'.sub_nonneg_of_le hEA))
    (Q'.sub_nonneg_of_le hFE)
  have he : (5+2*u)*((24+36*u)*A + -E)+(2*(1+u)*E + -(3*F)) ≈
      12*(predictionFactor C*A + -Z) := by
    have hp : (5+2*u)*((24+36*u)*A + -E)+(2*(1+u)*E + -(3*F)) ≈
        12*((5+2*u)*(2+3*u)*A) + -(3*(E+F)) :=
      poly_identity_of_normal_eq
        (.add
          (.mul (.add (.const 5) (.mul (.const 2) (.var 0)))
            (.add (.mul (.add (.const 24) (.mul (.const 36) (.var 0))) (.var 1))
              (.neg (.var 2))))
          (.add (.mul (.mul (.const 2) (.add (.const 1) (.var 0))) (.var 2))
            (.neg (.mul (.const 3) (.var 3)))))
        (.add (.mul (.const 12)
          (.mul (.mul (.add (.const 5) (.mul (.const 2) (.var 0)))
            (.add (.const 2) (.mul (.const 3) (.var 0)))) (.var 1)))
          (.neg (.mul (.const 3) (.add (.var 2) (.var 3)))))
        (by decide) (fun | 0 => u | 1 => A | 2 => E | _ => F)
    exact Q'.eqv_trans _ _ _ hp (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left 3 _ _ hkin)))
      (poly_identity_of_normal_eq
        (.add (.mul (.const 12) (.var 0))
          (.neg (.mul (.const 3) (.mul (.const 4) (.var 1)))))
        (.mul (.const 12) (.add (.var 0) (.neg (.var 1))))
        (by decide) (fun | 0 => predictionFactor C*A | _ => Z)))
  exact Q'.le_of_sub_nonneg (Q'.nonneg_of_mul_pos
    (by decide : (0 : Q') < 12)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv he)))

/-- Normalize by precisely the original positive mass, not a new law. -/
theorem normalized_prediction_bound (C A Z : Q') (hZ : (0 : Q') < Z)
    (h : Z ≤ predictionFactor C*A) :
    predictionFloor C ≤ A*Q'.recipPos Z hZ := by
  let P := predictionFactor C
  let r := predictionFloor C
  let s := Q'.recipPos Z hZ
  have hr : P*r ≈ 1 := Q'.mul_recipPos_eqv P (predictionFactor_positive C)
  have hs : Z*s ≈ 1 := Q'.mul_recipPos_eqv Z hZ
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (r*s) h
    (Q'.mul_nonneg _ _ (Q'.le_of_lt (predictionFloor_positive C))
      (Q'.le_of_lt (Q'.recipPos_pos Z hZ)))
  have hl : (r*s)*Z ≈ r := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 0) (.mul (.var 2) (.var 1)))
      (by decide) (fun | 0 => r | 1 => s | _ => Z))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left r _ _ hs) (Q'.mul_one_eqv r))
  have hh : (r*s)*(P*A) ≈ A*s := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 3) (.var 1)) (.mul (.var 2) (.var 0)))
      (by decide) (fun | 0 => r | 1 => s | 2 => P | _ => A))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (A*s) _ _ hr) (Q'.mul_one_eqv (A*s)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hh))

#print axioms predictionFactor_positive
#print axioms predictionFloor_positive
#print axioms square_le_energy
#print axioms energy_le_prediction
#print axioms prediction_bound
#print axioms normalized_prediction_bound

end YMGap.Continuum.RationalRelativeWardPrediction
