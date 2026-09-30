/-
# Rational scaling of the relative Ward prediction floor

This is a denominator-cleared polynomial estimate. It does not assert that
the resulting normalized prediction floor survives a scaling limit.
-/

import YMGap.Continuum.RationalRelativeWardPrediction

namespace YMGap.Continuum.RationalRelativePredictionScaling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RationalRelativeWardPrediction

local infix:50 " ≈ " => Q'.eqv

private theorem square_scale (r C A : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r ≤ 1)
    (hC : (0 : Q') ≤ C) (hA : (0 : Q') ≤ A)
    (hCr : C*r ≤ A) :
    r*r ≤ 1 ∧ (C*C)*(r*r) ≤ A*A := by
  have hrr : r*r ≤ r := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left r 1 r hr1 hr0)
    (Q'.le_of_eqv (Q'.mul_one_eqv r))
  have hCr0 : (0 : Q') ≤ C*r := Q'.mul_nonneg C r hC hr0
  have hsq : (C*r)*(C*r) ≤ A*A :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right (C*r) A (C*r) hCr hCr0)
      (Q'.mul_le_mul_of_nonneg_left (C*r) A A hCr hA)
  have he : (C*C)*(r*r) ≈ (C*r)*(C*r) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => C | _ => r)
  exact ⟨Q'.le_trans' _ _ _ hrr hr1,
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hsq⟩

private theorem affine_scale (a b u v s : Q')
    (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b)
    (hs : s ≤ 1) (huv : u*s ≤ v) :
    (a+b*u)*s ≤ a+b*v := by
  have ha' : a*s ≤ a := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left s 1 a hs ha)
    (Q'.le_of_eqv (Q'.mul_one_eqv a))
  have hb' : (b*u)*s ≤ b*v := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_assoc_eqv b u s))
    (Q'.mul_le_mul_of_nonneg_left (u*s) v b huv hb)
  have hadd : a*s+(b*u)*s ≤ a+b*v :=
    Q'.add_le_add ha' hb'
  have he : (a+b*u)*s ≈ a*s+(b*u)*s :=
    poly_identity_of_normal_eq
      (.mul (.add (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
      (.add (.mul (.var 0) (.var 3))
        (.mul (.mul (.var 1) (.var 2)) (.var 3)))
      (by decide) (fun | 0 => a | 1 => b | 2 => u | _ => s)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hadd

private theorem fourth_power_pair (r : Q') :
    r^4 ≈ (r*r)*(r*r) := by
  change r*(r*(r*(r*1))) ≈ (r*r)*(r*r)
  exact poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 0)
      (.mul (.var 0) (.mul (.var 0) (.const 1)))))
    (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0)))
    (by decide) (fun _ => r)

/-- If `C*r ≤ A` and `0 ≤ r ≤ 1`, the Ward denominator at `C` grows
by at most the reciprocal fourth power of `r`. -/
theorem predictionFactor_fourth_scale (r C A : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r ≤ 1)
    (hC : (0 : Q') ≤ C) (hA : (0 : Q') ≤ A)
    (hCr : C*r ≤ A) :
    predictionFactor C * r^4 ≤ predictionFactor A := by
  let u := C*C
  let v := A*A
  let s := r*r
  let x := 5+2*u
  let y := 2+3*u
  let X := 5+2*v
  let Y := 2+3*v
  have hscale := square_scale r C A hr0 hr1 hC hA hCr
  have hx : x*s ≤ X := affine_scale 5 2 u v s
    (by decide) (by decide) hscale.1 hscale.2
  have hy : y*s ≤ Y := affine_scale 2 3 u v s
    (by decide) (by decide) hscale.1 hscale.2
  have hu : (0 : Q') ≤ u := SumOfSquares.q_mul_self_nonneg C
  have hv : (0 : Q') ≤ v := SumOfSquares.q_mul_self_nonneg A
  have hys : (0 : Q') ≤ y*s := Q'.mul_nonneg y s
    (Q'.zero_le_add _ _ (by decide)
      (Q'.mul_nonneg 3 u (by decide) hu))
    (Q'.mul_nonneg r r hr0 hr0)
  have hX : (0 : Q') ≤ X := Q'.zero_le_add _ _ (by decide)
    (Q'.mul_nonneg 2 v (by decide) hv)
  have hprod : (x*s)*(y*s) ≤ X*Y :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right (x*s) X (y*s) hx hys)
      (Q'.mul_le_mul_of_nonneg_left (y*s) Y X hy hX)
  have he : predictionFactor C * r^4 ≈ (x*s)*(y*s) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (predictionFactor C) _ _ (fourth_power_pair r))
      (poly_identity_of_normal_eq
        (.mul (.mul (.add (.const 5) (.mul (.const 2) (.var 0)))
          (.add (.const 2) (.mul (.const 3) (.var 0))))
          (.mul (.var 1) (.var 1)))
        (.mul (.mul (.add (.const 5) (.mul (.const 2) (.var 0))) (.var 1))
          (.mul (.add (.const 2) (.mul (.const 3) (.var 0))) (.var 1)))
        (by decide) (fun | 0 => u | _ => s))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hprod

/-- A directly usable lower bound on the positive prediction floor. -/
theorem fourth_le_factor_times_floor (r C A : Q')
    (hr0 : (0 : Q') ≤ r) (hr1 : r ≤ 1)
    (hC : (0 : Q') ≤ C) (hA : (0 : Q') ≤ A)
    (hCr : C*r ≤ A) :
    r^4 ≤ predictionFactor A * predictionFloor C := by
  have h := predictionFactor_fourth_scale r C A hr0 hr1 hC hA hCr
  have hs := Q'.mul_le_mul_of_nonneg_right
    (predictionFactor C * r^4) (predictionFactor A)
    (predictionFloor C) h (Q'.le_of_lt (predictionFloor_positive C))
  have hc : predictionFactor C * predictionFloor C ≈ 1 :=
    Q'.mul_recipPos_eqv _ (predictionFactor_positive C)
  have he : (predictionFactor C * r^4) * predictionFloor C ≈ r^4 :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.var 1))
        (by decide)
        (fun | 0 => predictionFactor C | 1 => r^4 | _ => predictionFloor C))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hc)
        (Q'.one_mul_eqv (r^4)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hs

#print axioms predictionFactor_fourth_scale
#print axioms fourth_le_factor_times_floor

end YMGap.Continuum.RationalRelativePredictionScaling
