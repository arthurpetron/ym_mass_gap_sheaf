/-
# Cleared reverse Poincare law for the actual finite product attenuation

Squared attenuation pays the total Casimir from its actual norm decrement:

 (1-w*w)*totalCasimir(ds)*productAttenuation(w,K,ds)^2
 <= (w*w)*(1-productAttenuation(w,K,ds)^2).

The bound has no extent factor, cutoff guard, degree restriction or inverse.
Zero total Casimir and both nome endpoints are included. An omitted path
has attenuation zero and is handled literally. This scalar result does not
by itself identify an interacting transfer or completed OS norm decrement.
-/

import YMGap.Continuum.SU2HeatSquaredCasimirSmoothing
import YMGap.Continuum.SU2HeatProductCutoffDebt

namespace YMGap.Continuum.SU2HeatProductReversePoincare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport (qpow qpow_nonneg)
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.SU2HeatProductCutoffDebt

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a b c d : Q'} (ha : a ≈ b) (hb : c ≈ d) :
    a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- The smallest term in a finite geometric sum gives the extra nome
factor. The zero exponent is retained rather than divided away. -/
theorem casimir_power_le_mul_geomSum {u : Q'}
    (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (E : Nat) :
    Q'.ofNat E*qpow u E ≤ u*geomSum u E := by
  cases E with
  | zero =>
      exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.zero_mul_eqv 1)
        (Q'.eqv_symm (Q'.mul_zero_eqv u)))
  | succ E =>
      have hsmall : Q'.ofNat (E+1)*qpow u E ≤ geomSum u (E+1) := by
        simpa only [Nat.add_sub_cancel] using (geomSum_ge_pow hu0 hu1 (E+1))
      have hmul := Q'.mul_le_mul_of_nonneg_right _ _ u hsmall hu0
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (E+1)) (qpow u E) u)))
        (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))

private theorem power_reverse_poincare {u : Q'}
    (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (E : Nat) :
    (((1 : Q')-u)*Q'.ofNat E)*qpow u E ≤ u*(1-qpow u E) := by
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ ((1 : Q')-u)
    (casimir_power_le_mul_geomSum hu0 hu1 E) (Q'.sub_nonneg_of_le hu1)
  have hright : ((1 : Q')-u)*(u*geomSum u E) ≈ u*(1-qpow u E) :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
        (fun | 0 => (1 : Q')-u | 1 => u | _ => geomSum u E))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (oneSub_pow_factor u E)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))

private theorem qpow_square (w : Q') : ∀ E : Nat,
    qpow w E*qpow w E ≈ qpow (w*w) E
  | 0 => Q'.one_mul_eqv 1
  | E+1 => by
      change (qpow w E*w)*(qpow w E*w) ≈ qpow (w*w) E*(w*w)
      exact Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
          (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
          (by decide) (fun | 0 => qpow w E | _ => w))
        (Q'.mul_eqv_congr_right _ _ _ (qpow_square w E))

/-- The full scalar power law, with a squared nome multiplying the genuine
square loss. Valid also at E=0, w=0 and w=1, with no reciprocal. -/
theorem qpow_squared_reverse_poincare {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (E : Nat) :
    (((1 : Q')-w*w)*Q'.ofNat E)*(qpow w E*qpow w E) ≤
      (w*w)*(1-qpow w E*qpow w E) := by
  have hu0 : (0 : Q') ≤ w*w := Q'.mul_nonneg _ _ hw0 hw0
  have hu1 : w*w ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ w hw1 hw0)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv w)) hw1)
  have hs := qpow_square w E
  have hl : (((1 : Q')-w*w)*Q'.ofNat E)*(qpow w E*qpow w E) ≈
      (((1 : Q')-w*w)*Q'.ofNat E)*qpow (w*w) E :=
    Q'.mul_eqv_congr_left _ _ _ hs
  have hr : (w*w)*(1-qpow (w*w) E) ≈ (w*w)*(1-qpow w E*qpow w E) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl 1) (Q'.neg_eqv_congr _ _ hs.symm))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
    (Q'.le_trans' _ _ _ (power_reverse_poincare hu0 hu1 E) (Q'.le_of_eqv hr))

/-- Every actual coordinatewise-cutoff degree path obeys the cleared
reverse Poincare inequality. Omitted modes cost only the nonnegative
squared nome; no cutoff largeness or total-degree guard is assumed. -/
theorem product_squared_reverse_poincare {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat) (ds : List Nat) :
    (((1 : Q')-w*w)*totalCasimir ds)*
        (productAttenuation w K ds*productAttenuation w K ds) ≤
      (w*w)*(1-productAttenuation w K ds*productAttenuation w K ds) := by
  have hp := productAttenuation_retained w K ds
  have hc := totalCasimirNat_pin ds
  by_cases hr : retained K ds = true
  · simp only [hr, if_true] at hp
    have hleft : (((1 : Q')-w*w)*totalCasimir ds)*
          (productAttenuation w K ds*productAttenuation w K ds) ≈
        (((1 : Q')-w*w)*Q'.ofNat (totalCasimirNat ds))*
          (qpow w (totalCasimirNat ds)*qpow w (totalCasimirNat ds)) :=
      mul_congr (Q'.mul_eqv_congr_left _ _ _ hc.symm) (mul_congr hp hp)
    have hright : (w*w)*(1-qpow w (totalCasimirNat ds)*qpow w (totalCasimirNat ds)) ≈
        (w*w)*(1-productAttenuation w K ds*productAttenuation w K ds) :=
      Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl 1)
        (Q'.neg_eqv_congr _ _ (mul_congr hp hp).symm))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ (qpow_squared_reverse_poincare hw0 hw1 _)
        (Q'.le_of_eqv hright))
  · simp only [hr] at hp
    have hs : productAttenuation w K ds*productAttenuation w K ds ≈ 0 :=
      Q'.eqv_trans _ _ _ (mul_congr hp hp) (Q'.zero_mul_eqv 0)
    have hleft : (((1 : Q')-w*w)*totalCasimir ds)*
        (productAttenuation w K ds*productAttenuation w K ds) ≈ 0 :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hs) (Q'.mul_zero_eqv _)
    have hright : (w*w)*(1-productAttenuation w K ds*productAttenuation w K ds) ≈ w*w :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl 1) (Q'.neg_eqv_congr _ _ hs)))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (by decide : (1 : Q')-0 ≈ 1))
          (Q'.mul_one_eqv _))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ hw0 hw0) (Q'.ge_of_eqv hright))

end YMGap.Continuum.SU2HeatProductReversePoincare

#print axioms YMGap.Continuum.SU2HeatProductReversePoincare.casimir_power_le_mul_geomSum
#print axioms YMGap.Continuum.SU2HeatProductReversePoincare.qpow_squared_reverse_poincare
#print axioms YMGap.Continuum.SU2HeatProductReversePoincare.product_squared_reverse_poincare
