/-
# Exact omitted-mode debt of the original finite product heat

The reference powers below are finite scalar coefficients on the ORIGINAL
computed degree paths, not a replacement heat operator. A path survives only
when EVERY degree is below the actual cutoff. Its omitted coefficient stays
explicit in the second-order Taylor identity. No source degree bound or
interacting variance estimate is assumed.
-/

import YMGap.Continuum.SU2HeatProductTaylorRemainder
import YMGap.Continuum.SU2HeatRetainedCubicTaylor

namespace YMGap.Continuum.SU2HeatProductCutoffDebt

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.SU2HeatRetainedCubicTaylor

local infix:50 " ≈ " => Q'.eqv

/-- Natural exponent before embedding in the constructive rational setoid. -/
def totalCasimirNat : List Nat → Nat
  | [] => 0
  | d::ds => d*(d+2) + totalCasimirNat ds

theorem totalCasimirNat_pin : ∀ ds : List Nat,
    Q'.ofNat (totalCasimirNat ds) ≈ totalCasimir ds
  | [] => Q'.eqv_refl _
  | _d::ds => Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (totalCasimirNat_pin ds))

/-- The original cutoff is coordinatewise, not a cutoff on the total sum. -/
def retained (K : Nat) : List Nat → Bool
  | [] => true
  | d::ds => decide (d ≤ K) && retained K ds

theorem productAttenuation_retained (w : Q') (K : Nat) : ∀ ds : List Nat,
    productAttenuation w K ds ≈
      (if retained K ds = true then qpow w (totalCasimirNat ds) else 0)
  | [] => Q'.eqv_refl _
  | d::ds => by
      by_cases hd : d ≤ K
      · simp only [productAttenuation, attenuation, retained,
          hd, decide_true, Bool.true_and]
        cases ht : retained K ds with
        | false =>
            simp only [Bool.false_eq_true, if_false]
            have ih := productAttenuation_retained w K ds
            simp only [ht, Bool.false_eq_true, if_false] at ih
            exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ ih)
              (Q'.mul_zero_eqv _)
        | true =>
            simp only [if_true]
            have ih := productAttenuation_retained w K ds
            simp only [ht, if_true] at ih
            exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ ih)
              (Q'.eqv_symm (qpow_add w _ _))
      · simp only [productAttenuation, attenuation, retained,
          hd, decide_false, Bool.false_and, Bool.false_eq_true, if_false]
        exact Q'.zero_mul_eqv _

/-- Exactly the reference coefficient removed by the ORIGINAL cutoff. -/
def omittedDebt (w : Q') (K : Nat) (ds : List Nat) : Q' :=
  if retained K ds = true then 0 else qpow w (totalCasimirNat ds)

theorem productAttenuation_debt (w : Q') (K : Nat) (ds : List Nat) :
    productAttenuation w K ds ≈ qpow w (totalCasimirNat ds) - omittedDebt w K ds := by
  have hp := productAttenuation_retained w K ds
  by_cases hr : retained K ds = true
  · simp only [hr, if_true] at hp
    unfold omittedDebt
    rw [if_pos hr]
    exact Q'.eqv_trans _ _ _ hp (Q'.eqv_symm
      (poly_identity_of_normal_eq (.add (.var 0) (.neg (.const 0)))
        (.var 0) (by decide) (fun _ => qpow w (totalCasimirNat ds))))
  · simp only [hr] at hp
    unfold omittedDebt
    rw [if_neg hr]
    exact Q'.eqv_trans _ _ _ hp (Q'.eqv_symm
      (poly_identity_of_normal_eq (.add (.var 0) (.neg (.var 0)))
        (.const 0) (by decide) (fun _ => qpow w (totalCasimirNat ds))))

theorem omittedDebt_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K : Nat) (ds : List Nat) : (0 : Q') ≤ omittedDebt w K ds := by
  unfold omittedDebt
  split
  · exact Q'.le_refl' _
  · exact qpow_nonneg w hw0 _

theorem omitted_totalCasimir (K : Nat) : ∀ ds : List Nat,
    retained K ds = false → (K+1)*(K+3) ≤ totalCasimirNat ds
  | [], h => by contradiction
  | d::ds, h => by
      by_cases hd : d ≤ K
      · have ht : retained K ds = false := by
          simpa only [retained, hd, decide_true, Bool.true_and] using h
        exact Nat.le_trans (omitted_totalCasimir K ds ht) (Nat.le_add_left _ _)
      · have hk : K+1 ≤ d := by omega
        exact Nat.le_trans (Nat.mul_le_mul hk (by omega)) (Nat.le_add_right _ _)

/-- Explicit scalar tail factor. The signed pairing coefficients still have
to be paid; this is not a bound relative to interacting variance. -/
theorem omittedDebt_le_tail {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (K : Nat) (ds : List Nat) :
    omittedDebt w K ds ≤ qpow w ((K+1)*(K+3)) := by
  unfold omittedDebt
  by_cases hr : retained K ds = true
  · rw [if_pos hr]
    exact qpow_nonneg w hw0 _
  · rw [if_neg hr]
    have hf : retained K ds = false := by
      cases he : retained K ds
      · rfl
      · exact False.elim (hr he)
    exact qpow_antitone hw0 hw1 _ _ (omitted_totalCasimir K ds hf)

/-- Exact second order for EVERY actual cutoff path: retain its cubic
reference coefficient and its entire omitted-mode debt with the correct sign. -/
theorem productRemainder_secondOrder (w : Q') (K : Nat) (ds : List Nat) :
    productRemainder w K ds ≈
      (HalfPow.half * (((1 : Q')-w)*((1 : Q')-w))) *
        (totalCasimir ds*totalCasimir ds-totalCasimir ds) +
      cubicRemainder w (totalCasimirNat ds) - omittedDebt w K ds := by
  have hp := productAttenuation_debt w K ds
  have hc := Q'.eqv_symm (totalCasimirNat_pin ds)
  unfold productRemainder
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hp (Q'.eqv_refl _))
      (Q'.mul_eqv_congr_left _ _ _ hc)) ?_
  have hpoly :
      (qpow w (totalCasimirNat ds)-omittedDebt w K ds-1) +
        ((1 : Q')-w)*Q'.ofNat (totalCasimirNat ds) ≈
      (HalfPow.half * (((1 : Q')-w)*((1 : Q')-w))) *
        (Q'.ofNat (totalCasimirNat ds)*Q'.ofNat (totalCasimirNat ds)-
          Q'.ofNat (totalCasimirNat ds)) +
      cubicRemainder w (totalCasimirNat ds) - omittedDebt w K ds := by
    unfold cubicRemainder quadraticCoeff
    exact poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.neg (.var 1))) (.neg (.const 1)))
        (.mul (.var 2) (.var 3)))
      (.add (.add
        (.mul (.mul (.var 4) (.mul (.var 2) (.var 2)))
          (.add (.mul (.var 3) (.var 3)) (.neg (.var 3))))
        (.add (.add (.add (.var 0) (.neg (.const 1))) (.mul (.var 3) (.var 2)))
          (.neg (.mul (.mul (.var 4)
            (.add (.mul (.var 3) (.var 3)) (.neg (.var 3))))
            (.mul (.var 2) (.var 2)))))) (.neg (.var 1)))
      (by decide) (fun
        | 0 => qpow w (totalCasimirNat ds)
        | 1 => omittedDebt w K ds
        | 2 => (1 : Q')-w
        | 3 => Q'.ofNat (totalCasimirNat ds)
        | _ => HalfPow.half)
  exact Q'.eqv_trans _ _ _ hpoly
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _ (totalCasimirNat_pin ds))
            (Q'.mul_eqv_congr_left _ _ _ (totalCasimirNat_pin ds)))
          (Q'.neg_eqv_congr _ _ (totalCasimirNat_pin ds))))
        (Q'.eqv_refl _)) (Q'.eqv_refl _))

#print axioms totalCasimirNat
#print axioms totalCasimirNat_pin
#print axioms retained
#print axioms productAttenuation_retained
#print axioms omittedDebt
#print axioms productAttenuation_debt
#print axioms omittedDebt_nonnegative
#print axioms omitted_totalCasimir
#print axioms omittedDebt_le_tail
#print axioms productRemainder_secondOrder

end YMGap.Continuum.SU2HeatProductCutoffDebt
