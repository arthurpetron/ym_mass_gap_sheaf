/-
# Halving-time certificate ⇒ Wilson lower margin (REDUCTION, finite-check type)

Companion to `audits/SCOPE-RG-STEP-COMPOSITION-REDUCTION-2026-10-06.md`
§"Halving-time margin". ADDITIVE.

The margin half of `WilsonAFPaddedGapInput` (`m·2^{-j} ≤ 1 − r_j`) follows from ONE
integer halving-time certificate per scale: `r_j^{M0·2^j} ≤ 1/2` for a fixed `M0 ≥ 1`.
Physically: `n_j = M0·2^j` lattice steps at spacing `a_j = 2^{-j}` is the CONSTANT
physical time `M0`; the certificate says the vacuum-sector rate halves within physical
time `M0` at every scale. Then `m = 1/(2M0)`.

* `one_sub_pow_ge` (Bernoulli, reused from `bernoulli_pow`): `1 − n·d ≤ (1−d)^n`.
* `margin_of_pow_le_half`: `r^n ≤ 1/2`, `0 < n`, `0 ≤ r ≤ 1` ⇒ `1/(2n) ≤ 1 − r`
  (`halvingMargin n = 1/(2n)`); no case split, choice-free.
* `wilsonLowerMargin_of_halvingTime`, `wilsonLowerMarginFrom_of_halvingTime`.
* `wilsonAFPaddedGapInput_of_halvingTime`: DIRECT fit for the margin conjunct; the
  rate family, `r_j < 1` and the all-vector `WilsonVacuumSqContraction` stay OPEN inputs.

**REDUCTION.** No certificate is produced for any YM trajectory.
Constructive; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeWilsonMixRateDeadEnd
import YMGap.Continuum.BF4WilsonAllNomeStepRatioLinearCeiling

namespace YMGap.Continuum.BF4WilsonHalvingTimeMargin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeExprStepRatioWindowSurvival (bernoulli_pow)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonAllNomeWilsonDynamicFamily
  (WilsonDynamicFamily WilsonLowerMargin exprWilsonFamily)
open YMGap.Continuum.BF4WilsonAllNomeExprAFCalibrated (afPaddedZeroMomentumAFExpr)
open YMGap.Continuum.BF4WilsonAllNomeWilsonMixRateDeadEnd (WilsonAFPaddedGapInput)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition
  (WilsonLowerMarginFrom ofNat_two_pow_mul_half_pow exprWilsonFamily_spacing_half_pow)
open YMGap.Continuum.BF4WilsonAllNomeStepRatioLinearCeiling
  (lc_ofNat_mul lc_ofNat_nonneg lc_lt_of_lt_of_le lc_ofNat_le)

local infix:50 " ≈ " => Q'.eqv
local notation "trAF" => afPaddedZeroMomentumAFExpr.toExprAnchorTrajectory

/-- **Bernoulli.** `0 ≤ d ≤ 1` ⇒ `1 − n·d ≤ (1−d)^n`. -/
theorem one_sub_pow_ge (d : Q') (h0 : (0 : Q') ≤ d) (h1 : d ≤ 1) (n : Nat) :
    (1 : Q') - Q'.ofNat n * d ≤ ((1 : Q') - d) ^ n := by
  have hr0 : (0 : Q') ≤ (1 : Q') - d := Q'.sub_nonneg_of_le h1
  have hr1 : (1 : Q') - d ≤ 1 := by
    have h := Q'.add_le_add_left (1 : Q') (-d) 0
      (Q'.le_trans' _ _ _ (Q'.neg_le_neg h0) (by decide))
    rw [Q'.add_zero'] at h
    exact h
  have hb := bernoulli_pow ((1 : Q') - d) hr0 hr1 n
  have e : (1 : Q') - Q'.ofNat n * d ≈ (1 : Q') - Q'.ofNat n * ((1 : Q') - ((1 : Q') - d)) :=
    poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.mul (.var 0) (.var 1))))
      (.add (.const 1) (.neg (.mul (.var 0)
        (.add (.const 1) (.neg (.add (.const 1) (.neg (.var 1))))))))
      (by decide) (fun | 0 => Q'.ofNat n | _ => d)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e) hb

/-- `halvingMargin n = 1/(2n)` (for `n ≥ 1`). -/
def halvingMargin (n : Nat) : Q' := ⟨1, 2 * n - 1⟩

theorem halvingMargin_pos (n : Nat) : (0 : Q') < halvingMargin n := by
  show (0 : Int) * ((halvingMargin n).den : Int) < 1 * 1
  rw [Int.zero_mul]
  decide

theorem halvingMargin_mul_ofNat (n : Nat) (hn : 0 < n) :
    Q'.ofNat n * halvingMargin n ≈ half := by
  have hd : ((Q'.ofNat n * halvingMargin n).den : Int) = 2 * (n : Int) := by
    rw [Q'.mul_den_cast]
    show ((0 + 1 : Nat) : Int) * ((2 * n - 1 + 1 : Nat) : Int) = 2 * (n : Int)
    have : 2 * n - 1 + 1 = 2 * n := by omega
    rw [this]
    push_cast
    omega
  show ((n : Int) * 1) * (half.den : Int) = half.num * ((Q'.ofNat n * halvingMargin n).den : Int)
  rw [hd]
  show ((n : Int) * 1) * ((2 : Nat) : Int) = (1 : Int) * (2 * (n : Int))
  push_cast
  omega

/-- Multiplied form: `r^n ≤ 1/2`, `0 ≤ r ≤ 1` ⇒ `1/2 ≤ n·(1 − r)`. -/
theorem half_le_mul_margin_of_pow_le_half (r : Q') (n : Nat) (h0 : (0 : Q') ≤ r)
    (h1 : r ≤ 1) (h : r ^ n ≤ half) : half ≤ Q'.ofNat n * ((1 : Q') - r) := by
  have hb := bernoulli_pow r h0 h1 n
  have h2 : (1 : Q') - Q'.ofNat n * ((1 : Q') - r) ≤ half := Q'.le_trans' _ _ _ hb h
  -- 1 − X ≤ ½ ⇒ ½ ≤ X
  have h3 := Q'.add_le_add_right _ _ (Q'.ofNat n * ((1 : Q') - r) + -half) h2
  have e1 : (1 : Q') - Q'.ofNat n * ((1 : Q') - r) + (Q'.ofNat n * ((1 : Q') - r) + -half) ≈
      (1 : Q') + -half :=
    poly_identity_of_normal_eq
      (.add (.add (.const 1) (.neg (.var 0))) (.add (.var 0) (.neg (.var 1))))
      (.add (.const 1) (.neg (.var 1)))
      (by decide) (fun | 0 => Q'.ofNat n * ((1 : Q') - r) | _ => half)
  have e2 : half + (Q'.ofNat n * ((1 : Q') - r) + -half) ≈ Q'.ofNat n * ((1 : Q') - r) :=
    poly_identity_of_normal_eq
      (.add (.var 1) (.add (.var 0) (.neg (.var 1)))) (.var 0)
      (by decide) (fun | 0 => Q'.ofNat n * ((1 : Q') - r) | _ => half)
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ (by decide : half ≤ (1 : Q') + -half)
    (Q'.le_of_eqv (Q'.eqv_symm e1)))
    (Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv e2))

/-- **Halving margin.** `r^n ≤ 1/2`, `0 < n`, `0 ≤ r ≤ 1` ⇒ `1/(2n) ≤ 1 − r`.
Cancellation of the positive factor `n`; decidable `Q'` order, choice-free. -/
theorem margin_of_pow_le_half (r : Q') (n : Nat) (hn : 0 < n) (h0 : (0 : Q') ≤ r)
    (h1 : r ≤ 1) (h : r ^ n ≤ half) : halvingMargin n ≤ (1 : Q') - r := by
  have hm := half_le_mul_margin_of_pow_le_half r n h0 h1 h
  have hpos : (0 : Q') < Q'.ofNat n :=
    lc_lt_of_lt_of_le (by decide : (0 : Q') < Q'.ofNat 1) (lc_ofNat_le hn)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (halvingMargin_mul_ofNat n hn)) hm) hpos

/-- Scale step: `1/(2M0)·2^{-j}` vs `1/(2·M0·2^j)` in multiplied form. -/
theorem halvingMargin_scale (M0 j : Nat) (hM0 : 0 < M0) :
    Q'.ofNat (M0 * 2 ^ j) * (halvingMargin M0 * half ^ j) ≈ half := by
  have e1 : Q'.ofNat (M0 * 2 ^ j) * (halvingMargin M0 * half ^ j) ≈
      (Q'.ofNat M0 * Q'.ofNat (2 ^ j)) * (halvingMargin M0 * half ^ j) :=
    Q'.mul_eqv_congr_right _ _ _ (lc_ofNat_mul M0 (2 ^ j))
  have e2 : (Q'.ofNat M0 * Q'.ofNat (2 ^ j)) * (halvingMargin M0 * half ^ j) ≈
      (Q'.ofNat M0 * halvingMargin M0) * (Q'.ofNat (2 ^ j) * half ^ j) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
      (by decide)
      (fun | 0 => Q'.ofNat M0 | 1 => Q'.ofNat (2 ^ j) | 2 => halvingMargin M0 | _ => half ^ j)
  have e3 : (Q'.ofNat M0 * halvingMargin M0) * (Q'.ofNat (2 ^ j) * half ^ j) ≈ half * 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (halvingMargin_mul_ofNat M0 hM0))
      (Q'.mul_eqv_congr_left _ _ _ (ofNat_two_pow_mul_half_pow j))
  exact Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2
    (Q'.eqv_trans _ _ _ e3 (Q'.mul_one_eqv half)))

/-- One scale: certificate `r^{M0·2^j} ≤ 1/2` ⇒ `1/(2M0)·2^{-j} ≤ 1 − r`. -/
theorem scale_margin_of_halvingTime (r : Q') (M0 j : Nat) (hM0 : 0 < M0)
    (h0 : (0 : Q') ≤ r) (h1 : r ≤ 1) (h : r ^ (M0 * 2 ^ j) ≤ half) :
    halvingMargin M0 * half ^ j ≤ (1 : Q') - r := by
  have hm := half_le_mul_margin_of_pow_le_half r (M0 * 2 ^ j) h0 h1 h
  have hn : 0 < M0 * 2 ^ j := Nat.mul_pos hM0 (Nat.two_pow_pos j)
  have hpos : (0 : Q') < Q'.ofNat (M0 * 2 ^ j) :=
    lc_lt_of_lt_of_le (by decide : (0 : Q') < Q'.ofNat 1) (lc_ofNat_le hn)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (halvingMargin_scale M0 j hM0)) hm) hpos

/-- **PROVED (REDUCTION).** On dyadic spacing, `∀ j, r_j^{M0·2^j} ≤ 1/2` gives
`WilsonLowerMargin F (1/(2M0))`. -/
theorem wilsonLowerMargin_of_halvingTime (F : WilsonDynamicFamily) (M0 : Nat) (hM0 : 0 < M0)
    (hsp : ∀ j, F.transferSpacing.spacing j = half ^ j)
    (hcert : ∀ j, F.rate j ^ (M0 * 2 ^ j) ≤ half) :
    WilsonLowerMargin F (halvingMargin M0) := by
  refine ⟨halvingMargin_pos M0, fun j => ?_⟩
  rw [hsp j]
  exact scale_margin_of_halvingTime (F.rate j) M0 j hM0 (F.rate_nonnegative j)
    (Q'.le_of_lt (F.rate_lt_one j)) (hcert j)

/-- **PROVED (REDUCTION).** From-`j0` variant: certificates only for `j ≥ j0`. -/
theorem wilsonLowerMarginFrom_of_halvingTime (F : WilsonDynamicFamily) (j0 M0 : Nat)
    (hM0 : 0 < M0) (hsp : ∀ j, F.transferSpacing.spacing j = half ^ j)
    (hcert : ∀ j, j0 ≤ j → F.rate j ^ (M0 * 2 ^ j) ≤ half) :
    WilsonLowerMarginFrom F j0 (halvingMargin M0) := by
  refine ⟨halvingMargin_pos M0, fun j hj => ?_⟩
  rw [hsp j]
  exact scale_margin_of_halvingTime (F.rate j) M0 j hM0 (F.rate_nonnegative j)
    (Q'.le_of_lt (F.rate_lt_one j)) (hcert j hj)

/-- **Wiring (direct fit, REDUCTION).** A rate family on `trAF` with the all-vector
contraction (OPEN) and one halving-time certificate per scale witnesses
`WilsonAFPaddedGapInput` with `m = 1/(2M0)`. -/
theorem wilsonAFPaddedGapInput_of_halvingTime (r : Nat → Q')
    (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j < (1 : Q'))
    (Hc : ∀ j, WilsonVacuumSqContraction ((trAF).schedule.nome_pos j)
      ((trAF).schedule.nome_lt_one j) ((trAF).width j) (r j))
    (M0 : Nat) (hM0 : 0 < M0) (hcert : ∀ j, r j ^ (M0 * 2 ^ j) ≤ half) :
    WilsonAFPaddedGapInput :=
  ⟨r, hr0, hr1, Hc, halvingMargin M0,
    wilsonLowerMargin_of_halvingTime (exprWilsonFamily trAF r hr0 hr1 Hc) M0 hM0
      (exprWilsonFamily_spacing_half_pow trAF r hr0 hr1 Hc) hcert⟩

end YMGap.Continuum.BF4WilsonHalvingTimeMargin

#print axioms YMGap.Continuum.BF4WilsonHalvingTimeMargin.one_sub_pow_ge
#print axioms YMGap.Continuum.BF4WilsonHalvingTimeMargin.halvingMargin_mul_ofNat
#print axioms YMGap.Continuum.BF4WilsonHalvingTimeMargin.margin_of_pow_le_half
#print axioms YMGap.Continuum.BF4WilsonHalvingTimeMargin.wilsonLowerMargin_of_halvingTime
#print axioms YMGap.Continuum.BF4WilsonHalvingTimeMargin.wilsonLowerMarginFrom_of_halvingTime
#print axioms YMGap.Continuum.BF4WilsonHalvingTimeMargin.wilsonAFPaddedGapInput_of_halvingTime
