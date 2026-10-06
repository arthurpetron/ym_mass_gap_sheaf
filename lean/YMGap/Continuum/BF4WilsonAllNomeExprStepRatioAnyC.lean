/-
# Window survival from a BOUNDED step-ratio rate, any c (block Bernoulli)

Companion to `audits/AUDIT-STEP-RATIO-WINDOW-SURVIVAL-2026-10-06.md` §7–§10. ADDITIVE.

`BF4WilsonAllNomeExprStepRatioWindowSurvival` needed `c < 1`, which is an artifact of a
single Bernoulli step. Here the exponent `s/2+1` is split into `2C+2` blocks of length
`q = ⌊s/(2C)⌋`. Each block has `q(1-ρ) ≤ 1/2`, so Bernoulli gives `ρ^q ≥ 1/2` per block.

* `block_pow_floor`: assume `1 ≤ C`, `c ≤ C`, `2C ≤ s`, `0 ≤ ρ ≤ 1` and `s(1-ρ) ≤ c`.
  Then `θ_C := (1/2)^(2C+2) ≤ ρ^(s/2+1)`. θ_C depends only on the integer `C ≥ max(1, c)`.
  `C = 0` is excluded; take `C = 1` for `c ≤ 1`.
* `thetaC_c0`: `c0 := 2^(2C+3)` satisfies the compiler condition `2(1-θ_C) ≤ θ_C c0`,
  because `θ_C · 2^(2C+3) = 2`.

SMALL SCALES. With only `0 ≤ ρ_j ≤ 1`, the scales with `side_j < 2C` give no uniform θ.
They are handled in two honest ways, and nothing is weakened silently:
* (a) `ExprShiftedWindowSurvivalFrom tr j0 θ` is window survival for `j ≥ j0` only.
  The A03 package only reads scales `j ≥ a`. Its input `ExprShiftedEpsBound tr c0` is
  quantified over ALL `j`, but at a scale with `side_j ≤ c0` it holds TRIVIALLY
  (`oneStepEpsBound_le`: `side_j (R(0)-R(1)) ≤ side_j R(0) ≤ c0 R(0)`). So
  `exprShiftedEpsBound_of_windowSurvivalFrom` needs survival only for `j ≥ j0`, plus
  `side_j ≤ c0` for `j < j0`.
* (b) `expr_windowSurvival_of_stepRatio_anyC_small`: an explicit small-scale survival
  constant `θ_s` for `1 ≤ j < j0`, and any `θ ≤ min(θ_C, θ_s)`.

Combined (`expr_normalized_anchor_of_hvar_hray_anyC`): H-var and H-ray, with
`side_j(1-ρ_j) ≤ c ≤ C` for `j ≥ j0`, give the A03 package with `c0 = 2^(2C+3)`, under
these SIDE CONDITIONS:
* `2C ≤ side_{j0}` and `j0 ≤ 2C+4`;
* `2^(2C+3) ≤ side_a · δ`.
So `side_a` grows like `2^(2C+3)/δ`: exponential in C, i.e. the anchor scale `a` grows
LINEARLY in C.

Gap side: `expr_stepRatio_forces_rate_anyC` gives `side_j(1-r_j) ≤ 2^(2C+3)` for
`j ≥ max(2, j0)`. This is consistent.

The constant is crude. The true value is `ρ^(s/2+1) ≳ e^(-c/2)`, about 0.3 at `c ≈ 2.4`,
whereas θ_C = 2^(-8) at C = 3. The sharp constant would need exp/log bounds that are not
used here. HONEST SCOPE: this is a SUFFICIENT condition only. The open input is that
`side_j (1-ρ_j)` stays BOUNDED (any constant) along the trajectory. It is not proved for
any YM trajectory.

Constructive, no external library; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeExprStepRatioWindowSurvival
import YMGap.Continuum.BF4WilsonAllNomeExprShiftedAnchorPackage

namespace YMGap.Continuum.BF4WilsonAllNomeExprStepRatioAnyC

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion completedInner completedInner_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen (response_nonnegative response_le_of_le)
open YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor (OneStepEpsBound)
open YMGap.Continuum.BF4WilsonAllNomeShiftedWindowSurvival (window_epsBound oneStepEpsBound_one)
open YMGap.Continuum.BF4WilsonAllNomeWindowGapCompatibility (window_gap_compat side_rate_le_c0)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory
open YMGap.Continuum.BF4WilsonAllNomeExprWindowGapCompatibility (ExprPathOrbitContraction)
open YMGap.Continuum.BF4WilsonAllNomeExprShiftedAnchorPackage
  (ExprShiftedAnchorPackage expr_normalized_anchor_shifted)
open YMGap.Continuum.BF4WilsonAllNomeExprStepRatioWindowSurvival
  (bernoulli_pow ExprStepRatio expr_window_pow_of_stepRatio)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)
local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Rational helpers -/

private theorem ac_ofNat_le {a b : Nat} (h : a ≤ b) : Q'.ofNat a ≤ Q'.ofNat b := by
  change (a : Int)*1 ≤ (b : Int)*1
  simp only [Int.mul_one]
  omega

private theorem ac_ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  change (0 : Int)*1 ≤ (n : Int)*1
  simp only [Int.mul_one]
  omega

private theorem ac_ofNat_pos (n : Nat) (hn : 1 ≤ n) : (0 : Q') < Q'.ofNat n := by
  change (0 : Int)*1 < (n : Int)*1
  simp only [Int.mul_one]
  omega

private theorem ac_ofNat_mul (a b : Nat) :
    Q'.ofNat (a*b) ≈ Q'.ofNat a * Q'.ofNat b := by
  have hd1 : ((Q'.ofNat a * Q'.ofNat b).den : Int) = 1 := rfl
  have hd2 : ((Q'.ofNat (a*b)).den : Int) = 1 := rfl
  show ((a*b : Nat) : Int) * ((Q'.ofNat a * Q'.ofNat b).den : Int)
    = (((a : Nat) : Int) * ((b : Nat) : Int)) * ((Q'.ofNat (a*b)).den : Int)
  rw [hd1, hd2]
  push_cast
  omega

private theorem ac_two_mul (x : Q') : Q'.ofNat 2 * x ≈ x + x :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (Q'.ofNat 2) (1 + 1) x (by decide))
    (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 1 x)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv x))
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv x))))

private theorem ac_one_sub_nonneg {rho : Q'} (h1 : rho ≤ 1) : (0 : Q') ≤ (1 : Q') - rho :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv rho))
    (Q'.add_le_add_right rho 1 (-rho) h1)

private theorem ac_one_sub_le_one {rho : Q'} (h0 : (0 : Q') ≤ rho) : (1 : Q') - rho ≤ 1 :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_add_zero_eqv ((1 : Q') - rho)))
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left ((1 : Q') - rho) 0 rho h0)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0) (by decide)
        (fun | 0 => (1 : Q') | _ => rho))))

private theorem ac_pow_antitone (rho : Q') (h0 : (0 : Q') ≤ rho) (h1 : rho ≤ 1) (a : Nat) :
    ∀ d, rho^(a+d) ≤ rho^a
  | 0 => Q'.le_refl' _
  | d+1 => Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right rho 1 (rho^(a+d)) h1 (Q'.pow_nonneg rho h0 (a+d)))
        (Q'.le_of_eqv (Q'.one_mul_eqv _)))
      (ac_pow_antitone rho h0 h1 a d)

private theorem ac_pow_le_of_le (rho : Q') (h0 : (0 : Q') ≤ rho) (h1 : rho ≤ 1) {a b : Nat}
    (hab : a ≤ b) : rho^b ≤ rho^a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact ac_pow_antitone rho h0 h1 a d

private theorem ac_le_half {x : Q'} (h : x + x ≤ 1) : x ≤ HalfPow.half :=
  Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv HalfPow.half x x) (ExpNeg.two_halves x)))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left (x + x) 1 HalfPow.half h
        HalfPow.half_nonneg)
      (Q'.le_of_eqv (Q'.mul_one_eqv HalfPow.half)))

/-- Block count: `s = 2C q + r`, `r < 2C`, `1 ≤ q` ⇒ `s/2 + 1 ≤ q (2C+2)`. -/
private theorem ac_block_count (s C q r : Nat) (hq : 1 ≤ q)
    (hdm : 2*C*q + r = s) (hr : r < 2*C) : s/2 + 1 ≤ q*(2*C+2) := by
  have e1 : q*(2*C+2) = 2*(C*q) + 2*q := by
    rw [Nat.mul_add, Nat.mul_comm q (2*C), Nat.mul_assoc, Nat.mul_comm q 2]
  have hP : C*1 ≤ C*q := Nat.mul_le_mul_left C hq
  rw [Nat.mul_one] at hP
  rw [Nat.mul_assoc] at hdm
  rw [e1]
  generalize C*q = P at *
  omega

/-! ## 1. Block Bernoulli -/

/-- `θ_C = (1/2)^(2C+2)`. -/
def thetaC (C : Nat) : Q' := HalfPow.half ^ (2*C+2)

theorem thetaC_pos (C : Nat) : (0 : Q') < thetaC C := HKPos.pow_pos (by decide) _

theorem thetaC_le_one (C : Nat) : thetaC C ≤ 1 :=
  HKPos.pow_le_one HalfPow.half_nonneg (by decide) _

/-- **Block Bernoulli.** `1 ≤ C`, `c ≤ C`, `2C ≤ s`, `0 ≤ ρ ≤ 1`, `s(1-ρ) ≤ c` ⇒
`(1/2)^(2C+2) ≤ ρ^(s/2+1)`. -/
theorem block_pow_floor (rho c : Q') (C s : Nat) (hC : 1 ≤ C) (hs : 2*C ≤ s)
    (h0 : (0 : Q') ≤ rho) (h1 : rho ≤ 1) (hcC : c ≤ Q'.ofNat C)
    (hc : Q'.ofNat s * ((1 : Q') - rho) ≤ c) : thetaC C ≤ rho^(s/2+1) := by
  have h2C : 0 < 2*C := by omega
  have hdm := Nat.div_add_mod s (2*C)
  have hmod := Nat.mod_lt s h2C
  have hq1 : 0 < s/(2*C) := Nat.div_pos hs h2C
  generalize s/(2*C) = q at hdm hq1
  generalize s%(2*C) = r at hdm hmod
  have hn := ac_block_count s C q r hq1 hdm hmod
  have ht0 := ac_one_sub_nonneg h1
  have hqs : 2*C*q ≤ s := by omega
  -- the block estimate `q(1-ρ) ≤ 1/2`
  have a1 : Q'.ofNat (2*C*q) * ((1 : Q') - rho) ≤ Q'.ofNat C :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ (ac_ofNat_le hqs) ht0)
      (Q'.le_trans' _ _ _ hc hcC)
  have hnat : 2*C*q = C*(2*q) := by rw [Nat.mul_comm 2 C, Nat.mul_assoc]
  have s1 : Q'.ofNat (2*C*q) * ((1 : Q') - rho) ≈
      (Q'.ofNat C * (Q'.ofNat 2 * Q'.ofNat q)) * ((1 : Q') - rho) := by
    rw [hnat]
    exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _ (ac_ofNat_mul C (2*q))
      (Q'.mul_eqv_congr_left _ _ _ (ac_ofNat_mul 2 q)))
  have s2 : (Q'.ofNat C * (Q'.ofNat 2 * Q'.ofNat q)) * ((1 : Q') - rho) ≈
      Q'.ofNat C * (Q'.ofNat 2 * (Q'.ofNat q * ((1 : Q') - rho))) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
      (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (by decide)
      (fun | 0 => Q'.ofNat C | 1 => Q'.ofNat 2 | 2 => Q'.ofNat q | _ => (1 : Q') - rho)
  have s3 := Q'.mul_eqv_congr_left (Q'.ofNat C) _ _ (ac_two_mul (Q'.ofNat q * ((1 : Q') - rho)))
  have a2 : Q'.ofNat C * ((Q'.ofNat q * ((1 : Q') - rho)) + (Q'.ofNat q * ((1 : Q') - rho)))
      ≤ Q'.ofNat C * 1 :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ s1 (Q'.eqv_trans _ _ _ s2 s3)))
      (Q'.le_trans' _ _ _ a1 (Q'.ge_of_eqv (Q'.mul_one_eqv _)))
  have a3 := Q'.le_of_mul_le_mul_left a2 (ac_ofNat_pos C hC)
  have a4 : HalfPow.half ≤ (1 : Q') - Q'.ofNat q * ((1 : Q') - rho) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (by decide : ((1 : Q') + -HalfPow.half).eqv HalfPow.half))
      (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (ac_le_half a3)))
  have a5 : HalfPow.half ≤ rho^q := Q'.le_trans' _ _ _ a4 (bernoulli_pow rho h0 h1 q)
  -- `2C+2` blocks
  exact Q'.le_trans' _ _ _
    (CRealLog.pow_le_pow_base _ _ HalfPow.half_nonneg a5 (2*C+2))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (FiveHolonomyPerronCutoff.pow_mul_eqv rho q (2*C+2)))
      (ac_pow_le_of_le rho h0 h1 hn))

private theorem ac_half_pow_mul : ∀ k : Nat,
    HalfPow.half^k * Q'.ofNat (2^(k+1)) ≈ Q'.ofNat 2
  | 0 => by decide
  | k+1 =>
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (ac_ofNat_mul (2^(k+1)) 2))
        (Q'.eqv_trans _ _ _
          (poly_identity_of_normal_eq
            (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
            (.mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3))) (by decide)
            (fun | 0 => HalfPow.half | 1 => HalfPow.half^k | 2 => Q'.ofNat (2^(k+1))
                 | _ => Q'.ofNat 2))
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _ (by decide : (HalfPow.half * Q'.ofNat 2).eqv 1))
            (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (ac_half_pow_mul k))
              (Q'.mul_one_eqv _))))

/-- `c0 = 2^(2C+3)` satisfies `2(1-θ_C) ≤ θ_C c0` (indeed `θ_C c0 = 2`). -/
theorem thetaC_c0 (C : Nat) :
    (1 + -thetaC C) * Q'.ofNat 2 ≤ thetaC C * Q'.ofNat (2^(2*C+3)) :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (ac_one_sub_le_one (Q'.le_of_lt (thetaC_pos C)))
      (ac_ofNat_nonneg 2))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
      (Q'.ge_of_eqv (ac_half_pow_mul (2*C+2))))

theorem one_le_c0 (C : Nat) : (1 : Q') ≤ Q'.ofNat (2^(2*C+3)) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (1 : Q').eqv (Q'.ofNat 1)))
    (ac_ofNat_le (Nat.two_pow_pos _))

/-! ## 2. Window survival from `j0` on -/

/-- Window survival from scale `j0` on (`j ≥ j0`, `j ≥ 1`). -/
def ExprShiftedWindowSurvivalFrom (tr : ExprAnchorTrajectory) (j0 : Nat) (theta : Q') : Prop :=
  ∀ j, j0 ≤ j → 1 ≤ j →
    RCle (RCscale theta (tr.response j (side j / 2))) (tr.response j (side j + 1))

theorem windowSurvivalFrom_zero_iff (tr : ExprAnchorTrajectory) (theta : Q') :
    ExprShiftedWindowSurvivalFrom tr 0 theta ↔ ExprShiftedWindowSurvival tr theta :=
  ⟨fun H j hj => H j (Nat.zero_le _) hj, fun H j _ hj => H j hj⟩

theorem windowSurvivalFrom_of_windowSurvival (tr : ExprAnchorTrajectory) (theta : Q')
    (j0 : Nat) (H : ExprShiftedWindowSurvival tr theta) :
    ExprShiftedWindowSurvivalFrom tr j0 theta := fun j _ hj => H j hj

/-- **Any bounded rate.** For `j ≥ j0`, `side_j(1-ρ_j) ≤ c ≤ C`, `0 ≤ ρ_j ≤ 1`, and a step
ratio at `k_j ≤ side_j/2`, with `2C ≤ side_{j0}`, give window survival from `j0` with
`θ_C = (1/2)^(2C+2)`. -/
theorem expr_windowSurvivalFrom_of_stepRatio_anyC (tr : ExprAnchorTrajectory)
    (rho : Nat → Q') (k : Nat → Nat) (c : Q') (C j0 : Nat) (hC : 1 ≤ C)
    (hcC : c ≤ Q'.ofNat C) (hj0 : 2*C ≤ side j0)
    (hrho0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho j) (hrho1 : ∀ j, j0 ≤ j → rho j ≤ 1)
    (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho j) ≤ c)
    (H : ExprStepRatio tr rho k) :
    ExprShiftedWindowSurvivalFrom tr j0 (thetaC C) := by
  intro j hj hj1
  have hs : 2*C ≤ side j :=
    Nat.le_trans hj0 (Nat.pow_le_pow_right (by decide) hj)
  exact RCle_trans
    (RCscale_scalar_mono (block_pow_floor (rho j) c C (side j) hC hs (hrho0 j hj1) (hrho1 j hj)
      hcC (hc j hj))
      (response_nonnegative (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
        (tr.state j) (side j / 2)))
    (expr_window_pow_of_stepRatio tr rho k hrho0 hk H j hj1)

/-- Option (b): an explicit small-scale survival constant `θ_s` for `1 ≤ j < j0` and any
`θ ≤ θ_C`, `θ ≤ θ_s` give FULL `ExprShiftedWindowSurvival tr θ`. -/
theorem expr_windowSurvival_of_stepRatio_anyC_small (tr : ExprAnchorTrajectory)
    (rho : Nat → Q') (k : Nat → Nat) (c : Q') (C j0 : Nat) (theta thetaS : Q') (hC : 1 ≤ C)
    (hcC : c ≤ Q'.ofNat C) (hj0 : 2*C ≤ side j0)
    (hrho0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho j) (hrho1 : ∀ j, j0 ≤ j → rho j ≤ 1)
    (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho j) ≤ c)
    (H : ExprStepRatio tr rho k)
    (hsmall : ∀ j, 1 ≤ j → j < j0 →
      RCle (RCscale thetaS (tr.response j (side j / 2))) (tr.response j (side j + 1)))
    (hthC : theta ≤ thetaC C) (hthS : theta ≤ thetaS) :
    ExprShiftedWindowSurvival tr theta := by
  intro j hj
  have hR := response_nonnegative (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
    (tr.width j) (tr.state j) (side j / 2)
  rcases Nat.lt_or_ge j j0 with h | h
  · exact RCle_trans (RCscale_scalar_mono hthS hR) (hsmall j hj h)
  · exact RCle_trans (RCscale_scalar_mono hthC hR)
      (expr_windowSurvivalFrom_of_stepRatio_anyC tr rho k c C j0 hC hcC hj0 hrho0 hrho1 hk hc
        H j h hj)

/-- H-ray form: `ExprHRay` on the centered `x_j` with `side_j(1-ρ_j) ≤ c ≤ C` for
`j ≥ j0`. CAVEAT: this lag-0 H-ray survival hypothesis on the RAW slab vector is likely
vacuous, because UV contamination keeps its one-step ratio far from 1. The realistic route is
an intermediate-lag step ratio on the smoothed state; see
`expr_normalized_anchor_of_hvar_hray_stepRatio_anyC`. -/
theorem expr_windowSurvivalFrom_of_hray_anyC (tr : ExprAnchorTrajectory) (rho : Nat → Q')
    (c : Q') (C j0 : Nat) (hC : 1 ≤ C) (hcC : c ≤ Q'.ofNat C) (hj0 : 2*C ≤ side j0)
    (Hr : ExprHRay tr rho) (hrho1 : ∀ j, j0 ≤ j → rho j ≤ 1)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho j) ≤ c) :
    ExprShiftedWindowSurvivalFrom tr j0 (thetaC C) :=
  expr_windowSurvivalFrom_of_stepRatio_anyC tr rho (fun _ => 0) c C j0 hC hcC hj0
    (fun j _ => Q'.le_of_lt (Hr j).1) hrho1 (fun _ _ => Nat.zero_le _) hc
    (BF4WilsonAllNomeExprStepRatioWindowSurvival.expr_stepRatio_of_hray tr rho Hr)

/-! ## 3. Small scales are trivial for the shifted H1 when `side_j ≤ c0` -/

private theorem ac_sub_le_self (a b : RC) (hb : RCnonneg b) : RCle (RCsub a b) a := by
  have h := RCadd_le_add (RCle_refl (RCsub a b)) (show RCle RCzero b from hb)
  have e1 : RCadd (RCsub a b) RCzero = RCsub a b := by
    refine Quotient.inductionOn₂ a b ?_
    intro A B'
    exact Quotient.sound
      (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv _))
  have e2 : RCadd (RCsub a b) b = a := by
    refine Quotient.inductionOn₂ a b ?_
    intro A B'
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
        (by decide) (fun | 0 => A.approx n | _ => B'.approx n)))
  rw [e1, e2] at h
  exact h

/-- `ofNat L ≤ c0` ⇒ the one-step eps bound at block `L` holds for ANY vector. -/
theorem oneStepEpsBound_le {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)
    (x : Completion hw0 hw1 width) (L : Nat) (c0 : Q') (hL : Q'.ofNat L ≤ c0) :
    OneStepEpsBound hw0 hw1 width x L c0 := by
  unfold OneStepEpsBound
  have h1 := RCscale_mono (ac_ofNat_nonneg L)
    (ac_sub_le_self (completedInner hw0 hw1 x x) _ (response_nonnegative hw0 hw1 width x 1))
  exact RCle_trans h1 (RCscale_scalar_mono hL (completedInner_nonnegative hw0 hw1 x))

private theorem ac_one_sub_nonneg' {theta : Q'} (h1 : theta ≤ 1) : (0 : Q') ≤ 1 + -theta :=
  ac_one_sub_nonneg h1

private theorem ac_coeff (S n : Nat) (hS : S ≤ 2*(n+1)) (theta c0 : Q') (h1 : theta ≤ 1)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) :
    Q'.ofNat S * (1 + -theta) ≤ theta * Q'.ofNat (n+1) * c0 := by
  have hd := ac_one_sub_nonneg' h1
  have a1 : Q'.ofNat S * (1 + -theta) ≤ Q'.ofNat (2*(n+1)) * (1 + -theta) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (ac_ofNat_le hS) hd
  have a2 : Q'.ofNat (2*(n+1)) * (1 + -theta) ≈
      Q'.ofNat (n+1) * ((1 + -theta) * Q'.ofNat 2) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (ac_ofNat_mul 2 (n+1)))
      (poly_identity_of_normal_eq (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 1) (.mul (.var 2) (.var 0))) (by decide)
        (fun | 0 => Q'.ofNat 2 | 1 => Q'.ofNat (n+1) | _ => 1 + -theta))
  have a3 : Q'.ofNat (n+1) * ((1 + -theta) * Q'.ofNat 2) ≤ Q'.ofNat (n+1) * (theta * c0) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hc0 (ac_ofNat_nonneg _)
  have a4 : Q'.ofNat (n+1) * (theta * c0) ≈ theta * Q'.ofNat (n+1) * c0 :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 1) (.var 0)) (.var 2)) (by decide)
      (fun | 0 => Q'.ofNat (n+1) | 1 => theta | _ => c0)
  exact Q'.le_trans' _ _ _ a1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv a2)
    (Q'.le_trans' _ _ _ a3 (Q'.le_of_eqv a4)))

/-- **Window from `j0` ⟹ shifted H1 at ALL scales**, given `side_j ≤ c0` for `j < j0`
(the small scales are trivial, not assumed). -/
theorem exprShiftedEpsBound_of_windowSurvivalFrom (tr : ExprAnchorTrajectory)
    (c0 theta : Q') (j0 : Nat) (h0 : (0 : Q') < theta) (h1 : theta ≤ 1)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) (hc1 : (1 : Q') ≤ c0)
    (hside : ∀ j, j < j0 → Q'.ofNat (side j) ≤ c0)
    (Hw : ExprShiftedWindowSurvivalFrom tr j0 theta) : ExprShiftedEpsBound tr c0 := by
  intro j
  match j with
  | 0 =>
      exact oneStepEpsBound_one (tr.schedule.nome_pos 0) (tr.schedule.nome_lt_one 0)
        (tr.width 0) _ c0 hc1
  | j+1 =>
      rcases Nat.lt_or_ge (j+1) j0 with hlt | hge
      · exact oneStepEpsBound_le (tr.schedule.nome_pos (j+1)) (tr.schedule.nome_lt_one (j+1))
          (tr.width (j+1)) _ (side (j+1)) c0 (hside (j+1) hlt)
      · have hj : 1 ≤ j+1 := Nat.succ_pos j
        rw [exprShiftedEpsBound_iff_response tr c0 (j+1) hj]
        have hpn : side (j+1) / 2 + (side (j+1) - side (j+1) / 2) = side (j+1) := by omega
        have hS : side (j+1) ≤ 2 * ((side (j+1) - side (j+1) / 2) + 1) := by omega
        exact window_epsBound (tr.schedule.nome_pos (j+1)) (tr.schedule.nome_lt_one (j+1))
          (tr.width (j+1)) (tr.state (j+1)) (side (j+1) / 2) (side (j+1) - side (j+1) / 2)
          (side (j+1)) (side (j+1)) hpn theta c0 h0 h1
          (ac_coeff (side (j+1)) (side (j+1) - side (j+1) / 2) hS theta c0 h1 hc0)
          (Hw (j+1) hge hj)

/-- A03 package from window survival from `j0` on (any `a ≥ 1`; scales `< j0` need only
`side_j ≤ c0`). -/
theorem expr_normalized_anchor_of_windowSurvivalFrom (tr : ExprAnchorTrajectory)
    (c0 theta delta : Q') (a j0 : Nat) (ha : 1 ≤ a)
    (h0 : (0 : Q') < theta) (h1 : theta ≤ 1)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) (hc1 : (1 : Q') ≤ c0)
    (hside : ∀ j, j < j0 → Q'.ofNat (side j) ≤ c0)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : c0 ≤ Q'.ofNat (side a) * delta) (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (Hw : ExprShiftedWindowSurvivalFrom tr j0 theta) (Hnd : ExprShiftedNondegenerate tr fl) :
    ExprShiftedAnchorPackage tr delta hdelta a fl hfl :=
  expr_normalized_anchor_shifted tr c0 delta a ha hdelta0 hdelta hcd fl hfl
    (exprShiftedEpsBound_of_windowSurvivalFrom tr c0 theta j0 h0 h1 hc0 hc1 hside Hw) Hnd

/-- **Combined A03 one-liner, any bounded rate.** H-var + H-ray with
`side_j(1-ρ_j) ≤ c ≤ C`, `ρ_j ≤ 1` for `j ≥ j0`, where `2C ≤ side_{j0}`, `j0 ≤ 2C+4`,
and the anchor scale `a` satisfies `2^(2C+3) ≤ side_a · δ`. Constants: `θ = (1/2)^(2C+2)`,
`c0 = 2^(2C+3)`. CAVEAT: the same `ρ_j` serves both nondegeneracy and survival, and the
lag-0 H-ray survival hypothesis on the raw slab vector is likely vacuous. Prefer
`expr_normalized_anchor_of_hvar_hray_stepRatio_anyC`, which separates the two. -/
theorem expr_normalized_anchor_of_hvar_hray_anyC (tr : ExprAnchorTrajectory)
    (c delta : Q') (C j0 a : Nat) (ha : 1 ≤ a) (hC : 1 ≤ C) (hcC : c ≤ Q'.ofNat C)
    (hj0 : 2*C ≤ side j0) (hj0' : j0 ≤ 2*C+4)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : Q'.ofNat (2^(2*C+3)) ≤ Q'.ofNat (side a) * delta) (v rho : Nat → Q')
    (Hv : ExprHVar tr v) (Hr : ExprHRay tr rho) (hrho1 : ∀ j, j0 ≤ j → rho j ≤ 1)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho j) ≤ c) :
    ExprShiftedAnchorPackage tr delta hdelta a (exprNondegFloor tr v rho)
      (exprNondegFloor_pos tr v rho Hv Hr) :=
  expr_normalized_anchor_of_windowSurvivalFrom tr (Q'.ofNat (2^(2*C+3))) (thetaC C) delta a j0
    ha (thetaC_pos C) (thetaC_le_one C) (thetaC_c0 C) (one_le_c0 C)
    (fun j hj => ac_ofNat_le (Nat.pow_le_pow_right (by decide) (by omega)))
    hdelta0 hdelta hcd (exprNondegFloor tr v rho) (exprNondegFloor_pos tr v rho Hv Hr)
    (expr_windowSurvivalFrom_of_hray_anyC tr rho c C j0 hC hcC hj0 Hr hrho1 hc)
    (exprShiftedNondegenerate_of_hvar_hray tr v rho Hv Hr)

/-- **Combined A03, roles separated (realistic frontier).**
* H-var + H-ray (any `ρ_j > 0`) are used ONLY for nondegeneracy, with floor
  `ρ_j^(2M_j+side_j) v_j`.
* Survival comes from `ExprStepRatio tr ρ' k`, a lag-`k_j` (`k_j ≤ side_j/2`) step ratio with
  its OWN rate `ρ'_j`, where `side_j(1-ρ'_j) ≤ c ≤ C` and `ρ'_j ≤ 1` for `j ≥ j0`.
  It is stated on the window response `R_j(n) = B(Y_j, T^n Y_j)` of the SMOOTHED state
  `Y_j`, which is where a bounded rate is plausible.
* Same constants as before: `θ = (1/2)^(2C+2)`, `c0 = 2^(2C+3)`, `2C ≤ side_{j0}`, `j0 ≤ 2C+4`,
  `2^(2C+3) ≤ side_a · δ`.
SUFFICIENT only; the bounded intermediate-lag rate is OPEN. -/
theorem expr_normalized_anchor_of_hvar_hray_stepRatio_anyC (tr : ExprAnchorTrajectory)
    (c delta : Q') (C j0 a : Nat) (ha : 1 ≤ a) (hC : 1 ≤ C) (hcC : c ≤ Q'.ofNat C)
    (hj0 : 2*C ≤ side j0) (hj0' : j0 ≤ 2*C+4)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : Q'.ofNat (2^(2*C+3)) ≤ Q'.ofNat (side a) * delta) (v rho : Nat → Q')
    (Hv : ExprHVar tr v) (Hr : ExprHRay tr rho)
    (rho' : Nat → Q') (k : Nat → Nat)
    (hrho'0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho' j) (hrho'1 : ∀ j, j0 ≤ j → rho' j ≤ 1)
    (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho' j) ≤ c)
    (H : ExprStepRatio tr rho' k) :
    ExprShiftedAnchorPackage tr delta hdelta a (exprNondegFloor tr v rho)
      (exprNondegFloor_pos tr v rho Hv Hr) :=
  expr_normalized_anchor_of_windowSurvivalFrom tr (Q'.ofNat (2^(2*C+3))) (thetaC C) delta a j0
    ha (thetaC_pos C) (thetaC_le_one C) (thetaC_c0 C) (one_le_c0 C)
    (fun j hj => ac_ofNat_le (Nat.pow_le_pow_right (by decide) (by omega)))
    hdelta0 hdelta hcd (exprNondegFloor tr v rho) (exprNondegFloor_pos tr v rho Hv Hr)
    (expr_windowSurvivalFrom_of_stepRatio_anyC tr rho' k c C j0 hC hcC hj0 hrho'0 hrho'1 hk hc H)
    (exprShiftedNondegenerate_of_hvar_hray tr v rho Hv Hr)

/-! ## 4. Gap side with θ_C -/

private theorem ac_side_quarter (j : Nat) (hj : 2 ≤ j) : side j = 2*(2*(side j/4)) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i+2 := ⟨j-2, by omega⟩
  simp only [side, Nat.pow_succ]
  omega

/-- Gap-side necessary condition from window survival from `j0`: for `j ≥ max(2, j0)`,
`side_j (1-r_j) ≤ c0` whenever `2(1-θ) ≤ θ c0`. -/
theorem expr_windowSurvivalFrom_forces_rate_c0 (tr : ExprAnchorTrajectory) (theta c0 : Q')
    (j0 : Nat) (r fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j) (ht0 : (0 : Q') < theta)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0)
    (Hw : ExprShiftedWindowSurvivalFrom tr j0 theta) (Hnd : ExprShiftedNondegenerate tr fl)
    (Hc : ExprPathOrbitContraction tr r) (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j ≤ 1)
    (j : Nat) (hj : 2 ≤ j) (hj0 : j0 ≤ j) :
    Q'.ofNat (side j) * (1 + -r j) ≤ c0 := by
  have hq := ac_side_quarter j hj
  have hnd : RCle (Rq (fl j)) (tr.response j (side j / 2)) :=
    RCle_trans (Hnd j) (response_le_of_le (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (tr.width j) (tr.state j) (Nat.div_le_self (side j) 2))
  have h := window_gap_compat (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
    (tr.state j) (r j) theta (fl j) (hfl j) (side j / 2) (side j) (by omega) (Hc j) hnd
    (Hw j hj0 (by omega))
  rw [show (side j + 1)/2 - (side j/2 + 1)/2 = side j / 4 by omega] at h
  exact side_rate_le_c0 theta (r j) c0 (side j / 4) (side j) hq (hr0 j) (hr1 j) ht0 h hc0

/-- **Gap side, any bounded rate.** Step ratio with `side_j(1-ρ_j) ≤ c ≤ C` (`j ≥ j0`),
nondegeneracy and an orbit contraction give `side_j (1-r_j) ≤ 2^(2C+3)` for
`j ≥ max(2, j0)`. -/
theorem expr_stepRatio_forces_rate_anyC (tr : ExprAnchorTrajectory) (rho : Nat → Q')
    (k : Nat → Nat) (c : Q') (C j0 : Nat) (r fl : Nat → Q') (hC : 1 ≤ C)
    (hcC : c ≤ Q'.ofNat C) (hj0 : 2*C ≤ side j0)
    (hrho0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho j) (hrho1 : ∀ j, j0 ≤ j → rho j ≤ 1)
    (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho j) ≤ c)
    (H : ExprStepRatio tr rho k)
    (hfl : ∀ j, (0 : Q') < fl j) (Hnd : ExprShiftedNondegenerate tr fl)
    (Hc : ExprPathOrbitContraction tr r) (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j ≤ 1)
    (j : Nat) (hj : 2 ≤ j) (hjj0 : j0 ≤ j) :
    Q'.ofNat (side j) * (1 + -r j) ≤ Q'.ofNat (2^(2*C+3)) :=
  expr_windowSurvivalFrom_forces_rate_c0 tr (thetaC C) (Q'.ofNat (2^(2*C+3))) j0 r fl hfl
    (thetaC_pos C) (thetaC_c0 C)
    (expr_windowSurvivalFrom_of_stepRatio_anyC tr rho k c C j0 hC hcC hj0 hrho0 hrho1 hk hc H)
    Hnd Hc hr0 hr1 j hj hjj0

#print axioms thetaC_pos
#print axioms thetaC_le_one
#print axioms block_pow_floor
#print axioms thetaC_c0
#print axioms one_le_c0
#print axioms windowSurvivalFrom_zero_iff
#print axioms windowSurvivalFrom_of_windowSurvival
#print axioms expr_windowSurvivalFrom_of_stepRatio_anyC
#print axioms expr_windowSurvival_of_stepRatio_anyC_small
#print axioms expr_windowSurvivalFrom_of_hray_anyC
#print axioms oneStepEpsBound_le
#print axioms exprShiftedEpsBound_of_windowSurvivalFrom
#print axioms expr_normalized_anchor_of_windowSurvivalFrom
#print axioms expr_normalized_anchor_of_hvar_hray_anyC
#print axioms expr_normalized_anchor_of_hvar_hray_stepRatio_anyC
#print axioms expr_windowSurvivalFrom_forces_rate_c0
#print axioms expr_stepRatio_forces_rate_anyC

end YMGap.Continuum.BF4WilsonAllNomeExprStepRatioAnyC
