/-
# Linear step-ratio ceiling (ceiling sharpening for the B04 upper half)

Companion to `audits/SCOPE-RG-STEP-COMPOSITION-REDUCTION-2026-10-06.md` §"Ceiling
sharpening". ADDITIVE.

**Verdict: the exponential ceiling `2^(2C+3)` is an artifact of a crude conversion,
not intrinsic.** The chain in `expr_stepRatio_forces_rate_anyC` is

1. step ratio + `side_j(1−ρ'_j) ≤ c ≤ C` ⇒ window survival with
   `θ_C = (1/2)^(2C+2)` (`block_pow_floor`);
2. window survival + orbit contraction ⇒ `θ ≤ (r²)^q`, `side_j = 4q`
   (`window_gap_compat`);
3. `θ ≤ (r²)^q` ⇒ `side_j(1−r_j) ≤ c0` whenever `2(1−θ) ≤ θ·c0`
   (`side_rate_le_c0`), i.e. `c0 ≈ 2/θ_C = 2^(2C+3)`.

Step 1's `θ_C` really is exponential in `C` (a geometric response `R(n) = ρ^n` with
`s(1−ρ) = c` has `R(s+1)/R(s/2) = ρ^(s/2+1) ≈ e^{−c/2}`), so window survival
CANNOT carry a polynomial `θ`. But step 3 only needs `log(1/θ)`, not `1/θ`:
`(r²)^q ≥ θ` gives `2q(1−r) ≤ 2q·(−ln r) ≤ ln(1/θ)`. Step 3 used the rational
bound `x^q ≤ 1/(1+q(1−x))`, which turns `1/θ` into the ceiling.

Here step 3 is redone log-free by BLOCKS (the inverse of the block-Bernoulli in
step 1): split `q = pK + t` (`K = 2C+2`, `t < K`); then
`(1/2)^K ≤ (r²)^q ≤ ((r²)^p)^K`, and the upper Bernoulli
`x^p(1 + p(1−x)) ≤ 1` plus a `K`-th-root step give `p(1−r²) ≤ 1`, hence
`q(1−r) ≤ Kp(1−r²) + t ≤ 2K` and

  `side_j(1−r_j) ≤ 8K = 16(C+1)`   (`expr_stepRatio_forces_rate_linear`).

So `M = 16(C+1) + 2^(j0+2)` globally (`wilsonUpper_of_stepRatio_linear`), and from
any `J ≥ max(2, j0)` on, the ABSOLUTE ceiling `m_j ≤ 16(C+1)·2^{-j}` (relative
`U = 16(C+1)·2^{-J}`) with no `2^(j0+2)` term (`stepRatio_absolute_ceiling_from`).
At `C = 3`: `M = 64`, `M² = 2^12` (was `2^18`).

Labels: **REDUCTION** (same open inputs: step ratio, H-var/H-ray, orbit contraction);
the sharpening is a proved packaging improvement. No new analytic input.

Constructive; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeRGStepComposition

namespace YMGap.Continuum.BF4WilsonAllNomeStepRatioLinearCeiling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Constructive.SumOfSquares (q_mul_self_nonneg)
open YMGap.Continuum.BF4DyadicWilsonSquare (side spacing spacing_positive)
open YMGap.Continuum.BF4WilsonAllNomeOddResponseJensen (response_le_of_le)
open YMGap.Continuum.BF4WilsonAllNomeWindowGapCompatibility (window_gap_compat)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory
open YMGap.Continuum.BF4WilsonAllNomeExprWindowGapCompatibility (ExprPathOrbitContraction)
open YMGap.Continuum.BF4WilsonAllNomeExprStepRatioWindowSurvival (ExprStepRatio)
open YMGap.Continuum.BF4WilsonAllNomeExprStepRatioAnyC
  (thetaC expr_windowSurvivalFrom_of_stepRatio_anyC)
open YMGap.Continuum.BF4WilsonAllNomeExprTwoSidedBand (upper_spacing_form small_scale_upper)
open YMGap.Continuum.BF4WilsonAllNomeExprMixRateContraction (WilsonVacuumSqContraction)
open YMGap.Continuum.BF4WilsonAllNomeWilsonDynamicFamily
  (WilsonUpperMargin exprWilsonFamily exprOrbit_of_family)

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Rational helpers -/

theorem lc_ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  show (0 : Int) * 1 ≤ (n : Int) * 1
  rw [Int.mul_one, Int.mul_one]
  exact Int.natCast_nonneg n

theorem lc_ofNat_le {a b : Nat} (h : a ≤ b) : Q'.ofNat a ≤ Q'.ofNat b := by
  show (a : Int) * 1 ≤ (b : Int) * 1
  rw [Int.mul_one, Int.mul_one]
  exact Int.ofNat_le.mpr h

theorem lc_ofNat_mul (a b : Nat) : Q'.ofNat (a * b) ≈ Q'.ofNat a * Q'.ofNat b := by
  have hd1 : ((Q'.ofNat a * Q'.ofNat b).den : Int) = 1 := rfl
  have hd2 : ((Q'.ofNat (a * b)).den : Int) = 1 := rfl
  show ((a * b : Nat) : Int) * ((Q'.ofNat a * Q'.ofNat b).den : Int)
    = (((a : Nat) : Int) * ((b : Nat) : Int)) * ((Q'.ofNat (a * b)).den : Int)
  rw [hd1, hd2]
  push_cast
  omega

theorem lc_ofNat_add (a b : Nat) : Q'.ofNat (a + b) ≈ Q'.ofNat a + Q'.ofNat b := by
  have hd1 : ((Q'.ofNat a + Q'.ofNat b).den : Int) = 1 := rfl
  have hd2 : ((Q'.ofNat (a + b)).den : Int) = 1 := rfl
  show ((a + b : Nat) : Int) * ((Q'.ofNat a + Q'.ofNat b).den : Int)
    = (((a : Nat) : Int) * 1 + ((b : Nat) : Int) * 1) * ((Q'.ofNat (a + b)).den : Int)
  rw [hd1, hd2]
  push_cast
  omega

theorem lc_lt_of_lt_of_le {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have hcd : (0 : Int) < (c.den : Int) := by exact_mod_cast c.den_pos
  have had : (0 : Int) ≤ (a.den : Int) := by exact_mod_cast Nat.zero_le _
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have := Int.mul_lt_mul_of_pos_right e1 hcd
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at this
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_left e2 had
    have hl : (a.den : Int) * (b.num * (c.den : Int))
            = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_comm b.num (a.den : Int), Int.mul_assoc]
    have hrr : (a.den : Int) * (c.num * (b.den : Int))
             = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_comm c.num (a.den : Int), Int.mul_assoc]
    rwa [hl, hrr] at this
  exact Int.lt_of_mul_lt_mul_right (Int.lt_of_lt_of_le s1 s2)
    (by exact_mod_cast Nat.zero_le _)

theorem lc_add_neg_le (X N : Q') (hN : (0 : Q') ≤ N) : X + -N ≤ X := by
  have h1 : -N ≤ (0 : Q') :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hN) (by decide)
  have h2 := Q'.add_le_add_left X (-N) 0 h1
  rw [Q'.add_zero'] at h2
  exact h2

theorem lc_pow_antitone (x : Q') (h0 : (0 : Q') ≤ x) (h1 : x ≤ 1) (a : Nat) :
    ∀ d, x ^ (a + d) ≤ x ^ a
  | 0 => Q'.le_refl' _
  | d + 1 => Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right x 1 (x ^ (a + d)) h1 (Q'.pow_nonneg x h0 (a + d)))
        (Q'.le_of_eqv (Q'.one_mul_eqv _)))
      (lc_pow_antitone x h0 h1 a d)

theorem lc_pow_le_of_le (x : Q') (h0 : (0 : Q') ≤ x) (h1 : x ≤ 1) {a b : Nat}
    (hab : a ≤ b) : x ^ b ≤ x ^ a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact lc_pow_antitone x h0 h1 a d

theorem lc_pow_mono_base (a b : Q') (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => Q'.le_refl' _
  | n + 1 => by
    have hb : (0 : Q') ≤ b := Q'.le_trans' _ _ _ ha hab
    have h1 : a * a ^ n ≤ b * a ^ n :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hab (Q'.pow_nonneg a ha n)
    have h2 : b * a ^ n ≤ b * b ^ n :=
      Q'.mul_le_mul_of_nonneg_left _ _ b (lc_pow_mono_base a b ha hab n) hb
    exact Q'.le_trans' _ _ _ h1 h2

theorem lc_mul_pow (a b : Q') : ∀ n : Nat, (a * b) ^ n ≈ a ^ n * b ^ n
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | n + 1 => by
    have ih := lc_mul_pow a b n
    have e1 : (a * b) ^ (n + 1) ≈ (a * b) * (a ^ n * b ^ n) :=
      Q'.mul_eqv_congr_left _ _ _ ih
    have e2 : (a * b) * (a ^ n * b ^ n) ≈ (a * a ^ n) * (b * b ^ n) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (by decide) (fun | 0 => a | 1 => b | 2 => a ^ n | _ => b ^ n)
    exact Q'.eqv_trans _ _ _ e1 e2

theorem lc_one_pow : ∀ n : Nat, (1 : Q') ^ n ≈ (1 : Q')
  | 0 => Q'.eqv_refl _
  | n + 1 => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (lc_one_pow n)) (by decide)

theorem lc_pow_mul_eqv (x : Q') (a : Nat) : ∀ b : Nat, (x ^ a) ^ b ≈ x ^ (a * b)
  | 0 => by rw [Nat.mul_zero]; exact Q'.eqv_refl _
  | b + 1 => by
    have ih := lc_pow_mul_eqv x a b
    have hsplit : ∀ m k : Nat, x ^ (m + k) ≈ x ^ m * x ^ k := by
      intro m k
      induction k with
      | zero => exact Q'.eqv_symm (Q'.mul_one_eqv _)
      | succ k ihk =>
        exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left x _ _ ihk)
          (poly_identity_of_normal_eq
            (.mul (.var 0) (.mul (.var 1) (.var 2)))
            (.mul (.var 1) (.mul (.var 0) (.var 2)))
            (by decide) (fun | 0 => x | 1 => x ^ m | _ => x ^ k))
    have e1 : (x ^ a) ^ (b + 1) ≈ x ^ a * x ^ (a * b) :=
      Q'.mul_eqv_congr_left _ _ _ ih
    have e2 : x ^ (a * b + a) ≈ x ^ (a * b) * x ^ a := hsplit (a * b) a
    rw [Nat.mul_succ]
    exact Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.eqv_symm e2))

/-! ## 1. Upper Bernoulli and the root step -/

/-- **Upper Bernoulli.** `0 ≤ x ≤ 1` ⇒ `x^p (1 + p(1−x)) ≤ 1`. -/
theorem upper_bernoulli (x : Q') (h0 : (0 : Q') ≤ x) (h1 : x ≤ 1) :
    ∀ p : Nat, x ^ p * (1 + Q'.ofNat p * (1 + -x)) ≤ 1
  | 0 => Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.const 1) (.add (.const 1) (.mul (.const 0) (.add (.const 1) (.neg (.var 0))))))
      (.const 1) (by decide) (fun _ => x))
  | p + 1 => by
    have ih := upper_bernoulli x h0 h1 p
    have hd0 : (0 : Q') ≤ 1 + -x := Q'.sub_nonneg_of_le h1
    have e1 : x ^ (p + 1) * (1 + Q'.ofNat (p + 1) * (1 + -x)) ≈
        x * x ^ p * (1 + (Q'.ofNat p + 1) * (1 + -x)) :=
      Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (lc_ofNat_add p 1)))
    have e2 : x * x ^ p * (1 + (Q'.ofNat p + 1) * (1 + -x)) ≈
        x ^ p * (1 + Q'.ofNat p * (1 + -x)) +
          -(x ^ p * ((Q'.ofNat p + 1) * ((1 + -x) * (1 + -x)))) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1))
          (.add (.const 1) (.mul (.add (.var 2) (.const 1)) (.add (.const 1) (.neg (.var 0))))))
        (.add (.mul (.var 1) (.add (.const 1) (.mul (.var 2) (.add (.const 1) (.neg (.var 0))))))
          (.neg (.mul (.var 1) (.mul (.add (.var 2) (.const 1))
            (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.neg (.var 0))))))))
        (by decide) (fun | 0 => x | 1 => x ^ p | _ => Q'.ofNat p)
    have hN : (0 : Q') ≤ x ^ p * ((Q'.ofNat p + 1) * ((1 + -x) * (1 + -x))) :=
      Q'.mul_nonneg _ _ (Q'.pow_nonneg x h0 p)
        (Q'.mul_nonneg _ _ (Q'.zero_le_add _ _ (lc_ofNat_nonneg p) (by decide))
          (q_mul_self_nonneg _))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ e1 e2))
      (Q'.le_trans' _ _ _ (lc_add_neg_le _ _ hN) ih)

/-- `z ≥ 0`, `z^(K+1) ≤ 1` ⇒ `z ≤ 1` (constructive: `Q'` order is decidable on `Int`). -/
theorem le_one_of_pow_le_one (z : Q') (hz0 : (0 : Q') ≤ z) (K : Nat)
    (h : z ^ (K + 1) ≤ 1) : z ≤ 1 := by
  show z.num * ((1 : Q').den : Int) ≤ (1 : Q').num * (z.den : Int)
  refine Int.not_lt.mp (fun hlt => ?_)
  have hlt' : (1 : Q') < z := hlt
  have hz1 : (1 : Q') ≤ z := Q'.le_of_lt hlt'
  have hpow1 : ∀ n : Nat, (1 : Q') ≤ z ^ n := by
    intro n
    induction n with
    | zero => exact Q'.le_refl' _
    | succ n ih =>
      exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hz1 (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv z))))
        (Q'.mul_le_mul_of_nonneg_left _ _ z ih hz0)
  have hzK : z ≤ z ^ (K + 1) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv z)))
      (Q'.mul_le_mul_of_nonneg_left _ _ z (hpow1 K) hz0)
  have hcontra : (1 : Q') < 1 := lc_lt_of_lt_of_le hlt' (Q'.le_trans' _ _ _ hzK h)
  exact Int.lt_irrefl _ hcontra

/-- **Block root step.** `0 ≤ x ≤ 1`, `(1/2)^(K+1) ≤ (x^p)^(K+1)` ⇒ `p(1−x) ≤ 1`. -/
theorem block_rate_le_one (x : Q') (h0 : (0 : Q') ≤ x) (h1 : x ≤ 1) (K p : Nat)
    (h : half ^ (K + 1) ≤ (x ^ p) ^ (K + 1)) : Q'.ofNat p * (1 + -x) ≤ 1 := by
  have hY0 : (0 : Q') ≤ Q'.ofNat p * (1 + -x) :=
    Q'.mul_nonneg _ _ (lc_ofNat_nonneg p) (Q'.sub_nonneg_of_le h1)
  have h1Y : (0 : Q') ≤ 1 + Q'.ofNat p * (1 + -x) := Q'.zero_le_add _ _ (by decide) hY0
  have hb := upper_bernoulli x h0 h1 p
  have hxp0 : (0 : Q') ≤ x ^ p := Q'.pow_nonneg x h0 p
  -- z := half * (1 + Y)
  have hz0 : (0 : Q') ≤ half * (1 + Q'.ofNat p * (1 + -x)) := Q'.mul_nonneg _ _ half_nonneg h1Y
  have a1 : (half * (1 + Q'.ofNat p * (1 + -x))) ^ (K + 1) ≈
      half ^ (K + 1) * (1 + Q'.ofNat p * (1 + -x)) ^ (K + 1) := lc_mul_pow _ _ _
  have a2 : half ^ (K + 1) * (1 + Q'.ofNat p * (1 + -x)) ^ (K + 1) ≤
      (x ^ p) ^ (K + 1) * (1 + Q'.ofNat p * (1 + -x)) ^ (K + 1) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ h (Q'.pow_nonneg _ h1Y _)
  have a3 : (x ^ p) ^ (K + 1) * (1 + Q'.ofNat p * (1 + -x)) ^ (K + 1) ≈
      (x ^ p * (1 + Q'.ofNat p * (1 + -x))) ^ (K + 1) := Q'.eqv_symm (lc_mul_pow _ _ _)
  have a4 : (x ^ p * (1 + Q'.ofNat p * (1 + -x))) ^ (K + 1) ≤ (1 : Q') ^ (K + 1) :=
    lc_pow_mono_base _ _ (Q'.mul_nonneg _ _ hxp0 h1Y) hb _
  have hzK : (half * (1 + Q'.ofNat p * (1 + -x))) ^ (K + 1) ≤ 1 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv a1) (Q'.le_trans' _ _ _ a2
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv a3) (Q'.le_trans' _ _ _ a4
        (Q'.le_of_eqv (lc_one_pow _)))))
  have hz1 := le_one_of_pow_le_one _ hz0 K hzK
  -- 2·(half·(1+Y)) ≤ 2 ⇒ 1 + Y ≤ 2 ⇒ Y ≤ 1
  have b1 : (2 : Q') * (half * (1 + Q'.ofNat p * (1 + -x))) ≤ (2 : Q') * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ 2 hz1 (by decide)
  have b2 : (2 : Q') * (half * (1 + Q'.ofNat p * (1 + -x))) ≈
      ((2 : Q') * half) * (1 + Q'.ofNat p * (1 + -x)) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (by decide) (fun | 0 => (2 : Q') | 1 => half | _ => 1 + Q'.ofNat p * (1 + -x))
  have b3 : ((2 : Q') * half) * (1 + Q'.ofNat p * (1 + -x)) ≈
      1 + Q'.ofNat p * (1 + -x) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (by decide : ((2 : Q') * half) ≈ 1))
      (Q'.one_mul_eqv _)
  have b4 : 1 + Q'.ofNat p * (1 + -x) ≤ (1 : Q') + 1 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _ b2 b3)))
      (Q'.le_trans' _ _ _ b1 (by decide))
  have b5 := Q'.add_le_add_left (-(1 : Q')) _ _ b4
  have e5 : -(1 : Q') + (1 + Q'.ofNat p * (1 + -x)) ≈ Q'.ofNat p * (1 + -x) :=
    poly_identity_of_normal_eq
      (.add (.neg (.const 1)) (.add (.const 1) (.var 0))) (.var 0)
      (by decide) (fun _ => Q'.ofNat p * (1 + -x))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm e5))
    (Q'.le_trans' _ _ _ b5 (by decide))

/-! ## 2. The log-free linear conversion -/

/-- **Linear conversion (replaces `side_rate_le_c0`).** `0 ≤ r ≤ 1`,
`(1/2)^(K+1) ≤ θ ≤ (r²)^q`, `L = 4q` ⇒ `L(1−r) ≤ 8(K+1)`.
Compare `side_rate_le_c0`: `L(1−r) ≤ c0` with `c0 ≥ 2(1−θ)/θ ≈ 2^(K+2)`. -/
theorem side_rate_le_linear (theta r : Q') (q L K : Nat) (hL : L = 2 * (2 * q))
    (h0 : (0 : Q') ≤ r) (h1 : r ≤ 1) (htheta : half ^ (K + 1) ≤ theta)
    (ht : theta ≤ (r * r) ^ q) :
    Q'.ofNat L * (1 + -r) ≤ Q'.ofNat (8 * (K + 1)) := by
  have hx0 : (0 : Q') ≤ r * r := q_mul_self_nonneg r
  have hxr : r * r ≤ r :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ r h1 h0) (Q'.le_of_eqv (Q'.mul_one_eqv r))
  have hx1 : r * r ≤ 1 := Q'.le_trans' _ _ _ hxr h1
  have hdm := Nat.div_add_mod q (K + 1)
  have hmod := Nat.mod_lt q (Nat.succ_pos K)
  generalize q / (K + 1) = p at hdm
  generalize q % (K + 1) = t at hdm hmod
  -- (1/2)^(K+1) ≤ ((r²)^p)^(K+1)
  have hpk : (K + 1) * p ≤ q := by omega
  have hroot : half ^ (K + 1) ≤ ((r * r) ^ p) ^ (K + 1) := by
    have c1 : (r * r) ^ q ≤ (r * r) ^ (p * (K + 1)) :=
      lc_pow_le_of_le _ hx0 hx1 (by rw [Nat.mul_comm]; exact hpk)
    exact Q'.le_trans' _ _ _ htheta (Q'.le_trans' _ _ _ ht (Q'.le_trans' _ _ _ c1
      (Q'.le_of_eqv (Q'.eqv_symm (lc_pow_mul_eqv _ p (K + 1))))))
  have hp1 := block_rate_le_one (r * r) hx0 hx1 K p hroot
  -- q(1−r) ≤ q(1−r²) = (K+1)·p(1−r²) + t(1−r²) ≤ (K+1) + (K+1)
  have hd0 : (0 : Q') ≤ 1 + -(r * r) := Q'.sub_nonneg_of_le hx1
  have hd1 : 1 + -(r * r) ≤ (1 : Q') := lc_add_neg_le 1 _ hx0
  have hrx : 1 + -r ≤ 1 + -(r * r) := Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hxr)
  have eq : Q'.ofNat q ≈ Q'.ofNat (K + 1) * Q'.ofNat p + Q'.ofNat t := by
    rw [← hdm]
    exact Q'.eqv_trans _ _ _ (lc_ofNat_add _ _)
      (Q'.add_eqv_congr_right _ _ _ (lc_ofNat_mul _ _))
  have s1 : Q'.ofNat q * (1 + -r) ≤ Q'.ofNat q * (1 + -(r * r)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hrx (lc_ofNat_nonneg q)
  have s2 : Q'.ofNat q * (1 + -(r * r)) ≈
      Q'.ofNat (K + 1) * (Q'.ofNat p * (1 + -(r * r))) + Q'.ofNat t * (1 + -(r * r)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ eq)
      (poly_identity_of_normal_eq
        (.mul (.add (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
        (.add (.mul (.var 0) (.mul (.var 1) (.var 3))) (.mul (.var 2) (.var 3)))
        (by decide)
        (fun | 0 => Q'.ofNat (K + 1) | 1 => Q'.ofNat p | 2 => Q'.ofNat t | _ => 1 + -(r * r)))
  have s3 : Q'.ofNat (K + 1) * (Q'.ofNat p * (1 + -(r * r))) ≤ Q'.ofNat (K + 1) * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hp1 (lc_ofNat_nonneg _)
  have s4 : Q'.ofNat t * (1 + -(r * r)) ≤ Q'.ofNat (K + 1) * 1 :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hd1 (lc_ofNat_nonneg t))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (lc_ofNat_le (Nat.le_of_lt hmod)) (by decide))
  have hq2 : Q'.ofNat q * (1 + -r) ≤ Q'.ofNat (K + 1) * 1 + Q'.ofNat (K + 1) * 1 :=
    Q'.le_trans' _ _ _ s1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv s2) (Q'.add_le_add s3 s4))
  -- L(1−r) = 4·q(1−r) ≤ 4·2(K+1) = 8(K+1)
  have hL4 : Q'.ofNat L ≈ Q'.ofNat 4 * Q'.ofNat q := by
    rw [hL, show 2 * (2 * q) = 4 * q by omega]
    exact lc_ofNat_mul 4 q
  have h8 : Q'.ofNat (8 * (K + 1)) ≈
      Q'.ofNat 4 * (Q'.ofNat (K + 1) * 1 + Q'.ofNat (K + 1) * 1) :=
    Q'.eqv_trans _ _ _ (lc_ofNat_mul 8 (K + 1))
      (poly_identity_of_normal_eq
        (.mul (.const 8) (.var 0))
        (.mul (.const 4) (.add (.mul (.var 0) (.const 1)) (.mul (.var 0) (.const 1))))
        (by decide) (fun _ => Q'.ofNat (K + 1)))
  have f1 : Q'.ofNat L * (1 + -r) ≈ Q'.ofNat 4 * (Q'.ofNat q * (1 + -r)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hL4)
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (by decide) (fun | 0 => Q'.ofNat 4 | 1 => Q'.ofNat q | _ => 1 + -r))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv f1)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hq2 (lc_ofNat_nonneg 4))
      (Q'.le_of_eqv (Q'.eqv_symm h8)))

/-! ## 3. Gap side with a LINEAR ceiling -/

theorem lc_side_quarter (j : Nat) (hj : 2 ≤ j) : side j = 2 * (2 * (side j / 4)) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  simp only [side, Nat.pow_succ]
  omega

/-- **Gap side, LINEAR ceiling (REDUCTION).** Same hypotheses as
`expr_stepRatio_forces_rate_anyC`; conclusion `side_j(1−r_j) ≤ 8(2C+2) = 16(C+1)`
for `j ≥ max(2, j0)` (was `2^(2C+3)`). -/
theorem expr_stepRatio_forces_rate_linear (tr : ExprAnchorTrajectory) (rho : Nat → Q')
    (k : Nat → Nat) (c : Q') (C j0 : Nat) (r fl : Nat → Q') (hC : 1 ≤ C)
    (hcC : c ≤ Q'.ofNat C) (hj0 : 2 * C ≤ side j0)
    (hrho0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho j) (hrho1 : ∀ j, j0 ≤ j → rho j ≤ 1)
    (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho j) ≤ c)
    (H : ExprStepRatio tr rho k)
    (hfl : ∀ j, (0 : Q') < fl j) (Hnd : ExprShiftedNondegenerate tr fl)
    (Hc : ExprPathOrbitContraction tr r) (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j ≤ 1)
    (j : Nat) (hj : 2 ≤ j) (hjj0 : j0 ≤ j) :
    Q'.ofNat (side j) * (1 + -r j) ≤ Q'.ofNat (8 * (2 * C + 2)) := by
  have Hw := expr_windowSurvivalFrom_of_stepRatio_anyC tr rho k c C j0 hC hcC hj0
    hrho0 hrho1 hk hc H
  have hq := lc_side_quarter j hj
  have hnd : RCle (Quotient.mk crealSetoid (ofQ' (fl j))) (tr.response j (side j / 2)) :=
    RCle_trans (Hnd j) (response_le_of_le (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (tr.width j) (tr.state j) (Nat.div_le_self (side j) 2))
  have h := window_gap_compat (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (tr.width j)
    (tr.state j) (r j) (thetaC C) (fl j) (hfl j) (side j / 2) (side j) (by omega) (Hc j) hnd
    (Hw j hjj0 (by omega))
  rw [show (side j + 1) / 2 - (side j / 2 + 1) / 2 = side j / 4 by omega] at h
  exact side_rate_le_linear (thetaC C) (r j) (side j / 4) (side j) (2 * C + 1) hq
    (hr0 j) (hr1 j) (Q'.le_refl' _) h

/-- **Upper half with LINEAR ceiling `16(C+1) + 2^(j0+2)`** (was
`2^(2C+3) + 2^(j0+2)`). Same inputs as `wilsonUpper_of_stepRatio`. **REDUCTION.** -/
theorem wilsonUpper_of_stepRatio_linear (tr : ExprAnchorTrajectory) (r : Nat → Q')
    (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j < (1 : Q'))
    (Hc : ∀ j, WilsonVacuumSqContraction (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (tr.width j) (r j))
    (c : Q') (C j0 : Nat) (hC : 1 ≤ C) (hcC : c ≤ Q'.ofNat C) (hj0 : 2 * C ≤ side j0)
    (v rho : Nat → Q') (Hv : ExprHVar tr v) (Hr : ExprHRay tr rho)
    (rho' : Nat → Q') (k : Nat → Nat)
    (hrho'0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho' j) (hrho'1 : ∀ j, j0 ≤ j → rho' j ≤ 1)
    (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho' j) ≤ c)
    (H : ExprStepRatio tr rho' k) :
    WilsonUpperMargin (exprWilsonFamily tr r hr0 hr1 Hc)
      (Q'.ofNat (8 * (2 * C + 2) + 2 ^ (j0 + 2))) := by
  refine ⟨?_, fun j => ?_⟩
  · show (0 : Q') < Q'.ofNat (8 * (2 * C + 2) + 2 ^ (j0 + 2))
    have hN : (1 : Nat) ≤ 8 * (2 * C + 2) + 2 ^ (j0 + 2) :=
      Nat.le_trans (by omega : (1 : Nat) ≤ 8 * (2 * C + 2)) (Nat.le_add_right _ _)
    exact lc_lt_of_lt_of_le (by decide : (0 : Q') < Q'.ofNat 1) (lc_ofNat_le hN)
  · show (1 : Q') - r j ≤ Q'.ofNat (8 * (2 * C + 2) + 2 ^ (j0 + 2)) * spacing j
    rcases Nat.lt_or_ge j (j0 + 2) with h | h
    · exact Q'.le_trans' _ _ _ (small_scale_upper (r j) (hr0 j) j (j0 + 2) (by omega))
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (lc_ofNat_le (Nat.le_add_left _ _))
          (Q'.le_of_lt (spacing_positive j)))
    · exact Q'.le_trans' _ _ _
        (upper_spacing_form _ _ j
          (expr_stepRatio_forces_rate_linear tr rho' k c C j0 r (exprNondegFloor tr v rho) hC
            hcC hj0 hrho'0 hrho'1 hk hc H (exprNondegFloor_pos tr v rho Hv Hr)
            (exprShiftedNondegenerate_of_hvar_hray tr v rho Hv Hr) (exprOrbit_of_family tr r Hc)
            hr0 (fun j => Q'.le_of_lt (hr1 j)) j (by omega) (by omega)))
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (lc_ofNat_le (Nat.le_add_right _ _))
          (Q'.le_of_lt (spacing_positive j)))

/-- **Absolute ceiling from `J` on, no small-scale term.** For `J ≥ max(2, j0)`:
`m_j ≤ 16(C+1)·2^{-j}` for all `j ≥ J`. This is the `hup` input of
`rg_absolute_seed_lowerMarginFrom` with `M = 16(C+1)`. **REDUCTION.** -/
theorem stepRatio_absolute_ceiling_from (tr : ExprAnchorTrajectory) (r : Nat → Q')
    (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j < (1 : Q'))
    (Hc : ∀ j, WilsonVacuumSqContraction (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (tr.width j) (r j))
    (c : Q') (C j0 : Nat) (hC : 1 ≤ C) (hcC : c ≤ Q'.ofNat C) (hj0 : 2 * C ≤ side j0)
    (v rho : Nat → Q') (Hv : ExprHVar tr v) (Hr : ExprHRay tr rho)
    (rho' : Nat → Q') (k : Nat → Nat)
    (hrho'0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho' j) (hrho'1 : ∀ j, j0 ≤ j → rho' j ≤ 1)
    (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho' j) ≤ c)
    (H : ExprStepRatio tr rho' k) (J : Nat) (hJ2 : 2 ≤ J) (hJ0 : j0 ≤ J) :
    ∀ j, J ≤ j → (exprWilsonFamily tr r hr0 hr1 Hc).latticeMargin j ≤
      Q'.ofNat (8 * (2 * C + 2)) * (exprWilsonFamily tr r hr0 hr1 Hc).transferSpacing.spacing j :=
  fun j hj => upper_spacing_form _ _ j
    (expr_stepRatio_forces_rate_linear tr rho' k c C j0 r (exprNondegFloor tr v rho) hC
      hcC hj0 hrho'0 hrho'1 hk hc H (exprNondegFloor_pos tr v rho Hv Hr)
      (exprShiftedNondegenerate_of_hvar_hray tr v rho Hv Hr) (exprOrbit_of_family tr r Hc)
      hr0 (fun j => Q'.le_of_lt (hr1 j)) j (by omega) (by omega))

open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition
  (RgRateChainκ RgErrorSummable effectiveDefectSeq absSeedFloor WilsonLowerMarginFrom
   rg_absolute_seed_lowerMarginFrom exprWilsonFamily_spacing_half_pow)

/-- **Capstone (REDUCTION).** Step-ratio inputs + κ chain from `J ≥ max(2, j0)` +
summable effective defect `≤ S` give the lower margin from `J` with floor
`μ − (16(C+1))²·2^{-J} − Ŝ/2`, provided that single finite inequality is positive. -/
theorem exprWilson_lowerMarginFrom_linearCeiling (tr : ExprAnchorTrajectory) (r : Nat → Q')
    (hr0 : ∀ j, (0 : Q') ≤ r j) (hr1 : ∀ j, r j < (1 : Q'))
    (Hc : ∀ j, WilsonVacuumSqContraction (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (tr.width j) (r j))
    (c : Q') (C j0 : Nat) (hC : 1 ≤ C) (hcC : c ≤ Q'.ofNat C) (hj0 : 2 * C ≤ side j0)
    (v rho : Nat → Q') (Hv : ExprHVar tr v) (Hr : ExprHRay tr rho)
    (rho' : Nat → Q') (k : Nat → Nat)
    (hrho'0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho' j) (hrho'1 : ∀ j, j0 ≤ j → rho' j ≤ 1)
    (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho' j) ≤ c)
    (H : ExprStepRatio tr rho' k) (J : Nat) (hJ2 : 2 ≤ J) (hJ0 : j0 ≤ J)
    (ε κ : Nat → Q') (S : Q')
    (Hκ : RgRateChainκ r ε κ J)
    (hS : RgErrorSummable (effectiveDefectSeq κ ε r) J S)
    (hpos : (0 : Q') < absSeedFloor r J S (Q'.ofNat (8 * (2 * C + 2)))) :
    WilsonLowerMarginFrom (exprWilsonFamily tr r hr0 hr1 Hc) J
      (absSeedFloor r J S (Q'.ofNat (8 * (2 * C + 2)))) :=
  rg_absolute_seed_lowerMarginFrom (exprWilsonFamily tr r hr0 hr1 Hc) ε κ J S
    (Q'.ofNat (8 * (2 * C + 2))) (exprWilsonFamily_spacing_half_pow tr r hr0 hr1 Hc) Hκ hS
    (lc_ofNat_nonneg _)
    (stepRatio_absolute_ceiling_from tr r hr0 hr1 Hc c C j0 hC hcC hj0 v rho Hv Hr rho' k
      hrho'0 hrho'1 hk hc H J hJ2 hJ0) hpos

end YMGap.Continuum.BF4WilsonAllNomeStepRatioLinearCeiling

#print axioms YMGap.Continuum.BF4WilsonAllNomeStepRatioLinearCeiling.upper_bernoulli
#print axioms YMGap.Continuum.BF4WilsonAllNomeStepRatioLinearCeiling.le_one_of_pow_le_one
#print axioms YMGap.Continuum.BF4WilsonAllNomeStepRatioLinearCeiling.block_rate_le_one
#print axioms YMGap.Continuum.BF4WilsonAllNomeStepRatioLinearCeiling.side_rate_le_linear
#print axioms YMGap.Continuum.BF4WilsonAllNomeStepRatioLinearCeiling.expr_stepRatio_forces_rate_linear
#print axioms YMGap.Continuum.BF4WilsonAllNomeStepRatioLinearCeiling.wilsonUpper_of_stepRatio_linear
#print axioms YMGap.Continuum.BF4WilsonAllNomeStepRatioLinearCeiling.stepRatio_absolute_ceiling_from
#print axioms YMGap.Continuum.BF4WilsonAllNomeStepRatioLinearCeiling.exprWilson_lowerMarginFrom_linearCeiling
