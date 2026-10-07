/-
# Two-boundary RG envelope (REDUCTION)

ADDITIVE. Companion to `audits/SCOPE-RG-STEP-COMPOSITION-REDUCTION-2026-10-06.md`
§"Two-boundary envelope". The AF-compatible replacement for weighting errors by `2^n`.

Data on scales `0 ≤ j ≤ K` (`u` irrelevant/contracting coordinate, `λ` relevant/
expanding coordinate, `|λ|` via `Q'.abs`):

* forward  (`j < K`): `u_j ≤ q·u_{j+1} + η·|λ_{j+1}| + f_{j+1}`   — propagates `K → 0`,
  initial datum `u_K`;
* backward (`j < K`): `|λ_{j+1}| ≤ a·|λ_j| + a·CL·u_{j+1} + a·f_{j+1}` — propagates
  `0 → K`, terminal pin `λ_0 = 0`;
* `0 ≤ q < ρ < 1`, `a·ρ < 1`, `η, a, CL ≥ 0`, `u ≥ 0`.

Index check: both directions are consistent with the weight `ρ^{K−j}` (forward: `q < ρ`
makes `u` decay away from `K`; backward: `aρ < 1` keeps the `λ` growth from the pin
below `ρ^{-1}` per step). No discrepancy with the requested shape.

**Closure condition (derived, weighted-max argument).** With `α = ρ − q`, `β = 1 − aρ`:
`D := α·β − η·a·CL > 0`. Let `X = max_j u_j ρ^j`, `Y = max_j |λ_j| ρ^j` (finite folds,
attained). At the maximiser: `α X ≤ α u_K ρ^K + η Y + F ρ^K` and `β Y ≤ a CL X + a F ρ^K`;
eliminating `Y` gives `D X ≤ ρ^K N`, `N = αβ u_K + (ηa + β) F`.

**Envelope.** If `f_j ≤ F ρ^{K−j}` (`0 ≤ F`) then `u_j + |λ_j| ≤ C ρ^{K−j}` for every `C`
with `D·β·C ≥ Num`, `Num = (β + a·CL)·(αβ u_K + (ηa + β) F) + a·D·F`; explicit choice
`C = Num/(D·β)` (`twoBoundary_envelope_explicit`).

**Comparison.** `terminalWeighted_of_rgErrorSummable`: after the reflection `k = K − j`,
`RgErrorSummable` (`Σ 2^k ε_k ≤ S`) implies the max-form `f_j ≤ S ρ^{K−j}` for any
`ρ ≥ 1/2` (strictly weaker requirement: max not sum, base `ρ` not `1/2`). But
`terminal_weighting_necessary`: on the exact forward system the envelope FORCES
`f_{j+1} ≤ C ρ^{K−j}`; in particular `f_1 ≤ C ρ^K`. So errors that are polynomially
decaying in `j` with `K`-independent size at the far end force `C ≳ f_1 ρ^{-K}`: they do
NOT fit with a `K`-uniform constant. Geometric decay away from the terminal scale is
necessary, not just sufficient.

Constructive; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeRGStepComposition
import YMGap.Continuum.LocatedSpectralGap
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.RegularCRealArith
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.RGTwoBoundaryEnvelope

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.SpectralGap (pow_le_pow_left)
open YMGap.Continuum (one_sub_pos_of_lt_one)
open YMGap.Continuum.BF4WilsonAllNomeRGStepComposition
  (weightedErrorSum RgErrorSummable ofNat_two_pow_mul_half_pow)

local infix:50 " ≈ " => Q'.eqv

/-! ## Small helpers -/

theorem tb_add_le {a a' b b' : Q'} (h1 : a ≤ a') (h2 : b ≤ b') : a + b ≤ a' + b' :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right a a' b h1) (Q'.add_le_add_left a' b b' h2)

theorem tb_le_add_left_of_nonneg (x y : Q') (hy : (0 : Q') ≤ y) : x ≤ y + x := by
  have h := Q'.add_le_add_right _ _ x hy
  rw [Q'.zero_add'] at h
  exact h

theorem tb_pow_add (q : Q') (a : Nat) : ∀ b, q ^ (a + b) ≈ q ^ a * q ^ b
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv (q ^ a))
  | b + 1 => by
    show q * q ^ (a + b) ≈ q ^ a * (q * q ^ b)
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (tb_pow_add q a b))
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => q | 1 => q ^ a | _ => q ^ b))

theorem tb_pow_pos (a : Q') (ha : (0 : Q') < a) : ∀ n : Nat, (0 : Q') < a ^ n
  | 0 => by show (0 : Q') < (1 : Q'); decide
  | n + 1 => Q'.mul_pos ha (tb_pow_pos a ha n)

theorem tb_pow_split (ρ : Q') (K j : Nat) (h : j ≤ K) : ρ ^ K ≈ ρ ^ j * ρ ^ (K - j) := by
  have e := tb_pow_add ρ j (K - j)
  rw [Nat.add_sub_cancel' h] at e
  exact e

theorem tb_abs_zero : Q'.abs 0 = 0 := by
  unfold Q'.abs
  rw [if_pos (Q'.le_refl' 0)]

/-! ## Attained finite weighted maximum -/

def wmax (t : Nat → Q') : Nat → Q'
  | 0 => t 0
  | n + 1 => Q'.max' (wmax t n) (t (n + 1))

theorem le_wmax (t : Nat → Q') : ∀ n j, j ≤ n → t j ≤ wmax t n
  | 0, j, h => by
    have hj : j = 0 := Nat.le_zero.mp h
    subst hj
    exact Q'.le_refl' _
  | n + 1, j, h => by
    show t j ≤ Q'.max' (wmax t n) (t (n + 1))
    unfold Q'.max'
    by_cases hc : wmax t n ≤ t (n + 1)
    · rw [if_pos hc]
      rcases Nat.lt_or_ge j (n + 1) with hj | hj
      · exact Q'.le_trans' _ _ _ (le_wmax t n j (Nat.lt_succ_iff.mp hj)) hc
      · have hj' : j = n + 1 := Nat.le_antisymm h hj
        subst hj'
        exact Q'.le_refl' _
    · rw [if_neg hc]
      rcases Nat.lt_or_ge j (n + 1) with hj | hj
      · exact le_wmax t n j (Nat.lt_succ_iff.mp hj)
      · have hj' : j = n + 1 := Nat.le_antisymm h hj
        subst hj'
        show (t (n + 1)).num * ((wmax t n).den : Int) ≤ (wmax t n).num * ((t (n + 1)).den : Int)
        have h' : ¬ ((wmax t n).num * ((t (n + 1)).den : Int) ≤
            (t (n + 1)).num * ((wmax t n).den : Int)) := hc
        exact Int.le_of_lt (Int.not_le.mp h')

theorem wmax_attained (t : Nat → Q') : ∀ n, ∃ j, j ≤ n ∧ wmax t n = t j
  | 0 => ⟨0, Nat.le_refl 0, rfl⟩
  | n + 1 => by
    show ∃ j, j ≤ n + 1 ∧ Q'.max' (wmax t n) (t (n + 1)) = t j
    unfold Q'.max'
    by_cases hc : wmax t n ≤ t (n + 1)
    · rw [if_pos hc]; exact ⟨n + 1, Nat.le_refl _, rfl⟩
    · rw [if_neg hc]
      obtain ⟨j, hj, he⟩ := wmax_attained t n
      exact ⟨j, Nat.le_succ_of_le hj, he⟩

/-! ## The two-boundary recursion -/

/-- Two-boundary RG recursion on scales `0 ≤ j ≤ K`. -/
structure TwoBoundaryRecursion (K : Nat) : Type where
  u : Nat → Q'
  lam : Nat → Q'
  f : Nat → Q'
  q : Q'
  eta : Q'
  a : Q'
  CL : Q'
  rho : Q'
  u_nonneg : ∀ j, (0 : Q') ≤ u j
  q_nonneg : (0 : Q') ≤ q
  eta_nonneg : (0 : Q') ≤ eta
  a_nonneg : (0 : Q') ≤ a
  CL_nonneg : (0 : Q') ≤ CL
  q_lt_rho : q < rho
  rho_lt_one : rho < (1 : Q')
  a_rho_lt_one : a * rho < (1 : Q')
  forward : ∀ j, j < K →
    u j ≤ q * u (j + 1) + eta * Q'.abs (lam (j + 1)) + f (j + 1)
  backward : ∀ j, j < K →
    Q'.abs (lam (j + 1)) ≤ a * Q'.abs (lam j) + a * CL * u (j + 1) + a * f (j + 1)
  pin : lam 0 = 0

/-- Error condition anchored at the terminal scale: `f_j ≤ F·ρ^{K−j}`, `0 ≤ F`. -/
def TerminalWeightedErrors (f : Nat → Q') (ρ : Q') (K : Nat) (F : Q') : Prop :=
  (0 : Q') ≤ F ∧ ∀ j, j ≤ K → f j ≤ F * ρ ^ (K - j)

namespace TwoBoundaryRecursion

variable {K : Nat} (R : TwoBoundaryRecursion K)

def alpha : Q' := R.rho + -R.q
def beta : Q' := (1 : Q') + -(R.a * R.rho)
/-- Closure defect `D = (ρ − q)(1 − aρ) − η·a·CL`. The closure condition is `0 < D`. -/
def closureDefect : Q' := R.alpha * R.beta + -(R.eta * R.a * R.CL)
/-- `Num = (β + a·CL)·(αβ u_K + (ηa + β) F) + a·D·F`. -/
def envelopeNum (F : Q') : Q' :=
  (R.beta + R.a * R.CL) * (R.alpha * R.beta * R.u K + (R.eta * R.a + R.beta) * F) +
    R.a * R.closureDefect * F

def tu (j : Nat) : Q' := R.u j * R.rho ^ j
def tl (j : Nat) : Q' := Q'.abs (R.lam j) * R.rho ^ j

theorem rho_pos : (0 : Q') < R.rho := Q'.lt_of_le_of_lt R.q_nonneg R.q_lt_rho
theorem rho_nonneg : (0 : Q') ≤ R.rho := Q'.le_of_lt R.rho_pos
theorem beta_pos : (0 : Q') < R.beta := one_sub_pos_of_lt_one R.a_rho_lt_one
theorem alpha_nonneg : (0 : Q') ≤ R.alpha := Q'.sub_nonneg_of_le (Q'.le_of_lt R.q_lt_rho)

theorem wf (F : Q') (hw : TerminalWeightedErrors R.f R.rho K F) (j : Nat) (hj : j ≤ K) :
    R.f j * R.rho ^ j ≤ F * R.rho ^ K := by
  have h1 := Q'.mul_le_mul_of_nonneg_right _ _ (R.rho ^ j) (hw.2 j hj)
    (Q'.pow_nonneg _ R.rho_nonneg j)
  have e1 : F * R.rho ^ (K - j) * R.rho ^ j ≈ F * (R.rho ^ j * R.rho ^ (K - j)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 0) (.mul (.var 2) (.var 1)))
      (by decide) (fun | 0 => F | 1 => R.rho ^ (K - j) | _ => R.rho ^ j)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.eqv_trans _ _ _ e1
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (tb_pow_split R.rho K j hj)))))

theorem X_nonneg : (0 : Q') ≤ wmax R.tu K :=
  Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ (R.u_nonneg 0) (Q'.pow_nonneg _ R.rho_nonneg 0))
    (le_wmax R.tu K 0 (Nat.zero_le K))

theorem Y_nonneg : (0 : Q') ≤ wmax R.tl K :=
  Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ (Q'.abs_nonneg _) (Q'.pow_nonneg _ R.rho_nonneg 0))
    (le_wmax R.tl K 0 (Nat.zero_le K))

/-- Forward step at the maximiser of `u_j ρ^j`. -/
theorem forward_weighted (F : Q') (hw : TerminalWeightedErrors R.f R.rho K F) :
    R.alpha * wmax R.tu K ≤
      R.alpha * (R.u K * R.rho ^ K) + (R.eta * wmax R.tl K + F * R.rho ^ K) := by
  have hE : (0 : Q') ≤ R.eta * wmax R.tl K + F * R.rho ^ K :=
    Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ R.eta_nonneg R.Y_nonneg)
      (Q'.mul_nonneg _ _ hw.1 (Q'.pow_nonneg _ R.rho_nonneg K))
  obtain ⟨j, hj, he⟩ := wmax_attained R.tu K
  rcases Nat.lt_or_ge j K with hjK | hjK
  · have hfw := R.forward j hjK
    have hp1 : (0 : Q') ≤ R.rho * R.rho ^ j :=
      Q'.mul_nonneg _ _ R.rho_nonneg (Q'.pow_nonneg _ R.rho_nonneg j)
    have m := Q'.mul_le_mul_of_nonneg_right _ _ (R.rho * R.rho ^ j) hfw hp1
    have eF1 : (R.q * R.u (j + 1) + R.eta * Q'.abs (R.lam (j + 1)) + R.f (j + 1)) *
          (R.rho * R.rho ^ j) ≈
        R.q * (R.u (j + 1) * (R.rho * R.rho ^ j)) +
          R.eta * (Q'.abs (R.lam (j + 1)) * (R.rho * R.rho ^ j)) +
            R.f (j + 1) * (R.rho * R.rho ^ j) :=
      poly_identity_of_normal_eq
        (.mul (.add (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3))) (.var 4)) (.var 5))
        (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 5))) (.mul (.var 2) (.mul (.var 3) (.var 5))))
          (.mul (.var 4) (.var 5)))
        (by decide)
        (fun | 0 => R.q | 1 => R.u (j + 1) | 2 => R.eta | 3 => Q'.abs (R.lam (j + 1))
             | 4 => R.f (j + 1) | _ => R.rho * R.rho ^ j)
    have bq : R.q * (R.u (j + 1) * (R.rho * R.rho ^ j)) ≤ R.q * wmax R.tu K :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ (le_wmax R.tu K (j + 1) hjK) R.q_nonneg
    have bη : R.eta * (Q'.abs (R.lam (j + 1)) * (R.rho * R.rho ^ j)) ≤ R.eta * wmax R.tl K :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ (le_wmax R.tl K (j + 1) hjK) R.eta_nonneg
    have bf : R.f (j + 1) * (R.rho * R.rho ^ j) ≤ F * R.rho ^ K := R.wf F hw (j + 1) hjK
    have eF2 : R.u j * (R.rho * R.rho ^ j) ≈ R.rho * R.tu j :=
      poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => R.u j | 1 => R.rho | _ => R.rho ^ j)
    have h : R.rho * R.tu j ≤ R.q * wmax R.tu K + R.eta * wmax R.tl K + F * R.rho ^ K :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm eF2))
        (Q'.le_trans' _ _ _ m (Q'.le_trans' _ _ _ (Q'.le_of_eqv eF1)
          (tb_add_le (tb_add_le bq bη) bf)))
    rw [← he] at h
    have h2 := Q'.add_le_add_right _ _ (-(R.q * wmax R.tu K)) h
    have eA : R.alpha * wmax R.tu K ≈ R.rho * wmax R.tu K + -(R.q * wmax R.tu K) :=
      poly_identity_of_normal_eq
        (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
        (by decide) (fun | 0 => R.rho | 1 => R.q | _ => wmax R.tu K)
    have eB : R.q * wmax R.tu K + R.eta * wmax R.tl K + F * R.rho ^ K + -(R.q * wmax R.tu K) ≈
        R.eta * wmax R.tl K + F * R.rho ^ K :=
      poly_identity_of_normal_eq
        (.add (.add (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4))) (.var 5))
          (.neg (.mul (.var 1) (.var 2))))
        (.add (.mul (.var 3) (.var 4)) (.var 5))
        (by decide)
        (fun | 0 => R.rho | 1 => R.q | 2 => wmax R.tu K | 3 => R.eta | 4 => wmax R.tl K
             | _ => F * R.rho ^ K)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eA) (Q'.le_trans' _ _ _ h2
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv eB)
        (tb_le_add_left_of_nonneg _ _ (Q'.mul_nonneg _ _ R.alpha_nonneg
          (Q'.mul_nonneg _ _ (R.u_nonneg K) (Q'.pow_nonneg _ R.rho_nonneg K))))))
  · have hjK' : j = K := Nat.le_antisymm hj hjK
    subst hjK'
    rw [he]
    exact Q'.add_le_self_of_nonneg _ _ hE

/-- Backward step at the maximiser of `|λ_j| ρ^j` (uses the pin `λ_0 = 0`). -/
theorem backward_weighted (F : Q') (hw : TerminalWeightedErrors R.f R.rho K F) :
    R.beta * wmax R.tl K ≤ R.a * R.CL * wmax R.tu K + R.a * (F * R.rho ^ K) := by
  have hR : (0 : Q') ≤ R.a * R.CL * wmax R.tu K + R.a * (F * R.rho ^ K) :=
    Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ R.a_nonneg R.CL_nonneg) R.X_nonneg)
      (Q'.mul_nonneg _ _ R.a_nonneg (Q'.mul_nonneg _ _ hw.1 (Q'.pow_nonneg _ R.rho_nonneg K)))
  obtain ⟨j, hj, he⟩ := wmax_attained R.tl K
  cases j with
  | zero =>
    rw [he]
    show R.beta * (Q'.abs (R.lam 0) * R.rho ^ 0) ≤ _
    rw [R.pin, tb_abs_zero]
    have e0 : R.beta * ((0 : Q') * R.rho ^ 0) ≈ (0 : Q') :=
      poly_identity_of_normal_eq
        (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 1)))) (.mul (.const 0) (.var 2)))
        (.const 0) (by decide) (fun | 0 => R.a | 1 => R.rho | _ => R.rho ^ 0)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e0) hR
  | succ i =>
    have hi : i < K := hj
    have hbw := R.backward i hi
    have hp1 : (0 : Q') ≤ R.rho * R.rho ^ i :=
      Q'.mul_nonneg _ _ R.rho_nonneg (Q'.pow_nonneg _ R.rho_nonneg i)
    have m := Q'.mul_le_mul_of_nonneg_right _ _ (R.rho * R.rho ^ i) hbw hp1
    have eB1 : (R.a * Q'.abs (R.lam i) + R.a * R.CL * R.u (i + 1) + R.a * R.f (i + 1)) *
          (R.rho * R.rho ^ i) ≈
        R.a * R.rho * (Q'.abs (R.lam i) * R.rho ^ i) +
          R.a * R.CL * (R.u (i + 1) * (R.rho * R.rho ^ i)) +
            R.a * (R.f (i + 1) * (R.rho * R.rho ^ i)) :=
      poly_identity_of_normal_eq
        (.mul (.add (.add (.mul (.var 0) (.var 1)) (.mul (.mul (.var 0) (.var 4)) (.var 5)))
          (.mul (.var 0) (.var 6))) (.mul (.var 2) (.var 3)))
        (.add (.add (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
          (.mul (.mul (.var 0) (.var 4)) (.mul (.var 5) (.mul (.var 2) (.var 3)))))
          (.mul (.var 0) (.mul (.var 6) (.mul (.var 2) (.var 3)))))
        (by decide)
        (fun | 0 => R.a | 1 => Q'.abs (R.lam i) | 2 => R.rho | 3 => R.rho ^ i | 4 => R.CL
             | 5 => R.u (i + 1) | _ => R.f (i + 1))
    have aρ0 : (0 : Q') ≤ R.a * R.rho := Q'.mul_nonneg _ _ R.a_nonneg R.rho_nonneg
    have b1 : R.a * R.rho * (Q'.abs (R.lam i) * R.rho ^ i) ≤ R.a * R.rho * wmax R.tl K :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ (le_wmax R.tl K i (Nat.le_of_lt hi)) aρ0
    have b2 : R.a * R.CL * (R.u (i + 1) * (R.rho * R.rho ^ i)) ≤ R.a * R.CL * wmax R.tu K :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ (le_wmax R.tu K (i + 1) hi)
        (Q'.mul_nonneg _ _ R.a_nonneg R.CL_nonneg)
    have b3 : R.a * (R.f (i + 1) * (R.rho * R.rho ^ i)) ≤ R.a * (F * R.rho ^ K) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ (R.wf F hw (i + 1) hi) R.a_nonneg
    have h : R.tl (i + 1) ≤
        R.a * R.rho * wmax R.tl K + R.a * R.CL * wmax R.tu K + R.a * (F * R.rho ^ K) :=
      Q'.le_trans' _ _ _ m (Q'.le_trans' _ _ _ (Q'.le_of_eqv eB1)
        (tb_add_le (tb_add_le b1 b2) b3))
    rw [← he] at h
    have h2 := Q'.add_le_add_right _ _ (-(R.a * R.rho * wmax R.tl K)) h
    have eB2 : R.beta * wmax R.tl K ≈ wmax R.tl K + -(R.a * R.rho * wmax R.tl K) :=
      poly_identity_of_normal_eq
        (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 1)))) (.var 2))
        (.add (.var 2) (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2))))
        (by decide) (fun | 0 => R.a | 1 => R.rho | _ => wmax R.tl K)
    have eB3 : R.a * R.rho * wmax R.tl K + R.a * R.CL * wmax R.tu K + R.a * (F * R.rho ^ K) +
          -(R.a * R.rho * wmax R.tl K) ≈
        R.a * R.CL * wmax R.tu K + R.a * (F * R.rho ^ K) :=
      poly_identity_of_normal_eq
        (.add (.add (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.mul (.var 0) (.var 3)) (.var 4))) (.mul (.var 0) (.var 5)))
          (.neg (.mul (.mul (.var 0) (.var 1)) (.var 2))))
        (.add (.mul (.mul (.var 0) (.var 3)) (.var 4)) (.mul (.var 0) (.var 5)))
        (by decide)
        (fun | 0 => R.a | 1 => R.rho | 2 => wmax R.tl K | 3 => R.CL | 4 => wmax R.tu K
             | _ => F * R.rho ^ K)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eB2)
      (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv eB3))

end TwoBoundaryRecursion

/-- **Closure algebra.** Eliminate `Y` between the two weighted inequalities. -/
theorem closure_algebra (α β η a CL X Y P Φ D : Q') (hβ : (0 : Q') ≤ β) (hη : (0 : Q') ≤ η)
    (hD : (0 : Q') ≤ D) (haCL : (0 : Q') ≤ a * CL) (hDdef : D = α * β + -(η * a * CL))
    (h1 : α * X ≤ α * P + (η * Y + Φ)) (h2 : β * Y ≤ a * CL * X + a * Φ) :
    D * β * (X + Y) ≤ (β + a * CL) * (α * β * P + (η * a + β) * Φ) + a * D * Φ := by
  have s1 := Q'.mul_le_mul_of_nonneg_left _ _ β h1 hβ
  have s2 := Q'.mul_le_mul_of_nonneg_left _ _ η h2 hη
  have e0 : α * β * X ≈ β * (α * X) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => α | 1 => β | _ => X)
  have e1 : β * (α * P + (η * Y + Φ)) ≈ α * β * P + η * (β * Y) + β * Φ :=
    poly_identity_of_normal_eq
      (.mul (.var 1) (.add (.mul (.var 0) (.var 7)) (.add (.mul (.var 2) (.var 6)) (.var 8))))
      (.add (.add (.mul (.mul (.var 0) (.var 1)) (.var 7)) (.mul (.var 2) (.mul (.var 1) (.var 6))))
        (.mul (.var 1) (.var 8)))
      (by decide)
      (fun | 0 => α | 1 => β | 2 => η | 6 => Y | 7 => P | _ => Φ)
  have t1 : α * β * P + η * (β * Y) + β * Φ ≤ α * β * P + η * (a * CL * X + a * Φ) + β * Φ :=
    Q'.add_le_add_right _ _ (β * Φ) (Q'.add_le_add_left _ _ _ s2)
  have c1 : α * β * X ≤ α * β * P + η * (a * CL * X + a * Φ) + β * Φ :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv e0) (Q'.le_trans' _ _ _ s1
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) t1))
  have c2 := Q'.add_le_add_right _ _ (-(η * a * CL * X)) c1
  have e2 : α * β * P + η * (a * CL * X + a * Φ) + β * Φ + -(η * a * CL * X) ≈
      α * β * P + (η * a + β) * Φ :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.mul (.mul (.var 0) (.var 1)) (.var 7))
        (.mul (.var 2) (.add (.mul (.mul (.var 3) (.var 4)) (.var 5)) (.mul (.var 3) (.var 8)))))
        (.mul (.var 1) (.var 8))) (.neg (.mul (.mul (.mul (.var 2) (.var 3)) (.var 4)) (.var 5))))
      (.add (.mul (.mul (.var 0) (.var 1)) (.var 7)) (.mul (.add (.mul (.var 2) (.var 3)) (.var 1)) (.var 8)))
      (by decide)
      (fun | 0 => α | 1 => β | 2 => η | 3 => a | 4 => CL | 5 => X | 7 => P | _ => Φ)
  have e3 : D * X ≈ α * β * X + -(η * a * CL * X) := by
    rw [hDdef]
    exact poly_identity_of_normal_eq
      (.mul (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.mul (.var 2) (.var 3)) (.var 4)))) (.var 5))
      (.add (.mul (.mul (.var 0) (.var 1)) (.var 5)) (.neg (.mul (.mul (.mul (.var 2) (.var 3)) (.var 4)) (.var 5))))
      (by decide)
      (fun | 0 => α | 1 => β | 2 => η | 3 => a | 4 => CL | _ => X)
  have hi : D * X ≤ α * β * P + (η * a + β) * Φ :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv e3) (Q'.le_trans' _ _ _ c2 (Q'.le_of_eqv e2))
  have s3 := Q'.mul_le_mul_of_nonneg_left _ _ D h2 hD
  have s4 := Q'.mul_le_mul_of_nonneg_left _ _ (a * CL) hi haCL
  have s5 := Q'.mul_le_mul_of_nonneg_left _ _ β hi hβ
  have e4 : D * β * (X + Y) ≈ β * (D * X) + D * (β * Y) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 9) (.var 1)) (.add (.var 5) (.var 6)))
      (.add (.mul (.var 1) (.mul (.var 9) (.var 5))) (.mul (.var 9) (.mul (.var 1) (.var 6))))
      (by decide) (fun | 1 => β | 5 => X | 6 => Y | _ => D)
  have e5 : D * (a * CL * X + a * Φ) ≈ a * CL * (D * X) + a * D * Φ :=
    poly_identity_of_normal_eq
      (.mul (.var 9) (.add (.mul (.mul (.var 3) (.var 4)) (.var 5)) (.mul (.var 3) (.var 8))))
      (.add (.mul (.mul (.var 3) (.var 4)) (.mul (.var 9) (.var 5))) (.mul (.mul (.var 3) (.var 9)) (.var 8)))
      (by decide) (fun | 3 => a | 4 => CL | 5 => X | 8 => Φ | _ => D)
  have e6 : β * (α * β * P + (η * a + β) * Φ) +
        (a * CL * (α * β * P + (η * a + β) * Φ) + a * D * Φ) ≈
      (β + a * CL) * (α * β * P + (η * a + β) * Φ) + a * D * Φ :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 3)) (.add (.mul (.mul (.var 1) (.var 2)) (.var 3)) (.mul (.mul (.var 1) (.var 4)) (.var 5))))
      (.add (.mul (.add (.var 0) (.mul (.var 1) (.var 2))) (.var 3)) (.mul (.mul (.var 1) (.var 4)) (.var 5)))
      (by decide)
      (fun | 0 => β | 1 => a | 2 => CL | 3 => α * β * P + (η * a + β) * Φ | 4 => D | _ => Φ)
  have t2 := tb_add_le s5 s3
  have t3 : β * (α * β * P + (η * a + β) * Φ) + (a * CL * (D * X) + a * D * Φ) ≤
      β * (α * β * P + (η * a + β) * Φ) +
        (a * CL * (α * β * P + (η * a + β) * Φ) + a * D * Φ) :=
    Q'.add_le_add_left _ _ _ (Q'.add_le_add_right _ _ _ s4)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e4) (Q'.le_trans' _ _ _ t2
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ e5))
      (Q'.le_trans' _ _ _ t3 (Q'.le_of_eqv e6))))

namespace TwoBoundaryRecursion

variable {K : Nat} (R : TwoBoundaryRecursion K)

/-- **PROVED (REDUCTION). Two-boundary envelope.** Closure `0 < D`, terminal-weighted
errors `f_j ≤ F ρ^{K−j}`, and any `C` with `Num ≤ D·β·C` give
`u_j + |λ_j| ≤ C·ρ^{K−j}` for all `j ≤ K`. -/
theorem twoBoundary_envelope (F : Q') (hw : TerminalWeightedErrors R.f R.rho K F)
    (hD : (0 : Q') < R.closureDefect) (C : Q')
    (hC : R.envelopeNum F ≤ R.closureDefect * R.beta * C) :
    ∀ j, j ≤ K → R.u j + Q'.abs (R.lam j) ≤ C * R.rho ^ (K - j) := by
  intro j hj
  have H := closure_algebra R.alpha R.beta R.eta R.a R.CL (wmax R.tu K) (wmax R.tl K)
    (R.u K * R.rho ^ K) (F * R.rho ^ K) R.closureDefect (Q'.le_of_lt R.beta_pos)
    R.eta_nonneg (Q'.le_of_lt hD) (Q'.mul_nonneg _ _ R.a_nonneg R.CL_nonneg) rfl
    (R.forward_weighted F hw) (R.backward_weighted F hw)
  have e7 : (R.beta + R.a * R.CL) * (R.alpha * R.beta * (R.u K * R.rho ^ K) +
        (R.eta * R.a + R.beta) * (F * R.rho ^ K)) + R.a * R.closureDefect * (F * R.rho ^ K) ≈
      R.rho ^ K * R.envelopeNum F :=
    poly_identity_of_normal_eq
      (.add (.mul (.add (.var 1) (.mul (.var 3) (.var 4)))
        (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 5) (.var 7)))
          (.mul (.add (.mul (.var 2) (.var 3)) (.var 1)) (.mul (.var 6) (.var 7)))))
        (.mul (.mul (.var 3) (.var 8)) (.mul (.var 6) (.var 7))))
      (.mul (.var 7) (.add (.mul (.add (.var 1) (.mul (.var 3) (.var 4)))
        (.add (.mul (.mul (.var 0) (.var 1)) (.var 5)) (.mul (.add (.mul (.var 2) (.var 3)) (.var 1)) (.var 6))))
        (.mul (.mul (.var 3) (.var 8)) (.var 6))))
      (by decide)
      (fun | 0 => R.alpha | 1 => R.beta | 2 => R.eta | 3 => R.a | 4 => R.CL | 5 => R.u K
           | 6 => F | 7 => R.rho ^ K | _ => R.closureDefect)
  have hDβ0 : (0 : Q') ≤ R.closureDefect * R.beta :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt hD) (Q'.le_of_lt R.beta_pos)
  have hterm : R.closureDefect * R.beta * (R.tu j + R.tl j) ≤
      R.closureDefect * R.beta * (wmax R.tu K + wmax R.tl K) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (tb_add_le (le_wmax R.tu K j hj) (le_wmax R.tl K j hj))
      hDβ0
  have hC' := Q'.mul_le_mul_of_nonneg_left _ _ (R.rho ^ K) hC (Q'.pow_nonneg _ R.rho_nonneg K)
  have main : R.closureDefect * R.beta * (R.tu j + R.tl j) ≤
      R.rho ^ K * (R.closureDefect * R.beta * C) :=
    Q'.le_trans' _ _ _ hterm (Q'.le_trans' _ _ _ H
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv e7) hC'))
  have e8 : R.closureDefect * R.beta * R.rho ^ j * (R.u j + Q'.abs (R.lam j)) ≈
      R.closureDefect * R.beta * (R.tu j + R.tl j) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.add (.var 3) (.var 4)))
      (.mul (.mul (.var 0) (.var 1)) (.add (.mul (.var 3) (.var 2)) (.mul (.var 4) (.var 2))))
      (by decide)
      (fun | 0 => R.closureDefect | 1 => R.beta | 2 => R.rho ^ j | 3 => R.u j
           | _ => Q'.abs (R.lam j))
  have e9 : R.rho ^ j * R.rho ^ (K - j) * (R.closureDefect * R.beta * C) ≈
      R.closureDefect * R.beta * R.rho ^ j * (C * R.rho ^ (K - j)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 2) (.var 4)) (.mul (.mul (.var 0) (.var 1)) (.var 3)))
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 3) (.var 4)))
      (by decide)
      (fun | 0 => R.closureDefect | 1 => R.beta | 2 => R.rho ^ j | 3 => C
           | _ => R.rho ^ (K - j))
  have e10 : R.rho ^ K * (R.closureDefect * R.beta * C) ≈
      R.rho ^ j * R.rho ^ (K - j) * (R.closureDefect * R.beta * C) :=
    Q'.mul_eqv_congr_right _ _ _ (tb_pow_split R.rho K j hj)
  have hpos : (0 : Q') < R.closureDefect * R.beta * R.rho ^ j :=
    Q'.mul_pos (Q'.mul_pos hD R.beta_pos) (tb_pow_pos _ R.rho_pos j)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv e8) (Q'.le_trans' _ _ _ main
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ e10 e9)))) hpos

/-- Explicit constant `C = Num/(D·β)`. -/
def envelopeConst (F : Q') (hD : (0 : Q') < R.closureDefect) : Q' :=
  Q'.divPos (R.envelopeNum F) (R.closureDefect * R.beta) (Q'.mul_pos hD R.beta_pos)

/-- **PROVED (REDUCTION).** The envelope with the explicit constant `C = Num/(D·β)`. -/
theorem twoBoundary_envelope_explicit (F : Q') (hw : TerminalWeightedErrors R.f R.rho K F)
    (hD : (0 : Q') < R.closureDefect) :
    ∀ j, j ≤ K → R.u j + Q'.abs (R.lam j) ≤ R.envelopeConst F hD * R.rho ^ (K - j) :=
  R.twoBoundary_envelope F hw hD (R.envelopeConst F hD)
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (Q'.divPos_mul_eqv _ _ _))))

end TwoBoundaryRecursion

/-! ## Comparison with `RgErrorSummable` -/

theorem weightedErrorSum_nonneg (ε : Nat → Q') (j0 : Nat) (hε : ∀ k, (0 : Q') ≤ ε (j0 + k)) :
    ∀ n, (0 : Q') ≤ weightedErrorSum ε j0 n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
    show (0 : Q') ≤ weightedErrorSum ε j0 n + Q'.ofNat (2 ^ n) * ε (j0 + n)
    exact Q'.zero_le_add _ _ (weightedErrorSum_nonneg ε j0 hε n)
      (Q'.mul_nonneg _ _ (Q'.zero_le_iff_num_nonneg _ |>.mpr (Int.natCast_nonneg _)) (hε n))

/-- `RgErrorSummable` forces every term: `2^k·ε_{j0+k} ≤ S` (geometric decay). -/
theorem rgErrorSummable_term_le (ε : Nat → Q') (j0 : Nat) (S : Q')
    (hε : ∀ k, (0 : Q') ≤ ε (j0 + k)) (h : RgErrorSummable ε j0 S) (k : Nat) :
    Q'.ofNat (2 ^ k) * ε (j0 + k) ≤ S :=
  Q'.le_trans' _ _ _ (tb_le_add_left_of_nonneg _ _ (weightedErrorSum_nonneg ε j0 hε k)) (h.2 (k + 1))

/-- **PROVED (comparison).** After the reflection `k = K − j`, `RgErrorSummable` implies
the terminal-weighted max condition for any base `ρ ≥ 1/2`. -/
theorem terminalWeighted_of_rgErrorSummable (f : Nat → Q') (K : Nat) (ρ S : Q')
    (hρ : half ≤ ρ) (hf0 : ∀ j, (0 : Q') ≤ f j)
    (h : RgErrorSummable (fun k => f (K - k)) 0 S) : TerminalWeightedErrors f ρ K S := by
  refine ⟨h.1, fun j hj => ?_⟩
  have ht : Q'.ofNat (2 ^ (K - j)) * f (K - (0 + (K - j))) ≤ S :=
    rgErrorSummable_term_le (fun k => f (K - k)) 0 S (fun k => hf0 _) h (K - j)
  rw [show K - (0 + (K - j)) = j by omega] at ht
  have e : Q'.ofNat (2 ^ (K - j)) * f j * half ^ (K - j) ≈ f j :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => Q'.ofNat (2 ^ (K - j)) | 1 => f j | _ => half ^ (K - j)))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (ofNat_two_pow_mul_half_pow (K - j)))
        (Q'.mul_one_eqv (f j)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm e))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ ht (Q'.pow_nonneg _ half_nonneg (K - j)))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (pow_le_pow_left half_nonneg hρ (K - j)) h.1))

/-! ## Necessity: the exact forward system -/

def exactUAux (f : Nat → Q') (q : Q') (K : Nat) : Nat → Q'
  | 0 => 0
  | m + 1 => q * exactUAux f q K m + f (K - m)

/-- Exact solution of `u_j = q u_{j+1} + f_{j+1}`, `u_K = 0`. -/
def exactU (f : Nat → Q') (q : Q') (K j : Nat) : Q' := exactUAux f q K (K - j)

theorem exactU_eq (f : Nat → Q') (q : Q') (K j : Nat) (hj : j < K) :
    exactU f q K j = q * exactU f q K (j + 1) + f (j + 1) := by
  show exactUAux f q K (K - j) = q * exactUAux f q K (K - (j + 1)) + f (j + 1)
  rw [show K - j = (K - (j + 1)) + 1 by omega]
  show q * exactUAux f q K (K - (j + 1)) + f (K - (K - (j + 1))) = _
  rw [show K - (K - (j + 1)) = j + 1 by omega]

theorem exactUAux_nonneg (f : Nat → Q') (q : Q') (K : Nat) (hq : (0 : Q') ≤ q)
    (hf0 : ∀ j, (0 : Q') ≤ f j) : ∀ m, (0 : Q') ≤ exactUAux f q K m
  | 0 => Q'.le_refl' 0
  | m + 1 => Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hq (exactUAux_nonneg f q K hq hf0 m)) (hf0 _)

/-- The exact forward system as a `TwoBoundaryRecursion` (`λ ≡ 0`). -/
def exactForwardSystem (K : Nat) (f : Nat → Q') (q eta a CL rho : Q')
    (hf0 : ∀ j, (0 : Q') ≤ f j) (hq : (0 : Q') ≤ q) (heta : (0 : Q') ≤ eta)
    (ha : (0 : Q') ≤ a) (hCL : (0 : Q') ≤ CL) (hqρ : q < rho) (hρ1 : rho < (1 : Q'))
    (haρ : a * rho < (1 : Q')) : TwoBoundaryRecursion K where
  u := exactU f q K
  lam := fun _ => 0
  f := f
  q := q
  eta := eta
  a := a
  CL := CL
  rho := rho
  u_nonneg := fun j => exactUAux_nonneg f q K hq hf0 (K - j)
  q_nonneg := hq
  eta_nonneg := heta
  a_nonneg := ha
  CL_nonneg := hCL
  q_lt_rho := hqρ
  rho_lt_one := hρ1
  a_rho_lt_one := haρ
  forward := fun j hj => by
    show exactU f q K j ≤ q * exactU f q K (j + 1) + eta * Q'.abs 0 + f (j + 1)
    rw [exactU_eq f q K j hj]
    exact Q'.add_le_add_right _ _ _
      (Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _ heta (Q'.abs_nonneg 0)))
  backward := fun j _ => by
    show Q'.abs 0 ≤ a * Q'.abs 0 + a * CL * exactU f q K (j + 1) + a * f (j + 1)
    rw [tb_abs_zero]
    exact Q'.zero_le_add _ _
      (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ ha (Q'.le_refl' 0))
        (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ ha hCL) (exactUAux_nonneg f q K hq hf0 _)))
      (Q'.mul_nonneg _ _ ha (hf0 _))
  pin := rfl

/-- **PROVED (necessity).** On the exact forward system, any envelope
`u_j + |λ_j| ≤ C ρ^{K−j}` forces `f_{j+1} ≤ C ρ^{K−j}` for `j < K`. -/
theorem terminal_weighting_necessary (K : Nat) (f : Nat → Q') (q eta a CL rho : Q')
    (hf0 : ∀ j, (0 : Q') ≤ f j) (hq : (0 : Q') ≤ q) (heta : (0 : Q') ≤ eta)
    (ha : (0 : Q') ≤ a) (hCL : (0 : Q') ≤ CL) (hqρ : q < rho) (hρ1 : rho < (1 : Q'))
    (haρ : a * rho < (1 : Q')) (C : Q')
    (henv : ∀ j, j ≤ K →
      (exactForwardSystem K f q eta a CL rho hf0 hq heta ha hCL hqρ hρ1 haρ).u j +
        Q'.abs ((exactForwardSystem K f q eta a CL rho hf0 hq heta ha hCL hqρ hρ1 haρ).lam j)
        ≤ C * rho ^ (K - j))
    (j : Nat) (hj : j < K) : f (j + 1) ≤ C * rho ^ (K - j) := by
  have h := henv j (Nat.le_of_lt hj)
  have hu : f (j + 1) ≤ exactU f q K j := by
    rw [exactU_eq f q K j hj]
    exact tb_le_add_left_of_nonneg _ _
      (Q'.mul_nonneg _ _ hq (exactUAux_nonneg f q K hq hf0 _))
  exact Q'.le_trans' _ _ _ hu (Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ (Q'.abs_nonneg _)) h)

/-- **Far-end corollary.** `f_1 ≤ C ρ^K`: a `K`-independent far-end error (e.g. any
polynomially decaying `f_j = c/(j+1)^p` with `K` the terminal scale) forces
`C ≥ f_1 ρ^{-K}`, exponential in `K`. -/
theorem far_end_error_forces_C (K : Nat) (hK : 0 < K) (f : Nat → Q') (q eta a CL rho : Q')
    (hf0 : ∀ j, (0 : Q') ≤ f j) (hq : (0 : Q') ≤ q) (heta : (0 : Q') ≤ eta)
    (ha : (0 : Q') ≤ a) (hCL : (0 : Q') ≤ CL) (hqρ : q < rho) (hρ1 : rho < (1 : Q'))
    (haρ : a * rho < (1 : Q')) (C : Q')
    (henv : ∀ j, j ≤ K →
      (exactForwardSystem K f q eta a CL rho hf0 hq heta ha hCL hqρ hρ1 haρ).u j +
        Q'.abs ((exactForwardSystem K f q eta a CL rho hf0 hq heta ha hCL hqρ hρ1 haρ).lam j)
        ≤ C * rho ^ (K - j)) :
    f 1 ≤ C * rho ^ K :=
  terminal_weighting_necessary K f q eta a CL rho hf0 hq heta ha hCL hqρ hρ1 haρ C henv 0 hK

end YMGap.Continuum.RGTwoBoundaryEnvelope

#print axioms YMGap.Continuum.RGTwoBoundaryEnvelope.wmax_attained
#print axioms YMGap.Continuum.RGTwoBoundaryEnvelope.TwoBoundaryRecursion.forward_weighted
#print axioms YMGap.Continuum.RGTwoBoundaryEnvelope.TwoBoundaryRecursion.backward_weighted
#print axioms YMGap.Continuum.RGTwoBoundaryEnvelope.closure_algebra
#print axioms YMGap.Continuum.RGTwoBoundaryEnvelope.TwoBoundaryRecursion.twoBoundary_envelope
#print axioms YMGap.Continuum.RGTwoBoundaryEnvelope.TwoBoundaryRecursion.twoBoundary_envelope_explicit
#print axioms YMGap.Continuum.RGTwoBoundaryEnvelope.terminalWeighted_of_rgErrorSummable
#print axioms YMGap.Continuum.RGTwoBoundaryEnvelope.terminal_weighting_necessary
#print axioms YMGap.Continuum.RGTwoBoundaryEnvelope.far_end_error_forces_C
