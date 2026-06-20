/-
Track B / R2 — the QUOTIENT-COLLAPSE denominator anchor for the `n = 2`
(single self-fusion) bond-moving model, and a partial chip at the relative
fusion-residual quotient.

# Why this module exists — the denominator carries the τ-cancellation

The full-mode bond-moving gap chain is conditional on the per-mode relative
residual bound `absQ (rrel s) ≤ (1−w)²·Peval P (yArg w s)`, where the relative
residual is the VACUUM-NORMALIZED quotient

    rrel s  =  (g s · ĉ 0) / (g 0 · ĉ s)  −  1,
    g s = bondMovedCoeff N w p s,   ĉ s = coeffW (renormW p w) s.

The KEY structural fact is that this must be estimated AS A QUOTIENT: the
denominator factor `g 0` (the fused vacuum coefficient) carries a large negative
power of the margin `τ = 1 − w`, which cancels the τ-growth of the numerator.
A crude envelope on the numerator alone reintroduces a fake `τ^{−2}`.  The
DENOMINATOR ANCHOR below makes the τ-content of `g 0` explicit and quantitative.

# What is GENUINELY PROVED here (axiom-clean `Q'`/`Nat` arithmetic)

THE DENOMINATOR ANCHOR (`p = 2`, the single self-fusion `n = 2` model):

  * `qpow_mul_self` — `qpow (w*w) n ≃ qpow w n · qpow w n` (the `w²`-power is the
    square of the `w`-power), the seed of the diagonal collapse.
  * `coeffW_sq_eqv` — `(coeffW w a)² ≃ dimQ a · (dimQ a · qpow (w*w) (c4 a))`, i.e.
    the square of a heat-kernel coefficient is exactly the `Zsum(w²)` summand.
  * `fusionPow_one_eq` — the unit fusion identity `fusionPow N (coeffW w) 1 a =
    coeffW w a` for `a ≤ N` (the `χ_0 ⋆ c` law on all modes within the cutoff;
    `fusionUnit` collapses the outer index to `0`, then `fusionInd 0 d a` collapses
    the inner index to `d = a`).
  * `fusion_zeroCoeff_eq_Zsum_sq` — **THE ANCHOR (equality form):**
    `bondMovedCoeff N w 2 0 ≃ Zsum (w*w) (N+1)`.  The `s = 0` fusion channel of the
    self-fusion forces `a = b` (the `χ_a · χ_b ∋ χ_0` rule), collapsing the double
    sum to the diagonal `∑_{a≤N} (coeffW w a)²`, which equals `Zsum(w²)` termwise.
  * `fusion_zeroCoeff_Lp_lower` — **THE ANCHOR (cube / τ-scaling form):**
    `ofNat(S·S·S) ≤ ofNat 6 · bondMovedCoeff N w 2 0` under the head floors for the
    `w²`-partition.  In words `g 0 ≥ (1/6)·S³`; instantiated at the moving cutoff
    `S = S₀(w²) ≍ τ^{−1/2}` this is the denominator anchor `g 0 ≳ τ^{−3/2}` (the
    `−3(p−1)/2 = −3/2` power at `p = 2`).

A PARTIAL CHIP at the `n = 2` quotient bound:

  * `rrelFusion2_zero_bound` — the EXACT `s = 0` target bound
    `absQ (rrelFusion N w 2 0) ≤ (1−w)²·Peval residualP (yArg w 0)` (LHS = 0,
    re-exported at `p = 2`).
  * `coeffW_ratio_mono` — the PF₂ ratio-monotonicity GUARDRAIL
    `coeffW w s · coeffW w (s+2) ≤ coeffW w (s+1)²` repackaged as the statement
    that the consecutive ratio `coeffW(s+1)/coeffW(s)` is non-increasing
    (cross-multiplied form), the structural guardrail preventing dips between
    certified modes.

# NAMED OPEN — the genuine crossover (NOT inhabited, in the exact `hbound` shape)

  * `QuotientActiveWindowCert` — the per-mode quotient bound on the ACTIVE modes
    `1 ≤ s`, VERBATIM in the `absQ (rrel s) ≤ (1−w)²·Peval P (yArg w s)` shape, so a
    witness composes directly with the upstream genuine-residual interface.  It is
    NOT inhabited: collapsing the proved quadratic numerator defect through the
    division by `g 0 · ĉ s` — i.e. using the anchor `g 0 ≳ τ^{−3/2}` to beat the
    numerator's τ-growth UNIFORMLY in `s` — is the open weak↔strong crossover.

# Honest verdict and scope

This module proves the DENOMINATOR ANCHOR for the `n = 2` self-fusion model:
`g 0 = Zsum(w²)` exactly, and `g 0 ≥ (1/6)·S³` (the `τ^{−3/2}` lower bound) under
the `w²`-head floors.  It proves the `s = 0` quotient bound exactly and the PF₂
ratio-monotonicity guardrail.  It does NOT prove the per-mode quotient bound on the
active modes `s ≥ 1` — that (the genuine crossover, named `QuotientActiveWindowCert`
in the exact `hbound` shape) is left honestly open, NOT faked, NOT a C₄² envelope.
This is NOT a 4D Yang–Mills mass gap; it is the denominator anchor plus a partial
quotient for one self-fusion model.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, decidable `Nat`/`Q'` facts, and
reused order/`divPos` lemmas.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide` (only `decide` on decidable facts), no `sorry`.
All witnesses are `Type`-level data.
-/

import YMGap.Continuum.MovingCutoff
import YMGap.Continuum.FusionResidualBound

namespace YMGap.Continuum.FusionQuotientCollapse

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.MovingCutoff
open YMGap.Continuum.FusionResidualBound

/-! ## 0. The `w²`-power is the square of the `w`-power (seed of the collapse) -/

/-- **`qpow (w*w) n ≃ qpow w n · qpow w n`.**  The power of the squared base is the
square of the power.  Induction on `n`: at `n+1`,
`(w²)^{n+1} = (w²)^n · w² ≃ (w^n·w^n)·(w·w) ≃ (w^n·w)·(w^n·w) = w^{n+1}·w^{n+1}`. -/
theorem qpow_mul_self (w : Q') :
    ∀ n, (qpow (w * w) n).eqv (qpow w n * qpow w n)
  | 0 => by
      show (1 : Q').eqv ((1 : Q') * (1 : Q'))
      exact Q'.eqv_symm (Q'.one_mul_eqv 1)
  | n + 1 => by
      -- (w²)^{n+1} = (w²)^n · (w*w)
      show (qpow (w * w) n * (w * w)).eqv (qpow w (n + 1) * qpow w (n + 1))
      show (qpow (w * w) n * (w * w)).eqv ((qpow w n * w) * (qpow w n * w))
      -- (w²)^n · (w*w) ≃ (w^n·w^n)·(w*w)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (w * w) (qpow_mul_self w n)) ?_
      -- (w^n·w^n)·(w·w) ≃ (w^n·w)·(w^n·w)  [regroup the four factors]
      exact mul_four_regroup (qpow w n) (qpow w n) w w

/-- **`(coeffW w a)² ≃ Zsum(w²) summand at `a`.**  The square of a heat-kernel
coefficient is exactly the `Zsum(w*w)` summand:

    coeffW w a · coeffW w a  ≃  dimQ a · (dimQ a · qpow (w*w) (c4 a)).

PROOF: `coeffW w a = dimQ a · w^{c4 a}`, regroup into `(dimQ a·dimQ a)·(w^…·w^…)`,
then `w^…·w^… ≃ (w²)^…` (`qpow_mul_self`) and re-associate. -/
theorem coeffW_sq_eqv (w : Q') (a : Nat) :
    (coeffW w a * coeffW w a).eqv
      (dimQ a * (dimQ a * qpow (w * w) (c4 a))) := by
  show ((dimQ a * qpow w (c4 a)) * (dimQ a * qpow w (c4 a))).eqv
      (dimQ a * (dimQ a * qpow (w * w) (c4 a)))
  -- LHS regroup: (d·p)·(d·p) ≃ (d·d)·(p·p)
  refine Q'.eqv_trans _ _ _
    (mul_four_regroup (dimQ a) (qpow w (c4 a)) (dimQ a) (qpow w (c4 a))) ?_
  -- (d·d)·(p·p) ≃ (d·d)·((w²)^…)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (dimQ a * dimQ a) _ _
      (Q'.eqv_symm (qpow_mul_self w (c4 a)))) ?_
  -- (d·d)·q ≃ d·(d·q)
  exact Q'.mul_assoc_eqv (dimQ a) (dimQ a) (qpow (w * w) (c4 a))

/-! ## 1. The unit fusion identity `fusionPow N (coeffW w) 1 a = coeffW w a`

`fusionPow N c 1 a = fusionProduct N fusionUnit c a`, a double sum over `(d₁,d₂)`.
`fusionUnit d₁ = δ_{d₁,0}` collapses the outer index to `0`; then
`fusionInd 0 d₂ a = 1 ⇔ d₂ = a` collapses the inner index to `d₂ = a`.  We prove
the pointwise identity for `a ≤ N` by two delta-sum collapses. -/

/-- If every term `g b` with `b < n` is `≃ 0`, then `fsum g n ≃ 0`. -/
theorem fsum_zero_below {g : Nat → Q'} :
    ∀ n, (∀ b, b < n → (g b).eqv 0) → (fsum g n).eqv 0
  | 0, _ => Q'.eqv_refl 0
  | n + 1, hz => by
      show (fsum g n + g n).eqv 0
      have hpre : (fsum g n).eqv 0 :=
        fsum_zero_below n (fun b hb => hz b (Nat.lt_succ_of_lt hb))
      have hgn : (g n).eqv 0 := hz n (Nat.lt_succ_self n)
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hpre hgn) ?_
      exact q_add_zero_eqv 0

/-- **A delta-collapse for `fsum`.**  If `g b ≃ 0` for every `b ≠ k`, and `k < n`,
then `fsum g n ≃ g k`.  (Induction on `n`: at the top either `n = k` and the prefix
is `≃ 0` (`fsum_zero_below`), or the last term `g n ≃ 0` and we recurse.) -/
theorem fsum_collapse {g : Nat → Q'}
    (hz : ∀ b, b ≠ k → (g b).eqv 0) :
    ∀ n, k < n → (fsum g n).eqv (g k)
  | 0, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, hk => by
      show (fsum g n + g n).eqv (g k)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
      · -- k < n : last term g n ≃ 0 (n ≠ k since k < n), recurse on prefix
        have hgn : (g n).eqv 0 := hz n (fun h => absurd h.symm (Nat.ne_of_lt hlt))
        have hpre : (fsum g n).eqv (g k) := fsum_collapse hz n hlt
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hpre hgn) ?_
        exact q_add_zero_eqv (g k)
      · -- n = k : prefix fsum g k ≃ 0 (all b < k have b ≠ k), last term is g k
        subst heq
        have hpre0 : (fsum g k).eqv 0 :=
          fsum_zero_below k (fun b hb => hz b (Nat.ne_of_lt hb))
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (g k) hpre0) ?_
        exact q_zero_add_eqv (g k)

/-- `fusionOK a b s` as a decidable proposition: the membership conditions. -/
theorem fusionOK_eq_true_iff (a b s : Nat) :
    fusionOK a b s = true ↔
      (Nat.max a b - Nat.min a b ≤ s) ∧ (s ≤ a + b) ∧ ((a + b + s) % 2 = 0) := by
  unfold fusionOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

theorem fusionOK_eq_false_iff (a b s : Nat) :
    fusionOK a b s = false ↔
      ¬ ((Nat.max a b - Nat.min a b ≤ s) ∧ (s ≤ a + b) ∧ ((a + b + s) % 2 = 0)) := by
  rw [← fusionOK_eq_true_iff]
  cases h : fusionOK a b s <;> simp

/-- `fusionOK 0 d a = false` when `d ≠ a` (the `χ_0 · χ_d ∋ χ_a` rule forces
`d = a`: the range conditions are `d ≤ a` and `a ≤ d`). -/
theorem fusionOK_zero_left_ne (d a : Nat) (h : d ≠ a) : fusionOK 0 d a = false := by
  rw [fusionOK_eq_false_iff]
  -- d - 0 = d ; d ≤ a (h1) and a ≤ 0+d = d (h2) ⟹ d = a, contradicting h
  rintro ⟨h1, h2, _⟩
  simp only [Nat.zero_max, Nat.zero_min] at h1
  omega

/-- `fusionInd 0 d a = 0` when `d ≠ a`. -/
theorem fusionInd_zero_left_ne (d a : Nat) (h : d ≠ a) : fusionInd 0 d a = (0 : Q') := by
  unfold fusionInd
  rw [fusionOK_zero_left_ne d a h]; rfl

/-- `fusionOK 0 a a = true` (the diagonal `χ_0 · χ_a ∋ χ_a` channel). -/
theorem fusionOK_zero_left_self (a : Nat) : fusionOK 0 a a = true := by
  rw [fusionOK_eq_true_iff]
  simp only [Nat.zero_max, Nat.zero_min]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- `fusionInd 0 a a = 1`. -/
theorem fusionInd_zero_left_self (a : Nat) : fusionInd 0 a a = (1 : Q') := by
  unfold fusionInd
  rw [fusionOK_zero_left_self a]; rfl

/-- **The unit fusion identity (pointwise, within the cutoff).**  For `a ≤ N`,

    fusionPow N (coeffW w) 1 a  ≃  coeffW w a.

PROOF: `fusionPow N c 1 a = fsum (fun d₁ => fsum (fun d₂ => fusionInd d₁ d₂ a ·
(fusionUnit d₁ · c d₂)) (N+1)) (N+1)`.  Outer delta on `d₁` (`fusionUnit d₁ =
δ_{d₁,0}`) collapses to `d₁ = 0`; inner delta on `d₂` (`fusionInd 0 d₂ a =
δ_{d₂,a}`) collapses to `d₂ = a`, leaving `1·(1·c a) ≃ c a`. -/
theorem fusionPow_one_eq {w : Q'} {N a : Nat} (haN : a ≤ N) :
    (fusionPow N (coeffW w) 1 a).eqv (coeffW w a) := by
  show (fusionProduct N (fusionPow N (coeffW w) 0) (coeffW w) a).eqv (coeffW w a)
  show (fsum (fun d₁ => fsum (fun d₂ =>
      fusionInd d₁ d₂ a * (fusionUnit d₁ * coeffW w d₂)) (N + 1)) (N + 1)).eqv (coeffW w a)
  -- Outer collapse: only d₁ = 0 survives (fusionUnit d₁ = 0 for d₁ ≠ 0).
  have houter_zero : ∀ d₁, d₁ ≠ 0 →
      ((fun d₁ => fsum (fun d₂ =>
        fusionInd d₁ d₂ a * (fusionUnit d₁ * coeffW w d₂)) (N + 1)) d₁).eqv 0 := by
    intro d₁ hd₁
    show (fsum (fun d₂ => fusionInd d₁ d₂ a * (fusionUnit d₁ * coeffW w d₂)) (N + 1)).eqv 0
    -- fusionUnit d₁ = 0, so every inner summand ≃ 0, so the inner sum ≃ 0.
    have hunit : fusionUnit d₁ = (0 : Q') := by
      unfold fusionUnit
      have hb : (d₁ == 0) = false := by
        cases d₁ with
        | zero => exact absurd rfl hd₁
        | succ k => rfl
      rw [hb]; rfl
    -- each term ≃ 0
    refine fsum_zero_below (N + 1) (fun d₂ _ => ?_)
    show (fusionInd d₁ d₂ a * (fusionUnit d₁ * coeffW w d₂)).eqv 0
    rw [hunit]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (fusionInd d₁ d₂ a) _ _ (Q'.zero_mul_eqv (coeffW w d₂))) ?_
    exact q_mul_zero (fusionInd d₁ d₂ a)
  -- so outer sum ≃ outer 0
  have hcollapse_outer : (fsum (fun d₁ => fsum (fun d₂ =>
        fusionInd d₁ d₂ a * (fusionUnit d₁ * coeffW w d₂)) (N + 1)) (N + 1)).eqv
      ((fun d₁ => fsum (fun d₂ =>
        fusionInd d₁ d₂ a * (fusionUnit d₁ * coeffW w d₂)) (N + 1)) 0) :=
    fsum_collapse houter_zero (N + 1) (Nat.succ_pos N)
  refine Q'.eqv_trans _ _ _ hcollapse_outer ?_
  -- outer 0 = fsum (fun d₂ => fusionInd 0 d₂ a · (fusionUnit 0 · coeffW w d₂)) (N+1)
  -- fusionUnit 0 = 1.  Inner delta on d₂ : only d₂ = a survives.
  show (fsum (fun d₂ => fusionInd 0 d₂ a * (fusionUnit 0 * coeffW w d₂)) (N + 1)).eqv (coeffW w a)
  have hinner_zero : ∀ d₂, d₂ ≠ a →
      ((fun d₂ => fusionInd 0 d₂ a * (fusionUnit 0 * coeffW w d₂)) d₂).eqv 0 := by
    intro d₂ hd₂
    show (fusionInd 0 d₂ a * (fusionUnit 0 * coeffW w d₂)).eqv 0
    have hind : fusionInd 0 d₂ a = (0 : Q') := fusionInd_zero_left_ne d₂ a hd₂
    rw [hind]
    exact Q'.zero_mul_eqv _
  have hcollapse_inner : (fsum (fun d₂ => fusionInd 0 d₂ a * (fusionUnit 0 * coeffW w d₂)) (N + 1)).eqv
      ((fun d₂ => fusionInd 0 d₂ a * (fusionUnit 0 * coeffW w d₂)) a) :=
    fsum_collapse hinner_zero (N + 1) (Nat.lt_succ_of_le haN)
  refine Q'.eqv_trans _ _ _ hcollapse_inner ?_
  -- (fusionInd 0 a a) · ((fusionUnit 0) · coeffW w a) = 1·(1·coeffW w a) ≃ coeffW w a
  show (fusionInd 0 a a * (fusionUnit 0 * coeffW w a)).eqv (coeffW w a)
  have hind1 : fusionInd 0 a a = (1 : Q') := fusionInd_zero_left_self a
  have hunit1 : fusionUnit 0 = (1 : Q') := by unfold fusionUnit; rfl
  rw [hind1, hunit1]
  refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv ((1 : Q') * coeffW w a)) ?_
  exact Q'.one_mul_eqv (coeffW w a)

/-! ## 2. THE DENOMINATOR ANCHOR — `g 0 = Zsum(w²)` (equality form)

`g 0 = bondMovedCoeff N w 2 0 = fusionProduct N g₁ (coeffW w) 0` with
`g₁ = fusionPow N (coeffW w) 1`.  The `s = 0` channel of `fusionProduct` keeps only
`(a,b)` with `fusionInd a b 0 = 1`, i.e. `a = b` (`χ_a·χ_b ∋ χ_0 ⇔ a = b`).  So

    g 0  =  ∑_{a≤N} g₁(a) · coeffW w a  =  ∑_{a≤N} (coeffW w a)²  =  Zsum(w²)(N+1),

using `g₁(a) = coeffW w a` (`fusionPow_one_eq`, `a ≤ N`) and `(coeffW w a)² =
Zsum(w²) summand` (`coeffW_sq_eqv`). -/

/-- `fusionOK a b 0 = false` when `a ≠ b` (the `χ_0` channel is the diagonal:
`max a b - min a b ≤ 0` forces `a = b`). -/
theorem fusionOK_zero_diag_ne (a b : Nat) (h : a ≠ b) : fusionOK a b 0 = false := by
  rw [fusionOK_eq_false_iff]
  rintro ⟨h1, _, _⟩
  -- max a b - min a b ≤ 0 forces max ≤ min hence a = b
  have hmax : a ≤ Nat.max a b := Nat.le_max_left a b
  have hmax' : b ≤ Nat.max a b := Nat.le_max_right a b
  have hmin : Nat.min a b ≤ a := Nat.min_le_left a b
  have hmin' : Nat.min a b ≤ b := Nat.min_le_right a b
  omega

/-- `fusionInd a b 0 = 0` when `a ≠ b`. -/
theorem fusionInd_zero_diag_ne (a b : Nat) (h : a ≠ b) : fusionInd a b 0 = (0 : Q') := by
  unfold fusionInd
  rw [fusionOK_zero_diag_ne a b h]; rfl

/-- `fusionOK a a 0 = true` (the diagonal `χ_0` channel). -/
theorem fusionOK_zero_diag_self (a : Nat) : fusionOK a a 0 = true := by
  rw [fusionOK_eq_true_iff]
  simp only [Nat.max_self, Nat.min_self]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- `fusionInd a a 0 = 1`. -/
theorem fusionInd_zero_diag_self (a : Nat) : fusionInd a a 0 = (1 : Q') := by
  unfold fusionInd
  rw [fusionOK_zero_diag_self a]; rfl

/-- **The `s = 0` fusion channel collapses to the diagonal.**  For any `c, d`,

    fusionProduct N c d 0  ≃  ∑_{a≤N} c a · d a,

because only the `a = b` summands survive the `χ_0` fusion indicator.  (Inner delta
collapse on `b` at each fixed `a`, via `fsum_collapse`.) -/
theorem fusionProduct_zero_diag (N : Nat) (c d : Nat → Q') :
    (fusionProduct N c d 0).eqv (fsum (fun a => c a * d a) (N + 1)) := by
  show (fsum (fun a => fsum (fun b => fusionInd a b 0 * (c a * d b)) (N + 1)) (N + 1)).eqv
      (fsum (fun a => c a * d a) (N + 1))
  -- bridge fsum → finSum on both sides, use finSum_eqv_congr_lt termwise
  rw [fsum_eq_finSum (fun a => fsum (fun b => fusionInd a b 0 * (c a * d b)) (N + 1)) (N + 1),
    fsum_eq_finSum (fun a => c a * d a) (N + 1)]
  refine RationalTail.finSum_eqv_congr_lt
    (fun a => fsum (fun b => fusionInd a b 0 * (c a * d b)) (N + 1))
    (fun a => c a * d a) (N + 1) ?_
  intro a haN
  have haN' : a ≤ N := Nat.lt_succ_iff.mp haN
  show (fsum (fun b => fusionInd a b 0 * (c a * d b)) (N + 1)).eqv (c a * d a)
  -- only b = a survives (fusionInd a b 0 = 0 for b ≠ a).
  have hinner_zero : ∀ b, b ≠ a →
      ((fun b => fusionInd a b 0 * (c a * d b)) b).eqv 0 := by
    intro b hb
    show (fusionInd a b 0 * (c a * d b)).eqv 0
    have hind : fusionInd a b 0 = (0 : Q') := fusionInd_zero_diag_ne a b (fun h => hb h.symm)
    rw [hind]
    exact Q'.zero_mul_eqv _
  have hcollapse : (fsum (fun b => fusionInd a b 0 * (c a * d b)) (N + 1)).eqv
      ((fun b => fusionInd a b 0 * (c a * d b)) a) :=
    fsum_collapse hinner_zero (N + 1) (Nat.lt_succ_of_le haN')
  refine Q'.eqv_trans _ _ _ hcollapse ?_
  -- (fusionInd a a 0) · (c a · d a) = 1·(c a·d a) ≃ c a · d a
  show (fusionInd a a 0 * (c a * d a)).eqv (c a * d a)
  have hind1 : fusionInd a a 0 = (1 : Q') := fusionInd_zero_diag_self a
  rw [hind1]
  exact Q'.one_mul_eqv (c a * d a)

/-- **THE DENOMINATOR ANCHOR (equality form): `g 0 ≃ Zsum(w²)`.**  For the `p = 2`
self-fusion model,

    bondMovedCoeff N w 2 0  ≃  Zsum (w * w) (N + 1).

PROOF.  `g 0 = fusionProduct N g₁ (coeffW w) 0` with `g₁ = fusionPow N (coeffW w) 1`.
The `s = 0` channel collapses to the diagonal (`fusionProduct_zero_diag`):
`g 0 ≃ ∑_{a≤N} g₁(a)·coeffW w a`.  Termwise `g₁(a) ≃ coeffW w a` (`fusionPow_one_eq`,
`a ≤ N`), so `g 0 ≃ ∑_{a≤N} (coeffW w a)²`; each square is the `Zsum(w²)` summand
(`coeffW_sq_eqv`).  The cutoffs align: the fusion truncation `N` makes the diagonal
sum range `a < N+1`, exactly the `Zsum (w*w) (N+1)` range. -/
theorem fusion_zeroCoeff_eq_Zsum_sq {w : Q'} (N : Nat) :
    (bondMovedCoeff N w 2 0).eqv (Zsum (w * w) (N + 1)) := by
  -- g 0 = fusionProduct N (fusionPow N (coeffW w) 1) (coeffW w) 0
  show (fusionProduct N (fusionPow N (coeffW w) 1) (coeffW w) 0).eqv (Zsum (w * w) (N + 1))
  -- diagonal collapse
  refine Q'.eqv_trans _ _ _
    (fusionProduct_zero_diag N (fusionPow N (coeffW w) 1) (coeffW w)) ?_
  -- ∑_{a≤N} g₁(a)·coeffW w a ≃ ∑_{a≤N} dimQ a·(dimQ a·(w²)^{c4 a}) = Zsum(w²)(N+1)
  show (fsum (fun a => fusionPow N (coeffW w) 1 a * coeffW w a) (N + 1)).eqv
      (Zsum (w * w) (N + 1))
  show (fsum (fun a => fusionPow N (coeffW w) 1 a * coeffW w a) (N + 1)).eqv
      (fsum (fun s => dimQ s * (dimQ s * qpow (w * w) (c4 s))) (N + 1))
  rw [fsum_eq_finSum (fun a => fusionPow N (coeffW w) 1 a * coeffW w a) (N + 1),
    fsum_eq_finSum (fun s => dimQ s * (dimQ s * qpow (w * w) (c4 s))) (N + 1)]
  refine RationalTail.finSum_eqv_congr_lt
    (fun a => fusionPow N (coeffW w) 1 a * coeffW w a)
    (fun s => dimQ s * (dimQ s * qpow (w * w) (c4 s))) (N + 1) ?_
  intro a haN
  have haN' : a ≤ N := Nat.lt_succ_iff.mp haN
  -- g₁(a)·coeffW w a ≃ coeffW w a · coeffW w a ≃ Zsum(w²) summand
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (coeffW w a) (fusionPow_one_eq haN')) ?_
  exact coeffW_sq_eqv w a

/-! ## 3. THE DENOMINATOR ANCHOR — the cube / τ-scaling form `g 0 ≥ (1/6)·S³`

Transporting `Zsum_ge_cube` (MovingCutoff, Pillar 1) across the anchor equality
`g 0 = Zsum(w²)` gives the τ^{−3/2} lower bound on the fused vacuum coefficient.
The head floors are imposed for the `w²`-partition (`2·C₄(s)·(1−w²) ≤ 1`). -/

/-- **THE DENOMINATOR ANCHOR (cube form): `ofNat(S³) ≤ ofNat 6 · g 0`.**  For the
`p = 2` self-fusion model, under the `w²`-head floors (`2·C₄(s)·(1−w²) ≤ 1` for
`s < S`, `S ≤ N+1`, `0 ≤ w ≤ 1`),

    ofNat(S·S·S)  ≤  ofNat 6 · bondMovedCoeff N w 2 0,

i.e. `g 0 ≥ (1/6)·S³`.  Instantiated at the moving cutoff `S = S₀(w²) ≍ τ^{−1/2}`
(where `C₄(S₀) ≍ 1/(2(1−w²))`, so `S₀ ≍ (1−w²)^{−1/2} ≍ τ^{−1/2}`) this is the
denominator anchor `g 0 ≳ τ^{−3/2}` — the `−3(p−1)/2 = −3/2` power at `p = 2`.
PROOF: `Zsum_ge_cube` at base `w²` gives `ofNat(S³) ≤ ofNat 6 · Zsum(w²)(N+1)`;
transport across `fusion_zeroCoeff_eq_Zsum_sq`. -/
theorem fusion_zeroCoeff_Lp_lower {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (S N : Nat) (hSN : S ≤ N + 1)
    (hfloor : ∀ s, s < S →
      Q'.ofNat 2 * (Q'.ofNat (c4 s) * ((1 : Q') - w * w)) ≤ (1 : Q')) :
    Q'.ofNat (S * S * S) ≤ Q'.ofNat 6 * bondMovedCoeff N w 2 0 := by
  -- w² is in [0,1]
  have hww0 : (0 : Q') ≤ w * w := Q'.mul_nonneg _ _ hw0 hw0
  have hww1 : w * w ≤ (1 : Q') := by
    -- w·w ≤ w·1 = w ≤ 1
    have h1 : w * w ≤ w * (1 : Q') := Q'.mul_le_mul_of_nonneg_left _ _ _ hw1 hw0
    refine Q'.le_trans' _ _ _ h1 ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv w)) hw1
  -- Zsum cube bound at base w²
  have hcube : Q'.ofNat (S * S * S) ≤ Q'.ofNat 6 * Zsum (w * w) (N + 1) :=
    Zsum_ge_cube hww0 hww1 S (N + 1) hSN hfloor
  -- transport across g 0 ≃ Zsum(w²)(N+1)
  refine Q'.le_trans' _ _ _ hcube ?_
  refine Q'.le_of_eqv ?_
  exact Q'.mul_eqv_congr_left (Q'.ofNat 6) _ _
    (Q'.eqv_symm (fusion_zeroCoeff_eq_Zsum_sq N))

/-! ## 4. The `s = 0` quotient bound at `p = 2` (re-export, exact) -/

/-- **The `s = 0` quotient bound at `p = 2`.**  For `0 < w ≤ 1` (and the retuned
`0 < renormW 2 w`), the relative fusion residual at the vacuum mode meets the exact
target shape:

    absQ (rrelFusion N w 2 0)  ≤  ((1 − w)·(1 − w)) · Peval residualP (yArg w 0).

(Re-export of the general-`p` `rrelFusion_zero_bound` at `p = 2`; LHS = 0 by the
vacuum normalization.) -/
theorem rrelFusion2_zero_bound (N : Nat) {w : Q'} (hw : (0 : Q') < w)
    (hw1 : w ≤ (1 : Q')) (hw' : (0 : Q') < renormW 2 w) :
    absQ (rrelFusion N w 2 hw hw' 0)
      ≤ (((1 : Q') - w) * ((1 : Q') - w)) * Peval residualP (yArg w 0) :=
  rrelFusion_zero_bound N 2 hw hw1 hw'

/-! ## 5. PF₂ ratio-monotonicity GUARDRAIL

The log-concavity `coeffW_logConcave` is exactly the statement that the consecutive
ratio `coeffW(s+1)/coeffW(s)` is non-increasing (a Pólya-frequency-2 / unimodality
guardrail): in cross-multiplied form, the ratio at the higher index is `≤` the ratio
at the lower index.  This prevents dips between certified modes in the active
window. -/

/-- **PF₂ ratio-monotonicity (cross-multiplied form).**  On `0 ≤ w ≤ 1`, for every
`s`,

    coeffW w (s + 2) · coeffW w s  ≤  coeffW w (s + 1) · coeffW w (s + 1),

i.e. `coeffW(s+2)/coeffW(s+1) ≤ coeffW(s+1)/coeffW(s)` (the consecutive ratio is
non-increasing).  PROOF: `coeffW_logConcave` commuted on the left factor.  This is
the guardrail that the certified-mode ratios cannot dip back up between modes. -/
theorem coeffW_ratio_mono {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (s : Nat) :
    coeffW w (s + 2) * coeffW w s ≤ coeffW w (s + 1) * coeffW w (s + 1) := by
  have h := coeffW_logConcave hw0 hw1 s
  -- coeffW w s · coeffW w (s+2) ≤ coeffW w (s+1)² ; commute LHS.
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) h
  exact Q'.mul_comm_eqv (coeffW w (s + 2)) (coeffW w s)

/-! ## 6. NAMED OPEN — the active-window quotient certificate (exact `hbound` shape)

The genuine crossover frontier: the per-mode quotient bound on the ACTIVE modes
`1 ≤ s`.  We name it as a `Type`-level certificate whose field is VERBATIM the
per-mode bound the upstream genuine-residual interface consumes
(`absQ (rrel s) ≤ (1−w)²·Peval P (yArg w s)`), so a witness composes directly.  It
is NOT inhabited: collapsing the proved quadratic numerator defect
(`residualModeDefect_quadratic`) through the division by `g 0 · ĉ s` — using the
anchor `g 0 ≳ τ^{−3/2}` to beat the numerator τ-growth uniformly in `s` — is the
open content.  We do NOT fake it and we do NOT use a C₄² envelope. -/

/-- **The named active-window quotient certificate (`p = 2`).**  Carries the fixed
`w`-independent nonneg-coefficient polynomial `P` and — as a `Type`-level field — the
per-mode quotient bound on the active modes `1 ≤ s`, in the EXACT shape the upstream
genuine-residual interface consumes:

    absQ (rrelFusion N w 2 hw hw' s)  ≤  ((1−w)·(1−w))·Peval P (yArg w s),   1 ≤ s.

This is the genuine open crossover: the quotient bound that collapses the quadratic
numerator defect through the denominator anchor on the active modes.  NO inhabitant
is provided.  (The `s = 0` case is proved unconditionally by `rrelFusion2_zero_bound`;
this certificate covers precisely the remaining `s ≥ 1` window.) -/
structure QuotientActiveWindowCert (N : Nat) (w : Q') (hw : (0 : Q') < w)
    (hw' : (0 : Q') < renormW 2 w) : Type where
  /-- The fixed `w`-independent residual polynomial. -/
  P : BondMovingMoment.Poly
  /-- Its coefficients are nonnegative. -/
  P_nonneg : nonnegCoeffs P
  /-- **The OPEN content:** the per-mode quotient bound on the active modes `1 ≤ s`,
  verbatim the genuine-residual `hbound` shape. -/
  quot_bound : ∀ s, 1 ≤ s →
    absQ (rrelFusion N w 2 hw hw' s)
      ≤ (((1 : Q') - w) * ((1 : Q') - w)) * Peval P (yArg w s)

/-- **Honest non-inhabitation marker.**  `QuotientActiveWindowCert` is the genuine
open crossover and is deliberately left UN-inhabited.  This lemma records only the
trivial structural fact that IF a witness exists THEN its polynomial has nonnegative
coefficients — it does NOT construct one. -/
theorem quotientActiveWindowCert_P_nonneg {N : Nat} {w : Q'} {hw : (0 : Q') < w}
    {hw' : (0 : Q') < renormW 2 w} (cert : QuotientActiveWindowCert N w hw hw') :
    nonnegCoeffs cert.P :=
  cert.P_nonneg

/-! ## 7. Doc-section — what is PROVED vs. NAMED-open (CRITICAL honesty)

  * DENOMINATOR ANCHOR, equality (proved).  `fusion_zeroCoeff_eq_Zsum_sq`:
    `bondMovedCoeff N w 2 0 ≃ Zsum (w*w) (N+1)` — the fused vacuum coefficient of the
    `n = 2` self-fusion model is EXACTLY the `w²`-partition (the `s = 0` channel
    forces the diagonal `a = b`, and each square `(coeffW w a)²` is the `Zsum(w²)`
    summand).

  * DENOMINATOR ANCHOR, cube / τ-scaling (proved).  `fusion_zeroCoeff_Lp_lower`:
    `ofNat(S³) ≤ ofNat 6 · bondMovedCoeff N w 2 0` under the `w²`-head floors, i.e.
    `g 0 ≥ (1/6)·S³`.  At the moving cutoff `S = S₀(w²) ≍ τ^{−1/2}` this is the
    denominator anchor `g 0 ≳ τ^{−3/2}` (the `−3(p−1)/2 = −3/2` power at `p = 2`).

  * `s = 0` QUOTIENT BOUND (proved exact).  `rrelFusion2_zero_bound`: the target
    bound holds at the vacuum mode at `p = 2` (LHS = 0).

  * PF₂ RATIO-MONOTONICITY GUARDRAIL (proved).  `coeffW_ratio_mono`: the consecutive
    ratio `coeffW(s+1)/coeffW(s)` is non-increasing (from `coeffW_logConcave`), the
    structural guardrail against dips between certified modes.

  * ACTIVE-WINDOW QUOTIENT (named open).  `QuotientActiveWindowCert` names the
    per-mode quotient bound on `s ≥ 1`, VERBATIM in the genuine-residual `hbound`
    shape `absQ (rrelFusion … s) ≤ (1−w)²·Peval P (yArg w s)`.  It is NOT inhabited.

HONEST VERDICT and SCOPE.  This proves the DENOMINATOR ANCHOR for the `n = 2`
self-fusion model: `g 0 = Zsum(w²)` exactly, and `g 0 ≥ (1/6)·S³` (the `τ^{−3/2}`
lower bound) under the `w²`-head floors; the `s = 0` quotient bound exactly; and the
PF₂ ratio-monotonicity guardrail.  It does NOT prove the per-mode quotient bound on
the active modes `s ≥ 1` — that genuine crossover is named in the exact `hbound`
shape and left open, NOT faked, NOT a C₄² envelope.  This is NOT a 4D Yang–Mills mass
gap; it is the denominator anchor plus a partial quotient for one self-fusion
model. -/

end YMGap.Continuum.FusionQuotientCollapse

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionQuotientCollapse.qpow_mul_self
#print axioms YMGap.Continuum.FusionQuotientCollapse.coeffW_sq_eqv
#print axioms YMGap.Continuum.FusionQuotientCollapse.fsum_zero_below
#print axioms YMGap.Continuum.FusionQuotientCollapse.fsum_collapse
#print axioms YMGap.Continuum.FusionQuotientCollapse.fusionOK_eq_true_iff
#print axioms YMGap.Continuum.FusionQuotientCollapse.fusionOK_eq_false_iff
#print axioms YMGap.Continuum.FusionQuotientCollapse.fusionOK_zero_left_ne
#print axioms YMGap.Continuum.FusionQuotientCollapse.fusionOK_zero_left_self
#print axioms YMGap.Continuum.FusionQuotientCollapse.fusionOK_zero_diag_ne
#print axioms YMGap.Continuum.FusionQuotientCollapse.fusionOK_zero_diag_self
#print axioms YMGap.Continuum.FusionQuotientCollapse.fusionInd_zero_left_ne
#print axioms YMGap.Continuum.FusionQuotientCollapse.fusionInd_zero_left_self
#print axioms YMGap.Continuum.FusionQuotientCollapse.fusionPow_one_eq
#print axioms YMGap.Continuum.FusionQuotientCollapse.fusionInd_zero_diag_ne
#print axioms YMGap.Continuum.FusionQuotientCollapse.fusionInd_zero_diag_self
#print axioms YMGap.Continuum.FusionQuotientCollapse.fusionProduct_zero_diag
#print axioms YMGap.Continuum.FusionQuotientCollapse.fusion_zeroCoeff_eq_Zsum_sq
#print axioms YMGap.Continuum.FusionQuotientCollapse.fusion_zeroCoeff_Lp_lower
#print axioms YMGap.Continuum.FusionQuotientCollapse.rrelFusion2_zero_bound
#print axioms YMGap.Continuum.FusionQuotientCollapse.coeffW_ratio_mono
#print axioms YMGap.Continuum.FusionQuotientCollapse.quotientActiveWindowCert_P_nonneg
