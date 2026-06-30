/-
Track B / R2 — the HEAT-KERNEL GENERATING-FUNCTION route to `s = 1`-DOMINANCE: a
STRUCTURAL, `N`-uniform and `p`-uniform reduction of bond-moved first-excited
dominance to ONE log-concavity ("peak shape") property of the fusion tower, plus
the heat-kernel POSITIVITY FINGERPRINT that a generic sequence lacks.

# Why this module exists — the structural complement to per-`N` computation

The bond-moved transfer spectrum is the `p`-fold SU(2) Clebsch–Gordan FUSION power
of the heat-kernel weight `coeffW w s = (s+1)·w^{C₄(s)}` — equivalently, the
character coefficients of the positive class function `K_w(θ)^p`, where
`K_w(θ) = Σ_s coeffW(s)·χ_s(θ)` is the SU(2) heat kernel.  The mass gap survives
bond-moving iff that spectrum is `s = 1`-DOMINANT: the largest EXCITED coefficient
sits at the first-excited level `s = 1`.  `S1Dominance` (proved at `p = 1`) names
this; the genuine `p ≥ 2` content is the excited-channel upper bound.

This module attacks it STRUCTURALLY, exploiting the one thing the heat kernel has
that a generic positive sequence does NOT: the normalized coefficients
`w^{C₄(s)}` are LOG-CONCAVE in `s`, because the Casimir `C₄(s) = s(s+2)` has
CONSTANT second difference `2`:

    C₄(s+2) + C₄(s)  =  2·C₄(s+1) + 2,           (the heat-kernel fingerprint)

so `heatNorm(s)·heatNorm(s+2) = w²·heatNorm(s+1)²  ≤  heatNorm(s+1)²` on `[0,1]`
(the log-concavity defect is EXACTLY the factor `w²`).  Tensored with the
log-concave dimension factor `(s+1)`, the full heat-kernel weight `coeffW` is
log-concave.  And the GENERAL structural fact — proved here once and for all — is
that ANY positive log-concave sequence whose first ratio is `≤ 1` (`g(2) ≤ g(1)`)
is non-increasing from `s = 1`, hence `s = 1`-dominant.  This reduces the WHOLE
excited-channel family `{g(s) ≤ g(1) : s ≥ 2}` to ONE shape property
(log-concavity) plus ONE boundary comparison (`g(2) ≤ g(1)`).

# What is GENUINELY PROVED here (axiom-clean `Q'`/`Nat` arithmetic)

THE GENERAL PEAK LEMMA (proved, sequence-agnostic):
  * `nonincr_of_logConcave` / `peak_of_logConcave` — for ANY `g : Nat → Q'` that is
    nonnegative, strictly positive and log-concave on `[1,M]` with `g(2) ≤ g(1)`
    (the base needed only when `2 ≤ M`), `g` is non-increasing on `[1,M]` and
    `g(s) ≤ g(1)` for `1 ≤ s ≤ M`.  Pure positive-factor cancellation; NO
    heat-kernel input.  The clean "largest excited coefficient of a unimodal peak
    is at the edge" lemma.

THE HEAT-KERNEL FINGERPRINT (proved):
  * `c4_second_diff` — `C₄(s+2) + C₄(s) = 2·C₄(s+1) + 2` (constant second difference).
  * `heatNorm_logConcave_exact` — the EXACT identity
    `heatNorm(s)·heatNorm(s+2) ≃ qpow w 2 · heatNorm(s+1)²` (defect = `w²`).
  * `heatNorm_logConcave` — its `≤` consequence on `[0,1]`.
  * `dimQ_logConcave` — the dimension factor `(s+1)` is log-concave.
  * `coeffW_logConcave` — the heat-kernel weight `coeffW = dimQ · heatNorm` is
    log-concave (product of two log-concave nonneg sequences).
  * `heatNorm_decimate` — the convolution closed form: decimation `w ↦ w^b` acts
    as a POINTWISE POWER on the normalized coefficients,
    `heatNorm (w^b) s ≃ (heatNorm w s)^b` (the heat-semigroup duality).

THE REDUCTION (proved, the deliverable):
  * `FusionLogConcave N w p` — the named structural property: bond-moved fusion
    log-concavity on `[1,N]` plus the (conditional) base `bmc(2) ≤ bmc(1)`.
  * `s1Dominance_of_fusionLogConcave` — **the structural reduction**: a
    `FusionLogConcave N w p` witness yields `S1Dominance N w p` (general `N`, `p`),
    via the general peak lemma (excited positivity is free from `bmc ≥ coeffW`).
  * `fusionLogConcave_p1` — INHABITS `FusionLogConcave N w 1` on the character
    window `[0, wHi]`, reproving `p = 1` dominance through the log-concave route.
  * `fusionLogConcave_p2_of_core` / `s1Dominance_N1_p2_strong` — connects to
    `SelfFusionLogConcave`: a `FusionConvLogConcaveCore` (box log-concavity) IS the
    `logConcave` field, unifying the two named-open structures; inhabited (trivially
    on the single-excited-mode range) at `N = 1` strong coupling.

# Honest verdict and scope

The general peak lemma and the heat-kernel log-concavity fingerprint are GENUINELY
PROVED, and they REDUCE the named-open excited-channel family of `S1Dominance`
(general `N`, `p`) to ONE shape property — log-concavity of the `p`-fold fusion —
plus a single boundary comparison.  This is sharper and more uniform than per-`N`
enumeration: one `N`-uniform, `p`-uniform structural implication.  The RESIDUAL is
exactly the log-concavity of the GENERAL `p`-fold SU(2) fusion (`FusionLogConcave`
field), which — as `SelfFusionLogConcave` establishes — is NOT a generic
convolution fact but the heat-kernel-specific `(r,d)` Gaussian-theta local-CLT,
NOT a finite rational inequality available in `Q'`.  It is inhabited at `p = 1`
(any `N`, window) with genuine content, and connected to the proved box core at
`p = 2`.  This is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, decidable `Q'`/`Nat` facts, the
reused `qpow`/`coeffW`/fusion lemmas and the positive-factor cancellation
`Q'.le_of_mul_le_mul_left`.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide` (only `decide` on decidable facts), no `sorry`.
All witnesses are `Type`-level data.
-/

import YMGap.Continuum.BondMovingStep
import YMGap.Continuum.SelfFusionLogConcave
import YMGap.Continuum.BondMovingScaledNorm
import YMGap.Continuum.HeatKernelRGStep
import YMGap.Continuum.S1Dominance

namespace YMGap.Continuum.FusionGenFunction

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.CharacterWindowCeiling
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.S1Dominance
open YMGap.Continuum.FusionQuotientCollapse

/-! ## 0. The general peak lemma — sequence-agnostic, NO heat-kernel input -/

/-- **The non-increase from log-concavity + base.**  For `g : Nat → Q'`
nonnegative, strictly positive on `[1,M]`, log-concave on `[1,M]`
(`g(s)·g(s+2) ≤ g(s+1)²`) and with `g(2) ≤ g(1)` whenever `2 ≤ M`: `g(s+1) ≤ g(s)`
for every `1 ≤ s` with `s + 1 ≤ M`.  Induction on `s`; the step cancels the
strictly positive `g(s+1)` from `g(s+1)·g(s+2) ≤ g(s+1)·g(s+1)`. -/
theorem nonincr_of_logConcave (g : Nat → Q') (M : Nat)
    (hnn : ∀ s, (0 : Q') ≤ g s)
    (hpos : ∀ s, 1 ≤ s → s ≤ M → (0 : Q') < g s)
    (hlc : ∀ s, 1 ≤ s → s + 2 ≤ M → g s * g (s + 2) ≤ g (s + 1) * g (s + 1))
    (hbase : 2 ≤ M → g 2 ≤ g 1) :
    ∀ s, 1 ≤ s → s + 1 ≤ M → g (s + 1) ≤ g s := by
  intro s
  induction s with
  | zero => intro h; exact absurd h (by decide)
  | succ k ih =>
      intro _ hM
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0; exact hbase (by omega)
      · have hk1 : 1 ≤ k := hkpos
        have hkM : k + 1 ≤ M := by omega
        have hprev : g (k + 1) ≤ g k := ih hk1 hkM
        have hlck : g k * g (k + 2) ≤ g (k + 1) * g (k + 1) := hlc k hk1 (by omega)
        have h1 : g (k + 1) * g (k + 2) ≤ g k * g (k + 2) :=
          Q'.mul_le_mul_of_nonneg_right _ _ _ hprev (hnn (k + 2))
        have h2 : g (k + 1) * g (k + 2) ≤ g (k + 1) * g (k + 1) :=
          Q'.le_trans' _ _ _ h1 hlck
        have hposk1 : (0 : Q') < g (k + 1) := hpos (k + 1) (by omega) (by omega)
        exact Q'.le_of_mul_le_mul_left h2 hposk1

/-- **The peak lemma.**  Under the same hypotheses, `g(s) ≤ g(1)` for every
`1 ≤ s ≤ M`: a log-concave peak with non-positive first log-slope is maximized at
the first-excited edge `s = 1`. -/
theorem peak_of_logConcave (g : Nat → Q') (M : Nat)
    (hnn : ∀ s, (0 : Q') ≤ g s)
    (hpos : ∀ s, 1 ≤ s → s ≤ M → (0 : Q') < g s)
    (hlc : ∀ s, 1 ≤ s → s + 2 ≤ M → g s * g (s + 2) ≤ g (s + 1) * g (s + 1))
    (hbase : 2 ≤ M → g 2 ≤ g 1) :
    ∀ s, 1 ≤ s → s ≤ M → g s ≤ g 1 := by
  have hdown := nonincr_of_logConcave g M hnn hpos hlc hbase
  intro s
  induction s with
  | zero => intro h; exact absurd h (by decide)
  | succ k ih =>
      intro _ hM
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0; exact Q'.le_refl' (g 1)
      · have hk1 : 1 ≤ k := hkpos
        have hstep : g (k + 1) ≤ g k := hdown k hk1 (by omega)
        have hkle : g k ≤ g 1 := ih hk1 (by omega)
        exact Q'.le_trans' _ _ _ hstep hkle

/-! ## 1. The heat-kernel fingerprint — log-concavity of `w^{C₄(s)}` -/

/-- The normalized heat-kernel character coefficient `heatNorm(w,s) = w^{C₄(s)}`
(`coeffW w s = dimQ s · heatNorm w s`). -/
def heatNorm (w : Q') (s : Nat) : Q' := qpow w (c4 s)

/-- `coeffW w s = dimQ s · heatNorm w s` (definitional unfold). -/
theorem coeffW_eq_dim_heatNorm (w : Q') (s : Nat) :
    coeffW w s = dimQ s * heatNorm w s := rfl

/-- **The heat-kernel fingerprint:** `C₄` has constant second difference `2`:
`C₄(s+2) + C₄(s) = 2·C₄(s+1) + 2`. -/
theorem c4_second_diff (s : Nat) : c4 (s + 2) + c4 s = 2 * c4 (s + 1) + 2 := by
  have h1 : c4 (s + 1) = c4 s + (2 * s + 3) := BondMovingScaledNorm.c4_succ s
  have h2 : c4 (s + 2) = c4 (s + 1) + (2 * (s + 1) + 3) := BondMovingScaledNorm.c4_succ (s + 1)
  omega

/-- **The EXACT log-concavity identity** `heatNorm(s)·heatNorm(s+2) ≃ w²·heatNorm(s+1)²`:
the log-concavity defect of the normalized heat kernel is EXACTLY the factor `w²`. -/
theorem heatNorm_logConcave_exact (w : Q') (s : Nat) :
    (heatNorm w s * heatNorm w (s + 2)).eqv
      (qpow w 2 * (heatNorm w (s + 1) * heatNorm w (s + 1))) := by
  have hkey : c4 s + c4 (s + 2) = 2 * c4 (s + 1) + 2 := by
    have := c4_second_diff s; omega
  have hL : (heatNorm w s * heatNorm w (s + 2)).eqv (qpow w (2 * c4 (s + 1) + 2)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (qpow_add w (c4 s) (c4 (s + 2)))) ?_
    rw [hkey]; exact Q'.eqv_refl _
  have hsplit : (qpow w (2 * c4 (s + 1) + 2)).eqv
      (qpow w 2 * qpow w (2 * c4 (s + 1))) := by
    refine Q'.eqv_trans _ _ _ (qpow_add w (2 * c4 (s + 1)) 2) ?_
    exact Q'.mul_comm_eqv (qpow w (2 * c4 (s + 1))) (qpow w 2)
  have hsq : (qpow w (2 * c4 (s + 1))).eqv (heatNorm w (s + 1) * heatNorm w (s + 1)) := by
    have h2 : 2 * c4 (s + 1) = c4 (s + 1) + c4 (s + 1) := by omega
    rw [h2]; exact qpow_add w (c4 (s + 1)) (c4 (s + 1))
  refine Q'.eqv_trans _ _ _ hL ?_
  refine Q'.eqv_trans _ _ _ hsplit ?_
  exact Q'.mul_eqv_congr_left (qpow w 2) _ _ hsq

/-- **`heatNorm` is log-concave on `[0,1]`**:
`heatNorm(s)·heatNorm(s+2) ≤ heatNorm(s+1)²`, since the exact defect `w² ≤ 1`. -/
theorem heatNorm_logConcave {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (s : Nat) :
    heatNorm w s * heatNorm w (s + 2) ≤ heatNorm w (s + 1) * heatNorm w (s + 1) := by
  have hexact := heatNorm_logConcave_exact w s
  have hw2 : qpow w 2 ≤ (1 : Q') := qpow_le_one hw0 hw1 2
  have hsqnn : (0 : Q') ≤ heatNorm w (s + 1) * heatNorm w (s + 1) :=
    Q'.mul_nonneg _ _ (qpow_nonneg w hw0 _) (qpow_nonneg w hw0 _)
  have hstep : qpow w 2 * (heatNorm w (s + 1) * heatNorm w (s + 1))
      ≤ (1 : Q') * (heatNorm w (s + 1) * heatNorm w (s + 1)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hw2 hsqnn
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hexact) ?_
  refine Q'.le_trans' _ _ _ hstep ?_
  exact Q'.le_of_eqv (Q'.one_mul_eqv _)

/-- **The dimension factor is log-concave**: `dimQ s · dimQ (s+2) ≤ dimQ(s+1)²`
(`(s+1)(s+3) ≤ (s+2)²`, slack `1`). -/
theorem dimQ_logConcave (s : Nat) :
    dimQ s * dimQ (s + 2) ≤ dimQ (s + 1) * dimQ (s + 1) := by
  have hnat : (s + 1) * (s + 3) ≤ (s + 2) * (s + 2) := by
    have a : (s + 2) * (s + 2) = s * s + (4 * s + 4) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
    have b : (s + 1) * (s + 3) = s * s + (4 * s + 3) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.one_mul]; omega
    omega
  have hL : (dimQ s * dimQ (s + 2)).eqv (Q'.ofNat ((s + 1) * (s + 3))) := by
    show (Q'.ofNat (s + 1) * Q'.ofNat (s + 3)).eqv (Q'.ofNat ((s + 1) * (s + 3)))
    exact Q'.eqv_symm (ofNat_mul_eqv (s + 1) (s + 3))
  have hR : (Q'.ofNat ((s + 2) * (s + 2))).eqv (dimQ (s + 1) * dimQ (s + 1)) := by
    show (Q'.ofNat ((s + 2) * (s + 2))).eqv (Q'.ofNat (s + 2) * Q'.ofNat (s + 2))
    exact ofNat_mul_eqv (s + 2) (s + 2)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) ?_
  exact Q'.le_trans' _ _ _ (CReal.ofNat_le_ofNat hnat) (Q'.le_of_eqv hR)

/-- A four-factor regroup `(A·B)·(C·D) ≃ (A·C)·(B·D)`. -/
theorem mul_swap4 (A B C D : Q') : ((A * B) * (C * D)).eqv ((A * C) * (B * D)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A B (C * D)) ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.mul_assoc_eqv A C (B * D)))
  refine Q'.mul_eqv_congr_left A _ _ ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv B C D)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ D (Q'.mul_comm_eqv B C)) ?_
  exact Q'.mul_assoc_eqv C B D

/-- **The heat-kernel weight `coeffW` is log-concave** on `[0,1]`:
`coeffW(s)·coeffW(s+2) ≤ coeffW(s+1)²`.  Product of the two log-concave nonnegative
factors `dimQ` and `heatNorm`, via the four-factor regroup. -/
theorem coeffW_logConcave {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (s : Nat) :
    coeffW w s * coeffW w (s + 2) ≤ coeffW w (s + 1) * coeffW w (s + 1) := by
  show (dimQ s * heatNorm w s) * (dimQ (s + 2) * heatNorm w (s + 2))
      ≤ (dimQ (s + 1) * heatNorm w (s + 1)) * (dimQ (s + 1) * heatNorm w (s + 1))
  have hLre : ((dimQ s * heatNorm w s) * (dimQ (s + 2) * heatNorm w (s + 2))).eqv
      ((dimQ s * dimQ (s + 2)) * (heatNorm w s * heatNorm w (s + 2))) :=
    mul_swap4 (dimQ s) (heatNorm w s) (dimQ (s + 2)) (heatNorm w (s + 2))
  have hRre : ((dimQ (s + 1) * dimQ (s + 1)) * (heatNorm w (s + 1) * heatNorm w (s + 1))).eqv
      ((dimQ (s + 1) * heatNorm w (s + 1)) * (dimQ (s + 1) * heatNorm w (s + 1))) :=
    mul_swap4 (dimQ (s + 1)) (dimQ (s + 1)) (heatNorm w (s + 1)) (heatNorm w (s + 1))
  have hd := dimQ_logConcave s
  have hh := heatNorm_logConcave hw0 hw1 s
  have hhnn : (0 : Q') ≤ heatNorm w s * heatNorm w (s + 2) :=
    Q'.mul_nonneg _ _ (qpow_nonneg w hw0 _) (qpow_nonneg w hw0 _)
  have hd1nn : (0 : Q') ≤ dimQ (s + 1) * dimQ (s + 1) :=
    Q'.mul_nonneg _ _ (dimQ_nonneg _) (dimQ_nonneg _)
  have step1 : (dimQ s * dimQ (s + 2)) * (heatNorm w s * heatNorm w (s + 2))
      ≤ (dimQ (s + 1) * dimQ (s + 1)) * (heatNorm w s * heatNorm w (s + 2)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hd hhnn
  have step2 : (dimQ (s + 1) * dimQ (s + 1)) * (heatNorm w s * heatNorm w (s + 2))
      ≤ (dimQ (s + 1) * dimQ (s + 1)) * (heatNorm w (s + 1) * heatNorm w (s + 1)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hh hd1nn
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLre) ?_
  refine Q'.le_trans' _ _ _ step1 ?_
  exact Q'.le_trans' _ _ _ step2 (Q'.le_of_eqv hRre)

/-! ## 2. The convolution closed form — decimation as a pointwise power -/

/-- **The decimation duality:** `heatNorm (mkDecimate b w) s ≃ (heatNorm w s)^b`
(series decimation `w ↦ w^b` acts as a POINTWISE POWER on the normalized
coefficients — the dual of bond-moving's pointwise-product/fusion). -/
theorem heatNorm_decimate (b : Nat) (w : Q') (s : Nat) :
    (heatNorm (mkDecimate b w) s).eqv (qpow (heatNorm w s) b) := by
  show (qpow (qpow w b) (c4 s)).eqv (qpow (qpow w (c4 s)) b)
  refine Q'.eqv_trans _ _ _ (qpow_qpow w b (c4 s)) ?_
  rw [Nat.mul_comm b (c4 s)]
  exact Q'.eqv_symm (qpow_qpow w (c4 s) b)

/-! ## 3. The structural reduction `FusionLogConcave ⟹ S1Dominance` -/

/-- **The named structural property.**  The bond-moved fusion tower is log-concave
on the excited range `[1,N]` and its first ratio is `≤ 1` (`bmc(2) ≤ bmc(1)`,
needed only when `2 ≤ N`).  Equivalently: the `p`-fold SU(2)-fusion power of the
heat kernel has a unimodal peak whose excited edge is `s = 1`.  The log-concavity
field is the heat-kernel-specific content (`SelfFusionLogConcave`); the base is one
boundary comparison. -/
structure FusionLogConcave (N : Nat) (w : Q') (p : Nat) : Type where
  /-- Log-concavity of the bond-moved coefficients on `[1,N]`. -/
  logConcave : ∀ s, 1 ≤ s → s + 2 ≤ N →
    bondMovedCoeff N w p s * bondMovedCoeff N w p (s + 2)
      ≤ bondMovedCoeff N w p (s + 1) * bondMovedCoeff N w p (s + 1)
  /-- The base comparison `bmc(2) ≤ bmc(1)` (needed only when the range reaches `2`). -/
  base : 2 ≤ N → bondMovedCoeff N w p 2 ≤ bondMovedCoeff N w p 1

/-- **THE STRUCTURAL REDUCTION.**  A `FusionLogConcave N w p` witness yields the
`s = 1`-dominance datum `S1Dominance N w p` — for GENERAL `N` and `p` — by the
general peak lemma.  Excited positivity is supplied free by the identity fusion
channel (`bmc_ge_identity`, `coeffW_pos`); nonnegativity by `bondMovedCoeff_nonneg`.
This reduces the whole excited-channel UPPER-bound family to ONE shape property
(`logConcave`) plus ONE boundary comparison (`base`). -/
def s1Dominance_of_fusionLogConcave (N : Nat) {w : Q'} {p : Nat}
    (hw : (0 : Q') < w) (hw1 : w ≤ (1 : Q')) (hp : 0 < p)
    (flc : FusionLogConcave N w p) : S1Dominance N w p where
  dominates := by
    have hnn : ∀ s, (0 : Q') ≤ bondMovedCoeff N w p s :=
      fun s => bondMovedCoeff_nonneg N (Q'.le_of_lt hw) p s
    have hpos : ∀ s, 1 ≤ s → s ≤ N → (0 : Q') < bondMovedCoeff N w p s :=
      fun s _ hsN =>
        q_lt_of_lt_of_le (coeffW_pos hw s)
          (bmc_ge_identity N (Q'.le_of_lt hw) hw1 s hsN p hp)
    exact peak_of_logConcave (bondMovedCoeff N w p) N hnn hpos flc.logConcave flc.base

/-! ## 4. Inhabitation at `p = 1` (any `N`, the character window) -/

/-- **`FusionLogConcave N w 1` on the character window** `[0, wHi = 7/9]`.  The
bond-moved coefficients are `≃ coeffW` (unit fusion identity `fusionPow_one_eq`),
so log-concavity transports from `coeffW_logConcave` and the base from the window
non-increase `coeffW_succ_le_self_ext` (both indices `≤ N` under the `2 ≤ N` guard). -/
def fusionLogConcave_p1 (N : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ wHi) :
    FusionLogConcave N w 1 where
  logConcave := by
    intro s _ hsN
    have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hw (by decide)
    have e0 : (bondMovedCoeff N w 1 s).eqv (coeffW w s) := fusionPow_one_eq (by omega)
    have e1 : (bondMovedCoeff N w 1 (s + 1)).eqv (coeffW w (s + 1)) := fusionPow_one_eq (by omega)
    have e2 : (bondMovedCoeff N w 1 (s + 2)).eqv (coeffW w (s + 2)) := fusionPow_one_eq hsN
    have hL : (bondMovedCoeff N w 1 s * bondMovedCoeff N w 1 (s + 2)).eqv
        (coeffW w s * coeffW w (s + 2)) :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ e0) (Q'.mul_eqv_congr_left _ _ _ e2)
    have hR : (coeffW w (s + 1) * coeffW w (s + 1)).eqv
        (bondMovedCoeff N w 1 (s + 1) * bondMovedCoeff N w 1 (s + 1)) :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm e1))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm e1))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) ?_
    exact Q'.le_trans' _ _ _ (coeffW_logConcave hw0 hw1 s) (Q'.le_of_eqv hR)
  base := by
    intro hN
    -- 2 ≤ N: transport both indices to coeffW, use the window non-increase at s = 1.
    have e2 : (bondMovedCoeff N w 1 2).eqv (coeffW w 2) := fusionPow_one_eq hN
    have e1 : (bondMovedCoeff N w 1 1).eqv (coeffW w 1) := fusionPow_one_eq (by omega)
    have hcore : coeffW w (1 + 1) ≤ coeffW w 1 := coeffW_succ_le_self_ext hw0 hw 1 (by decide)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv e2) ?_
    exact Q'.le_trans' _ _ _ hcore (Q'.ge_of_eqv e1)

/-- **`s1Dominance` at `p = 1` via the log-concave route** — a STRUCTURAL reproof of
the heat-kernel `s = 1`-dominance on the character window, built from the general
peak lemma applied to the log-concave `coeffW`. -/
def s1Dominance_p1_logConcave (N : Nat) {w : Q'} (hw : (0 : Q') < w) (hwHi : w ≤ wHi) :
    S1Dominance N w 1 :=
  s1Dominance_of_fusionLogConcave N hw (Q'.le_trans' _ _ _ hwHi (by decide)) (by decide)
    (fusionLogConcave_p1 N (Q'.le_of_lt hw) hwHi)

/-! ## 5. The `p = 2` connection to the proved box log-concavity core -/

/-- **`FusionConvLogConcaveCore` IS the `logConcave` field at `p = 2`.**  Given a
box-log-concavity core (`SelfFusionLogConcave`) and the base comparison, the
`p = 2` fusion tower is `FusionLogConcave`: `bondMovedCoeff_logConcave_of_core`
transports the box cross-difference to the exact `logConcave` shape.  This UNIFIES
the two named-open structures — the box core is precisely the log-concavity input
the structural reduction needs. -/
def fusionLogConcave_p2_of_core {N : Nat} {w : Q'}
    {hw0 : (0 : Q') ≤ w} {hw1 : w ≤ (1 : Q')}
    (core : FusionConvLogConcaveCore N w hw0 hw1)
    (hbase : 2 ≤ N → bondMovedCoeff N w 2 2 ≤ bondMovedCoeff N w 2 1) :
    FusionLogConcave N w 2 where
  logConcave := fun s _ _ => bondMovedCoeff_logConcave_of_core core s
  base := hbase

/-- **`S1Dominance N w 2` from the box core** (general `N`), via the structural
reduction.  The box core supplies log-concavity; the caller supplies the base. -/
def s1Dominance_p2_of_core {N : Nat} {w : Q'}
    (hw : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (core : FusionConvLogConcaveCore N w (Q'.le_of_lt hw) hw1)
    (hbase : 2 ≤ N → bondMovedCoeff N w 2 2 ≤ bondMovedCoeff N w 2 1) :
    S1Dominance N w 2 :=
  s1Dominance_of_fusionLogConcave N hw hw1 (by decide)
    (fusionLogConcave_p2_of_core core hbase)

/-- **Strong-coupling `S1Dominance 1 w 2`.**  At `N = 1`, `0 < w ≤ 1/2`, the box
core is inhabited (`fusionConvLogConcaveCore_N1`, strong coupling discharged by
`coeffW1_sq_le_three_of_strong`) and the base is vacuous (`2 ≤ 1` is false), so the
`p = 2` `s = 1`-dominance datum is INHABITED — the structural reduction fires
end-to-end at `p = 2`.  (At `N = 1` the excited range is the single mode `s = 1`,
so dominance there is the boundary case; the genuine general-`N` content remains the
box core.) -/
def s1Dominance_N1_p2_strong {w : Q'} (hw : (0 : Q') < w)
    (hw12 : w ≤ Q'.mkPos 1 2 (by decide)) : S1Dominance 1 w 2 := by
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hw12 (by decide)
  have hb : coeffW w 1 * coeffW w 1 ≤ (3 : Q') :=
    coeffW1_sq_le_three_of_strong (Q'.le_of_lt hw) hw12
  exact s1Dominance_p2_of_core hw hw1
    (fusionConvLogConcaveCore_N1 hw hw1 hb)
    (fun hN => absurd hN (by decide))

/-! ## 6. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, pure `Q'`/`Nat`):
  * `nonincr_of_logConcave` / `peak_of_logConcave` — the general, sequence-agnostic
    peak lemma: a positive log-concave sequence with non-positive first log-slope is
    non-increasing, hence maximized at the first-excited edge.  NO heat-kernel input.
  * `c4_second_diff` — the heat-kernel fingerprint (`C₄` has constant second
    difference `2`).
  * `heatNorm_logConcave_exact` / `heatNorm_logConcave` — the normalized heat-kernel
    coefficients are log-concave with EXACT defect factor `w²`.
  * `dimQ_logConcave` / `mul_swap4` / `coeffW_logConcave` — the full heat-kernel
    weight `coeffW = dimQ · heatNorm` is log-concave (product of two log-concave
    nonneg factors).
  * `heatNorm_decimate` — the convolution closed form: decimation acts as a
    pointwise power on the normalized coefficients (heat-semigroup duality).
  * `FusionLogConcave` / `s1Dominance_of_fusionLogConcave` — THE STRUCTURAL
    REDUCTION: general-`N`, general-`p` `s = 1`-dominance follows from ONE
    log-concavity ("peak shape") property plus a single boundary comparison.
  * `fusionLogConcave_p1` / `s1Dominance_p1_logConcave` — INHABITED at `p = 1` on the
    window, reproving heat-kernel dominance through the log-concave route.
  * `fusionLogConcave_p2_of_core` / `s1Dominance_p2_of_core` /
    `s1Dominance_N1_p2_strong` — the box log-concavity core IS the `logConcave`
    field; inhabited end-to-end at `N = 1`, strong coupling, `p = 2`.

NAMED OPEN (NOT inhabited for general `N`, `p ≥ 2`):
  * The `logConcave` field of `FusionLogConcave N w p` for the genuine `p ≥ 2`
    bond-moving — i.e. log-concavity of the `p`-fold SU(2) fusion power of the heat
    kernel.  As `SelfFusionLogConcave` establishes, this is NOT a generic convolution
    fact (SU(2) fusion does not preserve log-concavity for generic inputs, and the
    finite-`N` truncation breaks it for `w → 1`); the genuine general-`N` content is
    the heat-kernel-specific `(r,d)` Gaussian-theta local-CLT — NOT a finite rational
    inequality available in `Q'`.

HONEST VERDICT.  The general peak lemma and the heat-kernel log-concavity fingerprint
are GENUINELY PROVED, and they REDUCE the named-open excited-channel family of
`S1Dominance` (general `N`, `p`) to ONE shape property — log-concavity of the
`p`-fold fusion — plus one boundary comparison.  This is sharper and more uniform
than per-`N` enumeration.  The residual is the genuine heat-kernel local-CLT
log-concavity, named precisely and connected to the proved `p = 2` box core.  This
is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FusionGenFunction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionGenFunction.nonincr_of_logConcave
#print axioms YMGap.Continuum.FusionGenFunction.peak_of_logConcave
#print axioms YMGap.Continuum.FusionGenFunction.c4_second_diff
#print axioms YMGap.Continuum.FusionGenFunction.heatNorm_logConcave_exact
#print axioms YMGap.Continuum.FusionGenFunction.heatNorm_logConcave
#print axioms YMGap.Continuum.FusionGenFunction.dimQ_logConcave
#print axioms YMGap.Continuum.FusionGenFunction.mul_swap4
#print axioms YMGap.Continuum.FusionGenFunction.coeffW_logConcave
#print axioms YMGap.Continuum.FusionGenFunction.heatNorm_decimate
#print axioms YMGap.Continuum.FusionGenFunction.s1Dominance_of_fusionLogConcave
#print axioms YMGap.Continuum.FusionGenFunction.fusionLogConcave_p1
#print axioms YMGap.Continuum.FusionGenFunction.s1Dominance_p1_logConcave
#print axioms YMGap.Continuum.FusionGenFunction.fusionLogConcave_p2_of_core
#print axioms YMGap.Continuum.FusionGenFunction.s1Dominance_p2_of_core
#print axioms YMGap.Continuum.FusionGenFunction.s1Dominance_N1_p2_strong
