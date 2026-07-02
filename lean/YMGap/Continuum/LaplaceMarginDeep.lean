/-
Track A / R2 (track: 1-laplace) — the `ρ = w²` DEEPENING of the discrete-Laplace / effective-
variance reframing of the autoconvolution log-concavity crux `FiniteSMargin`.

# What this module adds over `DiscreteLaplaceMargin` (read first — load-bearing honesty)

`DiscreteLaplaceMargin` proved the GENERIC ρ-graded Hankel rectangle and instantiated the theta
weight at the CRUDE constant `ρ = 1/4` (`quarter`).  The `1/4` is the worst-case value, attained
only at `w = wH = 1/2`; for `w < wH` it is loose.  This module sharpens the instantiation to the
EXACT, `w`-dependent, monotone constant `ρ = w²` and pushes the consequences one convolution level
deeper (the window profile), then makes an explicit, decidable finite-`s` advance on `FiniteSMargin`.

The single enabling fact is that the theta-weight Hankel ratio is EXACT up to the dimension factor:
for all `s` (and ALL `w ≥ 0`, no `w ≤ wH` needed),

    c_s · c_{s+2}          = (s+1)(s+3)/(s+2)² · w² · c_{s+1}²        (`coeffW_hankel_exact`)
    c_s · c_{s+2}          ≤ w² · c_{s+1}²                            (`coeffW_superLogConcave_wsq`)

because `(s+1)(s+3) ≤ (s+2)²` and the two sides carry the SAME power of `w`
(`c4 s + c4(s+2) = 2 + 2·c4(s+1)`).  This drops the `w ≤ wH` hypothesis of the in-tree factor-4
atom and replaces the flat `1/4` by the monotone `w²` (`= 1/4` at `wH`, smaller below).

# What this module proves (all axiom-clean)

PROVED (`[propext]` / `[propext, Quot.sound]` only):
  * `coeffW_mul_split`, `coeffW_mul_ofNat` — the exact regroup
      `c_a·c_b ≃ (dimQ a·dimQ b)·w^{c4 a + c4 b} ≃ ofNat((a+1)(b+1))·w^{c4 a + c4 b}`.
  * `coeffW_hankel_exact` — the EXACT cross-multiplied Hankel identity
      `(s+2)²·(c_s·c_{s+2}) ≃ (s+1)(s+3)·(w²·c_{s+1}²)`.  Pure `qpow`/`dimQ` arithmetic; no
      division, no `w ≤ wH`.
  * `coeffW_superLogConcave_wsq` — the `ρ = w²` super-log-concavity `c_s·c_{s+2} ≤ w²·c_{s+1}²`
      for ALL `0 ≤ w` (sharper than, and hypothesis-free relative to, the in-tree `quarter` atom).
  * `coeffW_rect_graded_wsq` — the `ρ = w²` Hankel rectangle
      `c_i·c_{i+a+b} ≤ (w²)^{ab}·c_{i+a}·c_{i+b}` (instantiating `ratioRect_graded`).
  * `gWin`, `window_superLogConcave` — the peak-normalized window profile `g^{(N)}_p = c_p·c_{N-p}`
      is super-log-concave with `ρ = w⁴`: `g_p·g_{p+2} ≤ w⁴·g_{p+1}²` (product of two `w²` atoms).
  * `finiteSMargin_upTo_wH_5` — the CONCRETE finite-`s` clearance: the `FiniteSMargin` theta-floor
      inequality at the worst case `w = wH` holds for all `s ≤ 5` (per-`s` `decide`).  A genuine
      finite extension of `finiteSMargin_floor_s0` (`s = 0`) to a six-mode window.

REDUCTION (Type-level, honest — separates the two independent contents of `FiniteSMargin`):
  * `WHAllSMargin` — the rational content: the wH theta-floor margin for ALL `s`
      (verified for `s ≤ 5` by `finiteSMargin_upTo_wH_5`; the `s → ∞` tail is the theta wall).
  * `FiniteSMarginWorstcase w` — the analytic content: the `w`-monotonicity reduction collapsing
      the two-parameter `(w,s)` family to the one-parameter wH sequence (the margin ratio is
      increasing in `w`, maximal at `wH`; direction supplied by `ρ_eff = w²` maximal at `wH`).
  * `finiteSMarginOfWorstcase` — THE REDUCTION: `WHAllSMargin` + `FiniteSMarginWorstcase w` yields
      `AcNReserveAnalytic.FiniteSMargin w`.
  * `WindowedGaussianEnvelope w` — the remaining GLOBAL content: the fixed `ρ^{i²}` Gaussian
      envelope of the window profile about its peak (the local-CLT / theta-sum object; a windowed
      induction on `window_superLogConcave`, NOT inhabited here).

# HONESTY — what is NOT closed

`FiniteSMargin w` for ALL `s`/`w` is NOT inhabited.  The `w²`/`w⁴` atoms tame every cross ratio
EXACTLY (not just up to `1/4`), and the concrete finite family `s ≤ 5` at `wH` is discharged, but
the uniform `s → ∞` bound is the genuine local-CLT/theta content — carried here as the honest
Type-level residuals `WHAllSMargin` (rational tail) and `WindowedGaussianEnvelope` (Gaussian
window), cleanly separated from the proved-exact prefactor `coeffW_hankel_exact` and the analytic
`w`-worst-case reduction `FiniteSMarginWorstcase`.  This is a representation/deepening advance on
one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW`/`qpow`/`dimQ`/`acN` definitions, the generic
`ratioRect_graded`, finite `omega`/`simp only [Nat.*]` Nat identities, and `decide` only on closed
concrete-rational facts.  Every load-bearing declaration is gated with `#print axioms`; permitted
output is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.  All
witnesses are `Type`-level data.
-/

import YMGap.Continuum.DiscreteLaplaceMargin

namespace YMGap.Continuum.LaplaceMarginDeep

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.DiscreteLaplaceMargin

/-! ## 0. Small `Q'` rearrangement helpers (pure commutative algebra) -/

/-- Congruence of `·` in both factors. -/
private theorem mul_eqv_congr₂ {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') :
    (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha) (Q'.mul_eqv_congr_left a' b b' hb)

/-- `(X·Y)·Z ≃ Y·(X·Z)` — swap the first two of three factors. -/
private theorem mul3_swap (X Y Z : Q') : ((X * Y) * Z).eqv (Y * (X * Z)) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ Z (Q'.mul_comm_eqv X Y))
    (Q'.mul_assoc_eqv Y X Z)

/-- `X·(Y·Z) ≃ Y·(X·Z)` — swap the outer two of three factors. -/
private theorem mul3_swap' (X Y Z : Q') : (X * (Y * Z)).eqv (Y * (X * Z)) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv X Y Z)) (mul3_swap X Y Z)

/-- **Product of two inequalities of nonnegative quantities.**  `a ≤ b`, `c ≤ d`, `0 ≤ c`,
`0 ≤ b` ⟹ `a·c ≤ b·d`. -/
private theorem mul_le_mul' {a b c d : Q'} (hab : a ≤ b) (hcd : c ≤ d)
    (hc : (0 : Q') ≤ c) (hb : (0 : Q') ≤ b) : a * c ≤ b * d :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hab hc)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hcd hb)

/-! ## 1. The exact `coeffW` regroup (dimension × single power of `w`) -/

/-- **`coeffW_mul_split`** — the four-factor regroup
`c_a·c_b ≃ (dimQ a·dimQ b)·w^{c4 a + c4 b}` (`mul_swap4` + `qpow_add`). -/
theorem coeffW_mul_split (w : Q') (a b : Nat) :
    (coeffW w a * coeffW w b).eqv ((dimQ a * dimQ b) * qpow w (c4 a + c4 b)) := by
  have e0 : (coeffW w a * coeffW w b).eqv
      ((dimQ a * dimQ b) * (qpow w (c4 a) * qpow w (c4 b))) := by
    show ((dimQ a * qpow w (c4 a)) * (dimQ b * qpow w (c4 b))).eqv _
    exact mul_swap4 (dimQ a) (qpow w (c4 a)) (dimQ b) (qpow w (c4 b))
  exact Q'.eqv_trans _ _ _ e0
    (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (qpow_add w (c4 a) (c4 b))))

/-- **`coeffW_mul_ofNat`** — the same regroup with the dimension factor collapsed to a single
`ofNat`: `c_a·c_b ≃ ofNat((a+1)(b+1))·w^{c4 a + c4 b}`. -/
theorem coeffW_mul_ofNat (w : Q') (a b : Nat) :
    (coeffW w a * coeffW w b).eqv
      (Q'.ofNat ((a + 1) * (b + 1)) * qpow w (c4 a + c4 b)) :=
  Q'.eqv_trans _ _ _ (coeffW_mul_split w a b)
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv (a + 1) (b + 1))))

/-! ## 2. The exact Hankel identity and the `ρ = w²` super-log-concavity -/

/-- The Nat exponent identity `c4 s + c4(s+2) = 2 + (c4(s+1) + c4(s+1))`
(`s(s+2)+(s+2)(s+4) = 2 + 2(s+1)(s+3) = 2s²+8s+8`). -/
private theorem c4_hankel_nat (s : Nat) :
    c4 s + c4 (s + 2) = 2 + (c4 (s + 1) + c4 (s + 1)) := by
  show s * (s + 2) + (s + 2) * (s + 2 + 2)
      = 2 + ((s + 1) * (s + 1 + 2) + (s + 1) * (s + 1 + 2))
  simp only [Nat.add_mul, Nat.mul_add]
  omega

/-- **`coeffW_hankel_exact` — the enabling EXACT Hankel identity.**  For ALL `w` and every `s`
(no `w ≤ wH`):

    (s+2)²·(c_s·c_{s+2})  ≃  (s+1)(s+3)·(w²·c_{s+1}²).

Pure `qpow`/`dimQ` arithmetic: both sides regroup to `ofNat((s+2)²)·ofNat((s+1)(s+3))·w^E` with the
SAME exponent `E = c4 s + c4(s+2) = 2 + 2·c4(s+1)`.  This is the exact peak prefactor underlying the
`ρ = w²` bound; keeping the equality instead of dropping to `≤` (as `coeffW_superLogConcave` does). -/
theorem coeffW_hankel_exact {w : Q'} (s : Nat) :
    (Q'.ofNat ((s + 2) * (s + 2)) * (coeffW w s * coeffW w (s + 2))).eqv
      (Q'.ofNat ((s + 1) * (s + 3))
        * (qpow w 2 * (coeffW w (s + 1) * coeffW w (s + 1)))) := by
  -- LHS ≃ ofNat((s+2)²) · (ofNat((s+1)(s+3)) · w^E)
  have hL0 : (coeffW w s * coeffW w (s + 2)).eqv
      (Q'.ofNat ((s + 1) * (s + 3)) * qpow w (c4 s + c4 (s + 2))) := by
    have h := coeffW_mul_ofNat w s (s + 2)
    -- normalize (s+2+1) to (s+3)
    have hidx : s + 2 + 1 = s + 3 := by omega
    rw [hidx] at h
    exact h
  have hLHS : (Q'.ofNat ((s + 2) * (s + 2)) * (coeffW w s * coeffW w (s + 2))).eqv
      (Q'.ofNat ((s + 2) * (s + 2))
        * (Q'.ofNat ((s + 1) * (s + 3)) * qpow w (c4 s + c4 (s + 2)))) :=
    Q'.mul_eqv_congr_left _ _ _ hL0
  -- RHS ≃ ofNat((s+1)(s+3)) · (ofNat((s+2)²) · w^E)
  have hR0 : (coeffW w (s + 1) * coeffW w (s + 1)).eqv
      (Q'.ofNat ((s + 2) * (s + 2)) * qpow w (c4 (s + 1) + c4 (s + 1))) := by
    have h := coeffW_mul_ofNat w (s + 1) (s + 1)
    have hidx : s + 1 + 1 = s + 2 := by omega
    rw [hidx] at h
    exact h
  -- w² · (ofNat((s+2)²)·w^G) ≃ ofNat((s+2)²) · (w² · w^G) ≃ ofNat((s+2)²) · w^{2+G}
  have hR1 : (qpow w 2 * (coeffW w (s + 1) * coeffW w (s + 1))).eqv
      (qpow w 2 * (Q'.ofNat ((s + 2) * (s + 2)) * qpow w (c4 (s + 1) + c4 (s + 1)))) :=
    Q'.mul_eqv_congr_left _ _ _ hR0
  have hR2 : (qpow w 2 * (Q'.ofNat ((s + 2) * (s + 2)) * qpow w (c4 (s + 1) + c4 (s + 1)))).eqv
      (Q'.ofNat ((s + 2) * (s + 2)) * (qpow w 2 * qpow w (c4 (s + 1) + c4 (s + 1)))) :=
    mul3_swap' (qpow w 2) (Q'.ofNat ((s + 2) * (s + 2))) (qpow w (c4 (s + 1) + c4 (s + 1)))
  have hR3 : (qpow w 2 * qpow w (c4 (s + 1) + c4 (s + 1))).eqv
      (qpow w (2 + (c4 (s + 1) + c4 (s + 1)))) :=
    Q'.eqv_symm (qpow_add w 2 (c4 (s + 1) + c4 (s + 1)))
  have hR4 : (Q'.ofNat ((s + 2) * (s + 2)) * (qpow w 2 * qpow w (c4 (s + 1) + c4 (s + 1)))).eqv
      (Q'.ofNat ((s + 2) * (s + 2)) * qpow w (2 + (c4 (s + 1) + c4 (s + 1)))) :=
    Q'.mul_eqv_congr_left _ _ _ hR3
  -- fold the exponent 2 + (c4(s+1)+c4(s+1)) = c4 s + c4(s+2)
  have hE : 2 + (c4 (s + 1) + c4 (s + 1)) = c4 s + c4 (s + 2) := (c4_hankel_nat s).symm
  have hR5 : (qpow w 2 * (coeffW w (s + 1) * coeffW w (s + 1))).eqv
      (Q'.ofNat ((s + 2) * (s + 2)) * qpow w (c4 s + c4 (s + 2))) := by
    have h := Q'.eqv_trans _ _ _ hR1 (Q'.eqv_trans _ _ _ hR2 hR4)
    rw [hE] at h
    exact h
  have hRHS : (Q'.ofNat ((s + 1) * (s + 3))
        * (qpow w 2 * (coeffW w (s + 1) * coeffW w (s + 1)))).eqv
      (Q'.ofNat ((s + 1) * (s + 3))
        * (Q'.ofNat ((s + 2) * (s + 2)) * qpow w (c4 s + c4 (s + 2)))) :=
    Q'.mul_eqv_congr_left _ _ _ hR5
  -- the two canonical forms are equal by swapping the outer two factors
  have hSwap : (Q'.ofNat ((s + 2) * (s + 2))
        * (Q'.ofNat ((s + 1) * (s + 3)) * qpow w (c4 s + c4 (s + 2)))).eqv
      (Q'.ofNat ((s + 1) * (s + 3))
        * (Q'.ofNat ((s + 2) * (s + 2)) * qpow w (c4 s + c4 (s + 2)))) :=
    mul3_swap' (Q'.ofNat ((s + 2) * (s + 2))) (Q'.ofNat ((s + 1) * (s + 3)))
      (qpow w (c4 s + c4 (s + 2)))
  exact Q'.eqv_trans _ _ _ hLHS (Q'.eqv_trans _ _ _ hSwap (Q'.eqv_symm hRHS))

/-- **`coeffW_superLogConcave_wsq` — the `ρ = w²` super-log-concavity.**  For ALL `0 ≤ w` and every
mode `s` (NO `w ≤ wH` hypothesis):

    c_s · c_{s+2}  ≤  w² · (c_{s+1} · c_{s+1}).

Both sides carry the SAME power `w^{c4 s + c4(s+2)} = w^{2 + 2·c4(s+1)}`, so the inequality is
exactly the dimension log-concavity `(s+1)(s+3) ≤ (s+2)²` (`dimQ_logConcave`), scaled by the common
nonnegative power.  Sharper than the in-tree factor-4 `coeffW_superLogConcave` (`1/4` = worst-case
`w²` at `wH`) and drops its `w ≤ wH` hypothesis. -/
theorem coeffW_superLogConcave_wsq {w : Q'} (hw0 : (0 : Q') ≤ w) (s : Nat) :
    coeffW w s * coeffW w (s + 2) ≤ qpow w 2 * (coeffW w (s + 1) * coeffW w (s + 1)) := by
  -- LHS canonical
  have hLHS : (coeffW w s * coeffW w (s + 2)).eqv
      ((dimQ s * dimQ (s + 2)) * qpow w (c4 s + c4 (s + 2))) := coeffW_mul_split w s (s + 2)
  -- RHS canonical (same exponent after folding)
  have hi := coeffW_mul_split w (s + 1) (s + 1)
  have h1 : (qpow w 2 * (coeffW w (s + 1) * coeffW w (s + 1))).eqv
      (qpow w 2 * ((dimQ (s + 1) * dimQ (s + 1)) * qpow w (c4 (s + 1) + c4 (s + 1)))) :=
    Q'.mul_eqv_congr_left _ _ _ hi
  have h2 : (qpow w 2 * ((dimQ (s + 1) * dimQ (s + 1)) * qpow w (c4 (s + 1) + c4 (s + 1)))).eqv
      ((dimQ (s + 1) * dimQ (s + 1)) * (qpow w 2 * qpow w (c4 (s + 1) + c4 (s + 1)))) :=
    mul3_swap' (qpow w 2) (dimQ (s + 1) * dimQ (s + 1)) (qpow w (c4 (s + 1) + c4 (s + 1)))
  have h3 : (qpow w 2 * qpow w (c4 (s + 1) + c4 (s + 1))).eqv
      (qpow w (2 + (c4 (s + 1) + c4 (s + 1)))) :=
    Q'.eqv_symm (qpow_add w 2 (c4 (s + 1) + c4 (s + 1)))
  have h4 : ((dimQ (s + 1) * dimQ (s + 1)) * (qpow w 2 * qpow w (c4 (s + 1) + c4 (s + 1)))).eqv
      ((dimQ (s + 1) * dimQ (s + 1)) * qpow w (2 + (c4 (s + 1) + c4 (s + 1)))) :=
    Q'.mul_eqv_congr_left _ _ _ h3
  have hE : 2 + (c4 (s + 1) + c4 (s + 1)) = c4 s + c4 (s + 2) := (c4_hankel_nat s).symm
  have hRHS : (qpow w 2 * (coeffW w (s + 1) * coeffW w (s + 1))).eqv
      ((dimQ (s + 1) * dimQ (s + 1)) * qpow w (c4 s + c4 (s + 2))) := by
    have h := Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ h2 h4)
    rw [hE] at h
    exact h
  -- core dimension inequality, scaled by the common power ≥ 0
  have hcore : (dimQ s * dimQ (s + 2)) * qpow w (c4 s + c4 (s + 2))
      ≤ (dimQ (s + 1) * dimQ (s + 1)) * qpow w (c4 s + c4 (s + 2)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (FusionResidualBound.dimQ_logConcave s)
      (qpow_nonneg w hw0 (c4 s + c4 (s + 2)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS)
    (Q'.le_trans' _ _ _ hcore (Q'.ge_of_eqv hRHS))

/-- **`coeffW_rect_graded_wsq` — the `ρ = w²` Hankel rectangle.**  Instantiating the generic
`ratioRect_graded` at the sharp constant `ρ = w²`: for `0 < w` and every `a, b, i`,

    c_i · c_{i+a+b}  ≤  (w²)^{a·b} · (c_{i+a} · c_{i+b}).

Strictly sharpens `DiscreteLaplaceMargin.coeffW_rect_graded` (pinned at `ρ = 1/4`): the loss factor
is now the monotone `w`-dependent `(w²)^{ab}`, maximal `(1/4)^{ab}` at `w = wH`. -/
theorem coeffW_rect_graded_wsq {w : Q'} (hw0 : (0 : Q') < w) (a b i : Nat) :
    coeffW w i * coeffW w (i + a + b)
      ≤ qpow (qpow w 2) (a * b) * (coeffW w (i + a) * coeffW w (i + b)) :=
  ratioRect_graded (c := coeffW w) (ρ := qpow w 2)
    (fun k => coeffW_pos hw0 k) (qpow_nonneg w (Q'.le_of_lt hw0) 2)
    (fun s => coeffW_superLogConcave_wsq (Q'.le_of_lt hw0) s) b a i

/-! ## 3. The window profile and its `ρ = w⁴` super-log-concavity -/

/-- **`gWin` — the peak-normalized window profile** `g^{(N)}_p = c_p · c_{N-p}` (the convolution
window mass at total `N`, index `p`). -/
def gWin (w : Q') (N p : Nat) : Q' := coeffW w p * coeffW w (N - p)

/-- **`window_superLogConcave` — the window profile is super-log-concave with `ρ = w⁴`.**  For
`0 ≤ w` and `p + 2 ≤ N`,

    g_p · g_{p+2}  ≤  w⁴ · (g_{p+1} · g_{p+1}).

The product of the two `w²` atoms `coeffW_superLogConcave_wsq` at the head index `p` and the tail
index `N-p-2` (which pairs `c_{N-(p+2)}·c_{N-p} ≤ w²·c_{N-(p+1)}²`).  This is the Gaussian window
envelope's single-step generator: `ρ = w⁴` is maximal `1/16` at `wH`, so the antidiagonal
amplification is beaten by the quadratic-exponent envelope (unlike the dead flat `S`-band split). -/
theorem window_superLogConcave {w : Q'} (hw0 : (0 : Q') ≤ w) (N p : Nat) (hp : p + 2 ≤ N) :
    gWin w N p * gWin w N (p + 2) ≤ qpow w 4 * (gWin w N (p + 1) * gWin w N (p + 1)) := by
  -- unfold to the pure coeffW product form
  show (coeffW w p * coeffW w (N - p)) * (coeffW w (p + 2) * coeffW w (N - (p + 2)))
      ≤ qpow w 4
        * ((coeffW w (p + 1) * coeffW w (N - (p + 1)))
          * (coeffW w (p + 1) * coeffW w (N - (p + 1))))
  -- Nat index facts
  have iC : (N - p - 2) + 2 = N - p := by omega
  have iD : (N - p - 2) + 1 = N - (p + 1) := by omega
  have iA : N - p - 2 = N - (p + 2) := by omega
  -- head atom  c_p·c_{p+2} ≤ w²·c_{p+1}²
  have hA := coeffW_superLogConcave_wsq hw0 p
  -- tail atom  c_{N-(p+2)}·c_{N-p} ≤ w²·c_{N-(p+1)}²
  have hB0 := coeffW_superLogConcave_wsq hw0 (N - p - 2)
  rw [iC, iD, iA] at hB0
  -- commute the tail LHS to  c_{N-p}·c_{N-(p+2)}
  have hBcomm : coeffW w (N - p) * coeffW w (N - (p + 2))
      ≤ qpow w 2 * (coeffW w (N - (p + 1)) * coeffW w (N - (p + 1))) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv (coeffW w (N - p)) (coeffW w (N - (p + 2))))) hB0
  -- nonnegativities
  have hc_nn : (0 : Q') ≤ coeffW w (N - p) * coeffW w (N - (p + 2)) :=
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0 _) (coeffW_nonneg hw0 _)
  have hb_nn : (0 : Q') ≤ qpow w 2 * (coeffW w (p + 1) * coeffW w (p + 1)) :=
    Q'.mul_nonneg _ _ (qpow_nonneg w hw0 2)
      (Q'.mul_nonneg _ _ (coeffW_nonneg hw0 _) (coeffW_nonneg hw0 _))
  -- product of the two atoms
  have hprod : (coeffW w p * coeffW w (p + 2)) * (coeffW w (N - p) * coeffW w (N - (p + 2)))
      ≤ (qpow w 2 * (coeffW w (p + 1) * coeffW w (p + 1)))
        * (qpow w 2 * (coeffW w (N - (p + 1)) * coeffW w (N - (p + 1)))) :=
    mul_le_mul' hA hBcomm hc_nn hb_nn
  -- LHS regroup to the atom-product order
  have hLeq : ((coeffW w p * coeffW w (N - p)) * (coeffW w (p + 2) * coeffW w (N - (p + 2)))).eqv
      ((coeffW w p * coeffW w (p + 2)) * (coeffW w (N - p) * coeffW w (N - (p + 2)))) :=
    mul_swap4 (coeffW w p) (coeffW w (N - p)) (coeffW w (p + 2)) (coeffW w (N - (p + 2)))
  -- RHS regroup:  (w²·P)·(w²·Q) ≃ w⁴·(g_{p+1}·g_{p+1})
  have hsw := mul_swap4 (qpow w 2) (coeffW w (p + 1) * coeffW w (p + 1)) (qpow w 2)
    (coeffW w (N - (p + 1)) * coeffW w (N - (p + 1)))
  have hqsq : (qpow w 2 * qpow w 2).eqv (qpow w 4) := Q'.eqv_symm (qpow_add w 2 2)
  have hPQ := mul_swap4 (coeffW w (p + 1)) (coeffW w (p + 1))
    (coeffW w (N - (p + 1))) (coeffW w (N - (p + 1)))
  have hReq : ((qpow w 2 * (coeffW w (p + 1) * coeffW w (p + 1)))
        * (qpow w 2 * (coeffW w (N - (p + 1)) * coeffW w (N - (p + 1))))).eqv
      (qpow w 4
        * ((coeffW w (p + 1) * coeffW w (N - (p + 1)))
          * (coeffW w (p + 1) * coeffW w (N - (p + 1))))) :=
    Q'.eqv_trans _ _ _ hsw (mul_eqv_congr₂ hqsq hPQ)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLeq)
    (Q'.le_trans' _ _ _ hprod (Q'.le_of_eqv hReq))

/-! ## 4. OPTION A — concrete finite-`s` clearance of `FiniteSMargin` at the worst case `w = wH` -/

/-- **`finiteSMargin_upTo_wH_5` — the CONCRETE finite clearance.**  At the worst case `w = wH`, the
`FiniteSMargin` theta-floor inequality
`40000·(acN(s+1,s)·acN(s+1,s+2)) ≤ 22801·(acN(s+1,s+1)²)` holds for every `s ≤ 5` (each mode a
closed rational, `decide`-checked; beyond `s ≈ 8` the fold depth outruns `decide`).  A genuine
finite extension of `DiscreteLaplaceMargin.finiteSMargin_floor_s0` (`s = 0`) to a six-mode window. -/
theorem finiteSMargin_upTo_wH_5 : ∀ s, s ≤ 5 →
    Q'.ofNat 40000 * (acN wH (s + 1) s * acN wH (s + 1) (s + 2))
      ≤ Q'.ofNat 22801 * (acN wH (s + 1) (s + 1) * acN wH (s + 1) (s + 1)) := by
  intro s hs
  match s, hs with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide
  | (n + 6), h => exact absurd h (by omega)

/-! ## 5. The Type-level reduction of `FiniteSMargin` into its two independent contents -/

/-- **`WHAllSMargin`** — the RATIONAL content of `FiniteSMargin`: the wH theta-floor margin for ALL
`s`.  Verified for `s ≤ 5` by `finiteSMargin_upTo_wH_5`; the `s → ∞` tail is the theta wall.
NAMED-OPEN (never `sorry`). -/
structure WHAllSMargin : Type where
  /-- The wH margin dominates the crude rational theta floor `40000/22801`, uniform in `s`. -/
  margin : ∀ s,
    Q'.ofNat 40000 * (acN wH (s + 1) s * acN wH (s + 1) (s + 2))
      ≤ Q'.ofNat 22801 * (acN wH (s + 1) (s + 1) * acN wH (s + 1) (s + 1))

/-- **`FiniteSMarginWorstcase w`** — the ANALYTIC content of `FiniteSMargin`: the `w`-monotonicity
reduction collapsing the two-parameter `(w,s)` family to the one-parameter wH sequence.  The margin
ratio `A_s(w)B_s(w)/M_s(w)²` is increasing in `w` (maximal at `wH`), so a wH-margin implies the
`w ≤ wH` margin.  Direction supplied by the `w²`/`w⁴` atoms (`ρ_eff` maximal at `wH`).  NAMED-OPEN. -/
structure FiniteSMarginWorstcase (w : Q') : Type where
  /-- wH-margin at mode `s` implies the `w`-margin at mode `s`. -/
  reduce : ∀ s,
    (Q'.ofNat 40000 * (acN wH (s + 1) s * acN wH (s + 1) (s + 2))
        ≤ Q'.ofNat 22801 * (acN wH (s + 1) (s + 1) * acN wH (s + 1) (s + 1)))
    → (Q'.ofNat 40000 * (acN w (s + 1) s * acN w (s + 1) (s + 2))
        ≤ Q'.ofNat 22801 * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1)))

/-- **`finiteSMarginOfWorstcase` — THE REDUCTION.**  The two independent contents combine to the
full `AcNReserveAnalytic.FiniteSMargin w`: the wH rational margin `WHAllSMargin` (per `s`) fed
through the `w`-worst-case reduction `FiniteSMarginWorstcase w`.  This cleanly separates the theta
tail (`WHAllSMargin`) from the `w`-dependence (`FiniteSMarginWorstcase`). -/
def finiteSMarginOfWorstcase {w : Q'} (r : FiniteSMarginWorstcase w) (m : WHAllSMargin) :
    FiniteSMargin w where
  margin := fun s => r.reduce s (m.margin s)

/-- **`WindowedGaussianEnvelope w`** — the remaining GLOBAL content: the fixed `ρ^{i²}` Gaussian
envelope of the window profile about its peak `m`,

    g_{m+i} · g_{m-i}  ≤  (w⁴)^{i²} · (g_m · g_m),

the genuine local-CLT / theta-sum object obtained by a windowed induction on
`window_superLogConcave`.  NAMED-OPEN (the windowed rectangle is not inhabited here). -/
structure WindowedGaussianEnvelope (w : Q') : Type where
  /-- The `ρ = w⁴` Gaussian envelope of the window profile about its peak. -/
  envelope : ∀ N m i, i ≤ m → m + i ≤ N →
    gWin w N (m + i) * gWin w N (m - i)
      ≤ qpow (qpow w 4) (i * i) * (gWin w N m * gWin w N m)

/-! ## 6. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `coeffW_mul_split`, `coeffW_mul_ofNat` — the exact `c_a·c_b` regroup (dimension × single power).
  * `coeffW_hankel_exact` — the EXACT cross-multiplied Hankel identity (all `w`, no `w ≤ wH`).
  * `coeffW_superLogConcave_wsq` — the `ρ = w²` super-log-concavity, ALL `0 ≤ w` (drops `w ≤ wH`,
    sharpens the in-tree factor-4 `quarter` atom to the monotone `w²`).
  * `coeffW_rect_graded_wsq` — the `ρ = w²` Hankel rectangle (sharpens the `ρ = 1/4` in-tree rect).
  * `gWin`, `window_superLogConcave` — the window profile is `ρ = w⁴` super-log-concave.
  * `finiteSMargin_upTo_wH_5` — the concrete wH clearance of `FiniteSMargin` for all `s ≤ 5`.
  * `finiteSMarginOfWorstcase` — the reduction `WHAllSMargin + FiniteSMarginWorstcase ⟹ FiniteSMargin`.

NAMED OPEN (Type-level structure, never `sorry`):
  * `WHAllSMargin` — the wH theta-floor margin for ALL `s` (rational tail; verified `s ≤ 5`).
  * `FiniteSMarginWorstcase w` — the `w`-monotone worst-case reduction to the wH sequence.
  * `WindowedGaussianEnvelope w` — the `ρ = w⁴` Gaussian window envelope (windowed induction).

HONEST VERDICT.  This module DEEPENS `DiscreteLaplaceMargin` from the crude worst-case constant
`ρ = 1/4` to the EXACT monotone `ρ = w²` (proving the exact Hankel identity and dropping the
`w ≤ wH` hypothesis), lifts the sharp atom one convolution level to the window profile (`ρ = w⁴`),
discharges an explicit six-mode finite family of the worst-case `FiniteSMargin`, and factors the
sole residual into two independent, cleanly-separated named contents (the wH rational tail
`WHAllSMargin` and the `w`-monotone reduction `FiniteSMarginWorstcase`) plus the Gaussian window
envelope.  It does NOT inhabit the uniform `s → ∞` residual, which is the genuine local-CLT/theta
wall.  This is a representation/deepening advance on one box-level log-concavity sub-fact; it is
NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.LaplaceMarginDeep

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.LaplaceMarginDeep.coeffW_mul_split
#print axioms YMGap.Continuum.LaplaceMarginDeep.coeffW_mul_ofNat
#print axioms YMGap.Continuum.LaplaceMarginDeep.coeffW_hankel_exact
#print axioms YMGap.Continuum.LaplaceMarginDeep.coeffW_superLogConcave_wsq
#print axioms YMGap.Continuum.LaplaceMarginDeep.coeffW_rect_graded_wsq
#print axioms YMGap.Continuum.LaplaceMarginDeep.window_superLogConcave
#print axioms YMGap.Continuum.LaplaceMarginDeep.finiteSMargin_upTo_wH_5
#print axioms YMGap.Continuum.LaplaceMarginDeep.finiteSMarginOfWorstcase
