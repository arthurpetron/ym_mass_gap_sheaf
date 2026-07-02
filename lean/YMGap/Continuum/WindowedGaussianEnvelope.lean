/-
Track A / R2 (track: 1-window) — INHABITING `LaplaceMarginDeep.WindowedGaussianEnvelope`.

# What this module proves

`LaplaceMarginDeep` carried the fixed-`ρ` Gaussian window envelope

    g_{m+i} · g_{m-i}  ≤  (w⁴)^{i²} · (g_m · g_m)          (`WindowedGaussianEnvelope.envelope`)

as an honest NAMED-OPEN Type-level residual, with a doc suggestion that it be reached by a
"windowed induction on `window_superLogConcave`".  That inductive route is genuinely BLOCKED:
`window_superLogConcave` carries the hypothesis `p + 2 ≤ N` (its index identity `(N-p-2)+2 = N-p`
fails once `p + 2 > N`), so `gWin` is NOT globally super-log-concave and iterating it hits the
window boundary.

This module shows the envelope is nonetheless inhabitable — WITHOUT any windowed induction and
WITHOUT any range-restricted re-derivation — as TWO instances of the single sharpest already-PROVED
global rectangle `LaplaceMarginDeep.coeffW_rect_graded_wsq` (`ρ = w²`, no range restriction), taken
at spread `a = b = i`:

  * HEAD  (base `m-i`, using `i ≤ m`):
        c_{m-i} · c_{m+i}      ≤ (w²)^{i²} · (c_m · c_m)
  * TAIL  (base `N-m-i`, using `m+i ≤ N`):
        c_{N-m-i} · c_{N-m+i}  ≤ (w²)^{i²} · (c_{N-m} · c_{N-m})

Multiplying the two nonnegative inequalities (in-tree `mul_le_mul'`) and regrouping (`mul_swap4`):

  * the LHS product regroups to `gWin(m+i) · gWin(m-i)` (using `N-(m+i)=N-m-i`, `N-(m-i)=N-m+i`);
  * the RHS product regroups to `(w⁴)^{i²} · (gWin m · gWin m)`, the sole non-index arithmetic being
        (w²)^{i²} · (w²)^{i²}  ≃  (w⁴)^{i²}
    both sides `≃ w^{4·i²}` via `qpow_qpow` + `qpow_add` (`2·i² + 2·i² = 4·i²`).

So `WindowedGaussianEnvelope w` is inhabited for every `0 < w` (`windowedGaussianEnvelopeOf`), and
concretely at the worst case `w = wH` (`windowedGaussianEnvelope_wH`).  Expected axioms:
`propext` / `Quot.sound` only.

# HONESTY — scope

This closes exactly ONE of the three residuals `LaplaceMarginDeep` left open (the fixed-`ρ` Gaussian
window envelope).  It does NOT touch the two genuine NAMED-OPEN residuals of that module —
`WHAllSMargin` (the `s → ∞` theta tail of the wH margin) and `FiniteSMarginWorstcase` (the
`w`-monotonicity worst-case reduction) — and it is NOT a 4D Yang–Mills mass gap.  It is a sharp
reduction: an "analytic wall" the doc named is shown to be a two-line consequence of proved global
machinery, so the real frontier stays exactly the two remaining residuals.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic on the reused `coeffW`/`qpow` definitions, the already-proved global
rectangle `coeffW_rect_graded_wsq`, `mul_swap4`, `qpow_qpow`/`qpow_add`, and finite `omega` Nat
identities.  Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses are
`Type`-level data.
-/

import YMGap.Continuum.LaplaceMarginDeep

namespace YMGap.Continuum.WindowedGaussianEnvelopeModule

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.DiscreteLaplaceMargin
open YMGap.Continuum.LaplaceMarginDeep

/-! ## 0. Small `Q'` rearrangement helpers (pure commutative algebra; the `private` in-tree twins). -/

/-- Congruence of `·` in both factors. -/
private theorem mul_eqv_congr₂ {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') :
    (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha) (Q'.mul_eqv_congr_left a' b b' hb)

/-- **Product of two inequalities of nonnegative quantities.**  `a ≤ b`, `c ≤ d`, `0 ≤ c`,
`0 ≤ b` ⟹ `a·c ≤ b·d`. -/
private theorem mul_le_mul' {a b c d : Q'} (hab : a ≤ b) (hcd : c ≤ d)
    (hc : (0 : Q') ≤ c) (hb : (0 : Q') ≤ b) : a * c ≤ b * d :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hab hc)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hcd hb)

/-! ## 1. The single sharpest exponent fold: `(w²)^{i²} · (w²)^{i²} ≃ (w⁴)^{i²}`. -/

/-- **`wsq_sq_fold`** — the ONLY non-index arithmetic of the envelope: the square of the head/tail
loss constant folds to the window loss constant, `(w²)^{i²} · (w²)^{i²} ≃ (w⁴)^{i²}`.  Both sides
`≃ w^{4·i²}` via `qpow_qpow` (`(w²)^{i²} ≃ w^{2i²}`, `(w⁴)^{i²} ≃ w^{4i²}`) + `qpow_add`
(`2i²+2i² = 4i²`). -/
theorem wsq_sq_fold (w : Q') (i : Nat) :
    (qpow (qpow w 2) (i * i) * qpow (qpow w 2) (i * i)).eqv (qpow (qpow w 4) (i * i)) := by
  have e1 : (qpow (qpow w 2) (i * i) * qpow (qpow w 2) (i * i)).eqv
      (qpow w (2 * (i * i)) * qpow w (2 * (i * i))) :=
    mul_eqv_congr₂ (qpow_qpow w 2 (i * i)) (qpow_qpow w 2 (i * i))
  have e2 : (qpow w (2 * (i * i)) * qpow w (2 * (i * i))).eqv
      (qpow w (2 * (i * i) + 2 * (i * i))) :=
    Q'.eqv_symm (qpow_add w (2 * (i * i)) (2 * (i * i)))
  have e3 : (qpow w (2 * (i * i) + 2 * (i * i))).eqv (qpow w (4 * (i * i))) :=
    Q'.eqv_of_eq (congrArg (qpow w) (by omega))
  have e4 : (qpow w (4 * (i * i))).eqv (qpow (qpow w 4) (i * i)) :=
    Q'.eqv_symm (qpow_qpow w 4 (i * i))
  exact Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2 (Q'.eqv_trans _ _ _ e3 e4))

/-! ## 2. The two graded-rectangle instances at spread `a = b = i`. -/

/-- **`head_rect`** — the HEAD instance of `coeffW_rect_graded_wsq` at spread `a = b = i`, base
`m-i` (using `i ≤ m`):  `c_{m-i} · c_{m+i} ≤ (w²)^{i²} · (c_m · c_m)`. -/
theorem head_rect {w : Q'} (hw0 : (0 : Q') < w) {m i : Nat} (hi : i ≤ m) :
    coeffW w (m - i) * coeffW w (m + i)
      ≤ qpow (qpow w 2) (i * i) * (coeffW w m * coeffW w m) := by
  have h := coeffW_rect_graded_wsq hw0 i i (m - i)
  have e1 : (m - i) + i + i = m + i := by omega
  have e2 : (m - i) + i = m := by omega
  rw [e1, e2] at h
  exact h

/-- **`tail_rect`** — the TAIL instance of `coeffW_rect_graded_wsq` at spread `a = b = i`, base
`N-m-i` (using `m+i ≤ N`):  `c_{N-m-i} · c_{N-m+i} ≤ (w²)^{i²} · (c_{N-m} · c_{N-m})`. -/
theorem tail_rect {w : Q'} (hw0 : (0 : Q') < w) {N m i : Nat} (hN : m + i ≤ N) :
    coeffW w (N - m - i) * coeffW w (N - m + i)
      ≤ qpow (qpow w 2) (i * i) * (coeffW w (N - m) * coeffW w (N - m)) := by
  have h := coeffW_rect_graded_wsq hw0 i i (N - m - i)
  have e1 : (N - m - i) + i + i = N - m + i := by omega
  have e2 : (N - m - i) + i = N - m := by omega
  rw [e1, e2] at h
  exact h

/-! ## 3. The Gaussian window envelope (the target `WindowedGaussianEnvelope.envelope`). -/

/-- **`windowedGaussianEnvelope` — the fixed-`ρ` Gaussian window envelope.**  For every `0 < w`,

    g_{m+i} · g_{m-i}  ≤  (w⁴)^{i²} · (g_m · g_m),

with `g_p = c_p · c_{N-p}`.  The product of the head and tail rectangle instances (`head_rect`,
`tail_rect`), regrouped by `mul_swap4` and closed by the exponent fold `wsq_sq_fold`.  No windowed
induction, no `window_superLogConcave`, no range-restricted re-derivation. -/
theorem windowedGaussianEnvelope {w : Q'} (hw0 : (0 : Q') < w) :
    ∀ N m i, i ≤ m → m + i ≤ N →
      gWin w N (m + i) * gWin w N (m - i)
        ≤ qpow (qpow w 4) (i * i) * (gWin w N m * gWin w N m) := by
  intro N m i hi hN
  have hw0' : (0 : Q') ≤ w := Q'.le_of_lt hw0
  -- Unfold `gWin` and normalise the `N`-side indices to the head/tail canonical forms.
  show (coeffW w (m + i) * coeffW w (N - (m + i))) * (coeffW w (m - i) * coeffW w (N - (m - i)))
      ≤ qpow (qpow w 4) (i * i)
        * ((coeffW w m * coeffW w (N - m)) * (coeffW w m * coeffW w (N - m)))
  have eA : N - (m + i) = N - m - i := by omega
  have eB : N - (m - i) = N - m + i := by omega
  rw [eA, eB]
  -- Abbreviations (documentary): A=c_{m+i} B=c_{N-m-i} C=c_{m-i} D=c_{N-m+i}, P=c_m R=c_{N-m}.
  -- HEAD, commuted to `A·C ≤ Θ·(P·P)`.
  have head' : coeffW w (m + i) * coeffW w (m - i)
      ≤ qpow (qpow w 2) (i * i) * (coeffW w m * coeffW w m) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv (coeffW w (m + i)) (coeffW w (m - i))))
      (head_rect hw0 hi)
  have tail' := tail_rect hw0 hN
  -- nonnegativities for the product
  have hBD : (0 : Q') ≤ coeffW w (N - m - i) * coeffW w (N - m + i) :=
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0' _) (coeffW_nonneg hw0' _)
  have hΘPP : (0 : Q') ≤ qpow (qpow w 2) (i * i) * (coeffW w m * coeffW w m) :=
    Q'.mul_nonneg _ _
      (qpow_nonneg (qpow w 2) (qpow_nonneg w hw0' 2) (i * i))
      (Q'.mul_nonneg _ _ (coeffW_nonneg hw0' _) (coeffW_nonneg hw0' _))
  -- product of the two inequalities:  (A·C)·(B·D) ≤ (Θ·(P·P))·(Θ·(R·R))
  have hprod := mul_le_mul' head' tail' hBD hΘPP
  -- LHS regroup:  (A·B)·(C·D) ≃ (A·C)·(B·D)
  have hLeq := mul_swap4 (coeffW w (m + i)) (coeffW w (N - m - i))
    (coeffW w (m - i)) (coeffW w (N - m + i))
  -- RHS regroup:  (Θ·(P·P))·(Θ·(R·R)) ≃ (w⁴)^{i²} · ((P·R)·(P·R))
  have hsw := mul_swap4 (qpow (qpow w 2) (i * i)) (coeffW w m * coeffW w m)
    (qpow (qpow w 2) (i * i)) (coeffW w (N - m) * coeffW w (N - m))
  have hPR := mul_swap4 (coeffW w m) (coeffW w m) (coeffW w (N - m)) (coeffW w (N - m))
  have hReq := Q'.eqv_trans _ _ _ hsw (mul_eqv_congr₂ (wsq_sq_fold w i) hPR)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLeq)
    (Q'.le_trans' _ _ _ hprod (Q'.le_of_eqv hReq))

/-! ## 4. Inhabiting the named residual. -/

/-- **`windowedGaussianEnvelopeOf`** — the parametric inhabitant: for EVERY `0 < w`, the named
residual `LaplaceMarginDeep.WindowedGaussianEnvelope w` is inhabited (the structure carries no
positivity, so the inhabitant supplies its own `hw0`). -/
def windowedGaussianEnvelopeOf {w : Q'} (hw0 : (0 : Q') < w) :
    LaplaceMarginDeep.WindowedGaussianEnvelope w where
  envelope := windowedGaussianEnvelope hw0

/-- **`windowedGaussianEnvelope_wH`** — the concrete inhabitant at the worst case `w = wH = 1/2`. -/
def windowedGaussianEnvelope_wH : LaplaceMarginDeep.WindowedGaussianEnvelope wH :=
  windowedGaussianEnvelopeOf (by decide)

end YMGap.Continuum.WindowedGaussianEnvelopeModule
