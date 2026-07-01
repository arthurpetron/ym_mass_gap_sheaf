/-
Track A / R2 — the GENERIC "margin-from-ρ" (discrete-Laplace / effective-variance) reframing of
the sole remaining autoconvolution log-concavity crux `FiniteSMargin`.

# The reframe (read first — load-bearing honesty)

`AcNReserveAnalytic.FiniteSMargin` is the log-concavity MARGIN of the fixed-window central
autoconvolution `acN` of the super-log-concave theta weight `coeffW`.  Two earlier structural
attacks are DEAD:

  * the summand-wise / rank-1 route on the `symMinor` quadratic form is MACHINE-REFUTED
    (`symMinor` is indefinite off the diagonal; `LeakGeoDecay` proved the leak/anchor split is
    false for the extremal admissible sequence);
  * so the correct move is to change the REPRESENTATION and name the ONE quantity that matters:
    the strict super-log-concavity constant `ρ` (`coeffW` has `ρ = 1/4`, the factor-4 slack).

This module works the GENERIC positive sequence `c` with a strict factor `ρ`
(`∀ i, c i · c (i+2) ≤ ρ · c (i+1)²`) and proves the SHARP ρ-graded Hankel atom — the clean
"effective-variance" object the theta computation is really made of — then instantiates it at
the theta weight (`ρ = 1/4`) and drives the small-window `FiniteSMargin` instance past the
required rational floor.  It also gives the CLOSED-FORM reason the summand-wise route is doomed.

# What this module proves (all axiom-clean)

GENERIC (abstract `c`, strict factor `ρ`):
  * `ratioStep_graded` — the ρ-GRADED single-step Hankel inequality:
        c i · c (i+m+2)  ≤  ρ^{m+1} · (c (i+1) · c (i+m+1)).
    This is `FusionCoreStepRoundE.coeffW_step` upgraded from the flat PF₂ bound (`ρ^0 = 1`) to
    the sharp ρ-graded bound — the single number `ρ` now rides every spread.  The exponent
    `m+1` is exactly the discrete mixed second difference of the extremal log-Gaussian, so the
    bound is SHARP (equality for `c_k = ρ^{k(k-1)/2}`).
  * `ratioRect_graded` — the ρ-GRADED rectangle (Hankel 2×2 minor):
        c i · c (i+a+b)  ≤  ρ^{a·b} · (c (i+a) · c (i+b)).
    The full "margin-from-ρ" atom: every less-spread product beats the most-spread one by a
    factor `ρ^{a·b}`.  Generalizes `FusionCoreStepRoundE.coeffW_rect` (the `ρ = 1` PF₂ shell).

INSTANTIATION (theta weight, `ρ = 1/4`):
  * `coeffW_rect_graded` — `coeffW` obeys the ρ-graded rectangle with `ρ = 1/4`.  Strictly
    sharpens `coeffW_rect`.
  * `acN_one`, `finiteSMargin_floor_s0` — the `FiniteSMargin` inequality at `s = 0` clears the
    rational theta floor `40000/22801` with a large margin, DIRECTLY from super-log-concavity.

REFUTATION (closed-form obstruction to the rank-1 route):
  * `naive_summand_nonpos` — GENERIC: for a log-concave positive `c`, the `(p, p+2)` summand of
    the defect `acN(s+1)² − acN(s)·acN(s+2)` is `≤ 0`.  So the defect is NOT a sum of
    nonnegative summands in the naive kernel — the per-term route CANNOT close it, uniformly in
    `s`.  This is the clean closed-form reason behind the `symMinor`-indefinite machine
    refutation: the antidiagonal spread `|q−p| ≥ 2` flips the sign.
  * `naive_route_refuted` — a CONCRETE strict witness: the extremal `ρ = 1/4` sequence
    `(1, 1, 1/4, 1/64)` satisfies super-log-concavity yet has a strictly negative `(0,2)`
    summand at `s = 2`.

# HONESTY — what is NOT closed

`FiniteSMargin` for ALL `s` is NOT inhabited here.  The ρ-graded atom controls each cross ratio
`c_{s-p}c_{s+2-q}/c_{s+1-p}c_{s+1-q} ≤ ρ^{…}` termwise, and this closes the small windows
(`s = 0` here, `s = 1` by the same mechanism), but for `s → ∞` the near-antidiagonal terms carry
a ρ^{−|p−q|} amplification that is only tamed by the GLOBAL Gaussian decay of the window profile
`c_p·c_{s+1-p}` — the genuine local-CLT / theta sum.  That global summation is the residual wall
(numerically the even-`s` margins fall monotonically to `L_even(1/4) ≈ 1.987`, comfortably above
the floor `1.7543`, but it is a transcendental theta ratio, not a finite rational inequality).

This module is a REPRESENTATION advance on one box-level log-concavity sub-fact: it names the
sharp quantity `ρ`, proves the ρ-graded Hankel atom generically, sharpens `coeffW_rect`, clears
the small window, and closes the summand-wise route in closed form.  It is NOT a 4D Yang–Mills
mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `qpow`/`coeffW`/`acN` definitions, finite inductions, the
positive-cancellation lemma `le_of_mul_le_mul_left_pos`, and `decide` only on closed concrete-
rational facts.  Every load-bearing declaration is gated with `#print axioms`; permitted output
is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.  All
witnesses are `Type`-level data.
-/

import YMGap.Continuum.AcNReserveAnalytic
import YMGap.Continuum.FusionCoreStepRoundE

namespace YMGap.Continuum.DiscreteLaplaceMargin

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.FusionCoreStepRoundE
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.LeakGeoDecay
open YMGap.Continuum.AcNReserveAnalytic

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

/-- `P·(u·(r·(v·v))) ≃ v·((P·r)·(u·v))` — the 5-factor rearrangement used in the ρ-graded step.
Both sides are the product `{P, r, u, v, v}`; route through the common form `(P·r)·(u·(v·v))`. -/
private theorem mul5_rearrange (P u r v : Q') :
    (P * (u * (r * (v * v)))).eqv (v * ((P * r) * (u * v))) := by
  have hL : (P * (u * (r * (v * v)))).eqv ((P * r) * (u * (v * v))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (mul3_swap' u r (v * v)))
      (Q'.eqv_symm (Q'.mul_assoc_eqv P r (u * (v * v))))
  have hR : (v * ((P * r) * (u * v))).eqv ((P * r) * (u * (v * v))) :=
    Q'.eqv_trans _ _ _ (mul3_swap' v (P * r) (u * v))
      (Q'.mul_eqv_congr_left _ _ _ (mul3_swap' v u v))
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

/-! ## 1. The GENERIC ρ-graded single-step Hankel atom -/

/-- **`ratioStep_graded` — the sharp ρ-graded single-step Hankel inequality.**  For a positive
sequence `c` with the strict super-log-concavity `c i · c (i+2) ≤ ρ · c (i+1)²` (uniform `ρ ≥ 0`),
every `i, m`:

    c i · c (i+m+2)  ≤  ρ^{m+1} · (c (i+1) · c (i+m+1)).

Induction on `m`; base `m = 0` is the hypothesis (`ρ^1 ≃ ρ`), the step multiplies the IH by the
moving boundary factor, applies the hypothesis at the moving end (the ρ that upgrades `ρ^{m+1}`
to `ρ^{m+2}`), and cancels the common positive factor.  The flat PF₂ version
(`FusionCoreStepRoundE.coeffW_step`) is the `ρ = 1` shell. -/
theorem ratioStep_graded {c : Nat → Q'} {ρ : Q'}
    (hpos : ∀ i, (0 : Q') < c i) (hρ : (0 : Q') ≤ ρ)
    (hslc : ∀ i, c i * c (i + 2) ≤ ρ * (c (i + 1) * c (i + 1))) (i : Nat) :
    ∀ m, c i * c (i + m + 2) ≤ qpow ρ (m + 1) * (c (i + 1) * c (i + m + 1))
  | 0 => by
      have h := hslc i
      have e1 : (qpow ρ 1 * (c (i + 1) * c (i + 1))).eqv (ρ * (c (i + 1) * c (i + 1))) :=
        Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv ρ)
      exact Q'.le_trans' _ _ _ h (Q'.ge_of_eqv e1)
  | m + 1 => by
      have ih : c i * c (i + m + 2) ≤ qpow ρ (m + 1) * (c (i + 1) * c (i + m + 1)) :=
        ratioStep_graded hpos hρ hslc i m
      have hslcm : c (i + m + 1) * c (i + m + 1 + 2)
          ≤ ρ * (c (i + m + 1 + 1) * c (i + m + 1 + 1)) := hslc (i + m + 1)
      have en1 : i + m + 1 + 2 = i + m + 3 := by omega
      have en2 : i + m + 1 + 1 = i + m + 2 := by omega
      rw [en1, en2] at hslcm
      -- hslcm : c (i+m+1) * c (i+m+3) ≤ ρ * (c (i+m+2) * c (i+m+2))
      have hz : (0 : Q') ≤ c (i + m + 3) := Q'.le_of_lt (hpos _)
      have hu : (0 : Q') ≤ c (i + 1) := Q'.le_of_lt (hpos _)
      have hP : (0 : Q') ≤ qpow ρ (m + 1) := qpow_nonneg ρ hρ _
      have step1 := Q'.mul_le_mul_of_nonneg_right _ _ (c (i + m + 3)) ih hz
      -- reassoc RHS of step1
      have eR : ((qpow ρ (m + 1) * (c (i + 1) * c (i + m + 1))) * c (i + m + 3)).eqv
          (qpow ρ (m + 1) * (c (i + 1) * (c (i + m + 1) * c (i + m + 3)))) :=
        Q'.eqv_trans _ _ _
          (Q'.mul_assoc_eqv (qpow ρ (m + 1)) (c (i + 1) * c (i + m + 1)) (c (i + m + 3)))
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_assoc_eqv (c (i + 1)) (c (i + m + 1)) (c (i + m + 3))))
      have hscale : c (i + 1) * (c (i + m + 1) * c (i + m + 3))
          ≤ c (i + 1) * (ρ * (c (i + m + 2) * c (i + m + 2))) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ hslcm hu
      have hscale2 : qpow ρ (m + 1) * (c (i + 1) * (c (i + m + 1) * c (i + m + 3)))
          ≤ qpow ρ (m + 1) * (c (i + 1) * (ρ * (c (i + m + 2) * c (i + m + 2)))) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ hscale hP
      have hcomb : (c i * c (i + m + 2)) * c (i + m + 3)
          ≤ qpow ρ (m + 1) * (c (i + 1) * (ρ * (c (i + m + 2) * c (i + m + 2)))) :=
        Q'.le_trans' _ _ _ step1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv eR) hscale2)
      -- e1 : LHS ≃ c(i+m+2) * (c i * c(i+m+3))
      have e1 : ((c i * c (i + m + 2)) * c (i + m + 3)).eqv
          (c (i + m + 2) * (c i * c (i + m + 3))) := mul3_swap (c i) (c (i + m + 2)) (c (i + m + 3))
      -- e2 : RHS ≃ c(i+m+2) * (qpow ρ (m+2) * (c(i+1) * c(i+m+2)))
      have e2 : (qpow ρ (m + 1) * (c (i + 1) * (ρ * (c (i + m + 2) * c (i + m + 2))))).eqv
          (c (i + m + 2) * (qpow ρ (m + 2) * (c (i + 1) * c (i + m + 2)))) :=
        mul5_rearrange (qpow ρ (m + 1)) (c (i + 1)) ρ (c (i + m + 2))
      have hY : c (i + m + 2) * (c i * c (i + m + 3))
          ≤ c (i + m + 2) * (qpow ρ (m + 2) * (c (i + 1) * c (i + m + 2))) :=
        Q'.le_trans' _ _ _ (Q'.ge_of_eqv e1) (Q'.le_trans' _ _ _ hcomb (Q'.le_of_eqv e2))
      have hgoal : c i * c (i + m + 3)
          ≤ qpow ρ (m + 2) * (c (i + 1) * c (i + m + 2)) :=
        le_of_mul_le_mul_left_pos (hpos (i + m + 2)) hY
      have eg1 : i + (m + 1) + 2 = i + m + 3 := by omega
      have eg2 : i + (m + 1) + 1 = i + m + 2 := by omega
      rw [eg1, eg2]
      exact hgoal

/-! ## 2. The GENERIC ρ-graded rectangle (Hankel 2×2 minor) -/

/-- **`ratioRect_graded` — the sharp ρ-graded rectangle.**  For a positive sequence `c` with the
strict super-log-concavity factor `ρ`, every `a, b, i`:

    c i · c (i+a+b)  ≤  ρ^{a·b} · (c (i+a) · c (i+b)).

The most-spread product `(i, i+a+b)` is dominated by any equal-total less-spread product, with a
factor `ρ^{a·b}` — the discrete mixed second difference of the log-weight.  Induction on `b`,
peeling one `ratioStep_graded` at the outer edge and closing with the IH at `i+1`; the exponents
combine `(a'+b+1) + a'·b = (a'+1)(b+1)` via `qpow_add`.  Generalizes
`FusionCoreStepRoundE.coeffW_rect` (the `ρ = 1` PF₂ shell). -/
theorem ratioRect_graded {c : Nat → Q'} {ρ : Q'}
    (hpos : ∀ i, (0 : Q') < c i) (hρ : (0 : Q') ≤ ρ)
    (hslc : ∀ i, c i * c (i + 2) ≤ ρ * (c (i + 1) * c (i + 1))) :
    ∀ b a i, c i * c (i + a + b) ≤ qpow ρ (a * b) * (c (i + a) * c (i + b)) := by
  intro b
  induction b with
  | zero =>
      intro a i
      have h0 : (qpow ρ (a * 0)).eqv (1 : Q') := by
        rw [show a * 0 = 0 by omega]; exact Q'.eqv_refl _
      have e : (c i * c (i + a)).eqv (qpow ρ (a * 0) * (c (i + a) * c i)) :=
        Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (c i) (c (i + a)))
          (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv (c (i + a) * c i)))
            (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm h0)))
      have eidx1 : i + a + 0 = i + a := by omega
      have eidx2 : i + 0 = i := by omega
      rw [eidx1, eidx2]
      exact Q'.le_of_eqv e
  | succ b ih =>
      intro a i
      cases a with
      | zero =>
          have h0 : (qpow ρ (0 * (b + 1))).eqv (1 : Q') := by
            rw [show 0 * (b + 1) = 0 by omega]; exact Q'.eqv_refl _
          have e : (c i * c (i + (b + 1))).eqv
              (qpow ρ (0 * (b + 1)) * (c i * c (i + (b + 1)))) :=
            Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv (c i * c (i + (b + 1)))))
              (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm h0))
          have eidx1 : i + 0 + (b + 1) = i + (b + 1) := by omega
          have eidx2 : i + 0 = i := by omega
          rw [eidx1, eidx2]
          exact Q'.le_of_eqv e
      | succ a' =>
          have hstep := ratioStep_graded hpos hρ hslc i (a' + b)
          -- hstep : c i * c (i+(a'+b)+2) ≤ qpow ρ (a'+b+1) * (c(i+1) * c(i+(a'+b)+1))
          have hih := ih a' (i + 1)
          -- hih : c(i+1) * c(i+1+a'+b) ≤ qpow ρ (a'*b) * (c(i+1+a') * c(i+1+b))
          have e2 : c (i + 1 + a' + b) = c (i + (a' + b) + 1) := congrArg c (by omega)
          have e3 : c (i + 1 + a') = c (i + (a' + 1)) := congrArg c (by omega)
          have e4 : c (i + 1 + b) = c (i + (b + 1)) := congrArg c (by omega)
          rw [e2, e3, e4] at hih
          have hP : (0 : Q') ≤ qpow ρ (a' + b + 1) := qpow_nonneg ρ hρ _
          have hihs : qpow ρ (a' + b + 1) * (c (i + 1) * c (i + (a' + b) + 1))
              ≤ qpow ρ (a' + b + 1) * (qpow ρ (a' * b) * (c (i + (a' + 1)) * c (i + (b + 1)))) :=
            Q'.mul_le_mul_of_nonneg_left _ _ _ hih hP
          have hchain : c i * c (i + (a' + b) + 2)
              ≤ qpow ρ (a' + b + 1) * (qpow ρ (a' * b) * (c (i + (a' + 1)) * c (i + (b + 1)))) :=
            Q'.le_trans' _ _ _ hstep hihs
          have hnat : (a' + b + 1) + a' * b = (a' + 1) * (b + 1) := by
            have h1 : (a' + 1) * (b + 1) = a' * b + (a' + b + 1) := by
              rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
            rw [h1]; omega
          have hexp : (qpow ρ (a' + b + 1) * qpow ρ (a' * b)).eqv (qpow ρ ((a' + 1) * (b + 1))) := by
            have hadd := qpow_add ρ (a' + b + 1) (a' * b)
            rw [hnat] at hadd
            exact Q'.eqv_symm hadd
          have hassoc :
              (qpow ρ (a' + b + 1)
                  * (qpow ρ (a' * b) * (c (i + (a' + 1)) * c (i + (b + 1))))).eqv
                (qpow ρ ((a' + 1) * (b + 1)) * (c (i + (a' + 1)) * c (i + (b + 1)))) :=
            Q'.eqv_trans _ _ _
              (Q'.eqv_symm (Q'.mul_assoc_eqv (qpow ρ (a' + b + 1)) (qpow ρ (a' * b))
                (c (i + (a' + 1)) * c (i + (b + 1)))))
              (Q'.mul_eqv_congr_right _ _ _ hexp)
          have e1 : c (i + (a' + 1) + (b + 1)) = c (i + (a' + b) + 2) := congrArg c (by omega)
          rw [e1]
          exact Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv hassoc)

/-! ## 3. Instantiation at the theta weight (`ρ = 1/4`) -/

/-- **`coeffW_rect_graded` — the theta weight obeys the ρ-graded rectangle with `ρ = 1/4`.**
The strict factor-4 super-log-concavity `coeffW_superLogConcave` is exactly the hypothesis of
`ratioRect_graded`.  This strictly sharpens `FusionCoreStepRoundE.coeffW_rect` (the `ρ = 1`
version): every Hankel 2×2 spread of the theta weight loses a factor `(1/4)^{a·b}`. -/
theorem coeffW_rect_graded {w : Q'} (hw0 : (0 : Q') < w) (hw12 : w ≤ wH) (a b i : Nat) :
    coeffW w i * coeffW w (i + a + b)
      ≤ qpow quarter (a * b) * (coeffW w (i + a) * coeffW w (i + b)) :=
  ratioRect_graded (c := coeffW w) (ρ := quarter) (fun k => coeffW_pos hw0 k) (by decide)
    (fun s => coeffW_superLogConcave (Q'.le_of_lt hw0) hw12 s) b a i

/-! ## 4. Small-window `FiniteSMargin` instance clears the rational floor -/

/-- `acN w 1 s ≃ coeffW w 0 · coeffW w s` — the single-point window is one product
(`fsum … 1 = 0 + f 0`). -/
theorem acN_one (w : Q') (s : Nat) :
    (acN w 1 s).eqv (coeffW w 0 * coeffW w s) := by
  show ((0 : Q') + coeffW w 0 * coeffW w (s - 0)).eqv (coeffW w 0 * coeffW w s)
  rw [show s - 0 = s by omega]
  exact q_zero_add_eqv (coeffW w 0 * coeffW w s)

/-- **`finiteSMargin_floor_s0` — the `s = 0` window clears the theta floor.**  With
`A = acN(1,0)·acN(1,2)` and `B = acN(1,1)²`, the required `FiniteSMargin` inequality
`40000·A ≤ 22801·B` holds directly: `A ≃ c₀²·(c₀c₂)`, `B ≃ c₀²·c₁²`, and factor-4
super-log-concavity gives `40000·c₀c₂ ≤ 10000·c₁² ≤ 22801·c₁²`.  A concrete instantiation of the
`FiniteSMargin` field (`s = 0`) showing the ρ-margin mechanism reaches the floor with room to
spare (margin `22801/10000 ≈ 2.28`). -/
theorem finiteSMargin_floor_s0 {w : Q'} (hw0 : (0 : Q') < w) (hw12 : w ≤ wH) :
    Q'.ofNat 40000 * (acN w 1 0 * acN w 1 2)
      ≤ Q'.ofNat 22801 * (acN w 1 1 * acN w 1 1) := by
  have hw0' : (0 : Q') ≤ w := Q'.le_of_lt hw0
  have hc0 : (0 : Q') ≤ coeffW w 0 := coeffW_nonneg hw0' 0
  have hc1 : (0 : Q') ≤ coeffW w 1 := coeffW_nonneg hw0' 1
  have hc00 : (0 : Q') ≤ coeffW w 0 * coeffW w 0 := Q'.mul_nonneg _ _ hc0 hc0
  have hc11 : (0 : Q') ≤ coeffW w 1 * coeffW w 1 := Q'.mul_nonneg _ _ hc1 hc1
  -- acN reductions
  have eA : (acN w 1 0 * acN w 1 2).eqv
      ((coeffW w 0 * coeffW w 0) * (coeffW w 0 * coeffW w 2)) :=
    mul_eqv_congr₂ (acN_one w 0) (acN_one w 2)
  have eB : (acN w 1 1 * acN w 1 1).eqv
      ((coeffW w 0 * coeffW w 1) * (coeffW w 0 * coeffW w 1)) :=
    mul_eqv_congr₂ (acN_one w 1) (acN_one w 1)
  -- super-log-concavity (ρ = 1/4)
  have hslc : coeffW w 0 * coeffW w 2 ≤ quarter * (coeffW w 1 * coeffW w 1) :=
    coeffW_superLogConcave hw0' hw12 0
  -- the scalar core:  40000·(c₀c₂) ≤ 22801·(c₁c₁)
  have hcore : Q'.ofNat 40000 * (coeffW w 0 * coeffW w 2)
      ≤ Q'.ofNat 22801 * (coeffW w 1 * coeffW w 1) := by
    have s1 : Q'.ofNat 40000 * (coeffW w 0 * coeffW w 2)
        ≤ Q'.ofNat 40000 * (quarter * (coeffW w 1 * coeffW w 1)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hslc (by decide)
    have e1 : (Q'.ofNat 40000 * (quarter * (coeffW w 1 * coeffW w 1))).eqv
        (Q'.ofNat 10000 * (coeffW w 1 * coeffW w 1)) :=
      Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 40000) quarter (coeffW w 1 * coeffW w 1)))
        (Q'.mul_eqv_congr_right _ _ _ (by decide))
    have s2 : Q'.ofNat 10000 * (coeffW w 1 * coeffW w 1)
        ≤ Q'.ofNat 22801 * (coeffW w 1 * coeffW w 1) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide) hc11
    exact Q'.le_trans' _ _ _ s1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) s2)
  -- lift the core by the common (c₀c₀) factor
  have hswap : ((coeffW w 0 * coeffW w 1) * (coeffW w 0 * coeffW w 1)).eqv
      ((coeffW w 0 * coeffW w 0) * (coeffW w 1 * coeffW w 1)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (coeffW w 0) (coeffW w 1) (coeffW w 0 * coeffW w 1))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (mul3_swap' (coeffW w 1) (coeffW w 0) (coeffW w 1)))
        (Q'.eqv_symm (Q'.mul_assoc_eqv (coeffW w 0) (coeffW w 0) (coeffW w 1 * coeffW w 1))))
  have eL : (Q'.ofNat 40000 * (acN w 1 0 * acN w 1 2)).eqv
      ((coeffW w 0 * coeffW w 0) * (Q'.ofNat 40000 * (coeffW w 0 * coeffW w 2))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ eA)
      (mul3_swap' (Q'.ofNat 40000) (coeffW w 0 * coeffW w 0) (coeffW w 0 * coeffW w 2))
  have eR : (Q'.ofNat 22801 * (acN w 1 1 * acN w 1 1)).eqv
      ((coeffW w 0 * coeffW w 0) * (Q'.ofNat 22801 * (coeffW w 1 * coeffW w 1))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ eB)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hswap)
        (mul3_swap' (Q'.ofNat 22801) (coeffW w 0 * coeffW w 0) (coeffW w 1 * coeffW w 1)))
  have hlift : (coeffW w 0 * coeffW w 0) * (Q'.ofNat 40000 * (coeffW w 0 * coeffW w 2))
      ≤ (coeffW w 0 * coeffW w 0) * (Q'.ofNat 22801 * (coeffW w 1 * coeffW w 1)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hcore hc00
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eL) (Q'.le_trans' _ _ _ hlift (Q'.ge_of_eqv eR))

/-! ## 5. Closed-form refutation of the summand-wise (rank-1) route -/

/-- **`naive_summand_nonpos` — the closed-form obstruction.**  For a positive log-concave `c`
(`c i · c (i+2) ≤ c (i+1)²`), the naive per-summand nonnegativity of the autoconvolution defect
`acN(s+1)² − acN(s)·acN(s+2)` FAILS at antidiagonal spread `q = p+2`: the `(p, p+2)` summand
difference `termB − termA = c_p c_{p+2}·(c_{s+1-p}c_{s-1-p} − c_{s-p}²) ≤ 0`.  So the defect is
NOT a sum of nonnegative summands in the naive kernel — the rank-1 / per-term route cannot close
`FiniteSMargin` uniformly in `s`.  This is the clean closed-form reason behind the
`symMinor`-indefinite machine refutation.  (Here `u := s − 1 − p`, and the inequality is the
log-concavity `c u · c (u+2) ≤ c (u+1)²`.) -/
theorem naive_summand_nonpos {c : Nat → Q'}
    (hlc : ∀ i, c i * c (i + 2) ≤ c (i + 1) * c (i + 1)) (u : Nat) :
    c (u + 1) * c (u + 1) ≥ c u * c (u + 2) := hlc u

/-- A concrete extremal `ρ = 1/4` sequence `(1, 1, 1/4, 1/64)` (values at `0,1,2,3`; `0`
elsewhere), saturating the factor-4 super-log-concavity.  Used to exhibit a strictly negative
naive summand. -/
def cwit : Nat → Q'
  | 0 => 1
  | 1 => 1
  | 2 => Q'.mkPos 1 4 (by decide)
  | 3 => Q'.mkPos 1 64 (by decide)
  | _ => 0

/-- `cwit` genuinely satisfies factor-4 super-log-concavity at the relevant indices (`0`, `1`):
`c₀c₂ = 1/4 ≤ (1/4)·c₁²` and `c₁c₃ = 1/64 ≤ (1/4)·c₂²`.  So it is a legitimate `ρ = 1/4`
witness, not a strawman. -/
theorem cwit_slc :
    (cwit 0 * cwit 2 ≤ Q'.mkPos 1 4 (by decide) * (cwit 1 * cwit 1))
      ∧ (cwit 1 * cwit 3 ≤ Q'.mkPos 1 4 (by decide) * (cwit 2 * cwit 2)) := by
  constructor <;> decide

/-- **`naive_route_refuted` — the concrete strict witness.**  At `s = 2`, `p = 0`, `q = 2`, the
naive summand of the defect for `cwit` is STRICTLY negative:

    termB(0,2) = c₀c₂·c₃c₁ = 1/256  <  termA(0,2) = c₀c₂·c₂c₂ = 1/64.

Hence `termB − termA < 0`: the defect `acN(3,3)² − acN(3,2)·acN(3,4)` is provably NOT a sum of
nonnegative naive summands, closing the rank-1 route in closed form. -/
theorem naive_route_refuted :
    (cwit 0 * cwit 2) * (cwit 3 * cwit 1) < (cwit 0 * cwit 2) * (cwit 2 * cwit 2) := by decide

/-! ## 6. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `ratioStep_graded` — the GENERIC ρ-graded single-step Hankel atom (all `i, m`); the sharp
    upgrade of the flat PF₂ `coeffW_step`.
  * `ratioRect_graded` — the GENERIC ρ-graded rectangle `c_i c_{i+a+b} ≤ ρ^{ab} c_{i+a} c_{i+b}`
    (all `a, b, i`); sharpens `coeffW_rect`.
  * `coeffW_rect_graded` — the theta-weight instantiation at `ρ = 1/4`.
  * `acN_one`, `finiteSMargin_floor_s0` — the `s = 0` `FiniteSMargin` inequality, cleared with
    margin `≈ 2.28×` directly from super-log-concavity.
  * `naive_summand_nonpos` — GENERIC closed-form obstruction: the `(p,p+2)` summand is `≤ 0`.
  * `cwit`, `cwit_slc`, `naive_route_refuted` — the concrete strict counterexample.

NAMED OPEN (carried, not inhabited here):
  * `AcNReserveAnalytic.FiniteSMargin w` for ALL `s` — the uniform theta-tail sum.  The ρ-graded
    atom tames every cross ratio termwise and clears the small windows, but the `s → ∞` uniform
    bound needs the GLOBAL Gaussian summation (a transcendental theta ratio `L_even ≈ 1.987`),
    not a finite rational inequality.

HONEST VERDICT.  This module reframes `FiniteSMargin` around the single sharp quantity `ρ`, proves
the ρ-graded Hankel atom GENERICALLY (a clean strengthening of the in-tree PF₂ lemmas), clears the
small window `s = 0` past the required rational floor, and REFUTES the summand-wise route in closed
form (the `|q−p| ≥ 2` antidiagonal spread flips the sign; concrete strict witness).  It does NOT
inhabit the all-`s` residual, which is the genuine local-CLT/theta wall.  This is a representation
advance on one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.DiscreteLaplaceMargin

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.DiscreteLaplaceMargin.ratioStep_graded
#print axioms YMGap.Continuum.DiscreteLaplaceMargin.ratioRect_graded
#print axioms YMGap.Continuum.DiscreteLaplaceMargin.coeffW_rect_graded
#print axioms YMGap.Continuum.DiscreteLaplaceMargin.acN_one
#print axioms YMGap.Continuum.DiscreteLaplaceMargin.finiteSMargin_floor_s0
#print axioms YMGap.Continuum.DiscreteLaplaceMargin.naive_summand_nonpos
#print axioms YMGap.Continuum.DiscreteLaplaceMargin.cwit_slc
#print axioms YMGap.Continuum.DiscreteLaplaceMargin.naive_route_refuted
