/-
Track A / R2 — Round E of the fusion box log-concavity node: the HANKEL (rectangle)
log-concavity atom of the theta weight — the single missing analytic lemma that the
truncated-lag-correlation TP₂ residual (A2 = `LagCorrTP2`) consumes — proved
symbolically for all shifts, together with the Cauchy–Binet per-pair minor-product
positivity that is the per-summand content of A2, and an HONEST correction of the A3
typing.

# What this module adds (read first — load-bearing honesty)

`FusionCoreStepRoundD` split the opaque `QuadGershgorinClosure` residual into three
sharply-named pieces — A1 (`reindex`, finite), A2 (`LagCorrTP2`, the analytic core),
A3 (`lineSumLogConcave`, the line-sum log-concavity) — and reduced `A1 + A3 ⟹ closure`.
Round E attacks A2 at its analytic root and audits A3.

ROUND-E DELIVERABLE 1 (the Hankel/rectangle log-concavity atom — PROVED, all shifts).
  * `coeffW_step` — the SINGLE-STEP Hankel log-concavity of the theta weight: for every
    `m`, `i`,
        coeffW w i · coeffW w (i+m+2)  ≤  coeffW w (i+1) · coeffW w (i+m+1).
    This is `coeffW_logConcave` "spread one notch outward" — the inductive backbone of
    total positivity.  PROOF: induction on `m`; the base is `coeffW_logConcave`, the step
    multiplies the induction hypothesis by the boundary factor, applies
    `coeffW_logConcave` at the moving end, and cancels the common positive factor
    (`coeffW_pos` + `le_of_mul_le_mul_left_pos`).  This is the genuinely NEW lemma the
    leads named as missing for A2.
  * `coeffW_rect` — the full RECTANGLE (Hankel `2×2`-minor) log-concavity: for all `a b i`,
        coeffW w i · coeffW w (i+a+b)  ≤  coeffW w (i+a) · coeffW w (i+b).
    The most-spread product is dominated by any less-spread product with the same total
    index.  PROOF: induction on `b`, peeling one `coeffW_step` at the outer edge and
    closing with the induction hypothesis at `i+1`.  This is exactly the statement that
    every Hankel `2×2` minor of `coeffW` is `≤ 0`, i.e. `coeffW` is Pólya-frequency of
    order 2.

ROUND-E DELIVERABLE 2 (the Cauchy–Binet per-summand atom — PROVED).
  * `coeffW_minor` — the Cauchy–Binet matrix-element form: for the strand rows `p, p+a`
    and columns `r, r+b`,
        coeffW w (p+r) · coeffW w ((p+a)+(r+b))  ≤  coeffW w (p+(r+b)) · coeffW w ((p+a)+r),
    i.e. the `2×2` minor of the Hankel matrix `V_{x,y} = coeffW(x+y)` is `≤ 0`.
  * `coeffMinor` / `coeffMinor_nonpos` — that minor in additive (`X + -Y`) form, proved
    `≤ 0`.
  * `coeffMinorProd_nonneg` — the per-PAIR positivity that drives the truncated-lag-
    correlation TP₂: the product of the two Hankel minors (over rows `(p,p+ap)` and
    `(q,q+aq)` sharing columns `(r,r+b)`) is `≥ 0` (two `≤ 0` factors).  This is the exact
    per-summand content of the Cauchy–Binet/Andréief expansion of `LagCorrTP2`; what
    remains genuinely open in A2 is the algebraic Andréief half-sum identity plus the
    `N`-truncation boundary defect (absorbed by `coeffW_superLogConcave`).

ROUND-E DELIVERABLE 3 (line-sum / lag-correlation finite facts — PROVED).
  * `lineSum_nonneg` — the antidiagonal line-sum of the lag-correlation is `≥ 0`.
  * `lagCorr_tp2_diag` — the DEGENERATE TP₂ slice `p = p'` holds with equality
    (commutativity), an honest green sub-case of `LagCorrTP2`.

# HONESTY — what is NOT closed, and a CORRECTION of the A3 typing

A2 (`LagCorrTP2`) is NOT inhabited here for general `N`.  Round E proves its analytic
ATOM (every Hankel `2×2` minor of `coeffW` is `≤ 0`, all shifts) and the per-summand
Cauchy–Binet positivity, leaving the Andréief half-sum identity and the truncation
boundary defect as the residual.

CORRECTION (A3).  The `RoundD` docstring bills A3 (`lineSumLogConcave`) as following from
the bare `LagCorrTP2.tp2` field by "TP₂ ⟹ line-sums are PF₂".  This is FALSE for a merely
TP₂ kernel: the symmetric rank-1 kernel `K(p,q)=f(p)f(q)` with `f=(1,0,1)` is TP₂ (every
`2×2` minor `= 0`), yet its antidiagonal sums `L=(1,0,2,0,1)` satisfy
`L(1)² = 0 < 2 = L(0)·L(2)` — NOT log-concave.  So A3 cannot be discharged from the
opaque `tp2` field alone; it needs the GRAM/TOEPLITZ structure `lagCorr = V Vᵀ` (`V`
Hankel), i.e. the same `coeffW`-Hankel-minor input proved here, not an abstract TP₂
hypothesis.  Round E records this as a sharp reduction: A3's honest seed is the Hankel
log-concavity of `coeffW` (`coeffW_rect`), NOT `LagCorrTP2`.

This is NOT a 4D Yang–Mills mass gap; it is the analytic Hankel-minor atom of one box-
level log-concavity sub-fact, its per-summand Cauchy–Binet positivity, and an honest
correction of the A3 reduction.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW`/`fsum`/`lagCorr` lemmas, the positive-
cancellation lemma `le_of_mul_le_mul_left_pos`, finite inductions, and `omega` on index
identities.  Every load-bearing declaration is gated with `#print axioms`; permitted
output is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no
`sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.FusionCoreStepRoundD
import YMGap.Continuum.FusionResidualBound

namespace YMGap.Continuum.FusionCoreStepRoundE

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.FusionCoreStepRoundD

/-! ## 1. The single-step Hankel log-concavity of the theta weight -/

/-- **`coeffW_step` — single-step Hankel log-concavity.**  For every `m`, `i`,

    coeffW w i · coeffW w (i+m+2)  ≤  coeffW w (i+1) · coeffW w (i+m+1).

`coeffW_logConcave` "spread one notch outward".  Induction on `m`: base is
`coeffW_logConcave`; the step multiplies the IH by the moving boundary factor, applies
`coeffW_logConcave` at the moving end, and cancels the common positive factor. -/
theorem coeffW_step {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) (i : Nat) :
    ∀ m, coeffW w i * coeffW w (i + m + 2) ≤ coeffW w (i + 1) * coeffW w (i + m + 1)
  | 0 => FusionGenFunction.coeffW_logConcave hw0 hw1 i
  | m + 1 => by
      have ih : coeffW w i * coeffW w (i + m + 2)
          ≤ coeffW w (i + 1) * coeffW w (i + m + 1) :=
        coeffW_step hw0 hw1 hwpos i m
      have hlc : coeffW w (i + m + 1) * coeffW w (i + m + 3)
          ≤ coeffW w (i + m + 2) * coeffW w (i + m + 2) :=
        FusionGenFunction.coeffW_logConcave hw0 hw1 (i + m + 1)
      have hz : (0 : Q') ≤ coeffW w (i + m + 3) := coeffW_nonneg hw0 _
      have hB : (0 : Q') ≤ coeffW w (i + 1) := coeffW_nonneg hw0 _
      have hypos : (0 : Q') < coeffW w (i + m + 2) := coeffW_pos hwpos _
      -- step1 : (A·y)·z ≤ (B·x)·z
      have step1 := Q'.mul_le_mul_of_nonneg_right _ _ (coeffW w (i + m + 3)) ih hz
      -- (B·x)·z ≃ B·(x·z)
      have eassoc :=
        Q'.mul_assoc_eqv (coeffW w (i + 1)) (coeffW w (i + m + 1)) (coeffW w (i + m + 3))
      -- step2 : B·(x·z) ≤ B·(y·y)
      have step2 := Q'.mul_le_mul_of_nonneg_left _ _ (coeffW w (i + 1)) hlc hB
      have hcomb : (coeffW w i * coeffW w (i + m + 2)) * coeffW w (i + m + 3)
          ≤ coeffW w (i + 1) * (coeffW w (i + m + 2) * coeffW w (i + m + 2)) :=
        Q'.le_trans' _ _ _ step1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv eassoc) step2)
      -- e1 : (A·y)·z ≃ y·(A·z)
      have e1 : ((coeffW w i * coeffW w (i + m + 2)) * coeffW w (i + m + 3)).eqv
          (coeffW w (i + m + 2) * (coeffW w i * coeffW w (i + m + 3))) := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_assoc_eqv (coeffW w i) (coeffW w (i + m + 2)) (coeffW w (i + m + 3))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (coeffW w i) _ _
            (Q'.mul_comm_eqv (coeffW w (i + m + 2)) (coeffW w (i + m + 3)))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv (coeffW w i) (coeffW w (i + m + 3)) (coeffW w (i + m + 2)))) ?_
        exact Q'.mul_comm_eqv (coeffW w i * coeffW w (i + m + 3)) (coeffW w (i + m + 2))
      -- e2 : B·(y·y) ≃ y·(B·y)
      have e2 : (coeffW w (i + 1) * (coeffW w (i + m + 2) * coeffW w (i + m + 2))).eqv
          (coeffW w (i + m + 2) * (coeffW w (i + 1) * coeffW w (i + m + 2))) := by
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv (coeffW w (i + 1)) (coeffW w (i + m + 2)) (coeffW w (i + m + 2)))) ?_
        exact Q'.mul_comm_eqv (coeffW w (i + 1) * coeffW w (i + m + 2)) (coeffW w (i + m + 2))
      have hY : coeffW w (i + m + 2) * (coeffW w i * coeffW w (i + m + 3))
          ≤ coeffW w (i + m + 2) * (coeffW w (i + 1) * coeffW w (i + m + 2)) :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm e1))
          (Q'.le_trans' _ _ _ hcomb (Q'.le_of_eqv e2))
      exact le_of_mul_le_mul_left_pos hypos hY

/-! ## 2. The rectangle (Hankel `2×2`-minor) log-concavity -/

/-- **`coeffW_rect` — the rectangle Hankel log-concavity.**  For all `a b i`,

    coeffW w i · coeffW w (i+a+b)  ≤  coeffW w (i+a) · coeffW w (i+b).

The most-spread product (extremes `i`, `i+a+b`) is dominated by the less-spread product
with the same index total.  Induction on `b`: peel one `coeffW_step` at the outer edge,
close with the IH at `i+1`.  This is exactly "every Hankel `2×2` minor of `coeffW` is
`≤ 0`" — `coeffW` is Pólya-frequency of order 2. -/
theorem coeffW_rect {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) :
    ∀ b a i, coeffW w i * coeffW w (i + a + b)
      ≤ coeffW w (i + a) * coeffW w (i + b) := by
  intro b
  induction b with
  | zero =>
      intro a i
      exact Q'.le_of_eqv (Q'.mul_comm_eqv (coeffW w i) (coeffW w (i + a)))
  | succ b ih =>
      intro a i
      cases a with
      | zero => exact Q'.le_refl' _
      | succ a' =>
          have hstep := coeffW_step hw0 hw1 hwpos i (a' + b)
          have hih := ih a' (i + 1)
          have e1 : coeffW w (i + (a' + 1) + (b + 1)) = coeffW w (i + (a' + b) + 2) :=
            congrArg (coeffW w) (by omega)
          have e2 : coeffW w (i + 1 + a' + b) = coeffW w (i + (a' + b) + 1) :=
            congrArg (coeffW w) (by omega)
          have e3 : coeffW w (i + 1 + a') = coeffW w (i + (a' + 1)) :=
            congrArg (coeffW w) (by omega)
          have e4 : coeffW w (i + 1 + b) = coeffW w (i + (b + 1)) :=
            congrArg (coeffW w) (by omega)
          rw [e1]
          rw [e2, e3, e4] at hih
          exact Q'.le_trans' _ _ _ hstep hih

/-! ## 3. The Cauchy–Binet per-summand atom -/

/-- **`coeffW_minor` — the Hankel `2×2` minor is `≤ 0`** (Cauchy–Binet matrix-element
form).  For strand rows `p, p+a` and columns `r, r+b`,

    coeffW w (p+r) · coeffW w ((p+a)+(r+b))  ≤  coeffW w (p+(r+b)) · coeffW w ((p+a)+r).

Reindexing of `coeffW_rect` with `i = p+r`, spreads `a` (rows) and `b` (columns). -/
theorem coeffW_minor {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) (p r a b : Nat) :
    coeffW w (p + r) * coeffW w (p + a + (r + b))
      ≤ coeffW w (p + (r + b)) * coeffW w (p + a + r) := by
  have h := coeffW_rect hw0 hw1 hwpos b a (p + r)
  have e1 : coeffW w (p + r + a + b) = coeffW w (p + a + (r + b)) :=
    congrArg (coeffW w) (by omega)
  have e2 : coeffW w (p + r + a) = coeffW w (p + a + r) :=
    congrArg (coeffW w) (by omega)
  have e3 : coeffW w (p + r + b) = coeffW w (p + (r + b)) :=
    congrArg (coeffW w) (by omega)
  rw [e1, e2, e3] at h
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))

/-- The Hankel `2×2` minor of `coeffW` in additive (`X + -Y`) form. -/
def coeffMinor (w : Q') (p a r b : Nat) : Q' :=
  coeffW w (p + r) * coeffW w (p + a + (r + b))
    + -(coeffW w (p + (r + b)) * coeffW w (p + a + r))

/-- `X ≤ Y ⟹ X + -Y ≤ 0`. -/
theorem q_add_neg_nonpos {X Y : Q'} (h : X ≤ Y) : X + -Y ≤ (0 : Q') :=
  Q'.le_trans' _ _ _ (Q'.add_le_add h (Q'.le_refl' (-Y)))
    (Q'.le_of_eqv (Q'.add_neg_self_eqv Y))

/-- **`coeffMinor_nonpos`** — the Hankel minor is `≤ 0` (from `coeffW_minor`). -/
theorem coeffMinor_nonpos {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) (p a r b : Nat) :
    coeffMinor w p a r b ≤ (0 : Q') :=
  q_add_neg_nonpos (coeffW_minor hw0 hw1 hwpos p r a b)

/-- Product of two nonpositive rationals is nonnegative. -/
theorem q_mul_nonpos_nonpos {a b : Q'} (ha : a ≤ (0 : Q')) (hb : b ≤ (0 : Q')) :
    (0 : Q') ≤ a * b := by
  have hna : (0 : Q') ≤ -a :=
    Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le ha) (Q'.le_of_eqv (q_zero_add_eqv (-a)))
  have hnb : (0 : Q') ≤ -b :=
    Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le hb) (Q'.le_of_eqv (q_zero_add_eqv (-b)))
  have h := Q'.mul_nonneg _ _ hna hnb
  have e : ((-a) * (-b)).eqv (a * b) :=
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv a (-b))
      (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv a b))
        (Q'.neg_neg_eqv (a * b)))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv e)

/-- **`coeffMinorProd_nonneg` — the Cauchy–Binet per-pair positivity.**  The product of
the two Hankel `2×2` minors (rows `(p, p+ap)` and `(q, q+aq)` sharing the column pair
`(r, r+b)`) is `≥ 0`: two `≤ 0` factors.  This is the exact per-summand content of the
Andréief expansion of the truncated-lag-correlation TP₂ residual `LagCorrTP2`. -/
theorem coeffMinorProd_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) (p ap q aq r b : Nat) :
    (0 : Q') ≤ coeffMinor w p ap r b * coeffMinor w q aq r b :=
  q_mul_nonpos_nonpos (coeffMinor_nonpos hw0 hw1 hwpos p ap r b)
    (coeffMinor_nonpos hw0 hw1 hwpos q aq r b)

/-! ## 4. Line-sum / lag-correlation finite facts -/

/-- **`lineSum_nonneg`** — the antidiagonal line-sum of the lag-correlation is `≥ 0`. -/
theorem lineSum_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (N t : Nat) :
    (0 : Q') ≤ lineSum (lagCorr w N) t := by
  unfold lineSum
  exact fsum_nonneg (fun p => lagCorr_nonneg hw0 N p (t - p)) _

/-- **`lagCorr_tp2_diag` — the degenerate TP₂ slice `p = p'`.**  With equal rows the
`LagCorrTP2` inequality holds with equality (commutativity), an honest green sub-case of
the analytic core A2. -/
theorem lagCorr_tp2_diag (w : Q') (N p q q' : Nat) :
    lagCorr w N p q' * lagCorr w N p q ≤ lagCorr w N p q * lagCorr w N p q' :=
  Q'.le_of_eqv (Q'.mul_comm_eqv _ _)

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `coeffW_step` — single-step Hankel log-concavity of `coeffW` (all `m`, `i`).
  * `coeffW_rect` — the rectangle Hankel `2×2`-minor log-concavity (all `a`, `b`, `i`);
    `coeffW` is Pólya-frequency of order 2.  THE analytic atom A2 was missing.
  * `coeffW_minor`, `coeffMinor`, `coeffMinor_nonpos` — the Cauchy–Binet matrix-element
    form: every Hankel minor of the theta weight is `≤ 0`.
  * `coeffMinorProd_nonneg` — the per-pair Cauchy–Binet positivity (product of two
    minors `≥ 0`): the per-summand content of `LagCorrTP2`.
  * `lineSum_nonneg`, `lagCorr_tp2_diag` — finite line-sum / lag-correlation facts and the
    degenerate `p = p'` TP₂ slice.
  * helpers `q_add_neg_nonpos`, `q_mul_nonpos_nonpos`.

NAMED OPEN (carried from `RoundD`, not inhabited here):
  * `LagCorrTP2 w` (A2) — full TP₂ of the TRUNCATED lag-correlation.  Round E supplies its
    analytic atom (`coeffW_rect`) and per-summand positivity (`coeffMinorProd_nonneg`);
    what remains is the Andréief half-sum identity for the common-range part plus the
    `N`-truncation boundary defect (absorbed by `coeffW_superLogConcave`).
  * `StrandReduction w` (A1 `reindex` + A3 `lineSumLogConcave`).  CORRECTION: A3 does NOT
    follow from the bare `LagCorrTP2.tp2` field (rank-1 `f=(1,0,1)` counterexample,
    `L=(1,0,2,0,1)`); its honest seed is the Gram/Hankel log-concavity of `coeffW`
    (`coeffW_rect`), proved here.

HONEST VERDICT.  Round E proves the missing analytic atom of A2 — every Hankel `2×2`
minor of the theta weight is `≤ 0` (`coeffW` is PF₂), for all shifts — and the per-pair
Cauchy–Binet positivity that is the per-summand content of the truncated-lag-correlation
TP₂, and CORRECTS the A3 reduction (the bare TP₂ field is insufficient; the Hankel
structure proved here is the right seed).  It does NOT inhabit `LagCorrTP2`,
`StrandReduction`, `QuadGershgorinClosure`, or `S1Dominance` for general `N`.  This is a
structural advance on one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills
mass gap. -/

end YMGap.Continuum.FusionCoreStepRoundE

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundE.coeffW_step
#print axioms YMGap.Continuum.FusionCoreStepRoundE.coeffW_rect
#print axioms YMGap.Continuum.FusionCoreStepRoundE.coeffW_minor
#print axioms YMGap.Continuum.FusionCoreStepRoundE.coeffMinor_nonpos
#print axioms YMGap.Continuum.FusionCoreStepRoundE.q_mul_nonpos_nonpos
#print axioms YMGap.Continuum.FusionCoreStepRoundE.coeffMinorProd_nonneg
#print axioms YMGap.Continuum.FusionCoreStepRoundE.lineSum_nonneg
#print axioms YMGap.Continuum.FusionCoreStepRoundE.lagCorr_tp2_diag
