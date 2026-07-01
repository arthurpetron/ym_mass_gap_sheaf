/-
Track A / R2 — Round I of the fusion box log-concavity node: CLOSING the geometric
shift-tail DOMINATION field of Round H's `AutoconvBumpBounds`, and REDUCING the two-field
residual to the single RESERVE field.

# What this module adds (read first — load-bearing honesty)

Round H reduced A3 (`StrandReduction.lineSumLogConcave`) to `AutoconvBumpBounds w`, whose
TWO fields are the genuine local-CLT "bump" content on the CONCRETE truncated central
autoconvolution:
  * `dominate` : `offAuto w N t ≤ (1/15)·H0auto w N t`   (the geometric shift-tail),
  * `reserve`  : `(1+31/225)·H0auto(s)·H0auto(s+2) ≤ H0auto(s+1)²`  (the log-concavity margin).

Round I PROVES the `dominate` field OUTRIGHT — for every `N, t`, uniformly, from the all-`s`
geometric ratio reserve `4·c_{s+1} ≤ c_s` (`coeffW_ratio_quarter`, Round G) — and reduces
`AutoconvBumpBounds` to a ONE-field residual `AutoconvReserveResidual` (just `reserve`).

ROUND-I DELIVERABLE 1 (the geometric-tail engine — PROVED, pure `Q'`/`Nat`).
  * `geoPow r n` — the explicit `r^n` power (`geoPow r 0 = 1`, `geoPow r (n+1) = r·geoPow r n`).
  * `quarter_of_four_le` — `4·x ≤ y ⟹ x ≤ (1/4)·y` (cancel the factor 4).
  * `leg_geo` — the per-leg geometric decay `c_{k+n} ≤ (1/4)^n·c_k` (induction on `n` off
    `coeffW_ratio_quarter`).  This is the `ρ ≤ 1/4` backbone at the coefficient level.
  * `geoPow_quarter_sq` — `(1/4)^n·(1/4)^n ≃ (1/16)^n` (the two-leg combine).
  * `ccT_geo` — the per-term two-leg bound `ccT t p σ ≤ (1/16)^σ·ccT t p 0`
    (`prod_le_prod` on the two legs + the square combine).
  * `geoSum_inv` — the EXACT finite geometric telescoping `Σ_{r<M}(1/16)^r + (16/15)·(1/16)^M
    ≃ 16/15`; hence `geoTail_le : Σ_{r<M}(1/16)^r ≤ 16/15` and `geoShiftTail_le :
    Σ_{r<M}(1/16)^{r+1} ≤ 1/15`.

ROUND-I DELIVERABLE 2 (the domination field — PROVED, uniform in `N, t`).
  * `off_slice_le` — the per-antidiagonal-position bound `offSlice p ≤ (1/15)·H0Slice p`
    (case split on the cutoff `nP`: both slices vanish when `nP = 0`; the geometric tail
    when `nP ≥ 1`).
  * `offAuto_dominate` — THE FIELD: `offAuto w N t ≤ (1/15)·H0auto w N t` for every `N, t`
    (`fsum` monotonicity + scalar pull-out over `off_slice_le`).

ROUND-I DELIVERABLE 3 (the one-field reduction — REDUCTION).
  * `AutoconvReserveResidual w` — the SOLE remaining sharp inequality: the reserve
    `(1+31/225)·H0auto(s)·H0auto(s+2) ≤ H0auto(s+1)²`.
  * `bumpBoundsOfReserve` — a reserve residual inhabits the full Round-H
    `AutoconvBumpBounds w` (its `dominate` field discharged by `offAuto_dominate`).
  * `centralReserveOfResidual`, `s1DominanceOfResidual` — wired through Round H:
    reserve residual (plus the A1 strand reindex + per-`N` edge input) drives
    `CentralAutoconvReserve` and `S1Dominance N w 2` for every `N`.

# HONESTY — what is NOT closed

The `reserve` field remains NAMED-OPEN (`AutoconvReserveResidual`, never `sorry`): it is the
genuine local-CLT central-autoconvolution log-concavity margin `δ ≥ 31/225`, which — as the
Round-H analysis records — consumes `coeffW`'s STRICT super-log-concavity (plain geometric
ratio-`1/4` coefficients give only `≈ 9/8 < 256/225`, so factor-1 log-concavity is provably
insufficient).  Round I does NOT prove it.  The A1 strand reindex (`reindex`) also remains a
threaded hypothesis.  What Round I DOES close is the `dominate` field in full and the
reduction of the two-field bump residual to the single reserve inequality.  This is a
structural sharpening of one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills
mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW`/`fsum`/`H0auto`/`offAuto` lemmas, finite
inductions, `Nat.min`/`omega` on the cutoff, and `decide` on closed concrete-rational facts.
Every load-bearing declaration is gated with `#print axioms`; permitted output is `propext` /
`Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses are
`Type`-level data.
-/

import YMGap.Continuum.FusionCoreStepRoundH

namespace YMGap.Continuum.FusionCoreStepRoundI

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionPositivity
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionCoreStepRoundG
open YMGap.Continuum.FusionCoreStepRoundH

/-! ## 0. The pinned geometric constants -/

/-- The per-leg decay ratio `1/4`. -/
abbrev qq4 : Q' := Q'.mkPos 1 4 (by decide)
/-- The two-leg (per-term) decay ratio `1/16`. -/
abbrev qq16 : Q' := Q'.mkPos 1 16 (by decide)
/-- The domination constant `ε = 1/15`. -/
abbrev qq15 : Q' := Q'.mkPos 1 15 (by decide)
/-- The full geometric-series bound `16/15 = Σ_{r≥0}(1/16)^r`. -/
abbrev qq1615 : Q' := Q'.mkPos 16 15 (by decide)

/-! ## 1. The explicit power `r^n` -/

/-- `geoPow r n = r^n` (`geoPow r 0 = 1`, `geoPow r (n+1) = r·geoPow r n`). -/
def geoPow (r : Q') : Nat → Q'
  | 0 => 1
  | (n + 1) => r * geoPow r n

/-- Powers of a nonneg base are nonneg. -/
theorem geoPow_nonneg {r : Q'} (hr : (0 : Q') ≤ r) (n : Nat) : (0 : Q') ≤ geoPow r n := by
  induction n with
  | zero => show (0 : Q') ≤ (1 : Q'); decide
  | succ n ih => exact Q'.mul_nonneg _ _ hr ih

/-! ## 2. The per-leg geometric decay -/

/-- **`quarter_of_four_le`** — cancel a factor 4: `4·x ≤ y ⟹ x ≤ (1/4)·y`. -/
theorem quarter_of_four_le {x y : Q'} (h : (4 : Q') * x ≤ y) : x ≤ qq4 * y := by
  have hnn : (0 : Q') ≤ qq4 := by decide
  have hstep : qq4 * ((4 : Q') * x) ≤ qq4 * y :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h hnn
  have e : (qq4 * ((4 : Q') * x)).eqv x := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv qq4 (4 : Q') x)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (qq4 * (4 : Q')) 1 x (by decide)) ?_
    exact Q'.one_mul_eqv x
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv e) hstep

/-- **`leg_geo`** — the per-leg geometric decay `c_{k+n} ≤ (1/4)^n·c_k` on `0 < w ≤ 1/2`.
Induction on `n` from `coeffW_ratio_quarter`. -/
theorem leg_geo {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (hwpos : (0 : Q') < w)
    (k : Nat) : ∀ n, coeffW w (k + n) ≤ geoPow qq4 n * coeffW w k := by
  intro n
  induction n with
  | zero =>
      show coeffW w k ≤ geoPow qq4 0 * coeffW w k
      exact Q'.ge_of_eqv (Q'.one_mul_eqv (coeffW w k))
  | succ n ih =>
      have hr := coeffW_ratio_quarter hw0 hw12 hwpos (k + n)
      have hq : coeffW w ((k + n) + 1) ≤ qq4 * coeffW w (k + n) := quarter_of_four_le hr
      have hstep : qq4 * coeffW w (k + n) ≤ qq4 * (geoPow qq4 n * coeffW w k) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ ih (by decide)
      have e : (qq4 * (geoPow qq4 n * coeffW w k)).eqv (geoPow qq4 (n + 1) * coeffW w k) :=
        Q'.eqv_symm (Q'.mul_assoc_eqv qq4 (geoPow qq4 n) (coeffW w k))
      show coeffW w (k + (n + 1)) ≤ geoPow qq4 (n + 1) * coeffW w k
      exact Q'.le_trans' _ _ _ hq (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv e))

/-- **`geoPow_quarter_sq`** — the two-leg square combine `(1/4)^n·(1/4)^n ≃ (1/16)^n`. -/
theorem geoPow_quarter_sq (n : Nat) :
    (geoPow qq4 n * geoPow qq4 n).eqv (geoPow qq16 n) := by
  induction n with
  | zero => show ((1 : Q') * 1).eqv 1; decide
  | succ n ih =>
      show ((qq4 * geoPow qq4 n) * (qq4 * geoPow qq4 n)).eqv (qq16 * geoPow qq16 n)
      refine Q'.eqv_trans _ _ _ (mul_swap4 qq4 (geoPow qq4 n) qq4 (geoPow qq4 n)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (qq4 * qq4) qq16 (geoPow qq4 n * geoPow qq4 n) (by decide)) ?_
      exact Q'.mul_eqv_congr_left qq16 _ _ ih

/-- **`ccT_geo`** — the per-term two-leg geometric bound `ccT t p σ ≤ (1/16)^σ·ccT t p 0`. -/
theorem ccT_geo {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (hwpos : (0 : Q') < w)
    (t p σ : Nat) : ccT w t p σ ≤ geoPow qq16 σ * ccT w t p 0 := by
  have hleg1 : coeffW w (p + σ) ≤ geoPow qq4 σ * coeffW w p := leg_geo hw0 hw12 hwpos p σ
  have hleg2 : coeffW w ((t - p) + σ) ≤ geoPow qq4 σ * coeffW w (t - p) :=
    leg_geo hw0 hw12 hwpos (t - p) σ
  have hy0 : (0 : Q') ≤ coeffW w ((t - p) + σ) := coeffW_nonneg hw0 _
  have hX : (0 : Q') ≤ geoPow qq4 σ * coeffW w p :=
    Q'.mul_nonneg _ _ (geoPow_nonneg (by decide) σ) (coeffW_nonneg hw0 _)
  have hprod : ccT w t p σ
      ≤ (geoPow qq4 σ * coeffW w p) * (geoPow qq4 σ * coeffW w (t - p)) :=
    prod_le_prod hleg1 hleg2 hy0 hX
  have eswap : ((geoPow qq4 σ * coeffW w p) * (geoPow qq4 σ * coeffW w (t - p))).eqv
      ((geoPow qq4 σ * geoPow qq4 σ) * (coeffW w p * coeffW w (t - p))) :=
    mul_swap4 (geoPow qq4 σ) (coeffW w p) (geoPow qq4 σ) (coeffW w (t - p))
  have esq : ((geoPow qq4 σ * geoPow qq4 σ) * (coeffW w p * coeffW w (t - p))).eqv
      (geoPow qq16 σ * (coeffW w p * coeffW w (t - p))) :=
    Q'.mul_eqv_congr_right _ _ _ (geoPow_quarter_sq σ)
  exact Q'.le_trans' _ _ _ hprod
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv eswap) (Q'.le_of_eqv esq))

/-! ## 3. The finite geometric telescoping tail -/

/-- **`geoSum_inv`** — the EXACT finite geometric telescoping identity
`Σ_{r<M}(1/16)^r + (16/15)·(1/16)^M ≃ 16/15`.  Induction on `M`. -/
theorem geoSum_inv (M : Nat) :
    (fsum (geoPow qq16) M + qq1615 * geoPow qq16 M).eqv qq1615 := by
  induction M with
  | zero =>
      show ((0 : Q') + qq1615 * (1 : Q')).eqv qq1615
      decide
  | succ M ih =>
      show ((fsum (geoPow qq16) M + geoPow qq16 M) + qq1615 * (qq16 * geoPow qq16 M)).eqv qq1615
      have hcqg : (qq1615 * (qq16 * geoPow qq16 M)).eqv (qq15 * geoPow qq16 M) := by
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv qq1615 qq16 (geoPow qq16 M))) ?_
        exact Q'.mul_eqv_congr_right (qq1615 * qq16) qq15 (geoPow qq16 M) (by decide)
      have hgg : (geoPow qq16 M + qq15 * geoPow qq16 M).eqv (qq1615 * geoPow qq16 M) := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right (geoPow qq16 M) ((1 : Q') * geoPow qq16 M)
            (qq15 * geoPow qq16 M) (Q'.eqv_symm (Q'.one_mul_eqv (geoPow qq16 M)))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.add_mul_eqv (1 : Q') qq15 (geoPow qq16 M))) ?_
        exact Q'.mul_eqv_congr_right ((1 : Q') + qq15) qq1615 (geoPow qq16 M) (by decide)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (fsum (geoPow qq16) M + geoPow qq16 M)
          (qq1615 * (qq16 * geoPow qq16 M)) (qq15 * geoPow qq16 M) hcqg) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (fsum (geoPow qq16) M) (geoPow qq16 M) (qq15 * geoPow qq16 M)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (fsum (geoPow qq16) M)
          (geoPow qq16 M + qq15 * geoPow qq16 M) (qq1615 * geoPow qq16 M) hgg) ?_
      exact ih

/-- **`geoTail_le`** — `Σ_{r<M}(1/16)^r ≤ 16/15` (drop the nonneg telescoping remainder). -/
theorem geoTail_le (M : Nat) : fsum (geoPow qq16) M ≤ qq1615 := by
  have hnn : (0 : Q') ≤ qq1615 * geoPow qq16 M :=
    Q'.mul_nonneg _ _ (by decide) (geoPow_nonneg (by decide) M)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (fsum (geoPow qq16) M) (qq1615 * geoPow qq16 M) hnn)
    (Q'.le_of_eqv (geoSum_inv M))

/-- **`geoShiftTail_le`** — the shifted tail `Σ_{r<M}(1/16)^{r+1} ≤ 1/15`. -/
theorem geoShiftTail_le (M : Nat) : fsum (fun r => geoPow qq16 (r + 1)) M ≤ qq15 := by
  have e1 : (fsum (fun r => geoPow qq16 (r + 1)) M).eqv (qq16 * fsum (geoPow qq16) M) :=
    Q'.eqv_symm (fsum_const_mul qq16 (geoPow qq16) M)
  have h2 : qq16 * fsum (geoPow qq16) M ≤ qq16 * qq1615 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (geoTail_le M) (by decide)
  have e3 : (qq16 * qq1615).eqv qq15 := by decide
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1)
    (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv e3))

/-! ## 4. The domination field -/

/-- **`off_slice_le`** — the per-antidiagonal-position domination
`offSlice p ≤ (1/15)·H0Slice p`.  Case split on the cutoff `nP N t p`: when `nP = 0` both
slices are the empty sum `0`; when `nP ≥ 1` the head is the single `r = 0` term and the tail
is the geometric shift-tail dominated by `1/15` of it. -/
theorem off_slice_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (hwpos : (0 : Q') < w)
    (N t p : Nat) :
    fsum (fun r => ccT w t p (Nat.min 1 (nP N t p) + r)) (nP N t p - Nat.min 1 (nP N t p))
      ≤ qq15 * fsum (ccT w t p) (Nat.min 1 (nP N t p)) := by
  rcases Nat.eq_zero_or_pos (nP N t p) with hK0 | hKpos
  · rw [hK0]
    have hmin : Nat.min 1 0 = 0 := by decide
    rw [hmin]
    show (0 : Q') ≤ qq15 * fsum (ccT w t p) 0
    exact Q'.mul_nonneg _ _ (by decide) (fsum_nonneg (fun i => ccT_nonneg hw0 t p i) 0)
  · have hmin : Nat.min 1 (nP N t p) = 1 := Nat.min_eq_left hKpos
    rw [hmin]
    have hterm : ∀ r, ccT w t p (1 + r) ≤ geoPow qq16 (r + 1) * ccT w t p 0 := by
      intro r
      have h := ccT_geo hw0 hw12 hwpos t p (1 + r)
      have e : geoPow qq16 (1 + r) = geoPow qq16 (r + 1) := by rw [Nat.add_comm 1 r]
      rw [e] at h
      exact h
    have hmono : fsum (fun r => ccT w t p (1 + r)) (nP N t p - 1)
        ≤ fsum (fun r => geoPow qq16 (r + 1) * ccT w t p 0) (nP N t p - 1) :=
      fsum_mono hterm (nP N t p - 1)
    have epull : (fsum (fun r => geoPow qq16 (r + 1) * ccT w t p 0) (nP N t p - 1)).eqv
        (fsum (fun r => geoPow qq16 (r + 1)) (nP N t p - 1) * ccT w t p 0) :=
      Q'.eqv_symm (fsum_mul_const (fun r => geoPow qq16 (r + 1)) (ccT w t p 0) (nP N t p - 1))
    have hstep : fsum (fun r => geoPow qq16 (r + 1)) (nP N t p - 1) * ccT w t p 0
        ≤ qq15 * ccT w t p 0 :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ (geoShiftTail_le (nP N t p - 1))
        (ccT_nonneg hw0 t p 0)
    have efs1 : (qq15 * ccT w t p 0).eqv (qq15 * fsum (ccT w t p) 1) :=
      Q'.mul_eqv_congr_left qq15 (ccT w t p 0) (fsum (ccT w t p) 1)
        (Q'.eqv_symm (q_zero_add_eqv (ccT w t p 0)))
    exact Q'.le_trans' _ _ _ hmono
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv epull)
        (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv efs1)))

/-- **`offAuto_dominate` — THE DOMINATION FIELD (PROVED).**  For every `N, t`,

    offAuto w N t  ≤  (1/15)·H0auto w N t.

`fsum` monotonicity over `off_slice_le`, then scalar pull-out (`fsum_const_mul`). -/
theorem offAuto_dominate {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (hwpos : (0 : Q') < w)
    (N t : Nat) : offAuto w N t ≤ qq15 * H0auto w N t := by
  have hmono : offAuto w N t
      ≤ fsum (fun p => qq15 * fsum (ccT w t p) (Nat.min 1 (nP N t p))) (t + 1) :=
    fsum_mono (fun p => off_slice_le hw0 hw12 hwpos N t p) (t + 1)
  have epull : (fsum (fun p => qq15 * fsum (ccT w t p) (Nat.min 1 (nP N t p))) (t + 1)).eqv
      (qq15 * H0auto w N t) :=
    Q'.eqv_symm
      (fsum_const_mul qq15 (fun p => fsum (ccT w t p) (Nat.min 1 (nP N t p))) (t + 1))
  exact Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv epull)

/-! ## 5. The one-field reduction of `AutoconvBumpBounds` -/

/-- **`AutoconvReserveResidual w`** — the SOLE remaining sharp inequality of the bump
residual after Round I closes `dominate`: the central-autoconvolution log-concavity margin
`(1+31/225)·H0auto(s)·H0auto(s+2) ≤ H0auto(s+1)²`.  NAMED-OPEN (never `sorry`); it is the
genuine local-CLT reserve consuming `coeffW`'s STRICT super-log-concavity. -/
structure AutoconvReserveResidual (w : Q') : Type where
  /-- The central-autoconvolution log-concavity margin (uniform in `N, s`). -/
  reserve : ∀ N s,
    (1 + Q'.mkPos 31 225 (by decide)) * (H0auto w N s * H0auto w N (s + 2))
      ≤ H0auto w N (s + 1) * H0auto w N (s + 1)

/-- **`bumpBoundsOfReserve` — THE ONE-FIELD REDUCTION.**  A reserve residual inhabits the
full Round-H `AutoconvBumpBounds w`: the `dominate` field is discharged by `offAuto_dominate`
(this round), the `reserve` field is carried through. -/
def bumpBoundsOfReserve {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (hwpos : (0 : Q') < w)
    (rr : AutoconvReserveResidual w) : AutoconvBumpBounds w where
  dominate := fun N t => offAuto_dominate hw0 hw12 hwpos N t
  reserve := rr.reserve

/-- **`centralReserveOfResidual`** — the reserve residual inhabits Round G's full
`CentralAutoconvReserve w` (its finite fields + the now-proved domination all discharged). -/
def centralReserveOfResidual {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (hwpos : (0 : Q') < w) (rr : AutoconvReserveResidual w) : CentralAutoconvReserve w :=
  reserveOfBumpBounds hw0 (bumpBoundsOfReserve hw0 hw12 hwpos rr)

/-- **`s1DominanceOfResidual` — end-to-end.**  The reserve residual (plus the A1 strand
reindex and the per-`N` edge input) drives `S1Dominance N w 2` for EVERY `N`, with the
`dominate` field now internally discharged. -/
def s1DominanceOfResidual {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (hwpos : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (reindex : ∀ N t, (boxSum w N t).eqv (lineSum (lagCorr w N) t))
    (rr : AutoconvReserveResidual w) (N : Nat)
    (hedge : bondMovedCoeff N w 2 2 ≤ bondMovedCoeff N w 2 1) :
    YMGap.Continuum.S1Dominance.S1Dominance N w 2 :=
  s1DominanceOfBumpBounds hw0 hw12 hwpos hw1 reindex
    (bumpBoundsOfReserve hw0 hw12 hwpos rr) N hedge

/-! ## 6. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `geoPow`, `geoPow_nonneg`, `quarter_of_four_le`, `leg_geo`, `geoPow_quarter_sq`,
    `ccT_geo` — the per-term geometric-tail engine.
  * `geoSum_inv`, `geoTail_le`, `geoShiftTail_le` — the exact finite geometric telescoping.
  * `off_slice_le` — the per-antidiagonal-position domination.
  * `offAuto_dominate` — THE DOMINATION FIELD `offAuto ≤ (1/15)·H0auto`, uniform in `N, t`.
  * `bumpBoundsOfReserve` — the one-field reduction (`dominate` discharged).
  * `centralReserveOfResidual`, `s1DominanceOfResidual` — the wiring to
    `CentralAutoconvReserve` and `S1Dominance` (every `N`).

NAMED OPEN (Type-level structure, never `sorry`):
  * `AutoconvReserveResidual w` — the SOLE remaining sharp inequality: the central-
    autoconvolution log-concavity margin `(1+31/225)·H0auto(s)·H0auto(s+2) ≤ H0auto(s+1)²`.
    This is the genuine local-CLT reserve consuming `coeffW`'s strict super-log-concavity.
  * the A1 strand reindex `reindex` remains a threaded hypothesis.

HONEST VERDICT.  Round I PROVES the geometric shift-tail domination field of Round H's
`AutoconvBumpBounds` outright — for every `N, t`, uniformly — and reduces the two-field bump
residual to the SINGLE reserve inequality.  It does NOT prove the reserve.  This is a
structural sharpening of one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass
gap. -/

end YMGap.Continuum.FusionCoreStepRoundI

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundI.quarter_of_four_le
#print axioms YMGap.Continuum.FusionCoreStepRoundI.leg_geo
#print axioms YMGap.Continuum.FusionCoreStepRoundI.geoPow_quarter_sq
#print axioms YMGap.Continuum.FusionCoreStepRoundI.ccT_geo
#print axioms YMGap.Continuum.FusionCoreStepRoundI.geoSum_inv
#print axioms YMGap.Continuum.FusionCoreStepRoundI.geoTail_le
#print axioms YMGap.Continuum.FusionCoreStepRoundI.geoShiftTail_le
#print axioms YMGap.Continuum.FusionCoreStepRoundI.off_slice_le
#print axioms YMGap.Continuum.FusionCoreStepRoundI.offAuto_dominate
#print axioms YMGap.Continuum.FusionCoreStepRoundI.bumpBoundsOfReserve
#print axioms YMGap.Continuum.FusionCoreStepRoundI.centralReserveOfResidual
#print axioms YMGap.Continuum.FusionCoreStepRoundI.s1DominanceOfResidual
