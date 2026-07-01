/-
Track A / R2 — Round H of the fusion box log-concavity node: PINNING the abstract
`CentralAutoconvReserve` residual (Round G) to CONCRETE objects and PROVING the finite
part.  Round G reduced A3 (`StrandReduction.lineSumLogConcave`) to a Type-level structure
`CentralAutoconvReserve w` whose `H0`, `off`, `decomp`, `H0nonneg`, `offNonneg` fields were
ALL abstract free data.  Round H replaces `H0`/`off` by the CONCRETE truncated central
autoconvolution `H0auto` (the `r = 0` shift slice of the antidiagonal line-sum) and its
tail `offAuto` (the `r ≥ 1` shifts), and PROVES `decomp`, `H0nonneg`, `offNonneg` against
the REAL `lineSum (lagCorr w N)` — no longer hypotheses.

# What this module adds (read first — load-bearing honesty)

The antidiagonal line-sum expands as
    lineSum (lagCorr w N) t = Σ_{p=0}^{t} Σ_{r=0}^{nP-1} c_{p+r}·c_{(t−p)+r},   nP = N+1−max(p,t−p),
i.e. a sum over shifts `r` of partial autoconvolutions.  Round H isolates the `r = 0` slice
(the pure central autoconvolution, TRUNCATED by the per-`p` cutoff `min 1 nP`) as `H0auto`
and the `r ≥ 1` remainder as `offAuto`, and closes the split.

ROUND-H DELIVERABLE 1 (the concrete objects + the PROVED finite split).
  * `H0auto` / `offAuto` — the concrete `r = 0` central-autoconvolution slice and its
    `r ≥ 1` tail, as explicit finite `fsum`s of the theta weight `coeffW`.
  * `fsum_split_at` — the generic front/tail `fsum` split `Σ_{k<a+b} f = Σ_{k<a} f +
    Σ_{k<b} f(a+·)` (clean induction on `b`).
  * `decomp_auto` — THE PROVED SPLIT: `lineSum (lagCorr w N) t ≃ H0auto w N t + offAuto w N t`
    for EVERY `N, t` (per-`p` front extraction via `fsum_split_at`, lifted by `fsum_add`).
    This was a HYPOTHESIS (`decomp`) in Round G; here it is a theorem against the real
    line-sum.
  * `H0auto_nonneg`, `offAuto_nonneg` — both slices are `≥ 0` (`coeffW_nonneg`).

ROUND-H DELIVERABLE 2 (the reduction of A3 to the TWO sharp bump inequalities).
  * `AutoconvBumpBounds w` — the sharpened residual: exactly the two remaining
    concrete inequalities, at the pinned constants `ε = 1/15`, `δ = 31/225`:
      - `dominate` : `offAuto ≤ (1/15)·H0auto`   (the geometric shift-tail domination),
      - `reserve`  : `(1+31/225)·H0auto(s)·H0auto(s+2) ≤ H0auto(s+1)²`   (the central-
        autoconvolution log-concavity margin).
    Both are the genuine local-CLT "bump" content, now stated on a CONCRETE object.
  * `reserveOfBumpBounds` — THE ASSEMBLY: a `AutoconvBumpBounds w` witness inhabits the
    full `CentralAutoconvReserve w`, discharging `decomp`/`H0nonneg`/`offNonneg` by the
    proved finite facts and `threshold` by `eps_fifteenth_threshold`.
  * `strandReductionOfBumpBounds`, `s1DominanceOfBumpBounds` — wired through Round G's
    `strandReductionOfReserve` and Round D's `s1DominanceOfStrandReduction`: a bump-bounds
    witness (plus the A1 strand reindex and the per-`N` edge input) yields `S1Dominance N w
    2` for EVERY `N`.

# HONESTY — what is NOT closed

`AutoconvBumpBounds w` is a Type-level NAMED-OPEN structure; it is NOT inhabited here for
general `N`.  Its two fields (`dominate`, `reserve`) are the genuine remaining local-CLT
content — the tail domination and the central-autoconvolution log-concavity margin, now
CONCRETE and sharply quantified, uniform in `s` and in the `N`-truncation.  Round H proves
the finite decomposition and nonnegativity that Round G assumed, shrinking the A3 residual
from "an abstract reserve structure" to "two explicit inequalities on the truncated
autoconvolution".  It does NOT prove those inequalities.  This is a structural sharpening of
one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW`/`fsum`/`lagCorr`/`lineSum` lemmas, finite
`fsum` algebra, `omega` on index identities, and `decide` on closed concrete-rational
facts.  Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.  All
witnesses are `Type`-level data.
-/

import YMGap.Continuum.FusionCoreStepRoundG

namespace YMGap.Continuum.FusionCoreStepRoundH

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionCoreStepRoundG

/-! ## 0. A generic front/tail `fsum` split -/

/-- **`fsum_split_at`** — split a finite sum at index `a`:
`Σ_{k<a+b} f k ≃ (Σ_{k<a} f k) + (Σ_{r<b} f (a+r))`.  Clean induction on `b`. -/
theorem fsum_split_at (f : Nat → Q') (a b : Nat) :
    (fsum f (a + b)).eqv (fsum f a + fsum (fun r => f (a + r)) b) := by
  induction b with
  | zero =>
      -- `a + 0 = a`, `fsum _ 0 = 0`
      exact Q'.eqv_symm (q_add_zero_eqv (fsum f a))
  | succ b ih =>
      show (fsum f (a + b) + f (a + b)).eqv
          (fsum f a + (fsum (fun r => f (a + r)) b + f (a + b)))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (f (a + b)) ih) ?_
      exact Q'.add_assoc_eqv (fsum f a) (fsum (fun r => f (a + r)) b) (f (a + b))

/-! ## 1. The concrete central-autoconvolution slice and its tail -/

/-- The per-pair shift cutoff `nP N t p = N + 1 − max(p, t−p)` (the `r`-range of the strand
correlation `lagCorr w N p (t−p)`). -/
def nP (N t p : Nat) : Nat := N + 1 - Nat.max p (t - p)

/-- The antidiagonal correlation summand `c_{p+r}·c_{(t−p)+r}` (the `r`-th shift term at
antidiagonal position `p` of the line-sum at total `t`). -/
def ccT (w : Q') (t p r : Nat) : Q' := coeffW w (p + r) * coeffW w ((t - p) + r)

/-- **`H0auto` — the concrete truncated central autoconvolution** (the `r = 0` shift slice).
For each `p` it keeps the single `r = 0` term `c_p·c_{t−p}` when the cutoff admits it
(`min 1 nP = 1`), else nothing (`min 1 nP = 0`). -/
def H0auto (w : Q') (N t : Nat) : Q' :=
  fsum (fun p => fsum (ccT w t p) (Nat.min 1 (nP N t p))) (t + 1)

/-- **`offAuto` — the concrete off-central tail** (the `r ≥ 1` shifts). -/
def offAuto (w : Q') (N t : Nat) : Q' :=
  fsum (fun p =>
    fsum (fun r => ccT w t p (Nat.min 1 (nP N t p) + r))
      (nP N t p - Nat.min 1 (nP N t p))) (t + 1)

/-- `lagCorr w N p (t−p)` is definitionally the `ccT`/`nP` correlation sum. -/
theorem lagCorr_ccT (w : Q') (N t p : Nat) :
    lagCorr w N p (t - p) = fsum (ccT w t p) (nP N t p) := rfl

/-! ### 1a. Nonnegativity of both slices -/

/-- `ccT ≥ 0` (product of nonneg theta weights). -/
theorem ccT_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (t p r : Nat) :
    (0 : Q') ≤ ccT w t p r :=
  Q'.mul_nonneg _ _ (coeffW_nonneg hw0 _) (coeffW_nonneg hw0 _)

/-- **`H0auto_nonneg`** — the central slice is `≥ 0`. -/
theorem H0auto_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (N t : Nat) :
    (0 : Q') ≤ H0auto w N t :=
  fsum_nonneg (fun p => fsum_nonneg (fun r => ccT_nonneg hw0 t p r) _) _

/-- **`offAuto_nonneg`** — the off-central tail is `≥ 0`. -/
theorem offAuto_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (N t : Nat) :
    (0 : Q') ≤ offAuto w N t :=
  fsum_nonneg (fun p =>
    fsum_nonneg (fun _ => ccT_nonneg hw0 t p _) _) _

/-! ### 1b. The proved finite decomposition -/

/-- **`decomp_auto` — THE PROVED SHIFT DECOMPOSITION.**  For every `N, t`,

    lineSum (lagCorr w N) t  ≃  H0auto w N t + offAuto w N t.

Per antidiagonal position `p`, the strand correlation `lagCorr w N p (t−p) =
Σ_{r<nP} c_{p+r}c_{(t−p)+r}` splits (`fsum_split_at` at `min 1 nP`) into its `r = 0` head
(kept iff `nP ≥ 1`) and its `r ≥ 1` tail; summing over `p` (`fsum_add`) gives the split.
This was a HYPOTHESIS in Round G; here it is a theorem against the real line-sum. -/
theorem decomp_auto {w : Q'} (N t : Nat) :
    (lineSum (lagCorr w N) t).eqv (H0auto w N t + offAuto w N t) := by
  have key : ∀ p, (lagCorr w N p (t - p)).eqv
      (fsum (ccT w t p) (Nat.min 1 (nP N t p))
        + fsum (fun r => ccT w t p (Nat.min 1 (nP N t p) + r))
            (nP N t p - Nat.min 1 (nP N t p))) := by
    intro p
    have hle : Nat.min 1 (nP N t p) ≤ nP N t p := Nat.min_le_right 1 (nP N t p)
    have hcount :
        Nat.min 1 (nP N t p) + (nP N t p - Nat.min 1 (nP N t p)) = nP N t p := by omega
    have hsplit := fsum_split_at (ccT w t p) (Nat.min 1 (nP N t p))
      (nP N t p - Nat.min 1 (nP N t p))
    rw [hcount] at hsplit
    rw [lagCorr_ccT]
    exact hsplit
  refine Q'.eqv_trans _ _ _ ?_ (fsum_add
    (fun p => fsum (ccT w t p) (Nat.min 1 (nP N t p)))
    (fun p => fsum (fun r => ccT w t p (Nat.min 1 (nP N t p) + r))
        (nP N t p - Nat.min 1 (nP N t p)))
    (t + 1))
  exact fsum_eqv_congr _ _ key (t + 1)

/-! ## 2. The reduction of A3 to the two sharp bump inequalities -/

/-- **`AutoconvBumpBounds w`** — the sharpened A3 residual on the CONCRETE truncated
autoconvolution.  Exactly the two remaining local-CLT "bump" inequalities, at the pinned
constants `ε = 1/15`, `δ = 31/225`:
  * `dominate` — the geometric shift-tail domination `offAuto ≤ (1/15)·H0auto`;
  * `reserve`  — the central-autoconvolution log-concavity margin
    `(1+31/225)·H0auto(s)·H0auto(s+2) ≤ H0auto(s+1)²`.
NAMED-OPEN (never `sorry`); these two are the genuine remaining content, now concrete. -/
structure AutoconvBumpBounds (w : Q') : Type where
  /-- The geometric shift-tail domination (uniform in `N, t`). -/
  dominate : ∀ N t, offAuto w N t ≤ Q'.mkPos 1 15 (by decide) * H0auto w N t
  /-- The central-autoconvolution log-concavity margin (uniform in `N, s`). -/
  reserve : ∀ N s,
    (1 + Q'.mkPos 31 225 (by decide)) * (H0auto w N s * H0auto w N (s + 2))
      ≤ H0auto w N (s + 1) * H0auto w N (s + 1)

/-- **`reserveOfBumpBounds` — THE ASSEMBLY.**  A `AutoconvBumpBounds w` witness inhabits the
full Round-G `CentralAutoconvReserve w`, with `H0`/`off` pinned to the concrete slices,
`decomp`/`H0nonneg`/`offNonneg` discharged by the proved finite facts, `ε = 1/15`,
`δ = 31/225`, and `threshold` by `eps_fifteenth_threshold`. -/
def reserveOfBumpBounds {w : Q'} (hw0 : (0 : Q') ≤ w) (bb : AutoconvBumpBounds w) :
    CentralAutoconvReserve w where
  H0 := H0auto w
  off := offAuto w
  decomp := fun N t => decomp_auto N t
  H0nonneg := fun N t => H0auto_nonneg hw0 N t
  offNonneg := fun N t => offAuto_nonneg hw0 N t
  eps := Q'.mkPos 1 15 (by decide)
  delta := Q'.mkPos 31 225 (by decide)
  epsNonneg := by decide
  threshold := eps_fifteenth_threshold
  dominate := bb.dominate
  reserve := bb.reserve

/-! ## 3. Wiring — a bump-bounds witness drives `S1Dominance` for every `N` -/

/-- **`strandReductionOfBumpBounds`** — with the A1 strand reindex, a bump-bounds witness
yields a full `StrandReduction w`. -/
def strandReductionOfBumpBounds {w : Q'} (hw0 : (0 : Q') ≤ w)
    (reindex : ∀ N t, (boxSum w N t).eqv (lineSum (lagCorr w N) t))
    (bb : AutoconvBumpBounds w) : StrandReduction w :=
  strandReductionOfReserve reindex (reserveOfBumpBounds hw0 bb)

/-- **`s1DominanceOfBumpBounds`** — end-to-end: a bump-bounds witness (plus the A1 strand
reindex and the per-`N` edge input) drives `S1Dominance N w 2` for EVERY `N`, through Round
G's `strandReductionOfReserve` and Round D's `s1DominanceOfStrandReduction`. -/
def s1DominanceOfBumpBounds {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (hwpos : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (reindex : ∀ N t, (boxSum w N t).eqv (lineSum (lagCorr w N) t))
    (bb : AutoconvBumpBounds w) (N : Nat)
    (hedge : bondMovedCoeff N w 2 2 ≤ bondMovedCoeff N w 2 1) :
    YMGap.Continuum.S1Dominance.S1Dominance N w 2 :=
  s1DominanceOfStrandReduction hw0 hw12 hwpos hw1
    (strandReductionOfBumpBounds hw0 reindex bb) N hedge

/-! ## 4. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `fsum_split_at` — the generic front/tail `fsum` split.
  * `H0auto_nonneg`, `offAuto_nonneg` — nonnegativity of both concrete slices.
  * `decomp_auto` — THE finite shift decomposition `lineSum ≃ H0auto + offAuto`, proved
    against the real line-sum (a HYPOTHESIS in Round G).
  * `reserveOfBumpBounds` — the assembly: bump-bounds ⟹ full `CentralAutoconvReserve`,
    with the finite fields discharged.
  * `strandReductionOfBumpBounds`, `s1DominanceOfBumpBounds` — the wiring to `S1Dominance`
    (every `N`).

NAMED OPEN (Type-level structure, never `sorry`):
  * `AutoconvBumpBounds w` — the two remaining sharp inequalities on the CONCRETE truncated
    autoconvolution: the geometric shift-tail domination `offAuto ≤ (1/15)·H0auto` and the
    central-autoconvolution log-concavity margin `(1+31/225)·H0auto(s)·H0auto(s+2) ≤
    H0auto(s+1)²`.  These are the genuine remaining local-CLT content, now concrete and
    sharply quantified, uniform in `s` and the `N`-truncation.

HONEST VERDICT.  Round H PINS the abstract Round-G reserve to the concrete truncated central
autoconvolution `H0auto` and its tail `offAuto`, PROVES the finite decomposition and
nonnegativity that Round G assumed, and reduces A3 to exactly TWO explicit bump inequalities.
It does NOT prove those inequalities.  This is a structural sharpening of one box-level
log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FusionCoreStepRoundH

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundH.fsum_split_at
#print axioms YMGap.Continuum.FusionCoreStepRoundH.H0auto_nonneg
#print axioms YMGap.Continuum.FusionCoreStepRoundH.offAuto_nonneg
#print axioms YMGap.Continuum.FusionCoreStepRoundH.decomp_auto
#print axioms YMGap.Continuum.FusionCoreStepRoundH.reserveOfBumpBounds
#print axioms YMGap.Continuum.FusionCoreStepRoundH.strandReductionOfBumpBounds
#print axioms YMGap.Continuum.FusionCoreStepRoundH.s1DominanceOfBumpBounds
