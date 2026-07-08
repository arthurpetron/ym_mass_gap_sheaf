/-
Track A / R2 — LOCAL-CLT STEEPEST-DESCENT step for the central-autoconvolution reserve.

# What this module adds (read first — load-bearing honesty)

Round I reduced Round H's `AutoconvBumpBounds` to the SINGLE open field
`AutoconvReserveResidual.reserve`,

    (1 + 31/225)·H0auto(s)·H0auto(s+2)  ≤  H0auto(s+1)²        (uniform in `N, s`),

and Round J supplied the DIAGONAL `(3/4)` minor reserve while MACHINE-CHECKING that the
symmetrized off-diagonal Menon minor `symMinor(m,n) = 2c_{m+1}c_{n+1} − c_m c_{n+2} − c_n c_{m+2}`
is NOT sign-definite: it is strictly negative at `(m,n) = (0,2)` (spread `|m−n| = 2`).  Round J
concluded the reserve is not a sum of manifestly nonnegative summands but needs an AGGREGATE
cancellation.

This module sharpens that picture in two honest, axiom-clean directions.

DELIVERABLE 1 (the ADJACENT-BAND nonnegativity — PROVED, all `m`).  The symmetrized
off-diagonal minor `symMinor` is NONNEGATIVE on the diagonal and the FIRST off-diagonal band,
uniform in `m`:
  * `symMinor_symm`      — `symMinor(m,n) ≃ symMinor(n,m)` (the minor is symmetric).
  * `symMinor_diag_nonneg` — `0 ≤ symMinor(m,m)` (twice the log-concavity minor).
  * `symMinor_adj_nonneg`  — `0 ≤ symMinor(m,m+1)` from the Hankel rectangle `coeffW_rect`
    (`c_m c_{m+3} ≤ c_{m+1} c_{m+2}`).
  * `symMinor_adj_nonneg'` — `0 ≤ symMinor(m+1,m)` (symmetry).
This LOCATES the indefiniteness EXACTLY: `symMinor` is `≥ 0` for `|m−n| ≤ 1` and can be `< 0`
only from spread `|m−n| ≥ 2` (Round J's witness is `|m−n| = 2`).  The Gershgorin/aggregate
argument therefore only has to dominate the `|m−n| ≥ 2` block — the strictly-decaying tail.
  * `symMinor_lower_env` — `−(c_m c_{n+2} + c_n c_{m+2}) ≤ symMinor(m,n)` (the Gershgorin
    negative-leakage envelope of the off-diagonal block; the positive part is `≥ 0`).

DELIVERABLE 2 (the DEFECT-FORM reduction of the reserve — PROVED).  The reserve inequality is
EQUIVALENT to a bound on the autoconvolution DEFECT `H0auto(s+1)² − H0auto(s)·H0auto(s+2)`:
  * `reserve_of_defect` — the pure `Q'` rearrangement `δ·A ≤ B + −A  ⟹  (1+δ)·A ≤ B`.
  * `AutoconvDefectReserve w` — the Type-level NAMED residual: the defect exceeds `δ` of the
    product, `δ·H0auto(s)·H0auto(s+2) ≤ H0auto(s+1)² + −(H0auto(s)·H0auto(s+2))`.
  * `reserveOfDefectBound` — a defect residual inhabits `AutoconvReserveResidual w`.
  * `s1DominanceOfDefectReserve` — end-to-end wiring: a defect residual (plus the A1 strand
    reindex and the per-`N` edge input) drives `S1Dominance N w 2` for every `N`.
This recasts the reserve as EXACTLY what the aggregate `symMinor` expansion targets: the defect
is (up to explicit edge terms) the quadratic form `Σ_{i,j} v_i v_j symMinor(i,j)`, whose
diagonal + adjacent band is now proved `≥ 0` and whose `|i−j| ≥ 2` block is the sole open
content.

# HONESTY — what is NOT closed

`AutoconvReserveResidual w` remains NAMED-OPEN.  This module does NOT inhabit it: it reduces it
to the equivalent `AutoconvDefectReserve` (defect form) and proves the diagonal + first
off-diagonal band of the `symMinor` quadratic form is `≥ 0`, LOCATING the indefinite content in
the `|i−j| ≥ 2` tail.  It does NOT prove the aggregate cancellation of that tail, nor the
`H0auto`-defect ↦ `Σ v_i v_j symMinor(i,j)` expansion identity (the Andréief half-sum for the
autoconvolution square, with its explicit truncation edge terms).  That expansion + the tail
Gershgorin domination is the remaining wall.  This is a structural sharpening of one box-level
log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW_logConcave_of_super` / `coeffW_rect` / `symMinor`
lemmas, and small `Q'`-algebra congruences.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.FusionCoreStep

namespace YMGap.Continuum.LocalCLTSteepestDescent

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.FusionCoreStepRoundE
open YMGap.Continuum.FusionCoreStepRoundH
open YMGap.Continuum.FusionCoreStepRoundI
open YMGap.Continuum.FusionCoreStepRoundJ

/-! ## 1. The symmetrized off-diagonal minor: symmetry and the ADJACENT-BAND nonnegativity -/

/-- **`symMinor_symm`** — the symmetrized off-diagonal Menon minor is symmetric in its two
mode indices: `symMinor(m,n) ≃ symMinor(n,m)`.  Commute the two positive products and the two
negative products. -/
theorem symMinor_symm (w : Q') (m n : Nat) :
    (symMinor w m n).eqv (symMinor w n m) := by
  unfold symMinor
  refine Q'.add_eqv_congr' ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_comm_eqv (coeffW w (m + 1)) (coeffW w (n + 1)))
      (Q'.mul_comm_eqv (coeffW w (m + 1)) (coeffW w (n + 1)))
  · exact Q'.neg_eqv_congr _ _
      (Q'.add_comm_eqv (coeffW w m * coeffW w (n + 2)) (coeffW w n * coeffW w (m + 2)))

/-- **`symMinor_diag_nonneg` — the DIAGONAL band is nonnegative** (all `m`).
`symMinor(m,m) = 2·c_{m+1}² − 2·c_m c_{m+2} ≥ 0` from log-concavity
(`coeffW_logConcave_of_super`: `c_m c_{m+2} ≤ c_{m+1}²`). -/
theorem symMinor_diag_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (m : Nat) :
    (0 : Q') ≤ symMinor w m m := by
  have h : coeffW w m * coeffW w (m + 2) ≤ coeffW w (m + 1) * coeffW w (m + 1) :=
    coeffW_logConcave_of_super hw0 hw12 m
  have h2 : (coeffW w m * coeffW w (m + 2) + coeffW w m * coeffW w (m + 2))
      ≤ (coeffW w (m + 1) * coeffW w (m + 1) + coeffW w (m + 1) * coeffW w (m + 1)) :=
    Q'.add_le_add h h
  exact Q'.sub_nonneg_of_le h2

/-- **`symMinor_adj_nonneg` — the FIRST off-diagonal band is nonnegative** (all `m`).
`symMinor(m,m+1) = c_{m+1} c_{m+2} − c_m c_{m+3} ≥ 0` from the Hankel rectangle log-concavity
`coeffW_rect` (`c_m c_{m+3} ≤ c_{m+1} c_{m+2}`).  Together with `symMinor_can_be_negative`
(Round J, spread `2`) this pins the indefiniteness at spread `|m−n| ≥ 2`. -/
theorem symMinor_adj_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) (m : Nat) :
    (0 : Q') ≤ symMinor w m (m + 1) := by
  have h : coeffW w m * coeffW w (m + 1 + 2) ≤ coeffW w (m + 1) * coeffW w (m + 2) :=
    coeffW_rect hw0 hw1 hwpos 2 1 m
  have h2 :
      (coeffW w m * coeffW w (m + 1 + 2) + coeffW w (m + 1) * coeffW w (m + 2))
        ≤ (coeffW w (m + 1) * coeffW w (m + 2) + coeffW w (m + 1) * coeffW w (m + 2)) :=
    Q'.add_le_add h (Q'.le_refl' _)
  exact Q'.sub_nonneg_of_le h2

/-- **`symMinor_adj_nonneg'`** — the same for the transposed band `symMinor(m+1,m) ≥ 0`
(by symmetry). -/
theorem symMinor_adj_nonneg' {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) (m : Nat) :
    (0 : Q') ≤ symMinor w (m + 1) m :=
  Q'.le_trans' _ _ _
    (symMinor_adj_nonneg hw0 hw1 hwpos m)
    (Q'.ge_of_eqv (symMinor_symm w (m + 1) m))

/-- **`symMinor_lower_env` — the Gershgorin negative-leakage envelope.**
`−(c_m c_{n+2} + c_n c_{m+2}) ≤ symMinor(m,n)`: the positive part `2 c_{m+1} c_{n+1}` of the
symmetrized minor is `≥ 0`, so the minor is bounded below by minus its negative block.  This is
the envelope the off-diagonal (`|m−n| ≥ 2`) Gershgorin domination bounds against. -/
theorem symMinor_lower_env {w : Q'} (hw0 : (0 : Q') ≤ w) (m n : Nat) :
    -(coeffW w m * coeffW w (n + 2) + coeffW w n * coeffW w (m + 2))
      ≤ symMinor w m n := by
  have hx : (0 : Q') ≤ coeffW w (m + 1) * coeffW w (n + 1) :=
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0 _) (coeffW_nonneg hw0 _)
  have hpos : (0 : Q')
      ≤ coeffW w (m + 1) * coeffW w (n + 1) + coeffW w (m + 1) * coeffW w (n + 1) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (q_zero_add_eqv 0)) (Q'.add_le_add hx hx)
  -- symMinor = P + -(neg) with P ≥ 0, so -(neg) ≃ 0 + -(neg) ≤ P + -(neg) = symMinor.
  have hstep :
      (0 : Q') + -(coeffW w m * coeffW w (n + 2) + coeffW w n * coeffW w (m + 2))
        ≤ (coeffW w (m + 1) * coeffW w (n + 1) + coeffW w (m + 1) * coeffW w (n + 1))
          + -(coeffW w m * coeffW w (n + 2) + coeffW w n * coeffW w (m + 2)) :=
    Q'.add_le_add hpos (Q'.le_refl' _)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (q_zero_add_eqv _)) hstep

/-! ## 2. The defect-form reduction of the reserve -/

/-- **`reserve_of_defect` — the defect ⟹ reserve rearrangement (pure `Q'`).**
From `δ·A ≤ B + −A` conclude `(1 + δ)·A ≤ B`.  Add `A` to both sides of the hypothesis and use
`(1+δ)·A ≃ A + δ·A` and `A + (B + −A) ≃ B`. -/
theorem reserve_of_defect {δ A B : Q'} (h : δ * A ≤ B + -A) :
    (1 + δ) * A ≤ B := by
  have hstep : A + δ * A ≤ A + (B + -A) := Q'.add_le_add (Q'.le_refl' A) h
  have e1 : ((1 + δ) * A).eqv (A + δ * A) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 δ A) ?_
    exact Q'.add_eqv_congr_right _ _ (δ * A) (Q'.one_mul_eqv A)
  have e2 : (A + (B + -A)).eqv B := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left A (B + -A) (-A + B) (Q'.add_comm_eqv B (-A))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv A (-A) B)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (A + -A) 0 B (Q'.add_neg_self_eqv A)) ?_
    exact q_zero_add_eqv B
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1)
    (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv e2))

/-- **`AutoconvDefectReserve w`** — the DEFECT-FORM residual, equivalent to
`AutoconvReserveResidual w`: the autoconvolution defect `H0auto(s+1)² − H0auto(s)·H0auto(s+2)`
exceeds `δ = 31/225` of the product, uniform in `N, s`.  This is the shape the aggregate
`symMinor` quadratic-form expansion targets.  NAMED-OPEN (never `sorry`). -/
structure AutoconvDefectReserve (w : Q') : Type where
  /-- The defect exceeds `δ` of the product (uniform in `N, s`). -/
  defectBound : ∀ N s,
    Q'.mkPos 31 225 (by decide) * (H0auto w N s * H0auto w N (s + 2))
      ≤ H0auto w N (s + 1) * H0auto w N (s + 1)
        + -(H0auto w N s * H0auto w N (s + 2))

/-- **`reserveOfDefectBound` — the defect residual inhabits the reserve residual.**
Each `reserve` field is `reserve_of_defect` applied to the corresponding `defectBound`. -/
def reserveOfDefectBound {w : Q'} (dr : AutoconvDefectReserve w) :
    AutoconvReserveResidual w where
  reserve := fun N s => reserve_of_defect (dr.defectBound N s)

/-- **`s1DominanceOfDefectReserve` — end-to-end.**  A defect residual (plus the A1 strand
reindex and the per-`N` edge input) drives `S1Dominance N w 2` for EVERY `N`, through Round I's
`s1DominanceOfResidual`. -/
def s1DominanceOfDefectReserve {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (hwpos : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (reindex : ∀ N t, (boxSum w N t).eqv (lineSum (lagCorr w N) t))
    (dr : AutoconvDefectReserve w) (N : Nat)
    (hedge : bondMovedCoeff N w 2 2 ≤ bondMovedCoeff N w 2 1) :
    YMGap.Continuum.S1Dominance.S1Dominance N w 2 :=
  s1DominanceOfResidual hw0 hw12 hwpos hw1 reindex (reserveOfDefectBound dr) N hedge

/-! ## 3. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `symMinor_symm` — symmetry of the symmetrized off-diagonal minor.
  * `symMinor_diag_nonneg`, `symMinor_adj_nonneg`, `symMinor_adj_nonneg'` — the diagonal and
    FIRST off-diagonal band of the `symMinor` quadratic form are `≥ 0` (all `m`), LOCATING the
    Round-J indefiniteness at spread `|m−n| ≥ 2`.
  * `symMinor_lower_env` — the Gershgorin negative-leakage envelope of the off-diagonal block.
  * `reserve_of_defect` — the pure-`Q'` defect ⟹ reserve rearrangement.
  * `reserveOfDefectBound` — a defect residual inhabits `AutoconvReserveResidual`.
  * `s1DominanceOfDefectReserve` — the wiring to `S1Dominance` (every `N`).

NAMED OPEN (Type-level structure, never `sorry`):
  * `AutoconvDefectReserve w` — the defect-form residual `δ·H0auto(s)H0auto(s+2) ≤
    H0auto(s+1)² + −(H0auto(s)H0auto(s+2))`, equivalent to `AutoconvReserveResidual`.  The
    remaining open content is the `H0auto`-defect ↦ `Σ_{i,j} v_i v_j symMinor(i,j)` expansion
    (Andréief half-sum of the autoconvolution square, with explicit truncation edge terms) plus
    the aggregate Gershgorin domination of the `|i−j| ≥ 2` `symMinor` tail against the proved
    diagonal `(3/4)` reserve — the same heat-kernel local-CLT wall.

HONEST VERDICT.  This module recasts the sole open reserve field as the equivalent
autoconvolution DEFECT bound, and proves the diagonal + first off-diagonal band of the
governing `symMinor` quadratic form is nonnegative, LOCATING the indefinite content at spread
`|i−j| ≥ 2`.  It does NOT close the aggregate cancellation.  This is a structural sharpening of
one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.LocalCLTSteepestDescent

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.LocalCLTSteepestDescent.symMinor_symm
#print axioms YMGap.Continuum.LocalCLTSteepestDescent.symMinor_diag_nonneg
#print axioms YMGap.Continuum.LocalCLTSteepestDescent.symMinor_adj_nonneg
#print axioms YMGap.Continuum.LocalCLTSteepestDescent.symMinor_adj_nonneg'
#print axioms YMGap.Continuum.LocalCLTSteepestDescent.symMinor_lower_env
#print axioms YMGap.Continuum.LocalCLTSteepestDescent.reserve_of_defect
#print axioms YMGap.Continuum.LocalCLTSteepestDescent.reserveOfDefectBound
#print axioms YMGap.Continuum.LocalCLTSteepestDescent.s1DominanceOfDefectReserve
