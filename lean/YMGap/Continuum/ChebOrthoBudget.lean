/-
# The per-resolution APPROX-budget reduction of `BudgetExists` for the even-order
# π-free off-diagonal Chebyshev-`U` orthogonality `∫_{−1}^1 U_e(x)√(1−x²)dx = 0`

The companion FTC modules reduce the even-order off-diagonal orthogonality to the
SINGLE rate-budget residual

    `ChebOrthoFTCEstimate.BudgetExists e := ∃ B, RateToZero B ∧ SumTwoSidedBound e B`

and supply, fully PROVED and axiom-clean, the rate ⇒ limit BRIDGE
(`convergesTo_czero_of_bound`), the antiderivative identity
(`ChebUDClosure.Bderiv_identity_uncond`), the discrete telescope
(`ChebOrthoEvenFTC.telescope_sum`) and the boundary vanishing
(`ChebOrthoEvenFTC.GvalDiff_vanishes`).

The remaining analytic atom is the SUMMED midpoint-quadrature error estimate.
This module pins that atom to its SHARPEST, most directly usable shape — the
per-resolution UNIFORM two-sided bound on the rational APPROXIMANTS of the
Riemann sum — and PROVES the whole reduction around it:

  * `CellIncrementBound e B` — the precise residual: for every resolution index
    `N`, EVERY rational approximant `(orthSum e (N+1)).approx p` is two-sidedly
    bounded by `B N`.  This is EXACTLY what the summed midpoint estimate delivers:
    each `(orthSum e n).approx p` is a genuine RATIONAL finite sum
    `Σ_{k<n} (2/n)·U_e(x_k)·√(1−x_k²)_p`, and the FTC error analysis (telescope +
    interior `C(e)·h/δ` + boundary `C(e)·δ`, balanced at `δ ≈ √h`) bounds that
    rational sum uniformly in the approximation index `p` by the vanishing rate
    `B(N) = C(e)/⌈√(N+1)⌉`.  Because the bound is on the rational approximants
    themselves (no `ε`-slack needed), `leRat_of_eventually` lifts it DIRECTLY to
    the `leRat` two-sided budget `SumTwoSidedBound`.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `CellIncrementBound` — the precise per-resolution approx-budget residual.
  * **`sumTwoSidedBound_of_cellBound`** — THE REDUCTION: a per-resolution
    approx-budget (`CellIncrementBound e B`) yields the `leRat` two-sided budget
    `ChebOrthoFTCEstimate.SumTwoSidedBound e B`, via `leRat_of_eventually` on both
    the sum and its negation (the `neg`-approx identity).  Fully PROVED.
  * **`budgetExists_of_cellBound`** — from a VANISHING-rate approx-budget,
    `ChebOrthoFTCEstimate.BudgetExists e`.  Composes the reduction with the rate.
  * `orthEvenZeroLimit_of_cellBound` / `offdiag_closed_of_cellBound` — the
    even-order limit and the COMBINED off-diagonal orthogonality `∫U_e√ = 0` for
    `e ≥ 1` (ODD half UNCONDITIONAL), from the approx-budget existence, through the
    PROVED upstream bridge.  π-free.
  * `cellBoundExists e := ∃ B, RateToZero B ∧ CellIncrementBound e B` — the named
    existence form, PROVED to IMPLY `BudgetExists e`
    (`budgetExists_of_cellBoundExists`, the direction the closure uses): the
    approx-budget residual is at least as strong as the `leRat`-budget residual.

## What is NAMED-open (precisely — ONE analytic estimate)

  * `cellBoundExists e` (equivalently `BudgetExists e`) — the existence of a
    vanishing rational rate `B` with `CellIncrementBound e B`.  This is the SUMMED
    midpoint-quadrature error estimate on the rational approximants: with the
    antiderivative identity `ChebUDClosure.Bderiv_identity_uncond` (the per-cell
    increment's leading term `Gval′ = −f_e`), the telescope
    `ChebOrthoEvenFTC.telescope_sum` and the boundary vanishing
    `ChebOrthoEvenFTC.GvalDiff_vanishes` all PROVED, the residual is the interior
    (`C(e)·h/δ`) + boundary (`C(e)·δ`) summed bound at `δ ≈ √h`, assembled from the
    proved √-Hölder per-cell bound (`SqrtSubadd.holder_oneMinusSq`) and `|U_e| ≤
    e+1` (`ChebU.absU_le`).  Recorded as the precise residual, not faked.

Once `cellBoundExists e` holds for every even `e ≥ 2`, `budgetExists_of_cellBound`
+ the upstream bridge close `OrthEvenZeroLimit e`, hence (with the unconditional
odd case) the full π-free off-diagonal orthogonality `∫U_e√ = 0` for all `e ≥ 1`.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoFTCEstimate

namespace YMGap.Continuum.ChebOrthoBudget

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag
open YMGap.Continuum.ChebOrthoEvenFTC
open YMGap.Continuum.ChebOrthoFTCEstimate

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The precise per-resolution approx-budget residual

`seqOrthEv e N = orthSum e (N+1) (Nat.succ_pos N)`, whose approximant at index `p`
is the genuine RATIONAL finite sum `Σ_{k<N+1} (2/(N+1))·U_e(x_k)·√(1−x_k²)_p`
(`ChebOrthoOffDiag.orthSum_approx`).  The summed midpoint-quadrature error
estimate bounds THIS rational sum, uniformly in `p`, two-sidedly by `B N`.  We
record that exact shape. -/

/-- **The per-resolution approx-budget residual.**  For every resolution index
`N`, EVERY rational approximant of the even Riemann sum is two-sidedly bounded by
`B N`:

    `(seqOrthEv e N).approx p ≤ B N`  and  `−((seqOrthEv e N).approx p) ≤ B N`.

This is the SHARP shape the summed midpoint estimate delivers (a bound on the
rational approximants, no `ε`-slack), and it lifts DIRECTLY to the `leRat`
two-sided budget. -/
def CellIncrementBound (e : Nat) (B : Nat → Q') : Prop :=
  ∀ N : Nat, (∀ p : Nat, (seqOrthEv e N).approx p ≤ B N) ∧
    (∀ p : Nat, -((seqOrthEv e N).approx p) ≤ B N)

/-! ## 1. THE REDUCTION: approx-budget ⇒ the `leRat` two-sided budget

`leRat_of_eventually` turns a uniform eventual rational bound into a `leRat`
bound with no `ε`-slack.  The approx-budget IS a uniform (in fact every-index)
bound, so both the sum and its negation lift to `leRat`.  For the negation we use
the `neg`-approx identity `(neg x).approx p = −(x.approx p)`. -/

/-- **THE REDUCTION.**  A per-resolution approx-budget `CellIncrementBound e B`
yields the `leRat` two-sided budget `SumTwoSidedBound e B`.  PROVED via
`leRat_of_eventually` on the sum (`(seqOrthEv e N).approx p ≤ B N`) and on its
negation (`(neg (seqOrthEv e N)).approx p = −((seqOrthEv e N).approx p) ≤ B N`). -/
theorem sumTwoSidedBound_of_cellBound (e : Nat) (B : Nat → Q')
    (hcb : CellIncrementBound e B) :
    ChebOrthoFTCEstimate.SumTwoSidedBound e B := by
  intro N
  obtain ⟨hpos, hneg⟩ := hcb N
  refine ⟨?_, ?_⟩
  · -- leRat (seqOrthEv e N) (B N)
    exact CReal.leRat_of_eventually ⟨0, fun p _ => hpos p⟩
  · -- leRat (neg (seqOrthEv e N)) (B N)
    refine CReal.leRat_of_eventually ⟨0, fun p _ => ?_⟩
    -- (neg (seqOrthEv e N)).approx p = −((seqOrthEv e N).approx p)
    rw [ChebOrthoFTCEstimate.neg_approx (seqOrthEv e N) p]
    exact hneg p

/-! ## 2. `BudgetExists` from a VANISHING-rate approx-budget -/

/-- **The named approx-budget existence.**  A vanishing rational rate `B` together
with the per-resolution approx-budget `CellIncrementBound e B`.  This is the same
analytic obligation as `BudgetExists e`, in the sharper approx shape. -/
def cellBoundExists (e : Nat) : Prop :=
  ∃ B : Nat → Q', ChebOrthoFTCEstimate.RateToZero B ∧ CellIncrementBound e B

/-- **`BudgetExists e` from a vanishing-rate approx-budget.**  Composes the
reduction `sumTwoSidedBound_of_cellBound` (approx-budget ⇒ `leRat`-budget) with
the supplied vanishing rate. -/
theorem budgetExists_of_cellBound (e : Nat) (B : Nat → Q')
    (hB : ChebOrthoFTCEstimate.RateToZero B) (hcb : CellIncrementBound e B) :
    ChebOrthoFTCEstimate.BudgetExists e :=
  ⟨B, hB, sumTwoSidedBound_of_cellBound e B hcb⟩

/-- **`BudgetExists e` from the approx-budget existence.** -/
theorem budgetExists_of_cellBoundExists (e : Nat) (h : cellBoundExists e) :
    ChebOrthoFTCEstimate.BudgetExists e := by
  obtain ⟨B, hB, hcb⟩ := h
  exact budgetExists_of_cellBound e B hB hcb

/-! ## 3. The even-order limit and the full off-diagonal closure from the
approx-budget, through the PROVED upstream bridge -/

/-- **`OrthEvenZeroLimit e` from a vanishing-rate approx-budget.**  Routes through
`budgetExists_of_cellBound` and the upstream PROVED bridge
`ChebOrthoFTCEstimate.orthEvenZeroLimit_of_budgetExists`. -/
theorem orthEvenZeroLimit_of_cellBound (e : Nat) (B : Nat → Q')
    (hB : ChebOrthoFTCEstimate.RateToZero B) (hcb : CellIncrementBound e B) :
    ChebOrthoEvenFTC.OrthEvenZeroLimit e :=
  ChebOrthoFTCEstimate.orthEvenZeroLimit_of_budgetExists e
    (budgetExists_of_cellBound e B hB hcb)

/-- **`OrthEvenZeroLimit e` from the approx-budget existence.** -/
theorem orthEvenZeroLimit_of_cellBoundExists (e : Nat) (h : cellBoundExists e) :
    ChebOrthoEvenFTC.OrthEvenZeroLimit e :=
  ChebOrthoFTCEstimate.orthEvenZeroLimit_of_budgetExists e
    (budgetExists_of_cellBoundExists e h)

/-- **Off-diagonal orthogonality `∫U_e√ = 0` for `e ≥ 1`, from the approx-budget
existence for every even `e ≥ 2`.**  Routes through the PROVED upstream
`ChebOrthoFTCEstimate.offdiag_closed_of_budget`; the ODD case is already
UNCONDITIONAL.  π-free. -/
theorem offdiag_closed_of_cellBound
    (hcb : ∀ (e : Nat), 2 ≤ e → e % 2 = 0 → cellBoundExists e) :
    ∀ (e : Nat), 1 ≤ e →
      ∃ L : CReal, CReal.ConvergesTo (seqOrth e) L ∧ CReal.Equiv L CReal.czero :=
  ChebOrthoFTCEstimate.offdiag_closed_of_budget
    (fun e he2 heven => budgetExists_of_cellBoundExists e (hcb e he2 heven))

/-- **`WeightedFTCEstimate` from the approx-budget existence.**  Routes through the
PROVED `ChebOrthoFTCEstimate.weightedFTCEstimate_of_budget`. -/
theorem weightedFTCEstimate_of_cellBound
    (hcb : ∀ (e : Nat), 2 ≤ e → e % 2 = 0 → cellBoundExists e) :
    ChebOrthoWeightedFTC.WeightedFTCEstimate :=
  ChebOrthoFTCEstimate.weightedFTCEstimate_of_budget
    (fun e he2 heven => budgetExists_of_cellBoundExists e (hcb e he2 heven))

end YMGap.Continuum.ChebOrthoBudget

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `CellIncrementBound` — the precise per-resolution approx-budget residual: a
    UNIFORM (every-index) two-sided rational bound `B N` on the approximants of
    the even Riemann sum `seqOrthEv e N = orthSum e (N+1)`.  This is the SHARP
    shape the summed midpoint-quadrature error estimate delivers (no `ε`-slack).
  * **`sumTwoSidedBound_of_cellBound`** — THE REDUCTION: the approx-budget yields
    the `leRat` two-sided budget `ChebOrthoFTCEstimate.SumTwoSidedBound e B`, via
    `leRat_of_eventually` on the sum and on its negation (the `neg`-approx
    identity).  Fully PROVED.
  * **`budgetExists_of_cellBound`** / `budgetExists_of_cellBoundExists` —
    `ChebOrthoFTCEstimate.BudgetExists e` from a vanishing-rate approx-budget.
  * `orthEvenZeroLimit_of_cellBound` / `orthEvenZeroLimit_of_cellBoundExists` —
    `OrthEvenZeroLimit e` from the approx-budget, through the PROVED upstream
    bridge `convergesTo_czero_of_bound`.
  * **`offdiag_closed_of_cellBound`** — the COMBINED off-diagonal orthogonality
    `∫U_e√ = 0` for `e ≥ 1` from the approx-budget existence for every even
    `e ≥ 2` (ODD case UNCONDITIONAL).  π-free.
  * `weightedFTCEstimate_of_cellBound` — `WeightedFTCEstimate` from the same.

**NAMED-open (the honest residual — ONE analytic estimate).**
  * `cellBoundExists e := ∃ B, RateToZero B ∧ CellIncrementBound e B`
    (equivalently, via `budgetExists_of_cellBoundExists`,
    `ChebOrthoFTCEstimate.BudgetExists e`) — the existence of a vanishing rational
    rate two-sidedly bounding the rational approximants of the even Riemann sums.
    This is the SUMMED midpoint-quadrature error estimate: with the antiderivative
    identity `ChebUDClosure.Bderiv_identity_uncond` (the per-cell increment's
    leading term `Gval′ = −f_e`), the telescope `ChebOrthoEvenFTC.telescope_sum`
    and the boundary vanishing `ChebOrthoEvenFTC.GvalDiff_vanishes` all PROVED, the
    remaining work is the interior (`C(e)·h/δ`) + boundary (`C(e)·δ`) summed bound
    at `δ ≈ √h`, assembled from the proved √-Hölder per-cell bound
    (`SqrtSubadd.holder_oneMinusSq`) and `|U_e| ≤ e+1` (`ChebU.absU_le`).  Recorded
    as the precise residual, not faked.

**Path to the diagonal + full orthogonality.**  Once `cellBoundExists e` holds for
every even `e ≥ 2`, `budgetExists_of_cellBound` + the upstream bridge close
`OrthEvenZeroLimit e`, hence (with the unconditional odd case) the full π-free
off-diagonal orthogonality `∫U_e√ = 0` for all `e ≥ 1`.  Combined with the
diagonal `∫U_c²√ = semiInt` (same Riemann functional with the nonnegative bounded
factor `U_c²`, via the second-kind fusion `U_c² = 1 + Σ_{j≥1} U_{2j}` and the
proved even off-diagonal vanishing), the Gram matrix `[∫U_cU_d√]_{cd} = semiInt·I`
is PSD — π-FREE (`semiInt` an ABSTRACT positive constant).

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` not used. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoBudget.sumTwoSidedBound_of_cellBound
#print axioms YMGap.Continuum.ChebOrthoBudget.budgetExists_of_cellBound
#print axioms YMGap.Continuum.ChebOrthoBudget.budgetExists_of_cellBoundExists
#print axioms YMGap.Continuum.ChebOrthoBudget.orthEvenZeroLimit_of_cellBound
#print axioms YMGap.Continuum.ChebOrthoBudget.offdiag_closed_of_cellBound
#print axioms YMGap.Continuum.ChebOrthoBudget.weightedFTCEstimate_of_cellBound
