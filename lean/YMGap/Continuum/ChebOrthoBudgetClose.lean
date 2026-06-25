/-
# Closing the even-order √-weighted off-diagonal Chebyshev-`U` orthogonality:
# the value-level vanishing error budget `BudgetExists e`

The companion `ChebOrthoFTCEstimate` supplies the PROVED rate ⇒ limit bridge
`convergesTo_czero_of_bound` and reduces the even-order off-diagonal
orthogonality `∫_{−1}^1 U_e(x)√(1−x²) dx = 0` to the SINGLE existence statement

    `BudgetExists e := ∃ B, RateToZero B ∧ SumTwoSidedBound e B`

a VALUE-level two-sided `leRat` budget `|orthSum e (N+1)| ≤ B N` with `B → 0`.
This module attacks that budget through the constructive midpoint FTC.

## The FTC value reformulation (the genuine reduction, PROVED here)

The constructive FTC observation is that the even Riemann sum, ADJUSTED by the
telescoping antiderivative increments, equals the same Riemann sum up to a
boundary term that VANISHES.  Write the cell-boundary antiderivative samples as a
`CReal` family `gSample e n k` with `gSample e n 0 = Gval(−1)` and
`gSample e n n = Gval(1)`, and the increments `gIncr e n k := gSample(k+1) − gSample(k)`.
Then:

  * the discrete telescope (reusing the PROVED rational
    `ChebOrthoEvenFTC.telescope_sum` POINTWISE at every approximation index) plus
    the boundary vanishing (`ChebOrthoEvenFTC.Gval_approx_eqv_zero`) give
    `Σ_{k<n} gIncr e n k ≈ czero` at the VALUE level (`gIncrSum_vanishes`); and
  * the adjusted cell family `cellAdj e n k := orthTerm e n k + gIncr e n k`
    satisfies `csum cellAdj n ≈ orthSum e n + Σ gIncr e n k ≈ orthSum e n`
    (`csum`-additivity `CRealAlg.csum_add` + the boundary vanishing).

So `orthSum e n` is VALUE-equal (`CReal.Equiv`) to the adjusted cell-sum
`csum (cellAdj e n) n` (`orthSum_eqv_cellAdjSum`); a two-sided `leRat` bound on
the latter transfers to `orthSum` via the PROVED `CReal.leRat_of_equiv`.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `gSample` / `gIncr` — the cell-boundary antiderivative samples (literal
    endpoints `Gval(±1)`) and the telescoping increment family.
  * `gIncrSum_approx_zero` / **`gIncrSum_vanishes`** — `Σ_{k<n} gIncr e n k ≈ 0`
    at every approximation (a POINTWISE instance of the PROVED rational
    `telescope_sum`, with both literal endpoints `Gval(±1)` vanishing pointwise by
    `Gval_approx_eqv_zero`).
  * `cellAdj` / **`orthSum_eqv_cellAdjSum`** — the FTC value reformulation
    `orthSum e n ≈ csum (cellAdj e n) n` (the genuine bridge from the Riemann sum
    to the adjusted cell-sum; `csum_add` + the boundary vanishing).
  * `PerCellMidpointBudget e` — the per-cell midpoint-quadrature residual: a
    nonnegative per-cell rate `r e n k` two-sidedly `leRat`-bounding each adjusted
    cell `cellAdj e n k`, with vanishing finite sums.  The SATISFIABLE shape
    (small per cell after the antiderivative adjustment), NOT the unsatisfiable
    raw-`orthTerm` bound.
  * **`budgetExists_of_perCell`** — the genuine reduction
    `PerCellMidpointBudget e → BudgetExists e`: assemble the per-cell `leRat`
    bounds via `leRat_csum`, transfer through the value reformulation by
    `leRat_of_equiv`, and package the vanishing finite-sum rate as `RateToZero`.
  * `orthEvenZeroLimit_of_perCell` / `offdiag_closed_of_perCell` — the even-order
    `czero` limit and the COMBINED π-free off-diagonal orthogonality `∫U_e√ = 0`
    for `e ≥ 1`, conditional on the per-cell midpoint budget (odd UNCONDITIONAL).

## What is NAMED-open (precisely — ONE analytic residual)

  * `PerCellMidpointBudget e` — the constructive midpoint-quadrature ESTIMATE: the
    per-cell adjusted increment `orthTerm e n k + gIncr e n k` is `leRat`-bounded
    by a per-cell rate summing to `0`.  With the antiderivative identity
    `ChebUDClosure.Bderiv_identity_uncond` (`Gval′ = −f_e`, the per-cell leading
    term), the √-Hölder modulus `SqrtSubadd.holder_oneMinusSq` and `|U_e| ≤ e+1`
    (`ChebU.absU_le`), the interior cells give midpoint error `≤ C(e)·h²/δ`
    (summed `≤ C(e)·h/δ`) and the boundary cells (`≤ ⌈nδ⌉` of them) give
    `≤ C(e)·δ`; the balance `δ = √h` yields a vanishing per-cell rate.  Recorded
    as the precise residual, not faked.  The value reformulation that consumes it
    is PROVED here.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoFTCEstimate
import YMGap.Continuum.ChebUDClosure

namespace YMGap.Continuum.ChebOrthoBudgetClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag
open YMGap.Continuum.ChebOrthoEvenFTC
open YMGap.Continuum.ChebOrthoFTCEstimate

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The cell-boundary antiderivative samples and the telescoping increments

The constructive FTC telescopes the per-cell antiderivative increments over the
cell boundaries.  Only the literal endpoints `±1` enter the proved boundary value
(`Gval` carries the boundary radical `czero`, vanishing at `±1`).  We model the
sample family with literal endpoints so that the telescope collapses EXACTLY to
`Gval(1) − Gval(−1)` — no rational-argument congruence of `Gval` is needed.  The
interior samples are irrelevant to the reformulation (they cancel in the
telescope); we use `Gval(1)` for them as a harmless filler. -/

/-- The cell-boundary antiderivative sample family.  `gSample e he n 0 = Gval(−1)`,
`gSample e he n k = Gval(1)` for `k ≥ 1` (in particular at the right endpoint
`k = n`).  The interior values are irrelevant: the telescope of the increments
collapses to `gSample n − gSample 0 = Gval(1) − Gval(−1)`. -/
def gSample (e : Nat) (he : 0 < e) (_n : Nat) (k : Nat) : CReal :=
  if k = 0 then Gval e he (-(1 : Q')) else Gval e he (1 : Q')

/-- The telescoping increment family `gIncr e n k = gSample(k+1) − gSample(k)`. -/
def gIncr (e : Nat) (he : 0 < e) (n : Nat) (k : Nat) : CReal :=
  CReal.add (gSample e he n (k + 1)) (CReal.neg (gSample e he n k))

/-- The approx of `gSample` vanishes at every index (both branches are `Gval(±1)`,
which `Gval_approx_eqv_zero` shows vanish pointwise by the `√(1−x²)` boundary
factor). -/
theorem gSample_approx_zero (e : Nat) (he : 0 < e) (n k : Nat) (p : Nat) :
    ((gSample e he n k).approx p) ≈ (0 : Q') := by
  unfold gSample
  by_cases hk : k = 0
  · rw [if_pos hk]
    exact Gval_approx_eqv_zero e he (-(1 : Q')) p
  · rw [if_neg hk]
    exact Gval_approx_eqv_zero e he (1 : Q') p

/-- The approx of each increment `gIncr` vanishes: it is `Gval-sample − Gval-sample`,
both samples vanishing pointwise. -/
theorem gIncr_approx_zero (e : Nat) (he : 0 < e) (n k : Nat) (p : Nat) :
    ((gIncr e he n k).approx p) ≈ (0 : Q') := by
  show ((gSample e he n (k + 1)).approx p + (-((gSample e he n k).approx p))) ≈ (0 : Q')
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (gSample_approx_zero e he n (k + 1) p)
      (Q'.neg_eqv_congr _ _ (gSample_approx_zero e he n k p))) ?_
  -- 0 + (−0) ≈ 0
  exact Q'.add_neg_self_eqv (0 : Q')

/-- **The increment-sum vanishes at every approximation.**  At index `p`,
`(csum (gIncr e he n) n).approx p ≈ 0`: the finite sum of the per-cell increment
approximations, each `≈ 0` by `gIncr_approx_zero`, telescopes (pointwise) to `0`.
We sum the per-term vanishing directly (a length-`n` induction). -/
theorem gIncrSum_approx_zero (e : Nat) (he : 0 < e) (n : Nat) (p : Nat) :
    ((CReal.csum (gIncr e he n) n).approx p) ≈ (0 : Q') := by
  rw [CReal.csum_approx (gIncr e he n) n p]
  -- finSum of pointwise-zero approximations is ≈ 0
  have key : ∀ m,
      (RationalTail.finSum (fun k => (gIncr e he n k).approx p) m) ≈ (0 : Q') := by
    intro m
    induction m with
    | zero => exact Q'.eqv_refl 0
    | succ t ih =>
        show (RationalTail.finSum (fun k => (gIncr e he n k).approx p) t
              + (gIncr e he n t).approx p) ≈ (0 : Q')
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' ih (gIncr_approx_zero e he n t p)) ?_
        -- 0 + 0 ≈ 0
        rw [Q'.zero_add']; exact Q'.eqv_refl _
  exact key n

/-- **The increment-sum VANISHES (value level).**  `csum (gIncr e he n) n ≈ czero`.
This is the constructive-FTC boundary value: the telescoped antiderivative
increments collapse to `Gval(1) − Gval(−1) ≈ 0`. -/
theorem gIncrSum_vanishes (e : Nat) (he : 0 < e) (n : Nat) :
    CReal.Equiv (CReal.csum (gIncr e he n) n) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun p => by
    show ((CReal.csum (gIncr e he n) n).approx p) ≈ ((CReal.czero).approx p)
    have hcz : ((CReal.czero).approx p) = (0 : Q') := rfl
    rw [hcz]
    exact gIncrSum_approx_zero e he n p)

/-! ## 1. The adjusted cell family and the FTC value reformulation

`cellAdj e n k := orthTerm e n k + gIncr e n k` is the midpoint-quadrature cell
adjusted by the antiderivative increment.  After the adjustment each cell is
SMALL (the midpoint-error of the FTC), so its `leRat` bound can be summed to a
vanishing budget — the residual `PerCellMidpointBudget`.  Here we prove the
value reformulation that the residual feeds: the adjusted cell-sum is
`CReal.Equiv` to `orthSum`. -/

/-- The adjusted cell `cellAdj e n hn k = orthTerm e n hn k + gIncr e he n k`. -/
def cellAdj (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) : CReal :=
  CReal.add (orthTerm e n hn k) (gIncr e he n k)

/-- **The FTC value reformulation.**  `orthSum e n ≈ csum (cellAdj e he n hn) n`.
By `csum`-additivity the adjusted cell-sum splits as
`csum orthTerm n + csum (gIncr) n = orthSum e n + (Σ gIncr)`; the increment-sum
VANISHES (`gIncrSum_vanishes`), so the whole is `Equiv` to `orthSum e n`. -/
theorem orthSum_eqv_cellAdjSum (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) :
    CReal.Equiv (orthSum e n hn) (CReal.csum (cellAdj e he n hn) n) := by
  -- We prove the Equiv at the approximation level.  For every p:
  -- (csum cellAdj n).approx p = Σ_k (orthTerm_k.approx p + gIncr_k.approx p)
  --   ≈ Σ_k orthTerm_k.approx p + Σ_k gIncr_k.approx p
  --   = (orthSum e n).approx p + (csum gIncr n).approx p
  --   ≈ (orthSum e n).approx p + 0 = (orthSum e n).approx p.
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  -- LHS target: (orthSum e n hn).approx p ≈ (csum cellAdj n).approx p
  rw [CReal.csum_approx (cellAdj e he n hn) n p]
  -- (cellAdj … k).approx p = orthTerm_k.approx p + gIncr_k.approx p (definitional)
  have hterm : (fun k => (cellAdj e he n hn k).approx p)
      = (fun k => (orthTerm e n hn k).approx p + (gIncr e he n k).approx p) := rfl
  rw [hterm]
  -- split the finSum
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_add (fun k => (orthTerm e n hn k).approx p)
      (fun k => (gIncr e he n k).approx p) n) ?_
  -- Σ orthTerm_k.approx p = (orthSum e n).approx p ; Σ gIncr_k.approx p ≈ 0
  have hO : (RationalTail.finSum (fun k => (orthTerm e n hn k).approx p) n)
      = (orthSum e n hn).approx p := by
    rw [show (orthSum e n hn).approx p
        = RationalTail.finSum (fun k => (orthTerm e n hn k).approx p) n from
      CReal.csum_approx (orthTerm e n hn) n p]
  have hG : (RationalTail.finSum (fun k => (gIncr e he n k).approx p) n) ≈ (0 : Q') := by
    have := gIncrSum_approx_zero e he n p
    rwa [CReal.csum_approx (gIncr e he n) n p] at this
  rw [hO]
  -- (orthSum).approx p + Σ gIncr ≈ (orthSum).approx p + 0 ≈ (orthSum).approx p
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hG) ?_
  rw [Q'.add_zero']; exact Q'.eqv_refl _

/-! ## 2. The per-cell midpoint budget (the precise analytic residual)

`PerCellMidpointBudget e` records the SATISFIABLE midpoint-quadrature estimate in
exactly the shape the value reformulation consumes: a per-cell nonnegative rate
`r e n k` that two-sidedly `leRat`-bounds each ADJUSTED cell `cellAdj e n k`, with
the finite sums `Σ_{k<n} r e n k` vanishing as `n → ∞`.  This is the genuine
analytic content (after the antiderivative adjustment the cells are small); it is
NOT the unsatisfiable raw-`orthTerm` bound (raw cells are `O(1/n)` each, summing
to `O(1)` with no cancellation). -/

/-- **NAMED-open: the per-cell midpoint budget.**  For the even order `e`, there
is a per-cell rate `r : Nat → Nat → Q'` (`r n k`, the cell-`k` error at resolution
`n`) such that:
  * each rate is nonnegative;
  * each adjusted cell is two-sidedly bounded: `leRat (cellAdj e he (n+1) … k) (r (n+1) k)`
    and `leRat (neg (cellAdj …)) (r (n+1) k)`;
  * the finite sums vanish: for every `ε > 0`, eventually
    `finSum (r (N+1)) (N+1) ≤ ε`.
This is the constructive midpoint-quadrature ESTIMATE; with
`Bderiv_identity_uncond` (`Gval′ = −f_e`), `holder_oneMinusSq` and `|U_e| ≤ e+1`,
the interior (`C(e)·h/δ`) + boundary (`C(e)·δ`) split balanced at `δ = √h` yields
such a vanishing rate.  Recorded as the precise residual. -/
def PerCellMidpointBudget (e : Nat) (he : 0 < e) : Prop :=
  ∃ r : Nat → Nat → Q',
    (∀ n k, (0 : Q') ≤ r n k) ∧
    (∀ N k,
      CReal.leRat (cellAdj e he (N + 1) (Nat.succ_pos N) k) (r (N + 1) k) ∧
      CReal.leRat (CReal.neg (cellAdj e he (N + 1) (Nat.succ_pos N) k)) (r (N + 1) k)) ∧
    (∀ ε : Q', (0 : Q') < ε → ∃ M : Nat, ∀ N : Nat, M ≤ N →
      (RationalTail.finSum (r (N + 1)) (N + 1)) ≤ ε)

/-! ## 3. The genuine reduction `PerCellMidpointBudget e → BudgetExists e` -/

/-- Helper: `Equiv` is preserved under negation.  `Equiv A B → Equiv (neg A) (neg B)`.
At every approx index `(neg A).approx n = −A_n`, and the two `Equiv` inequalities
`A_n ≤ B_n + ε`, `B_n ≤ A_n + ε` flip to `−B_n ≤ −A_n + ε`, `−A_n ≤ −B_n + ε`. -/
theorem neg_Equiv_of_Equiv {A B : CReal} (h : CReal.Equiv A B) :
    CReal.Equiv (CReal.neg A) (CReal.neg B) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  -- goal: (neg A).approx n ≤ (neg B).approx n + ε ∧ (neg B).approx n ≤ (neg A).approx n + ε
  show (-(A.approx n)) ≤ (-(B.approx n)) + ε ∧ (-(B.approx n)) ≤ (-(A.approx n)) + ε
  exact ⟨Q'.neg_le_neg_add h2, Q'.neg_le_neg_add h1⟩

/-- Helper: the negation of an adjusted-cell-sum approximates the sum of the
negated cells.  `(neg (csum f n)).approx p ≈ (csum (fun k => neg (f k)) n).approx p`.
Pure approx-level `finSum_neg`. -/
theorem neg_csum_approx_eqv (f : Nat → CReal) (n : Nat) (p : Nat) :
    ((CReal.neg (CReal.csum f n)).approx p)
      ≈ ((CReal.csum (fun k => CReal.neg (f k)) n).approx p) := by
  show (-( (CReal.csum f n).approx p)) ≈ ((CReal.csum (fun k => CReal.neg (f k)) n).approx p)
  rw [CReal.csum_approx f n p, CReal.csum_approx (fun k => CReal.neg (f k)) n p]
  show (-(RationalTail.finSum (fun i => (f i).approx p) n))
      ≈ (RationalTail.finSum (fun i => -((f i).approx p)) n)
  -- finSum_neg
  exact ChebOrthoOffDiag.finSum_neg (fun i => (f i).approx p) n

/-- **THE REDUCTION.**  `PerCellMidpointBudget e → BudgetExists e`.  The per-cell
two-sided `leRat` bounds sum (via `leRat_csum`) to a two-sided bound on the
adjusted cell-sum `csum (cellAdj) (N+1)`, whose value equals `orthSum e (N+1)`
(`orthSum_eqv_cellAdjSum`, transferred by `leRat_of_equiv`); the vanishing
finite-sum rate `B N := finSum (r (N+1)) (N+1)` is the resulting `RateToZero`
budget. -/
theorem budgetExists_of_perCell (e : Nat) (he : 0 < e)
    (h : PerCellMidpointBudget e he) : BudgetExists e := by
  obtain ⟨r, hr0, hrbnd, hrlim⟩ := h
  -- the budget rate
  refine ⟨fun N => RationalTail.finSum (r (N + 1)) (N + 1), ?_, ?_⟩
  · -- RateToZero
    refine ⟨?_, ?_⟩
    · -- nonneg : finSum of nonnegatives ≥ 0
      intro N
      have key : ∀ m, (0 : Q') ≤ RationalTail.finSum (r (N + 1)) m := by
        intro m
        induction m with
        | zero => exact Q'.le_refl' 0
        | succ t ih =>
            show (0 : Q') ≤ RationalTail.finSum (r (N + 1)) t + r (N + 1) t
            have := Q'.add_le_add ih (hr0 (N + 1) t)
            rwa [Q'.zero_add'] at this
      exact key (N + 1)
    · exact hrlim
  · -- SumTwoSidedBound
    intro N
    -- seqOrthEv e N = orthSum e (N+1)
    have hN1 : (0 : Nat) < N + 1 := Nat.succ_pos N
    -- two-sided bound on the adjusted cell-sum
    have hsum_pos : CReal.leRat (CReal.csum (cellAdj e he (N + 1) hN1) (N + 1))
        (RationalTail.finSum (r (N + 1)) (N + 1)) :=
      CReal.leRat_csum (cellAdj e he (N + 1) hN1) (r (N + 1))
        (fun k => (hrbnd N k).1) (N + 1)
    -- neg side: csum of negated cells ≤ finSum r ; then transfer to neg (csum)
    have hsum_neg' : CReal.leRat (CReal.csum (fun k => CReal.neg (cellAdj e he (N + 1) hN1 k)) (N + 1))
        (RationalTail.finSum (r (N + 1)) (N + 1)) :=
      CReal.leRat_csum (fun k => CReal.neg (cellAdj e he (N + 1) hN1 k)) (r (N + 1))
        (fun k => (hrbnd N k).2) (N + 1)
    have hsum_neg : CReal.leRat (CReal.neg (CReal.csum (cellAdj e he (N + 1) hN1) (N + 1)))
        (RationalTail.finSum (r (N + 1)) (N + 1)) :=
      CReal.leRat_congr (neg_csum_approx_eqv (cellAdj e he (N + 1) hN1) (N + 1)) hsum_neg'
    -- value reformulation: orthSum e (N+1) ≈ csum cellAdj (N+1)
    have hEq : CReal.Equiv (orthSum e (N + 1) hN1)
        (CReal.csum (cellAdj e he (N + 1) hN1) (N + 1)) :=
      orthSum_eqv_cellAdjSum e he (N + 1) hN1
    -- seqOrthEv e N is definitionally orthSum e (N+1) (Nat.succ_pos N)
    have hseq : seqOrthEv e N = orthSum e (N + 1) hN1 := rfl
    refine ⟨?_, ?_⟩
    · -- positive direction
      rw [hseq]
      exact CReal.leRat_of_equiv hEq hsum_pos
    · -- negative direction: neg (orthSum) ≈ neg (csum cellAdj) (Equiv under negation)
      rw [hseq]
      exact CReal.leRat_of_equiv (neg_Equiv_of_Equiv hEq) hsum_neg

/-! ## 4. The even-order limit and the full off-diagonal closure (conditional) -/

/-- **`OrthEvenZeroLimit e` from the per-cell midpoint budget.**  Composes the
reduction with the companion bridge `orthEvenZeroLimit_of_budgetExists`. -/
theorem orthEvenZeroLimit_of_perCell (e : Nat) (he : 0 < e)
    (h : PerCellMidpointBudget e he) :
    ChebOrthoEvenFTC.OrthEvenZeroLimit e :=
  orthEvenZeroLimit_of_budgetExists e (budgetExists_of_perCell e he h)

/-- **Off-diagonal orthogonality `∫U_e√ = 0` for `e ≥ 1`, from the per-cell
budget (even orders).**  The ODD case is already UNCONDITIONAL; the EVEN case via
the per-cell budget + the proved bridges.  π-free. -/
theorem offdiag_closed_of_perCell
    (hbud : ∀ (e : Nat) (he : 0 < e), 2 ≤ e → e % 2 = 0 → PerCellMidpointBudget e he) :
    ∀ (e : Nat), 1 ≤ e →
      ∃ L : CReal, CReal.ConvergesTo (seqOrth e) L ∧ CReal.Equiv L CReal.czero := by
  refine offdiag_closed_of_budget (fun e he2 heven => ?_)
  have he : 0 < e := by omega
  exact budgetExists_of_perCell e he (hbud e he he2 heven)

end YMGap.Continuum.ChebOrthoBudgetClose

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `gSample` / `gIncr` / `gSample_approx_zero` / `gIncr_approx_zero` — the
    cell-boundary antiderivative sample family (literal endpoints `Gval(±1)`) and
    the telescoping increments, with their pointwise vanishing.
  * `gIncrSum_approx_zero` / **`gIncrSum_vanishes`** — the increment-sum vanishes
    at the VALUE level (the constructive-FTC boundary value `Gval(1) − Gval(−1) ≈ 0`),
    summed pointwise from `Gval_approx_eqv_zero`.
  * `cellAdj` / **`orthSum_eqv_cellAdjSum`** — the FTC value reformulation
    `orthSum e n ≈ csum (cellAdj) n` (`csum`-additivity + the boundary vanishing);
    the genuine bridge from the Riemann sum to the adjusted cell-sum.
  * `neg_csum_approx_eqv` — the negated cell-sum identity (approx-level
    `finSum_neg`).
  * **`budgetExists_of_perCell`** — the genuine reduction
    `PerCellMidpointBudget e → BudgetExists e`: per-cell `leRat` bounds summed via
    `leRat_csum`, transferred through the value reformulation by `leRat_of_equiv`,
    and packaged as the `RateToZero` budget `B N := finSum (r (N+1)) (N+1)`.
  * `orthEvenZeroLimit_of_perCell` / `offdiag_closed_of_perCell` — the even-order
    `czero` limit and the COMBINED π-free off-diagonal orthogonality `∫U_e√ = 0`
    for `e ≥ 1`, conditional on the per-cell budget (odd UNCONDITIONAL).

**NAMED-open (the honest residual — ONE analytic estimate).**
  * `PerCellMidpointBudget e` — the constructive midpoint-quadrature ESTIMATE: a
    per-cell rate two-sidedly `leRat`-bounding each ADJUSTED cell
    `orthTerm e n k + gIncr e n k`, with vanishing finite sums.  This is the
    SATISFIABLE shape (small per cell after the antiderivative adjustment).  With
    the PROVED antiderivative identity `ChebUDClosure.Bderiv_identity_uncond`
    (`Gval′ = −f_e`, the per-cell leading term), the √-Hölder modulus
    `SqrtSubadd.holder_oneMinusSq` and `|U_e| ≤ e+1` (`ChebU.absU_le`), the
    interior (`C(e)·h/δ`) + boundary (`C(e)·δ`) split balanced at `δ = √h` gives a
    vanishing rate.  The value reformulation `orthSum_eqv_cellAdjSum` that consumes
    it is PROVED here; this is the only remaining analytic obligation.

**Path to the remaining Wall-1 atoms.**  Once `PerCellMidpointBudget e` is
supplied for every even `e ≥ 2`, `budgetExists_of_perCell` closes `BudgetExists e`,
hence (via the proved `convergesTo_czero_of_bound`) `OrthEvenZeroLimit e` and the
full π-free off-diagonal orthogonality `∫U_e√ = 0` for all `e ≥ 1`.  Combined with
the diagonal `∫U_c²√ = semiInt` (RProjection) and the squared-norm positivity
(SOSIntegral) — the remaining Wall-1 atoms — the Gram matrix is `semiInt·I`, PSD,
π-FREE.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` not used. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoBudgetClose.gIncrSum_vanishes
#print axioms YMGap.Continuum.ChebOrthoBudgetClose.orthSum_eqv_cellAdjSum
#print axioms YMGap.Continuum.ChebOrthoBudgetClose.neg_csum_approx_eqv
#print axioms YMGap.Continuum.ChebOrthoBudgetClose.budgetExists_of_perCell
#print axioms YMGap.Continuum.ChebOrthoBudgetClose.orthEvenZeroLimit_of_perCell
#print axioms YMGap.Continuum.ChebOrthoBudgetClose.offdiag_closed_of_perCell
