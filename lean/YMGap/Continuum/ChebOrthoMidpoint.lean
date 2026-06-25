/-
# The REAL-boundary midpoint reformulation of the even-order π-free
# off-diagonal Chebyshev-`U` orthogonality `∫_{−1}^1 U_e(x)√(1−x²)dx = 0`

The companion `ChebOrthoFTCEstimate` supplies the PROVED rate ⇒ limit bridge
`convergesTo_czero_of_bound` and reduces the even-order off-diagonal
orthogonality to the SINGLE existence statement

    `BudgetExists e := ∃ B, RateToZero B ∧ SumTwoSidedBound e B`

a VALUE-level two-sided `leRat` budget `|orthSum e (N+1)| ≤ B N` with `B → 0`.

A PRIOR attack (`ChebOrthoBudgetClose.gSample`) was DEGENERATE: it sampled the
antiderivative at `Gval(±1)` (both vanishing) for EVERY cell, so its adjusted
cells `cellAdj = orthTerm + (≈0)` were the RAW Riemann terms in disguise, whose
per-cell `leRat` bound is the unsatisfiable `Σ|orthTerm| = O(1) ↛ 0`.

This module builds the CORRECT real-boundary construction: the antiderivative
samples are taken at the genuine INTERIOR cell boundaries
`b_k = (2k − n)/n = −1 + 2k/n`, carrying the genuine radical `√(1 − b_k²)`
(a `CReal`, NON-vanishing for `0 < k < n`; only the endpoints `b_0 = −1`,
`b_n = 1` vanish).  The telescope of the increments then collapses to
`GsampR(n) − GsampR(0) = Gval(1) − Gval(−1) ≈ 0` with the INTERIOR samples
CANCELLING IN PAIRS (genuine telescoping, not the degenerate pointwise-zero).

## What is PROVED here (axiom-clean, GENUINE new content)

  * `bdyNum` / `bdyOneMinusSq` / `bdyRadical` — the genuine cell-boundary radical
    `√(1 − b_k²) : CReal` at the REAL boundary `b_k = (2k − n)/n`: a `sqrtFrom`
    for INTERIOR `0 < k < n` (non-vanishing) and `czero` at the endpoints
    `k = 0` (`b = −1`) and `k = n` (`b = 1`).
  * `bdyPoint` — the rational boundary `b_k = (2k − n)/n`.
  * `GsampR` — the REAL-boundary antiderivative sample
    `GsampR e he n k := ½·(√(1 − b_k²))·B_e(b_k)`, the genuine interior
    antiderivative value (NOT the degenerate `Gval(±1)` filler).
  * `GsampR_endpoint_zero` — `GsampR e he n 0 ≈ czero` and
    `GsampR e he n n ≈ czero` (only the ENDPOINTS vanish, via the `czero`
    radical; the interior samples are genuinely non-zero).
  * `gIncrR` / **`gIncrRSum_vanishes`** — the increment family
    `gIncrR k := GsampR(k+1) − GsampR(k)` and the GENUINE TELESCOPING
    `Σ_{k<n} gIncrR k ≈ czero`: the PROVED rational `telescope_sum` collapses the
    sum to `GsampR(n) + (−GsampR(0))`, both endpoints vanishing, the INTERIOR
    samples cancelling in pairs.  This is the constructive FTC boundary value
    with the REAL interior antiderivative — the correction of the degenerate path.
  * `cellAdjR` / **`orthSum_eqv_cellAdjRSum`** — the FTC value reformulation
    `orthSum e n ≈ csum (cellAdjR e he n hn) n` with the GENUINE adjusted cell
    `cellAdjR k := orthTerm k + gIncrR k`, so that `cellAdjR k` is the MIDPOINT
    ERROR `orthTerm k + (GsampR(b_{k+1}) − GsampR(b_k))` (NOT `orthTerm + ≈0`).
  * `RealPerCellBudget e` / **`budgetExists_of_realPerCell`** — the genuine
    reduction `RealPerCellBudget e → BudgetExists e`: per-cell two-sided `leRat`
    bounds on the REAL adjusted cells summed via `leRat_csum`, transferred through
    the value reformulation by `leRat_of_equiv`, packaged as the `RateToZero`
    budget.
  * `orthEvenZeroLimit_of_realPerCell` / `offdiag_closed_of_realPerCell` — the
    even-order `czero` limit and the COMBINED π-free off-diagonal orthogonality
    `∫U_e√ = 0` for `e ≥ 1`, conditional on the REAL per-cell budget (odd
    UNCONDITIONAL).

## What is NAMED-open (precisely — ONE analytic residual)

  * `RealPerCellBudget e` — the constructive midpoint-quadrature ESTIMATE on the
    GENUINE real-boundary adjusted cells `cellAdjR k = orthTerm k + (GsampR(b_{k+1})
    − GsampR(b_k))`.  This is the SATISFIABLE shape: by the antiderivative identity
    `ChebUDClosure.Bderiv_identity_uncond` (`Gval′ = −f_e`, `f_e = U_e·√(1−x²)`)
    the increment is `GsampR(b_{k+1}) − GsampR(b_k) ≈ −f_e(x_k)·h + (midpoint
    error)`, and `orthTerm k = f_e(x_k)·h`, so `cellAdjR k ≈ midpoint error`,
    bounded by the √-Hölder modulus of `f_e` (`SqrtSubadd.holder_oneMinusSq` +
    `|U_e| ≤ e+1` from `ChebyshevU.absU_le`).  The interior cells give
    `≤ C(e)·h^{3/2}` (summed `≤ C(e)·√h`); the boundary cells (the `O(nδ)` cells
    with `√(1−b²) < δ`) are bounded directly by `≤ C(e)·δ^{1/2}`; the balance
    `δ ≈ √h` sends both to `0`.  Recorded as the precise residual, not faked.
    The value reformulation that consumes it (the genuine REAL-boundary
    telescoping + adjustment) is PROVED here — correcting the degenerate path.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoFTCEstimate
import YMGap.Continuum.ChebOrthoEvenFTC
import YMGap.Continuum.ChebUDClosure

namespace YMGap.Continuum.ChebOrthoMidpoint

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag
open YMGap.Continuum.ChebOrthoEvenFTC
open YMGap.Continuum.ChebOrthoFTCEstimate

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The genuine cell-boundary radical `√(1 − b_k²)`

The cell boundary is `b_k = (2k − n)/n = −1 + 2k/n` (`k = 0..n`, width `h = 2/n`).
Its radicand is `1 − b_k² = (n² − (2k − n)²)/n²`, a NONNEGATIVE rational which is
STRICTLY POSITIVE for the interior `0 < k < n` and ZERO at the endpoints
`b_0 = −1` (`k = 0`) and `b_n = 1` (`k = n`).  We build the radical as a `CReal`
that is a genuine `sqrtFrom` for interior `k` and `czero` at the endpoints. -/

/-- The (Int) numerator `n² − (2k − n)²` of `1 − b_k²` at the cell boundary. -/
def bdyNum (n k : Nat) : Int :=
  (n : Int) * (n : Int) - (2 * (k : Int) - (n : Int)) * (2 * (k : Int) - (n : Int))

/-- **`0 < n² − (2k − n)²`** for the INTERIOR `0 < k < n`: factor
`= (2n − 2k)·(2k)`, a product of two positive even factors. -/
theorem bdyNum_pos {n k : Nat} (hk0 : 0 < k) (hkn : k < n) : 0 < bdyNum n k := by
  have hk0' : (0 : Int) < (k : Int) := by exact_mod_cast hk0
  have hkn' : (k : Int) < (n : Int) := by exact_mod_cast hkn
  show 0 < (n : Int) * (n : Int) - (2 * (k : Int) - (n : Int)) * (2 * (k : Int) - (n : Int))
  rw [SemicircleIntegral.int_sq_diff_factor (n : Int) (2 * (k : Int) - (n : Int))]
  have hf1 : (0 : Int) < (n : Int) - (2 * (k : Int) - (n : Int)) := by omega
  have hf2 : (0 : Int) < (n : Int) + (2 * (k : Int) - (n : Int)) := by omega
  exact Int.mul_pos hf1 hf2

/-- The positive rational radicand `1 − b_k² = (n² − (2k − n)²)/n²` at an INTERIOR
cell boundary `0 < k < n`. -/
def bdyOneMinusSq (n k : Nat) (hn : 0 < n) (_hk0 : 0 < k) (_hkn : k < n) : Q' :=
  Q'.mkPos (bdyNum n k) (SemicircleIntegral.omsDen n) (SemicircleIntegral.omsDen_pos hn)

/-- **`0 < 1 − b_k²`** for the interior boundary. -/
theorem bdyOneMinusSq_pos {n k : Nat} (hn : 0 < n) (hk0 : 0 < k) (hkn : k < n) :
    (0 : Q') < bdyOneMinusSq n k hn hk0 hkn := by
  show (0 : Int) * ((bdyOneMinusSq n k hn hk0 hkn).den : Int)
      < (bdyOneMinusSq n k hn hk0 hkn).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  show (0 : Int) < (Q'.mkPos (bdyNum n k) (SemicircleIntegral.omsDen n)
    (SemicircleIntegral.omsDen_pos hn)).num
  rw [Q'.mkPos_num]
  exact bdyNum_pos hk0 hkn

/-- The uniform lower-bound witness `L = 1/n` (reusing `SemicircleIntegral.nodeLB`):
`L² = 1/n² ≤ 1 − b_k²` for the interior boundary, since `n² − (2k − n)² ≥ 1`. -/
theorem bdyLB_sq_le {n k : Nat} (hn : 0 < n) (hk0 : 0 < k) (hkn : k < n) :
    SemicircleIntegral.nodeLB n hn * SemicircleIntegral.nodeLB n hn
      ≤ bdyOneMinusSq n k hn hk0 hkn := by
  show (SemicircleIntegral.nodeLB n hn * SemicircleIntegral.nodeLB n hn).num
        * ((bdyOneMinusSq n k hn hk0 hkn).den : Int)
      ≤ (bdyOneMinusSq n k hn hk0 hkn).num
        * ((SemicircleIntegral.nodeLB n hn * SemicircleIntegral.nodeLB n hn).den : Int)
  have hLnum : (SemicircleIntegral.nodeLB n hn * SemicircleIntegral.nodeLB n hn).num = 1 := by
    show (SemicircleIntegral.nodeLB n hn).num * (SemicircleIntegral.nodeLB n hn).num = 1
    show (Q'.mkPos 1 n hn).num * (Q'.mkPos 1 n hn).num = 1
    rw [Q'.mkPos_num]; decide
  have hd : (SemicircleIntegral.nodeLB n hn).den = n := Q'.mkPos_den 1 n hn
  have hLden : ((SemicircleIntegral.nodeLB n hn * SemicircleIntegral.nodeLB n hn).den : Int)
      = ((n * n : Nat) : Int) := by
    rw [Q'.mul_den_cast, hd]; push_cast; rfl
  rw [hLnum, hLden]
  show (1 : Int) * ((bdyOneMinusSq n k hn hk0 hkn).den : Int)
      ≤ (Q'.mkPos (bdyNum n k) (SemicircleIntegral.omsDen n)
            (SemicircleIntegral.omsDen_pos hn)).num
        * ((n * n : Nat) : Int)
  have hden2 : ((bdyOneMinusSq n k hn hk0 hkn).den : Int) = ((n * n : Nat) : Int) := by
    show ((Q'.mkPos (bdyNum n k) (SemicircleIntegral.omsDen n)
          (SemicircleIntegral.omsDen_pos hn)).den : Int) = ((n * n : Nat) : Int)
    rw [Q'.mkPos_den]; rfl
  rw [hden2, Q'.mkPos_num, Int.one_mul]
  have hnn : (0 : Int) < ((n * n : Nat) : Int) := by
    have := Nat.mul_pos hn hn; exact_mod_cast this
  have hge1 : 1 ≤ bdyNum n k := bdyNum_pos hk0 hkn
  calc ((n * n : Nat) : Int) = 1 * ((n * n : Nat) : Int) := by rw [Int.one_mul]
    _ ≤ bdyNum n k * ((n * n : Nat) : Int) :=
        Int.mul_le_mul_of_nonneg_right hge1 (Int.le_of_lt hnn)

/-- **The genuine cell-boundary radical** `√(1 − b_k²) : CReal`: the constructive
square root of the positive interior radicand for `0 < k < n`, and `czero` at the
endpoints `k = 0` (`b = −1`) and `k ≥ n` (in particular `k = n`, `b = 1`), where
`1 − b² = 0`. -/
def bdyRadical (n : Nat) (hn : 0 < n) (k : Nat) : CReal :=
  if hk0 : 0 < k then
    if hkn : k < n then
      CReal.sqrtFrom (bdyOneMinusSq n k hn hk0 hkn) (SemicircleIntegral.nodeLB n hn)
        (bdyOneMinusSq_pos hn hk0 hkn) (SemicircleIntegral.nodeLB_pos hn)
        (bdyLB_sq_le hn hk0 hkn)
    else CReal.czero
  else CReal.czero

/-- The radical at `k = 0` (the boundary `b_0 = −1`) is `czero`. -/
theorem bdyRadical_zero (n : Nat) (hn : 0 < n) : bdyRadical n hn 0 = CReal.czero := by
  unfold bdyRadical; rw [dif_neg (by decide : ¬ (0 < 0))]

/-- The radical at `k = n` (the boundary `b_n = 1`) is `czero`. -/
theorem bdyRadical_top (n : Nat) (hn : 0 < n) : bdyRadical n hn n = CReal.czero := by
  unfold bdyRadical
  rw [dif_pos hn, dif_neg (by omega : ¬ (n < n))]

/-! ## 1. The rational cell boundary `b_k = (2k − n)/n` -/

/-- The cell boundary `b_k = (2k − n)/n` (`= −1 + 2k/n`).  At `k = 0` this is `−1`,
at `k = n` it is `1` (used only as the `Gbracket` argument; the antiderivative
sample vanishes at the endpoints through the `czero` radical, independent of the
bracket value). -/
def bdyPoint (n : Nat) (hn : 0 < n) (k : Nat) : Q' :=
  Q'.mkPos (2 * (k : Int) - (n : Int)) n hn

/-! ## 2. The REAL-boundary antiderivative sample `GsampR`

`GsampR e he n k := ½·(√(1 − b_k²))·B_e(b_k) = Gfun e he (b_k) (bdyRadical n k)`.
This is the GENUINE antiderivative value at the interior boundary `b_k`, carrying
the real radical `√(1 − b_k²)` (NON-vanishing for `0 < k < n`).  Only the
endpoints `k = 0, n` vanish (their radical is `czero`).  This is the CORRECTION of
the degenerate `gSample` (which used `Gval(±1)` — the `czero` radical — for ALL
cells). -/

/-- The REAL-boundary antiderivative sample
`GsampR e he n k := ½·(√(1 − b_k²))·B_e(b_k)`. -/
def GsampR (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) : CReal :=
  Gfun e he (bdyPoint n hn k) (bdyRadical n hn k)

/-- **The endpoint samples vanish POINTWISE.**  For `k = 0` and `k = n` the
radical is `czero`, so `(GsampR …).approx p ≈ 0` (`½·(0·B) ≈ 0`).  The INTERIOR
samples do NOT vanish. -/
theorem GsampR_endpoint_approx_zero (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n)
    (k : Nat) (hk : k = 0 ∨ k = n) (p : Nat) :
    ((GsampR e he n hn k).approx p) ≈ (0 : Q') := by
  have hrad : bdyRadical n hn k = CReal.czero := by
    rcases hk with h0 | htop
    · rw [h0]; exact bdyRadical_zero n hn
    · rw [htop]; exact bdyRadical_top n hn
  show ((Q'.mkPos 1 2 (by decide))
        * ((bdyRadical n hn k).approx p * (Gbracket e he (bdyPoint n hn k))))
      ≈ (0 : Q')
  rw [hrad]
  have hcz : ((CReal.czero).approx p) = (0 : Q') := rfl
  rw [hcz]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv (Gbracket e he (bdyPoint n hn k)))) ?_
  exact Q'.mul_zero_eqv (Q'.mkPos 1 2 (by decide))

/-! ## 3. The telescoping increments and their VANISHING SUM (genuine FTC value)

`gIncrR e he n k := GsampR(k+1) − GsampR(k)`.  The PROVED rational
`ChebOrthoEvenFTC.telescope_sum` (instantiated at the approximation level) gives
`Σ_{k<n} gIncrR k ≈ GsampR(n) + (−GsampR(0))`.  Both endpoint samples vanish
(`GsampR_endpoint_approx_zero`), so `Σ_{k<n} gIncrR k ≈ 0` — with the INTERIOR
samples CANCELLING IN PAIRS through the telescope (genuine, not degenerate). -/

/-- The telescoping increment `gIncrR e he n k := GsampR(k+1) + (−GsampR(k))`. -/
def gIncrR (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) : CReal :=
  CReal.add (GsampR e he n hn (k + 1)) (CReal.neg (GsampR e he n hn k))

/-- **The increment-sum telescopes to the boundary difference (at every approx
index).**  `(csum (gIncrR e he n hn) n).approx p ≈ (GsampR n).approx p + (−(GsampR 0).approx p)`.
Pure application of the PROVED rational `telescope_sum` to the rational sequence
`g k := (GsampR e he n hn k).approx p`. -/
theorem gIncrRSum_telescope_approx (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (p : Nat) :
    ((CReal.csum (gIncrR e he n hn) n).approx p)
      ≈ (((GsampR e he n hn n).approx p) + (-((GsampR e he n hn 0).approx p))) := by
  rw [CReal.csum_approx (gIncrR e he n hn) n p]
  -- (gIncrR … k).approx p = (GsampR (k+1)).approx p + (−(GsampR k).approx p)  (definitional)
  have hterm : (fun k => (gIncrR e he n hn k).approx p)
      = (fun k => (GsampR e he n hn (k + 1)).approx p + (-((GsampR e he n hn k).approx p))) := rfl
  rw [hterm]
  -- telescope_sum applied to g k := (GsampR e he n hn k).approx p
  exact ChebOrthoEvenFTC.telescope_sum (fun k => (GsampR e he n hn k).approx p) n

/-- **The increment-sum vanishes at every approximation.**  Both telescoped
endpoints `GsampR(n)`, `GsampR(0)` vanish pointwise (`GsampR_endpoint_approx_zero`),
so the boundary difference is `≈ 0`. -/
theorem gIncrRSum_approx_zero (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (p : Nat) :
    ((CReal.csum (gIncrR e he n hn) n).approx p) ≈ (0 : Q') := by
  refine Q'.eqv_trans _ _ _ (gIncrRSum_telescope_approx e he n hn p) ?_
  have hn0 : ((GsampR e he n hn n).approx p) ≈ (0 : Q') :=
    GsampR_endpoint_approx_zero e he n hn n (Or.inr rfl) p
  have h00 : ((GsampR e he n hn 0).approx p) ≈ (0 : Q') :=
    GsampR_endpoint_approx_zero e he n hn 0 (Or.inl rfl) p
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hn0 (Q'.neg_eqv_congr _ _ h00)) ?_
  exact Q'.add_neg_self_eqv (0 : Q')

/-- **The increment-sum VANISHES (value level).**  `csum (gIncrR e he n hn) n ≈ czero`.
This is the constructive-FTC boundary value with the GENUINE interior antiderivative
samples: `Σ gIncrR ≈ GsampR(1) − GsampR(−1) ≈ 0` (interior samples cancel in pairs;
only the endpoints — vanishing — survive). -/
theorem gIncrRSum_vanishes (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) :
    CReal.Equiv (CReal.csum (gIncrR e he n hn) n) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun p => by
    show ((CReal.csum (gIncrR e he n hn) n).approx p) ≈ ((CReal.czero).approx p)
    have hcz : ((CReal.czero).approx p) = (0 : Q') := rfl
    rw [hcz]
    exact gIncrRSum_approx_zero e he n hn p)

/-! ## 4. The adjusted cell family and the FTC value reformulation

`cellAdjR e he n hn k := orthTerm e n hn k + gIncrR e he n hn k` is the
midpoint-quadrature cell adjusted by the GENUINE antiderivative increment.  After
the adjustment each cell is the MIDPOINT ERROR `orthTerm k + (GsampR(b_{k+1}) −
GsampR(b_k))` (small, by `Gval′ = −f_e`), so its `leRat` bound CAN be summed to a
vanishing budget — the residual `RealPerCellBudget`. -/

/-- The adjusted cell `cellAdjR e he n hn k := orthTerm e n hn k + gIncrR e he n hn k`. -/
def cellAdjR (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) (k : Nat) : CReal :=
  CReal.add (orthTerm e n hn k) (gIncrR e he n hn k)

/-- **The FTC value reformulation (REAL boundaries).**
`orthSum e n ≈ csum (cellAdjR e he n hn) n`.  By `csum`-additivity (proved
pointwise) the adjusted cell-sum splits as `csum orthTerm n + csum (gIncrR) n =
orthSum e n + (Σ gIncrR)`; the increment-sum VANISHES (`gIncrRSum_approx_zero`),
so the whole is `Equiv` to `orthSum e n`.  This is the genuine bridge from the
Riemann sum to the GENUINE adjusted (midpoint-error) cell-sum. -/
theorem orthSum_eqv_cellAdjRSum (e : Nat) (he : 0 < e) (n : Nat) (hn : 0 < n) :
    CReal.Equiv (orthSum e n hn) (CReal.csum (cellAdjR e he n hn) n) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  rw [CReal.csum_approx (cellAdjR e he n hn) n p]
  -- (cellAdjR … k).approx p = orthTerm_k.approx p + gIncrR_k.approx p (definitional)
  have hterm : (fun k => (cellAdjR e he n hn k).approx p)
      = (fun k => (orthTerm e n hn k).approx p + (gIncrR e he n hn k).approx p) := rfl
  rw [hterm]
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_add (fun k => (orthTerm e n hn k).approx p)
      (fun k => (gIncrR e he n hn k).approx p) n) ?_
  have hO : (RationalTail.finSum (fun k => (orthTerm e n hn k).approx p) n)
      = (orthSum e n hn).approx p := by
    rw [show (orthSum e n hn).approx p
        = RationalTail.finSum (fun k => (orthTerm e n hn k).approx p) n from
      CReal.csum_approx (orthTerm e n hn) n p]
  have hG : (RationalTail.finSum (fun k => (gIncrR e he n hn k).approx p) n) ≈ (0 : Q') := by
    have := gIncrRSum_approx_zero e he n hn p
    rwa [CReal.csum_approx (gIncrR e he n hn) n p] at this
  rw [hO]
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hG) ?_
  rw [Q'.add_zero']; exact Q'.eqv_refl _

/-! ## 5. The REAL per-cell midpoint budget (the precise analytic residual)

`RealPerCellBudget e` records the SATISFIABLE midpoint-quadrature estimate in
exactly the shape the value reformulation consumes: a per-cell nonnegative rate
`r n k` that two-sidedly `leRat`-bounds each GENUINE adjusted cell `cellAdjR e n k`,
with the finite sums `Σ_{k<n} r n k` vanishing as `n → ∞`.  Because `cellAdjR k`
is the REAL midpoint error (interior `Gval(b_k)` samples, not the degenerate
`Gval(±1)` filler), this is the SATISFIABLE shape, NOT the unsatisfiable raw-
`orthTerm` bound. -/

/-- **NAMED-open: the REAL per-cell midpoint budget.**  For the even order `e`
(`he : 0 < e`), there is a per-cell rate `r : Nat → Nat → Q'` such that:
  * each rate is nonnegative;
  * each REAL adjusted cell is two-sidedly bounded:
    `leRat (cellAdjR e he (N+1) … k) (r (N+1) k)` and the negation;
  * the finite sums vanish: for every `ε > 0`, eventually
    `finSum (r (N+1)) (N+1) ≤ ε`.
This is the constructive midpoint-quadrature ESTIMATE on the GENUINE
real-boundary adjusted cells; with `Bderiv_identity_uncond` (`Gval′ = −f_e`),
`holder_oneMinusSq` and `|U_e| ≤ e+1`, the interior (`C(e)·h^{3/2}`, summed
`C(e)·√h`) + boundary (`C(e)·δ^{1/2}` over `O(nδ)` cells) split balanced at
`δ ≈ √h` yields such a vanishing rate.  Recorded as the precise residual. -/
def RealPerCellBudget (e : Nat) (he : 0 < e) : Prop :=
  ∃ r : Nat → Nat → Q',
    (∀ n k, (0 : Q') ≤ r n k) ∧
    (∀ N k,
      CReal.leRat (cellAdjR e he (N + 1) (Nat.succ_pos N) k) (r (N + 1) k) ∧
      CReal.leRat (CReal.neg (cellAdjR e he (N + 1) (Nat.succ_pos N) k)) (r (N + 1) k)) ∧
    (∀ ε : Q', (0 : Q') < ε → ∃ M : Nat, ∀ N : Nat, M ≤ N →
      (RationalTail.finSum (r (N + 1)) (N + 1)) ≤ ε)

/-! ## 6. The genuine reduction `RealPerCellBudget e → BudgetExists e` -/

/-- Helper: `Equiv` is preserved under negation. -/
theorem neg_Equiv_of_Equiv {A B : CReal} (h : CReal.Equiv A B) :
    CReal.Equiv (CReal.neg A) (CReal.neg B) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  show (-(A.approx n)) ≤ (-(B.approx n)) + ε ∧ (-(B.approx n)) ≤ (-(A.approx n)) + ε
  exact ⟨Q'.neg_le_neg_add h2, Q'.neg_le_neg_add h1⟩

/-- Helper: the negation of a cell-sum approximates the sum of the negated cells. -/
theorem neg_csum_approx_eqv (f : Nat → CReal) (n : Nat) (p : Nat) :
    ((CReal.neg (CReal.csum f n)).approx p)
      ≈ ((CReal.csum (fun k => CReal.neg (f k)) n).approx p) := by
  show (-( (CReal.csum f n).approx p)) ≈ ((CReal.csum (fun k => CReal.neg (f k)) n).approx p)
  rw [CReal.csum_approx f n p, CReal.csum_approx (fun k => CReal.neg (f k)) n p]
  show (-(RationalTail.finSum (fun i => (f i).approx p) n))
      ≈ (RationalTail.finSum (fun i => -((f i).approx p)) n)
  exact ChebOrthoOffDiag.finSum_neg (fun i => (f i).approx p) n

/-- **THE REDUCTION.**  `RealPerCellBudget e → BudgetExists e`.  The per-cell
two-sided `leRat` bounds sum (via `leRat_csum`) to a two-sided bound on the
REAL adjusted cell-sum `csum (cellAdjR) (N+1)`, whose value equals `orthSum e (N+1)`
(`orthSum_eqv_cellAdjRSum`, transferred by `leRat_of_equiv`); the vanishing
finite-sum rate `B N := finSum (r (N+1)) (N+1)` is the resulting `RateToZero`
budget. -/
theorem budgetExists_of_realPerCell (e : Nat) (he : 0 < e)
    (h : RealPerCellBudget e he) : BudgetExists e := by
  obtain ⟨r, hr0, hrbnd, hrlim⟩ := h
  refine ⟨fun N => RationalTail.finSum (r (N + 1)) (N + 1), ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro N
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
  · intro N
    have hN1 : (0 : Nat) < N + 1 := Nat.succ_pos N
    have hsum_pos : CReal.leRat (CReal.csum (cellAdjR e he (N + 1) hN1) (N + 1))
        (RationalTail.finSum (r (N + 1)) (N + 1)) :=
      CReal.leRat_csum (cellAdjR e he (N + 1) hN1) (r (N + 1))
        (fun k => (hrbnd N k).1) (N + 1)
    have hsum_neg' : CReal.leRat
        (CReal.csum (fun k => CReal.neg (cellAdjR e he (N + 1) hN1 k)) (N + 1))
        (RationalTail.finSum (r (N + 1)) (N + 1)) :=
      CReal.leRat_csum (fun k => CReal.neg (cellAdjR e he (N + 1) hN1 k)) (r (N + 1))
        (fun k => (hrbnd N k).2) (N + 1)
    have hsum_neg : CReal.leRat (CReal.neg (CReal.csum (cellAdjR e he (N + 1) hN1) (N + 1)))
        (RationalTail.finSum (r (N + 1)) (N + 1)) :=
      CReal.leRat_congr (neg_csum_approx_eqv (cellAdjR e he (N + 1) hN1) (N + 1)) hsum_neg'
    have hEq : CReal.Equiv (orthSum e (N + 1) hN1)
        (CReal.csum (cellAdjR e he (N + 1) hN1) (N + 1)) :=
      orthSum_eqv_cellAdjRSum e he (N + 1) hN1
    have hseq : seqOrthEv e N = orthSum e (N + 1) hN1 := rfl
    refine ⟨?_, ?_⟩
    · rw [hseq]
      exact CReal.leRat_of_equiv hEq hsum_pos
    · rw [hseq]
      exact CReal.leRat_of_equiv (neg_Equiv_of_Equiv hEq) hsum_neg

/-! ## 7. The even-order limit and the full off-diagonal closure (conditional) -/

/-- **`OrthEvenZeroLimit e` from the REAL per-cell midpoint budget.**  Composes the
reduction with the companion bridge `orthEvenZeroLimit_of_budgetExists`. -/
theorem orthEvenZeroLimit_of_realPerCell (e : Nat) (he : 0 < e)
    (h : RealPerCellBudget e he) :
    ChebOrthoEvenFTC.OrthEvenZeroLimit e :=
  orthEvenZeroLimit_of_budgetExists e (budgetExists_of_realPerCell e he h)

/-- **Off-diagonal orthogonality `∫U_e√ = 0` for `e ≥ 1`, from the REAL per-cell
budget (even orders).**  The ODD case is already UNCONDITIONAL; the EVEN case via
the REAL per-cell budget + the proved bridges.  π-free. -/
theorem offdiag_closed_of_realPerCell
    (hbud : ∀ (e : Nat) (he : 0 < e), 2 ≤ e → e % 2 = 0 → RealPerCellBudget e he) :
    ∀ (e : Nat), 1 ≤ e →
      ∃ L : CReal, CReal.ConvergesTo (seqOrth e) L ∧ CReal.Equiv L CReal.czero := by
  refine offdiag_closed_of_budget (fun e he2 heven => ?_)
  have he : 0 < e := by omega
  exact budgetExists_of_realPerCell e he (hbud e he he2 heven)

end YMGap.Continuum.ChebOrthoMidpoint

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `bdyNum` / `bdyNum_pos` / `bdyOneMinusSq` / `bdyOneMinusSq_pos` / `bdyLB_sq_le`
    — the genuine cell-boundary radicand `1 − b_k² = (n² − (2k − n)²)/n²` at the
    REAL boundary `b_k = (2k − n)/n`, its strict interior positivity, and the
    `L = 1/n` `sqrtFrom` witness.
  * `bdyRadical` / `bdyRadical_zero` / `bdyRadical_top` — the genuine radical
    `√(1 − b_k²) : CReal` (`sqrtFrom` for `0 < k < n`, `czero` at the endpoints).
  * `bdyPoint` — the rational boundary `b_k = (2k − n)/n`.
  * `GsampR` / **`GsampR_endpoint_approx_zero`** — the REAL-boundary antiderivative
    sample `½·√(1 − b_k²)·B_e(b_k)` (genuine interior values), with ONLY the
    endpoints vanishing pointwise (via the `czero` radical).
  * `gIncrR` / `gIncrRSum_telescope_approx` / `gIncrRSum_approx_zero` /
    **`gIncrRSum_vanishes`** — the GENUINE telescoping `Σ gIncrR ≈ czero`: the
    PROVED rational `telescope_sum` collapses to the endpoint difference (both
    vanishing), the INTERIOR samples cancelling in pairs.  This corrects the
    degenerate `gSample` path (where the interior samples were the constant filler
    `Gval(1)` and never cancelled meaningfully).
  * `cellAdjR` / **`orthSum_eqv_cellAdjRSum`** — the FTC value reformulation
    `orthSum e n ≈ csum (cellAdjR) n` with the GENUINE midpoint-error cell
    `cellAdjR k = orthTerm k + (GsampR(b_{k+1}) − GsampR(b_k))`.
  * `neg_Equiv_of_Equiv` / `neg_csum_approx_eqv` — the negation helpers.
  * **`budgetExists_of_realPerCell`** — the genuine reduction
    `RealPerCellBudget e → BudgetExists e`: per-cell `leRat` bounds summed via
    `leRat_csum`, transferred through the REAL value reformulation by
    `leRat_of_equiv`, packaged as the `RateToZero` budget.
  * `orthEvenZeroLimit_of_realPerCell` / `offdiag_closed_of_realPerCell` — the
    even-order `czero` limit and the COMBINED π-free off-diagonal orthogonality
    `∫U_e√ = 0` for `e ≥ 1`, conditional on the REAL per-cell budget (odd
    UNCONDITIONAL).

**NAMED-open (the honest residual — ONE analytic estimate).**
  * `RealPerCellBudget e` — the constructive midpoint-quadrature ESTIMATE on the
    GENUINE real-boundary adjusted cells `cellAdjR k = orthTerm k + (GsampR(b_{k+1})
    − GsampR(b_k))`.  This is the SATISFIABLE shape (the cells are the REAL
    midpoint error, NOT the raw Riemann terms): by `Bderiv_identity_uncond`
    (`Gval′ = −f_e`, `f_e = U_e·√(1−x²)`) the increment is
    `GsampR(b_{k+1}) − GsampR(b_k) ≈ −f_e(x_k)·h + (midpoint error)`, and
    `orthTerm k = f_e(x_k)·h`, so `cellAdjR k ≈ midpoint error`, bounded by the
    √-Hölder modulus of `f_e` (`SqrtSubadd.holder_oneMinusSq` + `|U_e| ≤ e+1`).
    Interior cells `≤ C(e)·h^{3/2}` (summed `C(e)·√h`); boundary cells (the
    `O(nδ)` cells with `√(1−b²) < δ`) `≤ C(e)·δ^{1/2}`; the balance `δ ≈ √h` sends
    both to `0`.  The value reformulation that consumes it is PROVED here — the
    degenerate `gSample` mistake is corrected (the adjustment uses the REAL
    interior `GsampR(b_k)`, so `cellAdjR` genuinely captures the midpoint
    cancellation).

**Path to closure.**  Once `RealPerCellBudget e` holds for every even `e ≥ 2`,
`budgetExists_of_realPerCell` closes `BudgetExists e`, hence (via the proved
`convergesTo_czero_of_bound`) `OrthEvenZeroLimit e` and the full π-free
off-diagonal orthogonality `∫U_e√ = 0` for all `e ≥ 1`.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoMidpoint.bdyNum_pos
#print axioms YMGap.Continuum.ChebOrthoMidpoint.bdyOneMinusSq_pos
#print axioms YMGap.Continuum.ChebOrthoMidpoint.bdyLB_sq_le
#print axioms YMGap.Continuum.ChebOrthoMidpoint.bdyRadical_zero
#print axioms YMGap.Continuum.ChebOrthoMidpoint.bdyRadical_top
#print axioms YMGap.Continuum.ChebOrthoMidpoint.GsampR_endpoint_approx_zero
#print axioms YMGap.Continuum.ChebOrthoMidpoint.gIncrRSum_telescope_approx
#print axioms YMGap.Continuum.ChebOrthoMidpoint.gIncrRSum_vanishes
#print axioms YMGap.Continuum.ChebOrthoMidpoint.orthSum_eqv_cellAdjRSum
#print axioms YMGap.Continuum.ChebOrthoMidpoint.budgetExists_of_realPerCell
#print axioms YMGap.Continuum.ChebOrthoMidpoint.orthEvenZeroLimit_of_realPerCell
#print axioms YMGap.Continuum.ChebOrthoMidpoint.offdiag_closed_of_realPerCell
