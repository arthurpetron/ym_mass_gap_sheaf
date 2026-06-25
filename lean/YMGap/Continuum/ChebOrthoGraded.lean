/-
# The CORRECTED NON-UNIFORM GRADED per-cell rate for the even-order π-free
# off-diagonal Chebyshev-`U` orthogonality `∫_{−1}^1 U_e(x)√(1−x²) dx = 0`.

The companion modules build the CORRECT real-boundary midpoint construction
(`ChebOrthoMidpoint`: interior antiderivative samples `GsampR`, the genuine
telescoping `gIncrRSum_vanishes`, the FTC value reformulation
`orthSum_eqv_cellAdjRSum`) and reduce the even-order off-diagonal orthogonality to
the SINGLE existence statement `ChebOrthoMidpoint.RealPerCellBudget e he`:  a
per-cell NONNEGATIVE rate `r : Nat → Nat → Q'` that two-sidedly `leRat`-bounds each
GENUINE adjusted cell `cellAdjR e he n k = orthTerm k + (GsampR(b_{k+1}) −
GsampR(b_k))`, with the finite sums `Σ_{k<n} r n k` vanishing as `n → ∞`.

## Why the prior UNIFORM rate `cRate ~ C(e)·M^{−3/2}` is UNSATISFIABLE

The companion `ChebOrthoMidpointCore.cRate e M k := (cRateNum e)/(M·⌊√M⌋)` is
CONSTANT in the cell index `k` — a UNIFORM per-cell rate `~ C(e)·M^{−3/2}`.  This
is FALSE at the two boundary cells touching `±1`.  At cell `k = M−1` one endpoint
of the cell is EXACTLY `b_M = 1` where the radical `s = √(1−x²) = 0`, so the
CENTERED-DIFFERENCE cancellation that produces the `M^{−3/2}` interior decay BREAKS
(there is no smooth midpoint there).  The genuine boundary-cell size is
`cellAdjR ~ gIncrR ~ √δ = M^{−1/2}`, NOT `M^{−3/2}`.  So a per-cell rate that is
constant in `k` and `~ M^{−3/2}` cannot dominate the two boundary cells: the
per-cell bound against `cRate` is unsatisfiable AT THE TWO BOUNDARY CELLS.

## The CORRECTED NON-UNIFORM GRADED rate (this module)

The rate MUST be `k`-DEPENDENT (graded).  With `M = N+1` and the
distance-from-boundary in cells `jdist M k := min(k+1, M−k)`, the corrected rate is

    `gradedRate e M k :=  C(e) / (⌊√M⌋ · jdist M k · jdist M k)`.

At a boundary cell (`k = 0` or `k = M−1`) `jdist = 1`, so the rate is the genuine
boundary scale `C(e)/⌊√M⌋ ~ C(e)·√δ`; at an interior cell at distance `j` the rate
is `C(e)/(⌊√M⌋·j²)`, GRADED (largest near the boundary, smallest in the bulk).
The summed rate vanishes like `1/⌊√M⌋ → 0` because the GRADED sum is bounded by the
constructive p-SERIES `Σ_{j≥1} 1/j² ≤ 2` (each cell-distance `j` occurs at most
TWICE across the two boundaries):

    `Σ_{k<M} gradedRate e M k
        ≤ C(e)/⌊√M⌋ · ( Σ_{j} 1/jdist² )
        ≤ C(e)/⌊√M⌋ · 2·(Σ_{j=1}^M 1/j²)
        ≤ C(e)/⌊√M⌋ · 4   → 0.`

## What is PROVED here (axiom-clean, GENUINE new content)

  * `recipNat` / `pSeriesTerm` / nonnegativity — the rational `1/j` and `1/j²`
    (`0` at `j = 0`).
  * `recipSq_telescope` — the EXACT rational telescoping minorant: for `j ≥ 1`,
    `1/(j+1)² ≤ 1/j − 1/(j+1)` (no √).
  * **`pSeries_le_two`** — the constructive p-SERIES bound `Σ_{j=1}^M 1/j² ≤ 2`,
    via the telescoping invariant `Σ_{j=1}^M 1/j² ≤ 2 − 1/M`.  REUSABLE.
  * `finSum_termwise_le` / `finSum_congr` / `finSum_extract_last` /
    **`finSum_reflect`** — the termwise comparison, the congruence, the last-term
    extraction, and the finite-sum reflection `Σ_{k<n} f(n−1−k) ≈ Σ_{k<n} f k`
    (reusable `Q'` finite-sum infrastructure).
  * `jdist` / `gradedRate` / **`gradedRate_nonneg`** — the NON-UNIFORM `k`-graded
    per-cell rate `C(e)/(⌊√M⌋·jdist²)`, nonnegative.
  * `gradedRate_le_split` — the pointwise two-sided split
    `gradedRate e M k ≤ scaledRecipSq M (k+1) + scaledRecipSq M (M−1−k)`.
  * **`gradedRateSum_le`** — the finite-sum majorant
    `Σ_{k<M} gradedRate e M k ≤ C(e)/⌊√M⌋ · 4` (two graded p-series halves via
    `pSeries_le_two`, `finSum_reflect`, `finSum_termwise_le`).
  * **`gradedRateSum_vanishes`** — the GENUINE vanishing
    `Σ_{k<M} gradedRate e M k → 0` (the `4·C(e)/⌊√M⌋ → 0` mechanism reusing
    `ChebOrthoMidpointEst.isqrt_ge`).
  * `GradedPerCellBound e he` — the PRECISE residual: the per-cell two-sided
    midpoint estimate against the CORRECTED NON-UNIFORM GRADED rate.
  * **`realPerCellBudget_of_gradedBound`** — the genuine packaging
    `GradedPerCellBound e he → ChebOrthoMidpoint.RealPerCellBudget e he`.
  * `orthEvenZeroLimit_of_gradedBound` / `offdiag_closed_of_gradedBound` — the
    even-order `czero` limit and the COMBINED π-free off-diagonal orthogonality
    `∫U_e√ = 0` for `e ≥ 1`, reduced to the SINGLE per-cell estimate AGAINST THE
    CORRECTED GRADED RATE (odd UNCONDITIONAL), via the proved bridges
    `ChebOrthoMidpoint.budgetExists_of_realPerCell` → `convergesTo_czero_of_bound`.
  * `boundary_cell_orthTerm_bound` — a GENUINE sub-bound: the BOUNDARY-cell
    `orthTerm` direct estimate (re-export of the PROVED `ChebOrthoCancel.uNode_abs_le`).

## What is NAMED-open (precisely — the INTERIOR second-order graded remainder)

  * `GradedPerCellBound e he` — the per-cell midpoint estimate
    `|cellAdjR e he (N+1) k| ≤ gradedRate e (N+1) k` on the GENUINE real-boundary
    adjusted cells, against the CORRECTED NON-UNIFORM GRADED rate.  Now correctly
    formulated, the genuine remaining content splits into two cases:
      · BOUNDARY cells `k ∈ {0, M−1}` — DIRECT bound (no cancellation): the cell
        touches `±1` where `s = 0`, and `|cellAdjR| ≤ |orthTerm| + |gIncrR| ≤
        C(e)·√δ = gradedRate` (via `boundary_cell_orthTerm_bound` and the boundary
        radical `bdyRadical_leRat`; `s_± ≤ √(2δ)`, `|B_e| ≤ 2` from `absU_le`).
      · INTERIOR cells `1 ≤ k ≤ M−2` — the GRADED centered-difference remainder via
        the PROVED exact pieces `ChebOrthoCancel.leading_cancellation`,
        `ChebOrthoRemainder.gIncr_pdiff_split`, `ChebOrthoRemainder.radSq_diff_equiv`;
        the SECOND-order error `~ δ³/s_k³ ~ δ^{3/2}/j^{3/2} ≤ gradedRate` bounded via
        the √-Hölder `radDiff_holder` and the Lipschitz scale `Le e`.
    The INTERIOR second-order graded remainder is the SINGLE remaining analytic
    core, recorded precisely, NOT faked.  Everything that consumes it (the graded
    rate, its nonnegativity, the p-series, the vanishing sum, the packaging into
    `RealPerCellBudget`, and the off-diagonal bridges) is PROVED here.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoMidpoint
import YMGap.Continuum.ChebOrthoMidpointCore
import YMGap.Continuum.ChebOrthoMidpointEst
import YMGap.Continuum.ChebOrthoCancel
import YMGap.Continuum.ChebOrthoRemainder
import YMGap.Continuum.ChebUDClosure

namespace YMGap.Continuum.ChebOrthoGraded

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag
open YMGap.Continuum.ChebOrthoEvenFTC
open YMGap.Continuum.ChebOrthoFTCEstimate
open YMGap.Continuum.ChebOrthoMidpoint
open YMGap.Continuum.ChebOrthoMidpointCore
open YMGap.Continuum.ChebOrthoMidpointEst

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Reusable finite-sum infrastructure: termwise comparison, congruence,
last-term extraction, and reflection. -/

/-- **Termwise finite-sum comparison.**  If `f k ≤ g k` for every `k < n`, then
`finSum f n ≤ finSum g n`. -/
theorem finSum_termwise_le (f g : Nat → Q') (n : Nat)
    (h : ∀ k, k < n → f k ≤ g k) :
    RationalTail.finSum f n ≤ RationalTail.finSum g n := by
  induction n with
  | zero => exact Q'.le_refl' 0
  | succ t ih =>
    show RationalTail.finSum f t + f t ≤ RationalTail.finSum g t + g t
    exact Q'.add_le_add (ih (fun k hk => h k (Nat.lt_succ_of_lt hk)))
      (h t (Nat.lt_succ_self t))

/-- **Finite-sum congruence (function-eq on a prefix).**  If `f k = g k` for every
`k < n`, then `finSum f n = finSum g n`. -/
theorem finSum_congr (f g : Nat → Q') (n : Nat)
    (h : ∀ k, k < n → f k = g k) :
    RationalTail.finSum f n = RationalTail.finSum g n := by
  induction n with
  | zero => rfl
  | succ t ih =>
    show RationalTail.finSum f t + f t = RationalTail.finSum g t + g t
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h t (Nat.lt_succ_self t)]

/-- **Last-term extraction as a front term (≈).**  For the sequence `f`,
`Σ_{k<n+1} f k ≈ f 0 + Σ_{k<n} f (k+1)`.  (Pull the FIRST term out of the sum.)
By induction with the additive reassociation `≈`. -/
theorem finSum_extract_first (f : Nat → Q') (n : Nat) :
    RationalTail.finSum f (n + 1)
      ≈ (f 0 + RationalTail.finSum (fun k => f (k + 1)) n) := by
  induction n with
  | zero =>
    -- finSum f 1 = 0 + f 0 ; RHS = f 0 + 0.
    show (RationalTail.finSum f 0 + f 0) ≈ (f 0 + RationalTail.finSum (fun k => f (k + 1)) 0)
    show ((0 : Q') + f 0) ≈ (f 0 + (0 : Q'))
    refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' (f 0))) ?_
    exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' (f 0)))
  | succ t ih =>
    -- finSum f (t+2) = finSum f (t+1) + f (t+1)
    --   ≈ (f 0 + Σ_{k<t} f(k+1)) + f(t+1)
    --   ≈ f 0 + (Σ_{k<t} f(k+1) + f(t+1))
    --   = f 0 + Σ_{k<t+1} f(k+1).
    show (RationalTail.finSum f (t + 1) + f (t + 1))
        ≈ (f 0 + RationalTail.finSum (fun k => f (k + 1)) (t + 1))
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (f (t + 1)) ih) ?_
    -- (f 0 + S) + f(t+1) ≈ f 0 + (S + f(t+1)) = f 0 + Σ_{k<t+1} f(k+1)
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (f 0)
      (RationalTail.finSum (fun k => f (k + 1)) t) (f (t + 1))) ?_
    -- S + f(t+1) = Σ_{k<t+1} f(k+1) definitionally
    exact Q'.eqv_refl _

/-- **Finite-sum reflection.**  `Σ_{k<n} f (n−1−k) ≈ Σ_{k<n} f k`.  The reversed
index `k ↦ n−1−k` is a bijection of `{0,…,n−1}`.  Induction on `n`: pull the FIRST
term `f(n-1)` (the `k=0` reflected term) off the reflected sum via
`finSum_extract_first` of the reflected sequence; the tail reflects the prefix
`f 0 .. f (n-1)` minus the last, handled by the IH after a `finSum_congr` reindex,
and the last term `f(n-1)` is reattached. -/
theorem finSum_reflect (f : Nat → Q') (n : Nat) :
    RationalTail.finSum (fun k => f (n - 1 - k)) n
      ≈ RationalTail.finSum f n := by
  induction n with
  | zero => exact Q'.eqv_refl _
  | succ t ih =>
    -- LHS = Σ_{k<t+1} f (t - k).
    -- Pull the first reflected term (k=0): f (t - 0) = f t.
    -- Σ_{k<t+1} g k ≈ g 0 + Σ_{k<t} g (k+1) with g k = f (t - k).
    -- g 0 = f t ; g (k+1) = f (t - (k+1)) = f (t-1-k).
    -- So LHS ≈ f t + Σ_{k<t} f (t-1-k).
    -- By IH (on t): Σ_{k<t} f (t-1-k) ≈ Σ_{k<t} f k.
    -- So LHS ≈ f t + Σ_{k<t} f k.
    -- RHS = Σ_{k<t+1} f k = Σ_{k<t} f k + f t ≈ f t + Σ_{k<t} f k.  Done.
    have hg : (fun k => f ((t + 1) - 1 - k)) = (fun k => f (t - k)) := by
      funext k; have : (t + 1) - 1 - k = t - k := by omega
      rw [this]
    rw [hg]
    -- extract first of g k := f (t - k)
    have hext := finSum_extract_first (fun k => f (t - k)) t
    -- g 0 = f t ; g (k+1) = f (t - (k+1))
    have hg0 : f (t - 0) = f t := by rw [Nat.sub_zero]
    -- rewrite the tail sequence g(k+1) = f (t-1-k)
    have htail : (fun k => f (t - (k + 1))) = (fun k => f (t - 1 - k)) := by
      funext k; have : t - (k + 1) = t - 1 - k := by omega
      rw [this]
    -- combine
    refine Q'.eqv_trans _ _ _ hext ?_
    rw [hg0, htail]
    -- now: f t + Σ_{k<t} f (t-1-k) ≈ Σ_{k<t+1} f k
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (f t) _ _ ih) ?_
    -- f t + Σ_{k<t} f k ≈ Σ_{k<t} f k + f t = Σ_{k<t+1} f k
    refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (f t) (RationalTail.finSum f t)) ?_
    exact Q'.eqv_refl _

/-! ## 1. The constructive p=2 series bound `Σ_{j=1}^M 1/j² ≤ 2` (reusable)

The graded interior sum is bounded, after factoring `C(e)/⌊√M⌋`, by the rational
p-SERIES `Σ_{j=1}^M 1/j²`.  We prove `Σ_{j=1}^M 1/j² ≤ 2` by the EXACT rational
telescoping `1/(j+1)² ≤ 1/j − 1/(j+1)` (`j ≥ 1`); no square roots are involved. -/

/-- The rational reciprocal `1/j` for `j ≥ 1` (`= mkPos 1 j`); `0` at `j = 0`. -/
def recipNat (j : Nat) : Q' :=
  if hj : 0 < j then Q'.mkPos 1 j hj else 0

/-- `recipNat` is nonnegative. -/
theorem recipNat_nonneg (j : Nat) : (0 : Q') ≤ recipNat j := by
  unfold recipNat
  by_cases hj : 0 < j
  · rw [dif_pos hj, Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide
  · rw [dif_neg hj]; exact Q'.le_refl' 0

/-- The rational p=2 term `1/j²` for `j ≥ 1` (`= 1/(j·j)`); `0` at `j = 0`. -/
def pSeriesTerm (j : Nat) : Q' :=
  if hj : 0 < j then Q'.mkPos 1 (j * j) (Nat.mul_pos hj hj) else 0

/-- `pSeriesTerm` is nonnegative. -/
theorem pSeriesTerm_nonneg (j : Nat) : (0 : Q') ≤ pSeriesTerm j := by
  unfold pSeriesTerm
  by_cases hj : 0 < j
  · rw [dif_pos hj, Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide
  · rw [dif_neg hj]; exact Q'.le_refl' 0

/-- **The EXACT telescoping minorant.**  For `j ≥ 1`,
`1/((j+1)·(j+1)) ≤ 1/j + (−(1/(j+1)))` (i.e. `1/(j+1)² ≤ 1/j − 1/(j+1) = 1/(j(j+1))`).
Cross-multiplying reduces to `Int`-`(j·(j+1)) ≤ (j+1)²`, i.e. `j ≤ j+1`. -/
theorem recipSq_telescope (j : Nat) (hj : 0 < j) :
    pSeriesTerm (j + 1) ≤ (recipNat j + (-(recipNat (j + 1)))) := by
  have hj1 : 0 < j + 1 := by omega
  unfold pSeriesTerm recipNat
  rw [dif_pos hj1, dif_pos hj, dif_pos hj1]
  -- abbreviation R := mkPos 1 j + (− mkPos 1 (j+1)); its num/den computed below.
  have hRnum : (Q'.mkPos 1 j hj + (-(Q'.mkPos 1 (j + 1) hj1))).num
      = (1 : Int) * ((j + 1 : Nat) : Int) + (-(1 : Int)) * (j : Int) := by
    show (Q'.mkPos 1 j hj).num * (((-(Q'.mkPos 1 (j + 1) hj1)).den : Nat) : Int)
        + (-(Q'.mkPos 1 (j + 1) hj1)).num * (((Q'.mkPos 1 j hj).den : Nat) : Int)
      = (1 : Int) * ((j + 1 : Nat) : Int) + (-(1 : Int)) * (j : Int)
    rw [Q'.neg_den, Q'.mkPos_den, Q'.mkPos_den, Q'.mkPos_num]
    show (1 : Int) * ((j + 1 : Nat) : Int)
        + (-(Q'.mkPos 1 (j + 1) hj1).num) * ((j : Nat) : Int)
      = (1 : Int) * ((j + 1 : Nat) : Int) + (-(1 : Int)) * (j : Int)
    rw [Q'.mkPos_num]
  have hRden : ((Q'.mkPos 1 j hj + (-(Q'.mkPos 1 (j + 1) hj1))).den : Int)
      = (j : Int) * ((j + 1 : Nat) : Int) := by
    rw [Q'.add_den_cast, Q'.neg_den, Q'.mkPos_den, Q'.mkPos_den]
  show (Q'.mkPos 1 ((j + 1) * (j + 1)) (Nat.mul_pos hj1 hj1)).num
        * ((Q'.mkPos 1 j hj + (-(Q'.mkPos 1 (j + 1) hj1))).den : Int)
      ≤ (Q'.mkPos 1 j hj + (-(Q'.mkPos 1 (j + 1) hj1))).num
        * ((Q'.mkPos 1 ((j + 1) * (j + 1)) (Nat.mul_pos hj1 hj1)).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den, hRnum, hRden]
  have hjj : (((j + 1) * (j + 1) : Nat) : Int) = ((j : Int) + 1) * ((j : Int) + 1) := by
    have h1 : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by push_cast; rfl
    rw [Int.natCast_mul, h1]
  have hj1c : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by push_cast; rfl
  rw [hjj, hj1c]
  -- 1·(j·(j+1)) ≤ (1·(j+1) + (−1)·j)·((j+1)·(j+1))
  -- coefficient (j+1) + (−j) = 1, so RHS = (j+1)·(j+1).  Need j·(j+1) ≤ (j+1)·(j+1).
  have hcoef : (1 : Int) * ((j : Int) + 1) + (-(1 : Int)) * (j : Int) = 1 := by
    rw [Int.one_mul, Int.neg_one_mul]; omega
  rw [hcoef, Int.one_mul, Int.one_mul]
  -- j·(j+1) ≤ (j+1)·(j+1):  j ≤ j+1 times (j+1) ≥ 0.
  have hjpos : (0 : Int) ≤ (j : Int) + 1 := by
    have : (0 : Int) ≤ (j : Int) := Int.natCast_nonneg j
    omega
  have hjle : (j : Int) ≤ (j : Int) + 1 := by omega
  exact Int.mul_le_mul_of_nonneg_right hjle hjpos

/-- The telescoping invariant `Σ_{j=1}^M 1/j² ≤ 2 − 1/M`. -/
theorem pSeries_invariant (M : Nat) :
    (RationalTail.finSum pSeriesTerm (M + 1)) ≤ ((2 : Q') + (-(recipNat M))) := by
  induction M with
  | zero =>
    show (RationalTail.finSum pSeriesTerm 1) ≤ ((2 : Q') + (-(recipNat 0)))
    have hsum0 : RationalTail.finSum pSeriesTerm 1 = (0 : Q') := by
      show RationalTail.finSum pSeriesTerm 0 + pSeriesTerm 0 = 0
      have hp0 : pSeriesTerm 0 = 0 := by
        unfold pSeriesTerm; rw [dif_neg (by decide : ¬ 0 < 0)]
      rw [hp0]; rfl
    rw [hsum0]
    have hr0 : recipNat 0 = 0 := by unfold recipNat; rw [dif_neg (by decide : ¬ 0 < 0)]
    rw [hr0]
    refine Q'.le_trans' _ _ _ (by decide : (0:Q') ≤ (2:Q')) ?_
    exact Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.add_zero' (2:Q')))
  | succ t ih =>
    show (RationalTail.finSum pSeriesTerm (t + 1) + pSeriesTerm (t + 1))
        ≤ ((2 : Q') + (-(recipNat (t + 1))))
    by_cases ht : 0 < t
    · have hstep := recipSq_telescope t ht
      have hadd := Q'.add_le_add ih hstep
      refine Q'.le_trans' _ _ _ hadd ?_
      refine Q'.ge_of_eqv ?_
      calc ((2 : Q') + (-(recipNat (t + 1))))
          ≈ (2 : Q') + ((0 : Q') + (-(recipNat (t + 1)))) :=
            Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' (-(recipNat (t + 1))))))
        _ ≈ (2 : Q') + (((-(recipNat t)) + (recipNat t)) + (-(recipNat (t + 1)))) :=
            Q'.add_eqv_congr_left _ _ _
              (Q'.add_eqv_congr_right _ _ _
                (Q'.eqv_symm (Q'.neg_add_self_eqv (recipNat t))))
        _ ≈ (2 : Q') + ((-(recipNat t)) + ((recipNat t) + (-(recipNat (t + 1))))) :=
            Q'.add_eqv_congr_left _ _ _ (Q'.add_assoc_eqv _ _ _)
        _ ≈ ((2 : Q') + (-(recipNat t))) + ((recipNat t) + (-(recipNat (t + 1)))) :=
            Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
    · have ht0 : t = 0 := by omega
      subst ht0
      have hsum0 : RationalTail.finSum pSeriesTerm 1 = (0 : Q') := by
        show RationalTail.finSum pSeriesTerm 0 + pSeriesTerm 0 = 0
        have hp0 : pSeriesTerm 0 = 0 := by
          unfold pSeriesTerm; rw [dif_neg (by decide : ¬ 0 < 0)]
        rw [hp0]; rfl
      rw [hsum0]
      have hp1 : pSeriesTerm 1 = Q'.mkPos 1 1 (by decide) := by
        unfold pSeriesTerm; rw [dif_pos (by decide : 0 < 1)]
      have hr1 : recipNat 1 = Q'.mkPos 1 1 (by decide) := by
        unfold recipNat; rw [dif_pos (by decide : 0 < 1)]
      rw [hp1, hr1]
      show ((0 : Q') + Q'.mkPos 1 1 (by decide))
          ≤ ((2 : Q') + (-(Q'.mkPos 1 1 (by decide))))
      refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (Q'.mkPos 1 1 (by decide))))) ?_
      decide

/-- **The constructive p-SERIES bound (reusable).**  `Σ_{j=1}^M 1/j² ≤ 2`. -/
theorem pSeries_le_two (M : Nat) :
    (RationalTail.finSum pSeriesTerm (M + 1)) ≤ (2 : Q') := by
  refine Q'.le_trans' _ _ _ (pSeries_invariant M) ?_
  show ((2 : Q') + (-(recipNat M))) ≤ (2 : Q')
  have hr : (0 : Q') ≤ recipNat M := recipNat_nonneg M
  -- −recipNat M ≤ 0
  have h1 : (-(recipNat M)) ≤ (0 : Q') := by
    rw [Q'.zero_le_iff_num_nonneg] at hr
    show (-(recipNat M)).num * ((0:Q').den : Int) ≤ (0:Q').num * ((-(recipNat M)).den : Int)
    show (-(recipNat M).num) * (((0:Q').den : Nat) : Int)
        ≤ (0:Q').num * (((-(recipNat M)).den : Nat) : Int)
    have hd : (((0:Q').den : Nat) : Int) = 1 := rfl
    have hn : (0:Q').num = 0 := rfl
    rw [hd, hn, Int.mul_one, Int.zero_mul]
    omega
  have h2 := Q'.add_le_add_left (2 : Q') (-(recipNat M)) (0 : Q') h1
  refine Q'.le_trans' _ _ _ h2 ?_
  exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' (2:Q')))

/-! ## 2. The scaled inverse-square term and the NON-UNIFORM GRADED rate

`scale e M := C(e)/⌊√M⌋` (the boundary scale `~ C(e)·√δ`).  The scaled
inverse-square term `scaledTerm e M j := C(e)/(⌊√M⌋·j²)` for `j ≥ 1` is the value
of the rate at an interior cell at distance `j`; the graded rate is
`gradedRate e M k := scaledTerm e M (jdist M k)` with `jdist M k := min(k+1, M−k)`. -/

/-- The boundary scale `C(e)/⌊√M⌋` (`~ C(e)·√δ`). -/
def scale (e M : Nat) (hM : 0 < M) : Q' :=
  Q'.mkPos (cRateNum e : Int) (isqrt M) (isqrt_pos hM)

/-- `0 ≤ scale e M`. -/
theorem scale_nonneg (e M : Nat) (hM : 0 < M) : (0 : Q') ≤ scale e M hM := by
  show (0 : Q') ≤ Q'.mkPos (cRateNum e : Int) (isqrt M) (isqrt_pos hM)
  rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; exact Int.natCast_nonneg _

/-- The scaled inverse-square term `C(e)/(⌊√M⌋·j²)` for `j ≥ 1`; `0` at `j = 0`. -/
def scaledTerm (e M : Nat) (hM : 0 < M) (j : Nat) : Q' :=
  if hj : 0 < j then
    Q'.mkPos (cRateNum e : Int) (isqrt M * (j * j))
      (Nat.mul_pos (isqrt_pos hM) (Nat.mul_pos hj hj))
  else 0

/-- `0 ≤ scaledTerm e M j`. -/
theorem scaledTerm_nonneg (e M : Nat) (hM : 0 < M) (j : Nat) :
    (0 : Q') ≤ scaledTerm e M hM j := by
  unfold scaledTerm
  by_cases hj : 0 < j
  · rw [dif_pos hj, Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; exact Int.natCast_nonneg _
  · rw [dif_neg hj]; exact Q'.le_refl' 0

/-- **The scaled term IS the scale times the p-series term.**
`scaledTerm e M j ≈ scale e M · pSeriesTerm j`.  At `j ≥ 1` both are
`C(e)/(⌊√M⌋·j²)` (pure `mkPos` product identity); at `j = 0` both are `0`. -/
theorem scaledTerm_eqv (e M : Nat) (hM : 0 < M) (j : Nat) :
    scaledTerm e M hM j ≈ (scale e M hM * pSeriesTerm j) := by
  unfold scaledTerm pSeriesTerm scale
  by_cases hj : 0 < j
  · rw [dif_pos hj, dif_pos hj]
    have hden : 0 < isqrt M * (j * j) := Nat.mul_pos (isqrt_pos hM) (Nat.mul_pos hj hj)
    -- mkPos C (isqrt M · (j·j)) ≈ mkPos C (isqrt M) · mkPos 1 (j·j)
    show (Q'.mkPos (cRateNum e : Int) (isqrt M * (j * j)) hden).num
          * ((Q'.mkPos (cRateNum e : Int) (isqrt M) (isqrt_pos hM)
              * Q'.mkPos 1 (j * j) (Nat.mul_pos hj hj)).den : Int)
        = (Q'.mkPos (cRateNum e : Int) (isqrt M) (isqrt_pos hM)
              * Q'.mkPos 1 (j * j) (Nat.mul_pos hj hj)).num
          * ((Q'.mkPos (cRateNum e : Int) (isqrt M * (j * j)) hden).den : Int)
    -- LHS num = C, LHS den (cast) = isqrt M·(j·j).
    -- RHS = (mkPos C (isqrt M))·(mkPos 1 (j·j)): num = C·1 = C, den = isqrt M·(j·j).
    rw [Q'.mkPos_num, Q'.mkPos_den, Q'.mul_den_cast, Q'.mkPos_den, Q'.mkPos_den]
    rw [show (Q'.mkPos (cRateNum e : Int) (isqrt M) (isqrt_pos hM)
              * Q'.mkPos 1 (j * j) (Nat.mul_pos hj hj)).num
          = (cRateNum e : Int) * (1 : Int) from rfl]
    -- goal: C · ↑(isqrt M · (j·j)) = (C·1) · (↑(isqrt M) · ↑(j·j))
    have hcast : (((isqrt M * (j * j) : Nat)) : Int)
        = ((isqrt M : Nat) : Int) * (((j * j : Nat)) : Int) := by rw [Int.natCast_mul]
    rw [hcast, Int.mul_one]
  · rw [dif_neg hj, dif_neg hj]
    -- 0 ≈ scale · 0
    refine Q'.eqv_symm ?_
    exact Q'.mul_zero_eqv (scale e M hM)

/-- The distance-from-boundary in cells `jdist M k := min(k+1, M−k)`. -/
def jdist (M k : Nat) : Nat := Nat.min (k + 1) (M - k)

/-- For `k < M`, `0 < jdist M k`. -/
theorem jdist_pos {M k : Nat} (hk : k < M) : 0 < jdist M k := by
  unfold jdist
  have h1 : 0 < k + 1 := by omega
  have h2 : 0 < M - k := by omega
  exact Nat.lt_min.mpr ⟨h1, h2⟩

/-- **The NON-UNIFORM GRADED per-cell rate** `gradedRate e M k :=
C(e)/(⌊√M⌋·jdist M k²)`.  At a boundary cell (`k=0` or `k=M−1`) `jdist=1`, giving
the boundary scale `C(e)/⌊√M⌋`; at an interior cell at distance `j`, `C(e)/(⌊√M⌋·j²)`,
GRADED.  Uniform in `k` only through `jdist` — genuinely `k`-DEPENDENT. -/
def gradedRate (e M : Nat) (hM : 0 < M) (k : Nat) : Q' :=
  scaledTerm e M hM (jdist M k)

/-- **`gradedRate` is nonnegative.** -/
theorem gradedRate_nonneg (e M : Nat) (hM : 0 < M) (k : Nat) :
    (0 : Q') ≤ gradedRate e M hM k :=
  scaledTerm_nonneg e M hM (jdist M k)

/-! ## 3. The pointwise two-sided split and the finite-sum majorant -/

/-- **The pointwise two-sided split.**  For `k < M`,
`gradedRate e M k ≤ scaledTerm e M (k+1) + scaledTerm e M (M−k)`.  Since
`jdist M k = min(k+1, M−k) ≥ 1` equals one of `k+1` or `M−k`, the rate
`C(e)/(⌊√M⌋·jdist²)` is one of the two scaled terms, hence `≤` their sum
(both nonnegative). -/
theorem gradedRate_le_split (e M : Nat) (hM : 0 < M) (k : Nat) (_hk : k < M) :
    gradedRate e M hM k
      ≤ (scaledTerm e M hM (k + 1) + scaledTerm e M hM (M - k)) := by
  -- jdist M k = min(k+1, M-k); it equals one of the two arms.
  show scaledTerm e M hM (jdist M k)
      ≤ (scaledTerm e M hM (k + 1) + scaledTerm e M hM (M - k))
  by_cases harm : k + 1 ≤ M - k
  · -- min = k+1.
    have hj : jdist M k = k + 1 := Nat.min_eq_left harm
    rw [hj]
    refine Q'.add_le_self_of_nonneg _ _ (scaledTerm_nonneg e M hM (M - k))
  · -- min = M-k.
    have hj : jdist M k = M - k := Nat.min_eq_right (by omega : M - k ≤ k + 1)
    rw [hj]
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _))) ?_
    exact Q'.add_le_add_right _ _ _ (scaledTerm_nonneg e M hM (k + 1))

/-- The half-sum `Σ_{k<M} scaledTerm e M (k+1) ≤ scale e M · 2`.
`scaledTerm e M (k+1) ≈ scale · pSeriesTerm (k+1)`; the sum factors `scale` out and
`Σ_{k<M} pSeriesTerm (k+1) ≤ 2` (the `j=0` term of `pSeries_le_two` is `0`). -/
theorem half_sum_left_le (e M : Nat) (hM : 0 < M) :
    (RationalTail.finSum (fun k => scaledTerm e M hM (k + 1)) M)
      ≤ (scale e M hM * (2 : Q')) := by
  -- Step 1: Σ scaledTerm(k+1) ≤ Σ (scale · pSeriesTerm(k+1)) (termwise, via scaledTerm_eqv).
  have h1 : (RationalTail.finSum (fun k => scaledTerm e M hM (k + 1)) M)
      ≤ (RationalTail.finSum (fun k => scale e M hM * pSeriesTerm (k + 1)) M) :=
    finSum_termwise_le _ _ M (fun k _ => Q'.le_of_eqv (scaledTerm_eqv e M hM (k + 1)))
  refine Q'.le_trans' _ _ _ h1 ?_
  -- Step 2: Σ (scale · pSeriesTerm(k+1)) = scale · Σ pSeriesTerm(k+1) ≤ scale · 2.
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (RationalTail.const_mul_finSum (fun k => pSeriesTerm (k + 1)) (scale e M hM) M)) ?_
  -- scale · Σ pSeriesTerm(k+1) ≤ scale · 2.
  refine Q'.mul_le_mul_of_nonneg_left _ _ (scale e M hM) ?_ (scale_nonneg e M hM)
  -- Σ_{k<M} pSeriesTerm(k+1) ≤ 2.  Relate to finSum pSeriesTerm (M+1) via extract_first.
  have hext := finSum_extract_first pSeriesTerm M
  -- finSum pSeriesTerm (M+1) ≈ pSeriesTerm 0 + Σ pSeriesTerm(k+1) = 0 + Σ...
  have hp0 : pSeriesTerm 0 = 0 := by unfold pSeriesTerm; rw [dif_neg (by decide : ¬ 0 < 0)]
  rw [hp0] at hext
  -- hext : finSum pSeriesTerm (M+1) ≈ 0 + Σ pSeriesTerm(k+1)
  have hcollapse : (RationalTail.finSum (fun k => pSeriesTerm (k + 1)) M)
      ≈ (RationalTail.finSum pSeriesTerm (M + 1)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))) (Q'.eqv_symm hext)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollapse) (pSeries_le_two M)

/-- The half-sum `Σ_{k<M} scaledTerm e M (M−1−k) ≤ scale e M · 2`.  By the finite-sum
reflection `Σ_{k<M} g(M−1−k) ≈ Σ_{k<M} g k` (`g k := scaledTerm e M (k+1)`),
reduced to `half_sum_left_le`. -/
theorem half_sum_right_le (e M : Nat) (hM : 0 < M) :
    (RationalTail.finSum (fun k => scaledTerm e M hM (M - k)) M)
      ≤ (scale e M hM * (2 : Q')) := by
  -- Reflect with f k := scaledTerm e M (k+1):  f (M-1-k) = scaledTerm e M ((M-1-k)+1)
  --   = scaledTerm e M (M-k)  for k < M.  So Σ scaledTerm(M-k) ≈ Σ scaledTerm(k+1).
  -- First rewrite the summand scaledTerm(M-k) = f(M-1-k).
  have hcongr : RationalTail.finSum (fun k => scaledTerm e M hM (M - k)) M
      = RationalTail.finSum (fun k => (fun j => scaledTerm e M hM (j + 1)) (M - 1 - k)) M := by
    refine finSum_congr _ _ M (fun k hk => ?_)
    show scaledTerm e M hM (M - k) = scaledTerm e M hM ((M - 1 - k) + 1)
    have : M - k = (M - 1 - k) + 1 := by omega
    rw [this]
  rw [hcongr]
  -- reflect: Σ f(M-1-k) ≈ Σ f k = Σ scaledTerm(k+1)
  have href := finSum_reflect (fun j => scaledTerm e M hM (j + 1)) M
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv href) ?_
  exact half_sum_left_le e M hM

/-- **The finite-sum majorant.**  `Σ_{k<M} gradedRate e M k ≤ scale e M · 4`.
The pointwise split (`gradedRate_le_split`) bounds the sum by the two half-sums,
each `≤ scale · 2` (`half_sum_left_le`/`half_sum_right_le`). -/
theorem gradedRateSum_le (e M : Nat) (hM : 0 < M) :
    (RationalTail.finSum (gradedRate e M hM) M)
      ≤ (scale e M hM * (4 : Q')) := by
  -- Σ gradedRate ≤ Σ (scaledTerm(k+1) + scaledTerm(M-k)) (termwise split).
  have hsplit : (RationalTail.finSum (gradedRate e M hM) M)
      ≤ (RationalTail.finSum
          (fun k => scaledTerm e M hM (k + 1) + scaledTerm e M hM (M - k)) M) :=
    finSum_termwise_le _ _ M (fun k hk => gradedRate_le_split e M hM k hk)
  refine Q'.le_trans' _ _ _ hsplit ?_
  -- split the sum of sums: Σ (a_k + b_k) = Σ a_k + Σ b_k.
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (RationalTail.finSum_add
      (fun k => scaledTerm e M hM (k + 1)) (fun k => scaledTerm e M hM (M - k)) M)) ?_
  -- Σ a_k + Σ b_k ≤ scale·2 + scale·2 = scale·4.
  have hL := half_sum_left_le e M hM
  have hR := half_sum_right_le e M hM
  refine Q'.le_trans' _ _ _ (Q'.add_le_add hL hR) ?_
  -- scale·2 + scale·2 ≤ scale·4.
  refine Q'.le_of_eqv ?_
  -- scale·2 + scale·2 ≈ scale·(2+2) ≈ scale·4.
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv (scale e M hM) 2 2)) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (by decide : ((2:Q') + (2:Q')) ≈ (4:Q'))

/-! ## 4. The vanishing of the GRADED summed rate -/

/-- `scale e M · 4 ≈ (4·C(e))/⌊√M⌋` (collapsing the scalar `4` into the numerator). -/
theorem scale_mul_four_eqv (e M : Nat) (hM : 0 < M) :
    (scale e M hM * (4 : Q'))
      ≈ (Q'.mkPos ((4 * cRateNum e : Nat) : Int) (isqrt M) (isqrt_pos hM)) := by
  unfold scale
  -- LHS = mkPos C t · 4 :  num = C·4, den (cast) = t·1.
  -- RHS = mkPos (4·C) t :  num = 4·C, den (cast) = t.
  -- eqv cross product: (C·4)·t = (4·C)·(t·1).
  have hLnum : (Q'.mkPos (cRateNum e : Int) (isqrt M) (isqrt_pos hM) * (4 : Q')).num
      = (cRateNum e : Int) * (4 : Int) := by
    show (Q'.mkPos (cRateNum e : Int) (isqrt M) (isqrt_pos hM)).num * (4 : Q').num
        = (cRateNum e : Int) * (4 : Int)
    rw [Q'.mkPos_num]; rfl
  have hLden : ((Q'.mkPos (cRateNum e : Int) (isqrt M) (isqrt_pos hM) * (4 : Q')).den : Int)
      = ((isqrt M : Nat) : Int) * (1 : Int) := by
    rw [Q'.mul_den_cast, Q'.mkPos_den]; rfl
  show (Q'.mkPos (cRateNum e : Int) (isqrt M) (isqrt_pos hM) * (4 : Q')).num
        * ((Q'.mkPos ((4 * cRateNum e : Nat) : Int) (isqrt M) (isqrt_pos hM)).den : Int)
      = (Q'.mkPos ((4 * cRateNum e : Nat) : Int) (isqrt M) (isqrt_pos hM)).num
        * ((Q'.mkPos (cRateNum e : Int) (isqrt M) (isqrt_pos hM) * (4 : Q')).den : Int)
  rw [hLnum, hLden, Q'.mkPos_num, Q'.mkPos_den]
  have hcast : ((4 * cRateNum e : Nat) : Int) = (4 : Int) * (cRateNum e : Int) := by
    push_cast; rfl
  rw [hcast, Int.mul_one]
  -- (C·4)·t = (4·C)·t
  rw [Int.mul_comm (cRateNum e : Int) (4 : Int)]

/-- **The corrected GRADED summed cell-rate VANISHES.**  For every `ε > 0` there is
a threshold `M₀` past which `Σ_{k<M} gradedRate e M k ≤ ε`.  The summed rate
`Σ gradedRate ≤ (4·C(e))/⌊√M⌋ → 0`: choose `K := (4·C(e))·ε.den` and threshold
`M₀ := K·K`, so `M ≥ M₀ ⟹ K² ≤ M ⟹ K ≤ ⌊√M⌋` (`isqrt_ge`), hence
`(4·C(e))/⌊√M⌋ ≤ ε` (the `cRate_over_t_le`-style rational vanishing). -/
theorem gradedRateSum_vanishes (e : Nat) :
    ∀ ε : Q', (0 : Q') < ε → ∃ M₀ : Nat, ∀ M : Nat, M₀ ≤ M → (hM : 0 < M) →
      (RationalTail.finSum (gradedRate e M hM) M) ≤ ε := by
  intro ε hε
  refine ⟨((4 * cRateNum e) * ε.den) * ((4 * cRateNum e) * ε.den), fun M hM₀ hM => ?_⟩
  -- isqrt M ≥ (4·C)·ε.den.
  have hKle : (4 * cRateNum e) * ε.den ≤ isqrt M :=
    isqrt_ge (m := M) (K := (4 * cRateNum e) * ε.den) hM₀
  -- Σ gradedRate ≤ scale·4 ≈ (4·C)/⌊√M⌋ ≤ ε.
  refine Q'.le_trans' _ _ _ (gradedRateSum_le e M hM) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (scale_mul_four_eqv e M hM)) ?_
  -- (4·C)/⌊√M⌋ ≤ ε via the cross-multiplication rational vanishing.
  have hisqrt_pos : 0 < isqrt M := isqrt_pos hM
  -- mirror `cRate_over_t_le`.
  have hεnum : (0 : Int) < ε.num := by
    have : (0 : Int) * (ε.den : Int) < ε.num * ((0 : Q').den : Int) := hε
    rw [Int.zero_mul] at this
    have hd : ((0 : Q').den : Int) = 1 := rfl
    rw [hd, Int.mul_one] at this; exact this
  show (Q'.mkPos ((4 * cRateNum e : Nat) : Int) (isqrt M) hisqrt_pos).num * (ε.den : Int)
      ≤ ε.num * ((Q'.mkPos ((4 * cRateNum e : Nat) : Int) (isqrt M) hisqrt_pos).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]
  have htge' : (((4 * cRateNum e) * ε.den : Nat) : Int) ≤ ((isqrt M : Nat) : Int) := by
    exact_mod_cast hKle
  have hcast : (((4 * cRateNum e) * ε.den : Nat) : Int)
      = ((4 * cRateNum e : Nat) : Int) * (ε.den : Int) := by push_cast; rfl
  rw [hcast] at htge'
  have ht0 : (0 : Int) ≤ ((isqrt M : Nat) : Int) := Int.natCast_nonneg _
  have hstep : ((isqrt M : Nat) : Int) ≤ ε.num * ((isqrt M : Nat) : Int) := by
    calc ((isqrt M : Nat) : Int) = 1 * ((isqrt M : Nat) : Int) := by rw [Int.one_mul]
      _ ≤ ε.num * ((isqrt M : Nat) : Int) :=
          Int.mul_le_mul_of_nonneg_right hεnum ht0
  exact Int.le_trans htge' hstep

/-! ## 5. The GENUINE boundary-cell `orthTerm` sub-bound (rigorous boundary leg) -/

/-- **The boundary-cell `|U_e(x)| ≤ e+1` factor** at a node value inside `[−1,1]`
(re-export of the PROVED `ChebOrthoCancel.uNode_abs_le`).  Together with the
boundary radical bound `ChebOrthoCancel.bdyRadical_leRat` (`s_± ≤ √(2δ)`) and
`|B_e| ≤ 2` (from `ChebyshevU.absU_le`) this gives the DIRECT boundary-cell
estimate `|cellAdjR k| ≤ C(e)·√δ` (no centered-difference cancellation needed;
the cell touches `±1`).  Recorded as the rigorous boundary leg. -/
theorem boundary_cell_orthTerm_bound (e : Nat) (x : Q')
    (hx1 : x ≤ 1) (hxm1 : (-1 : Q') ≤ x) :
    Cheb.U e x ≤ Q'.ofNat (e + 1) ∧ (-(Q'.ofNat (e + 1))) ≤ Cheb.U e x :=
  ChebOrthoCancel.uNode_abs_le e x hx1 hxm1

/-! ## 6. The PRECISE residual: the per-cell estimate against the GRADED rate -/

/-- **NAMED-open: the per-cell midpoint estimate against the CORRECTED NON-UNIFORM
GRADED rate.**  For the even order `e` (`he : 0 < e`), every GENUINE real-boundary
adjusted cell `cellAdjR e he (N+1) k = orthTerm k + (GsampR(b_{k+1}) − GsampR(b_k))`
is two-sidedly bounded by the graded rate `gradedRate e (N+1) k`:

    `leRat (cellAdjR e he (N+1) … k) (gradedRate e (N+1) … k)`  and the negation.

This is the correctly-formulated bounded-derivative midpoint error bound: graded by
the distance-from-boundary `jdist`, so it is large (`~ √δ`) at the two boundary
cells touching `±1` (where the cancellation breaks) and small (`~ δ^{3/2}/j^{3/2}`)
at interior cells.  Its two cases — the DIRECT boundary bound and the INTERIOR
graded centered-difference remainder (via `ChebOrthoCancel.leading_cancellation`,
`ChebOrthoRemainder.gIncr_pdiff_split`, `ChebOrthoRemainder.radSq_diff_equiv`,
`ChebOrthoMidpointCore.radDiff_holder`, `Le`) — are the SINGLE remaining analytic
core.  Recorded precisely. -/
def GradedPerCellBound (e : Nat) (he : 0 < e) : Prop :=
  ∀ N k : Nat,
    CReal.leRat (cellAdjR e he (N + 1) (Nat.succ_pos N) k)
        (gradedRate e (N + 1) (Nat.succ_pos N) k) ∧
    CReal.leRat (CReal.neg (cellAdjR e he (N + 1) (Nat.succ_pos N) k))
        (gradedRate e (N + 1) (Nat.succ_pos N) k)

/-! ## 7. The genuine packaging `GradedPerCellBound → RealPerCellBudget` -/

/-- **THE PACKAGING.**  `GradedPerCellBound e he → ChebOrthoMidpoint.RealPerCellBudget e he`.
The named per-cell two-sided bound supplies the `leRat` data; the graded
`gradedRate` supplies nonnegativity (`gradedRate_nonneg`) and the vanishing
finite-sum (`gradedRateSum_vanishes`); the three are assembled into the
`RealPerCellBudget` existential with witness rate
`r n k := if hn : 0 < n then gradedRate e n hn k else 0`.  Note the rate is
GENUINELY `k`-DEPENDENT (graded), as `RealPerCellBudget` permits. -/
theorem realPerCellBudget_of_gradedBound (e : Nat) (he : 0 < e)
    (h : GradedPerCellBound e he) : ChebOrthoMidpoint.RealPerCellBudget e he := by
  refine ⟨fun n k => if hn : 0 < n then gradedRate e n hn k else 0, ?_, ?_, ?_⟩
  · intro n k
    show (0 : Q') ≤ (if hn : 0 < n then gradedRate e n hn k else 0)
    by_cases hn : 0 < n
    · rw [dif_pos hn]; exact gradedRate_nonneg e n hn k
    · rw [dif_neg hn]; exact Q'.le_refl' 0
  · intro N k
    have hN1 : (0 : Nat) < N + 1 := Nat.succ_pos N
    show CReal.leRat (cellAdjR e he (N + 1) (Nat.succ_pos N) k)
          (if hn : 0 < N + 1 then gradedRate e (N + 1) hn k else 0) ∧
        CReal.leRat (CReal.neg (cellAdjR e he (N + 1) (Nat.succ_pos N) k))
          (if hn : 0 < N + 1 then gradedRate e (N + 1) hn k else 0)
    rw [dif_pos hN1]
    exact h N k
  · intro ε hε
    obtain ⟨M₀, hM₀⟩ := gradedRateSum_vanishes e ε hε
    refine ⟨M₀, fun N hN => ?_⟩
    have hN1 : (0 : Nat) < N + 1 := Nat.succ_pos N
    show (RationalTail.finSum
        (fun k => if hn : 0 < N + 1 then gradedRate e (N + 1) hn k else 0) (N + 1)) ≤ ε
    have hfun : (fun k => if hn : 0 < N + 1 then gradedRate e (N + 1) hn k else 0)
        = gradedRate e (N + 1) hN1 := by
      funext k; rw [dif_pos hN1]
    rw [hfun]
    have hM₀N : M₀ ≤ N + 1 := Nat.le_trans hN (Nat.le_succ N)
    exact hM₀ (N + 1) hM₀N hN1

/-! ## 8. The even-order limit and full off-diagonal closure, reduced to the SINGLE
per-cell estimate against the GRADED rate -/

/-- **`OrthEvenZeroLimit e` from the graded per-cell estimate.**  Composes the
packaging with the proved bridges `ChebOrthoMidpoint.budgetExists_of_realPerCell`
→ `orthEvenZeroLimit_of_budgetExists`. -/
theorem orthEvenZeroLimit_of_gradedBound (e : Nat) (he : 0 < e)
    (h : GradedPerCellBound e he) :
    ChebOrthoEvenFTC.OrthEvenZeroLimit e :=
  ChebOrthoMidpoint.orthEvenZeroLimit_of_realPerCell e he
    (realPerCellBudget_of_gradedBound e he h)

/-- **Off-diagonal orthogonality `∫U_e√ = 0` for `e ≥ 1`, from the graded per-cell
estimate (even orders).**  The ODD case is already UNCONDITIONAL; the EVEN case via
the graded per-cell bound + the proved bridges.  π-free. -/
theorem offdiag_closed_of_gradedBound
    (hinc : ∀ (e : Nat) (he : 0 < e), 2 ≤ e → e % 2 = 0 → GradedPerCellBound e he) :
    ∀ (e : Nat), 1 ≤ e →
      ∃ L : CReal, CReal.ConvergesTo (seqOrth e) L ∧ CReal.Equiv L CReal.czero := by
  refine ChebOrthoMidpoint.offdiag_closed_of_realPerCell (fun e he he2 heven => ?_)
  exact realPerCellBudget_of_gradedBound e he (hinc e he he2 heven)

end YMGap.Continuum.ChebOrthoGraded

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `finSum_termwise_le` / `finSum_congr` / `finSum_extract_first` /
    **`finSum_reflect`** — reusable `Q'` finite-sum infrastructure: the termwise
    comparison, the prefix congruence, the first-term extraction, and the
    finite-sum reflection `Σ_{k<n} f(n−1−k) ≈ Σ_{k<n} f k`.
  * `recipNat` / `pSeriesTerm` (+ nonnegativity) / `recipSq_telescope` /
    `pSeries_invariant` / **`pSeries_le_two`** — the constructive p-SERIES bound
    `Σ_{j=1}^M 1/j² ≤ 2` via the EXACT rational telescoping `1/(j+1)² ≤ 1/j −
    1/(j+1)` (no √); REUSABLE.
  * `scale` / `scaledTerm` (+ nonnegativity) / **`scaledTerm_eqv`** — the boundary
    scale `C(e)/⌊√M⌋` and the scaled inverse-square term `C(e)/(⌊√M⌋·j²) ≈
    scale·(1/j²)`.
  * `jdist` / `jdist_pos` / `gradedRate` / **`gradedRate_nonneg`** — the CORRECTED
    NON-UNIFORM `k`-graded per-cell rate `C(e)/(⌊√M⌋·jdist M k²)` (boundary cells
    `jdist=1` ⇒ `~√δ`; interior cells graded by `1/j²`), nonnegative.
  * `gradedRate_le_split` — the pointwise two-sided split
    `gradedRate e M k ≤ scaledTerm(k+1) + scaledTerm(M−k)`.
  * `half_sum_left_le` / `half_sum_right_le` (via `finSum_reflect`) /
    **`gradedRateSum_le`** — the finite-sum majorant
    `Σ_{k<M} gradedRate e M k ≤ scale e M · 4 = 4·C(e)/⌊√M⌋` (two graded p-series
    halves bounded by `pSeries_le_two`).
  * `scale_mul_four_eqv` / **`gradedRateSum_vanishes`** — the GENUINE vanishing
    `Σ_{k<M} gradedRate e M k → 0` (rate `4·C(e)/⌊√M⌋ → 0`, threshold
    `M ≥ ((4·C(e))·ε.den)²` via `isqrt_ge`).
  * `boundary_cell_orthTerm_bound` — the rigorous boundary leg `|U_e(x)| ≤ e+1`
    (re-export of the PROVED `ChebOrthoCancel.uNode_abs_le`).
  * **`realPerCellBudget_of_gradedBound`** — the genuine packaging
    `GradedPerCellBound e he → ChebOrthoMidpoint.RealPerCellBudget e he` (the
    `k`-DEPENDENT graded rate is admissible for `RealPerCellBudget`).
  * `orthEvenZeroLimit_of_gradedBound` / `offdiag_closed_of_gradedBound` — the
    even-order `czero` limit and the COMBINED π-free off-diagonal orthogonality
    `∫U_e√ = 0` for `e ≥ 1`, reduced to the SINGLE per-cell estimate AGAINST THE
    CORRECTED GRADED RATE (odd UNCONDITIONAL), via the proved bridges
    `ChebOrthoMidpoint.budgetExists_of_realPerCell` → `convergesTo_czero_of_bound`.

**NAMED-open (the honest residual — the INTERIOR second-order graded remainder).**
  * `GradedPerCellBound e he` — the per-cell midpoint estimate
    `|cellAdjR e he (N+1) k| ≤ gradedRate e (N+1) k` against the CORRECTED
    NON-UNIFORM GRADED rate.  This SUPERSEDES the unsatisfiable uniform
    `ChebOrthoMidpointCore.CorrectedPerCellBound` (whose constant-in-`k` rate
    `~C(e)·M^{−3/2}` is FALSE at the 2 boundary cells touching `±1`, where the
    centered-difference cancellation breaks and the genuine cell size is `~√δ`).
    With the graded rate the bound is correctly formulated; the genuine remaining
    content is the two-case estimate:
      · BOUNDARY cells `k ∈ {0, M−1}` — the DIRECT bound `|cellAdjR| ≤
        |orthTerm| + |gIncrR| ≤ C(e)·√δ = gradedRate` (the cell touches `±1` where
        `s = 0`; `boundary_cell_orthTerm_bound`, `bdyRadical_leRat`,
        `|B_e| ≤ 2`).
      · INTERIOR cells `1 ≤ k ≤ M−2` — the GRADED second-order centered-difference
        remainder `~δ³/s_k³ ~ δ^{3/2}/jdist^{3/2} ≤ gradedRate` via the PROVED exact
        pieces `ChebOrthoCancel.leading_cancellation` (leading terms cancel
        `orthTerm`), `ChebOrthoRemainder.gIncr_pdiff_split` (exact product split),
        `ChebOrthoRemainder.radSq_diff_equiv` (exact `s_+²−s_-² = −4xδ`), bounded by
        the √-Hölder `radDiff_holder` and the Lipschitz scale `Le e`.
    The INTERIOR second-order graded remainder is the SINGLE remaining analytic
    core, recorded precisely, NOT faked.  Everything that consumes it (the graded
    rate, its nonnegativity, the reusable p-series, the vanishing sum, the
    packaging into `RealPerCellBudget`, and the off-diagonal bridges) is PROVED
    here.

**Path to closure.**  Once `GradedPerCellBound e he` holds for every even `e ≥ 2`,
`realPerCellBudget_of_gradedBound` + the companion
`ChebOrthoMidpoint.budgetExists_of_realPerCell` close `BudgetExists e`, hence (via
the proved `convergesTo_czero_of_bound`) `OrthEvenZeroLimit e` and the full π-free
off-diagonal orthogonality `∫U_e√ = 0` for all `e ≥ 1`.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoGraded.finSum_termwise_le
#print axioms YMGap.Continuum.ChebOrthoGraded.finSum_reflect
#print axioms YMGap.Continuum.ChebOrthoGraded.recipSq_telescope
#print axioms YMGap.Continuum.ChebOrthoGraded.pSeries_le_two
#print axioms YMGap.Continuum.ChebOrthoGraded.scaledTerm_eqv
#print axioms YMGap.Continuum.ChebOrthoGraded.jdist_pos
#print axioms YMGap.Continuum.ChebOrthoGraded.gradedRate_nonneg
#print axioms YMGap.Continuum.ChebOrthoGraded.gradedRate_le_split
#print axioms YMGap.Continuum.ChebOrthoGraded.gradedRateSum_le
#print axioms YMGap.Continuum.ChebOrthoGraded.gradedRateSum_vanishes
#print axioms YMGap.Continuum.ChebOrthoGraded.boundary_cell_orthTerm_bound
#print axioms YMGap.Continuum.ChebOrthoGraded.realPerCellBudget_of_gradedBound
#print axioms YMGap.Continuum.ChebOrthoGraded.orthEvenZeroLimit_of_gradedBound
#print axioms YMGap.Continuum.ChebOrthoGraded.offdiag_closed_of_gradedBound
