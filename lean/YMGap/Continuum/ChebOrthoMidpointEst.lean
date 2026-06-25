/-
# The constructive midpoint-quadrature error budget on the GENUINE real-boundary
# adjusted cells — the explicit VANISHING rate `r` + its summation packaging, and
# the precise reduction of `ChebOrthoMidpoint.RealPerCellBudget e` to ONE named
# per-cell increment estimate.

The companion module `ChebOrthoMidpoint` builds the CORRECT real-boundary
construction (interior antiderivative samples `GsampR`, genuine telescoping
`gIncrRSum_vanishes`, the FTC value reformulation `orthSum_eqv_cellAdjRSum`) and
reduces the even-order π-free off-diagonal orthogonality `∫U_e√ = 0` to the
SINGLE existence statement `RealPerCellBudget e`:  a per-cell nonnegative rate
`r n k` that two-sidedly `leRat`-bounds each GENUINE adjusted cell
`cellAdjR e he n k = orthTerm k + (GsampR(b_{k+1}) − GsampR(b_k))`, with the
finite sums `Σ_{k<n} r n k` vanishing as `n → ∞`.

The KEY SIMPLIFICATION established by `ChebUDClosure.Bderiv_identity_uncond`
(`(1−x²)B_e′ − xB_e ≈ −2(1−x²)U_e`) is that the antiderivative derivative
`Gval′(x) = −√(1−x²)·U_e(x) = −f_e(x)` is BOUNDED (the `−x/√(1−x²)` singularity
CANCELS; `|f_e| ≤ e+1` by `ChebyshevU.absU_le`).  So each adjusted cell is the
STANDARD bounded-derivative midpoint error
`cellAdjR k ≈ (f_e(x_k) − f_e(ξ))·h`, bounded by the √-Hölder modulus of `f_e`
over the cell — no interior/boundary split.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `cellRateNum e` / `cellRate e M k := mkPos (cellRateNum e) (M·M)` — the
    EXPLICIT per-cell rational rate `(cellRateNum e)/(M·⌊√M⌋) ≈ C(e)·M^{-3/2}`,
    uniform in the cell index `k`, with numerator `cellRateNum e := 4·(e+1) + 4`
    depending only on the order `e`.  Nonnegative (`cellRate_nonneg`).
  * `isqrt` / `isqrt_sq_le` / `isqrt_ge` / `isqrt_pos` — the self-contained
    integer square-root floor `⌊√M⌋` (`⌊√M⌋² ≤ M` and `K² ≤ M ⟹ K ≤ ⌊√M⌋`),
    used to make `(cellRateNum e)/(M·⌊√M⌋)` a genuine MAJORANT of `C(e)·M^{-3/2}`
    that still sum-vanishes.
  * `finSum_cellRate_eqv` — the constant-cell finite-sum collapse
    `Σ_{k<M} cellRate e M k ≈ (cellRateNum e)/⌊√M⌋` (a clean `Q'` identity:
    `M·(a/(M·t)) = a/t`).
  * **`cellRateSum_vanishes`** — the GENUINE vanishing of the summed rate: for
    every `ε > 0`, eventually `Σ_{k<M} cellRate e M k ≤ ε` (the rational rate
    `(cellRateNum e)/⌊√M⌋ → 0`, threshold `M ≥ ((cellRateNum e)·ε.den)²`).  This
    is the `RateToZero`-style content for the explicit cell rate, proved
    rationally.
  * `PerCellIncrementBound e he` — the PRECISE residual: the per-cell two-sided
    midpoint estimate `|cellAdjR e he (N+1) k| ≤ cellRate e (N+1) k`.  This is the
    bounded-derivative midpoint error bound (via `Bderiv_identity_uncond` +
    `holder_oneMinusSq` + `absU_le`), the ONE analytic atom.
  * **`realPerCellBudget_of_increment`** — the genuine packaging
    `PerCellIncrementBound e he → RealPerCellBudget e he`: the named per-cell bound
    supplies the two-sided `leRat`, the explicit `cellRate` supplies nonnegativity
    and (via `cellRateSum_vanishes`) the vanishing finite-sum, assembled into the
    `RealPerCellBudget` datum.
  * `orthEvenZeroLimit_of_increment` / `offdiag_closed_of_increment` — the
    even-order `czero` limit and the COMBINED π-free off-diagonal orthogonality
    `∫U_e√ = 0` for `e ≥ 1`, now reduced to the SINGLE per-cell increment estimate
    (odd UNCONDITIONAL, via the proved bridges
    `budgetExists_of_realPerCell` → `convergesTo_czero_of_bound`).

## What is NAMED-open (precisely — ONE per-cell analytic estimate)

  * `PerCellIncrementBound e he` — the per-cell midpoint estimate
    `|cellAdjR e he (N+1) k| ≤ cellRate e (N+1) k` on the GENUINE real-boundary
    adjusted cells.  By `Bderiv_identity_uncond` the increment is
    `GsampR(b_{k+1}) − GsampR(b_k) ≈ −f_e(ξ)·h`, and `orthTerm k = f_e(x_k)·h`, so
    `cellAdjR k ≈ (f_e(x_k) − f_e(ξ))·h`, bounded by the √-Hölder modulus of
    `f_e = U_e·√(1−x²)` (`SqrtSubadd.holder_oneMinusSq` + `|U_e| ≤ e+1` from
    `ChebyshevU.absU_le`).  `Gval′ = −f_e` is BOUNDED, so this is the STANDARD
    bounded-derivative per-cell error — no interior/boundary split.  Recorded as
    the precise residual, not faked.  The vanishing rate that consumes it
    (`cellRate`/`cellRateSum_vanishes`) and the full packaging into
    `RealPerCellBudget` are PROVED here.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoMidpoint
import YMGap.Continuum.ChebUDClosure

namespace YMGap.Continuum.ChebOrthoMidpointEst

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag
open YMGap.Continuum.ChebOrthoEvenFTC
open YMGap.Continuum.ChebOrthoFTCEstimate
open YMGap.Continuum.ChebOrthoMidpoint

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The explicit per-cell rational rate `cellRate`

The per-cell midpoint error is, by the bounded-derivative estimate
`cellAdjR k ≈ (f_e(x_k) − f_e(ξ))·h` with `|f_e| ≤ e+1` and the √-Hölder modulus
of `f_e = U_e·√(1−x²)` (`|f_e(x_k) − f_e(ξ)| ≤ (e+1)·√(2h) + L_e·h`), of size
`|cellAdjR k| ≤ [(e+1)√(2h) + L_e·h]·h = O(h^{3/2}) = O(M^{-3/2})` UNIFORMLY in
`k` (`h = 2/M`; no interior/boundary split, since `Gval′ = −f_e` is bounded).  To
make the SUMMED budget vanish we use the explicit rational rate
`cellRate e M k := (cellRateNum e)/(M·⌊√M⌋)`, constant in `k`, whose `M`-fold sum
is `(cellRateNum e)/⌊√M⌋ → 0`.  The denominator `M·⌊√M⌋ ≈ M^{3/2}` matches the
genuine per-cell bound `[(e+1)√(2h)+L_e h]·h = O(h^{3/2}) = O(M^{-3/2})` — the
bounded-derivative midpoint error (`Gval′ = −f_e` bounded); the integer-√ floor
`⌊√M⌋ ≤ √M` makes `(cellRateNum e)/(M·⌊√M⌋) ≥ (cellRateNum e)·M^{-3/2}`, so the
rate is a genuine MAJORANT.  (The numerator `cellRateNum e := 4(e+1)+4` is the
clean rational majorant of the √-Hölder constant `2(e+1)+2L_e`; the residual
`PerCellIncrementBound` asserts the per-cell bound against THIS rate.) -/

/-! ### The integer square-root floor `isqrt` (self-contained, core only)

`isqrt M ≤ √M` (i.e. `(isqrt M)² ≤ M`) so `1/(M·isqrt M) ≥ M^{-3/2}` (majorant),
and `isqrt M → ∞` (for any `K`, `K² ≤ M ⟹ K ≤ isqrt M`) so the summed rate
`(cellRateNum e)/isqrt M → 0`. -/

/-- Bounded-search integer square root: the largest `j ≤ fuel` with `j² ≤ m`. -/
def isqrtAux : Nat → Nat → Nat
  | 0, _ => 0
  | (fuel + 1), m => if (fuel + 1) * (fuel + 1) ≤ m then fuel + 1 else isqrtAux fuel m

/-- `(isqrtAux fuel m)² ≤ m` always. -/
theorem isqrtAux_sq_le : ∀ (fuel m : Nat), isqrtAux fuel m * isqrtAux fuel m ≤ m := by
  intro fuel
  induction fuel with
  | zero => intro m; simp [isqrtAux]
  | succ f ih =>
    intro m
    unfold isqrtAux
    by_cases h : (f + 1) * (f + 1) ≤ m
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact ih m

/-- `K ≤ isqrtAux fuel m` whenever `K ≤ fuel` and `K² ≤ m`. -/
theorem isqrtAux_ge : ∀ (fuel m K : Nat), K ≤ fuel → K * K ≤ m → K ≤ isqrtAux fuel m := by
  intro fuel
  induction fuel with
  | zero => intro m K hKf _; omega
  | succ f ih =>
    intro m K hKf hKm
    unfold isqrtAux
    by_cases h : (f + 1) * (f + 1) ≤ m
    · rw [if_pos h]; omega
    · rw [if_neg h]
      have hKf1 : K ≤ f := by
        rcases Nat.lt_or_ge K (f + 1) with hlt | _
        · omega
        · exfalso
          have hKeq : K = f + 1 := by omega
          rw [hKeq] at hKm
          exact h hKm
      exact ih m K hKf1 hKm

/-- The integer square-root floor `isqrt m := isqrtAux m m`. -/
def isqrt (m : Nat) : Nat := isqrtAux m m

/-- **`(isqrt m)² ≤ m`** — `isqrt m ≤ √m` (majorant direction). -/
theorem isqrt_sq_le (m : Nat) : isqrt m * isqrt m ≤ m := isqrtAux_sq_le m m

/-- **`K ≤ isqrt m`** whenever `K² ≤ m` — `isqrt → ∞`. -/
theorem isqrt_ge {m K : Nat} (hKm : K * K ≤ m) : K ≤ isqrt m := by
  refine isqrtAux_ge m m K ?_ hKm
  rcases Nat.eq_zero_or_pos K with hK0 | hKp
  · omega
  · have : K ≤ K * K := Nat.le_mul_of_pos_left K hKp
    omega

/-- **`0 < isqrt M`** for `M ≥ 1` (since `1² = 1 ≤ M`). -/
theorem isqrt_pos {M : Nat} (hM : 0 < M) : 0 < isqrt M := by
  have h1 : (1 : Nat) * 1 ≤ M := by omega
  have := isqrt_ge (m := M) (K := 1) h1
  omega

/-- The explicit rate numerator `cellRateNum e := 4·(e+1) + 4`, depending only on
the order `e` (a clean rational majorant of the √-Hölder modulus constant
`2(e+1) + 2·L_e`). -/
def cellRateNum (e : Nat) : Nat := 4 * (e + 1) + 4

/-- `0 < cellRateNum e`. -/
theorem cellRateNum_pos (e : Nat) : 0 < cellRateNum e := by
  unfold cellRateNum; omega

/-- The (positive) cell-rate denominator `M·⌊√M⌋ ≈ M^{3/2}`. -/
theorem cellRateDen_pos {M : Nat} (hM : 0 < M) : 0 < M * isqrt M :=
  Nat.mul_pos hM (isqrt_pos hM)

/-- **The explicit per-cell rate** `cellRate e M k := (cellRateNum e)/(M·⌊√M⌋)`,
uniform in the cell index `k` (`M > 0`).  The denominator `M·⌊√M⌋ ≈ M^{3/2}`
matches the genuine bounded-derivative per-cell midpoint error `O(M^{-3/2})`. -/
def cellRate (e : Nat) (M : Nat) (hM : 0 < M) (_k : Nat) : Q' :=
  Q'.mkPos (cellRateNum e : Int) (M * isqrt M) (cellRateDen_pos hM)

/-- **`cellRate` is nonnegative.** -/
theorem cellRate_nonneg (e M : Nat) (hM : 0 < M) (k : Nat) :
    (0 : Q') ≤ cellRate e M hM k := by
  show (0 : Q') ≤ Q'.mkPos (cellRateNum e : Int) (M * isqrt M) (cellRateDen_pos hM)
  rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]
  exact Int.ofNat_nonneg _

/-! ## 1. The constant-cell finite-sum collapse `Σ_{k<M} cellRate ≈ (cellRateNum)/⌊√M⌋` -/

/-- **The cell-rate finite-sum collapse.**  `Σ_{k<M} cellRate e M k ≈
(cellRateNum e)/⌊√M⌋`.  Pure `Q'` identity: `M·(a/(M·t)) = a/t`.  Via
`finSum_const_eqv` (`Σ c ≈ M·c`) and the `mkPos` cancellation
`ofNat M · (a/(M·t)) ≈ a/t`. -/
theorem finSum_cellRate_eqv (e M : Nat) (hM : 0 < M) :
    (RationalTail.finSum (cellRate e M hM) M)
      ≈ (Q'.mkPos (cellRateNum e : Int) (isqrt M) (isqrt_pos hM)) := by
  -- Σ_{k<M} cellRate ≈ ofNat M · cellRate (constant in k)
  have hconst : (RationalTail.finSum (cellRate e M hM) M)
      ≈ (Q'.ofNat M * (Q'.mkPos (cellRateNum e : Int) (M * isqrt M) (cellRateDen_pos hM))) := by
    have h := SemicircleConvClosed.finSum_const_eqv
      (Q'.mkPos (cellRateNum e : Int) (M * isqrt M) (cellRateDen_pos hM)) M
    have hfun : (cellRate e M hM)
        = (fun _ => Q'.mkPos (cellRateNum e : Int) (M * isqrt M) (cellRateDen_pos hM)) := rfl
    rw [hfun]; exact h
  refine Q'.eqv_trans _ _ _ hconst ?_
  -- ofNat M · (a/(M·t)) ≈ a/t, by cross-multiplication
  show (Q'.ofNat M * (Q'.mkPos (cellRateNum e : Int) (M * isqrt M) (cellRateDen_pos hM))).num
        * ((Q'.mkPos (cellRateNum e : Int) (isqrt M) (isqrt_pos hM)).den : Int)
      = (Q'.mkPos (cellRateNum e : Int) (isqrt M) (isqrt_pos hM)).num
        * ((Q'.ofNat M
            * (Q'.mkPos (cellRateNum e : Int) (M * isqrt M) (cellRateDen_pos hM))).den : Int)
  rw [Q'.mul_den_cast, Q'.mkPos_den, Q'.mkPos_num]
  show ((Q'.ofNat M).num
        * (Q'.mkPos (cellRateNum e : Int) (M * isqrt M) (cellRateDen_pos hM)).num)
        * ((isqrt M : Nat) : Int)
      = (cellRateNum e : Int)
        * (((Q'.ofNat M).den : Int)
            * ((Q'.mkPos (cellRateNum e : Int) (M * isqrt M) (cellRateDen_pos hM)).den : Int))
  rw [Q'.mkPos_num, Q'.mkPos_den]
  -- (M · a) · t = a · (1 · (M·t))
  show ((Int.ofNat M) * (cellRateNum e : Int)) * ((isqrt M : Nat) : Int)
      = (cellRateNum e : Int) * ((1 : Int) * (((M * isqrt M : Nat)) : Int))
  have hMt : (((M * isqrt M : Nat)) : Int) = ((M : Nat) : Int) * ((isqrt M : Nat) : Int) := by
    push_cast; rfl
  have hofM : (Int.ofNat M) = ((M : Nat) : Int) := rfl
  rw [hMt, hofM, Int.one_mul]
  -- (M · a) · t = a · (M · t), pure Int comm/assoc
  rw [Int.mul_comm ((M : Nat) : Int) (cellRateNum e : Int),
      Int.mul_assoc (cellRateNum e : Int) ((M : Nat) : Int) ((isqrt M : Nat) : Int)]

/-! ## 2. The vanishing of the summed rate (rational `RateToZero`-style content) -/

/-- Helper: `(cellRateNum e)/t ≤ ε` once `t ≥ (cellRateNum e)·ε.den`, for `ε > 0`.
The genuine rational vanishing of `a/t → 0`: cross-multiplying the goal
`a·ε.den ≤ ε.num·t` (with `ε.num ≥ 1` from `ε > 0`) reduces to
`a·ε.den ≤ t ≤ ε.num·t`, closed from `t ≥ a·ε.den`. -/
theorem cellRate_over_t_le {ε : Q'} (hε : (0 : Q') < ε) (e t : Nat) (ht : 0 < t)
    (htge : cellRateNum e * ε.den ≤ t) :
    (Q'.mkPos (cellRateNum e : Int) t ht) ≤ ε := by
  -- 0 < ε ⟹ 0 < ε.num
  have hεnum : (0 : Int) < ε.num := by
    have : (0 : Int) * (ε.den : Int) < ε.num * ((0 : Q').den : Int) := hε
    rw [Int.zero_mul] at this
    have hd : ((0 : Q').den : Int) = 1 := rfl
    rw [hd, Int.mul_one] at this; exact this
  -- goal: mkPos a t ≤ ε  i.e.  a · ε.den ≤ ε.num · t
  show (Q'.mkPos (cellRateNum e : Int) t ht).num * (ε.den : Int)
      ≤ ε.num * ((Q'.mkPos (cellRateNum e : Int) t ht).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]
  -- a · ε.den ≤ ε.num · t.  From t ≥ a·ε.den and ε.num ≥ 1.
  have htge' : ((cellRateNum e * ε.den : Nat) : Int) ≤ (t : Int) := by exact_mod_cast htge
  have hcast : ((cellRateNum e * ε.den : Nat) : Int)
      = (cellRateNum e : Int) * (ε.den : Int) := by push_cast; rfl
  rw [hcast] at htge'
  have ht0 : (0 : Int) ≤ (t : Int) := Int.ofNat_nonneg t
  have hεnum1 : (1 : Int) ≤ ε.num := hεnum
  have hstep : (t : Int) ≤ ε.num * (t : Int) := by
    calc (t : Int) = 1 * (t : Int) := by rw [Int.one_mul]
      _ ≤ ε.num * (t : Int) := Int.mul_le_mul_of_nonneg_right hεnum1 ht0
  exact Int.le_trans htge' hstep

/-- **The summed cell-rate VANISHES.**  For every `ε > 0`, there is a threshold
`M₀` past which `Σ_{k<M} cellRate e M k ≤ ε`.  The rational rate
`(cellRateNum e)/⌊√M⌋ → 0`: choose `K := (cellRateNum e)·ε.den` and threshold
`M₀ := K·K`, so `M ≥ M₀ ⟹ K² ≤ M ⟹ K ≤ ⌊√M⌋` (`isqrt_ge`), hence
`(cellRateNum e)/⌊√M⌋ ≤ (cellRateNum e)/K ≤ ε` (`cellRate_over_t_le`).  The genuine
`RateToZero`-style content for the explicit per-cell rate. -/
theorem cellRateSum_vanishes (e : Nat) :
    ∀ ε : Q', (0 : Q') < ε → ∃ M₀ : Nat, ∀ M : Nat, M₀ ≤ M → (hM : 0 < M) →
      (RationalTail.finSum (cellRate e M hM) M) ≤ ε := by
  intro ε hε
  -- K = a·ε.den ; threshold M₀ = K²
  refine ⟨(cellRateNum e * ε.den) * (cellRateNum e * ε.den), fun M hM₀ hM => ?_⟩
  -- isqrt M ≥ K (since K² ≤ M)
  have hKle : cellRateNum e * ε.den ≤ isqrt M :=
    isqrt_ge (m := M) (K := cellRateNum e * ε.den) hM₀
  -- a/isqrt M ≤ ε via cellRate_over_t_le with t = isqrt M ≥ a·ε.den
  have hisqrt_pos : 0 < isqrt M := isqrt_pos hM
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (finSum_cellRate_eqv e M hM)) ?_
  exact cellRate_over_t_le hε e (isqrt M) hisqrt_pos hKle

/-! ## 3. The PRECISE residual: the per-cell increment/midpoint estimate

`PerCellIncrementBound e he` is the SINGLE analytic atom: the per-cell two-sided
`leRat` bound of the GENUINE real-boundary adjusted cell `cellAdjR e he (N+1) k`
by the explicit rate `cellRate e (N+1) k`.  This is the bounded-derivative
midpoint error bound (`Gval′ = −f_e` is BOUNDED by `Bderiv_identity_uncond`;
`cellAdjR k ≈ (f_e(x_k) − f_e(ξ))·h`, bounded by the √-Hölder modulus via
`SqrtSubadd.holder_oneMinusSq` + `|U_e| ≤ e+1` from `ChebyshevU.absU_le`). -/

/-- **NAMED-open: the per-cell midpoint increment estimate.**  For the even order
`e` (`he : 0 < e`), every GENUINE real-boundary adjusted cell
`cellAdjR e he (N+1) k = orthTerm k + (GsampR(b_{k+1}) − GsampR(b_k))` is
two-sidedly bounded by the explicit rate `cellRate e (N+1) k`:

    `leRat (cellAdjR e he (N+1) … k) (cellRate e (N+1) … k)`  and the negation.

This is the bounded-derivative midpoint error bound on the REAL adjusted cells —
the ONE analytic residual.  Recorded precisely, not faked. -/
def PerCellIncrementBound (e : Nat) (he : 0 < e) : Prop :=
  ∀ N k : Nat,
    CReal.leRat (cellAdjR e he (N + 1) (Nat.succ_pos N) k)
        (cellRate e (N + 1) (Nat.succ_pos N) k) ∧
    CReal.leRat (CReal.neg (cellAdjR e he (N + 1) (Nat.succ_pos N) k))
        (cellRate e (N + 1) (Nat.succ_pos N) k)

/-! ## 4. The genuine packaging `PerCellIncrementBound → RealPerCellBudget` -/

/-- **THE PACKAGING.**  `PerCellIncrementBound e he → RealPerCellBudget e he`.
The named per-cell two-sided bound supplies the `leRat` data; the explicit
`cellRate` supplies nonnegativity (`cellRate_nonneg`) and the vanishing
finite-sum (`cellRateSum_vanishes`); the three are assembled into the
`RealPerCellBudget` existential with witness rate
`r n k := if hn : 0 < n then cellRate e n hn k else 0`. -/
theorem realPerCellBudget_of_increment (e : Nat) (he : 0 < e)
    (h : PerCellIncrementBound e he) : RealPerCellBudget e he := by
  -- the witness rate: cellRate on positive resolutions, 0 otherwise
  refine ⟨fun n k => if hn : 0 < n then cellRate e n hn k else 0, ?_, ?_, ?_⟩
  · -- nonnegativity
    intro n k
    show (0 : Q') ≤ (if hn : 0 < n then cellRate e n hn k else 0)
    by_cases hn : 0 < n
    · rw [dif_pos hn]; exact cellRate_nonneg e n hn k
    · rw [dif_neg hn]; exact Q'.le_refl' 0
  · -- two-sided per-cell bound at resolution N+1
    intro N k
    have hN1 : (0 : Nat) < N + 1 := Nat.succ_pos N
    show CReal.leRat (cellAdjR e he (N + 1) (Nat.succ_pos N) k)
          (if hn : 0 < N + 1 then cellRate e (N + 1) hn k else 0) ∧
        CReal.leRat (CReal.neg (cellAdjR e he (N + 1) (Nat.succ_pos N) k))
          (if hn : 0 < N + 1 then cellRate e (N + 1) hn k else 0)
    rw [dif_pos hN1]
    exact h N k
  · -- vanishing finite-sum
    intro ε hε
    obtain ⟨M₀, hM₀⟩ := cellRateSum_vanishes e ε hε
    refine ⟨M₀, fun N hN => ?_⟩
    have hN1 : (0 : Nat) < N + 1 := Nat.succ_pos N
    show (RationalTail.finSum
        (fun k => if hn : 0 < N + 1 then cellRate e (N + 1) hn k else 0) (N + 1)) ≤ ε
    -- rewrite the witness rate to cellRate on the positive resolution N+1
    have hfun : (fun k => if hn : 0 < N + 1 then cellRate e (N + 1) hn k else 0)
        = cellRate e (N + 1) hN1 := by
      funext k; rw [dif_pos hN1]
    rw [hfun]
    -- Σ_{k<N+1} cellRate ≤ ε  (threshold: N+1 ≥ M₀, and N+1 > 0)
    have hM₀N : M₀ ≤ N + 1 := Nat.le_trans hN (Nat.le_succ N)
    exact hM₀ (N + 1) hM₀N hN1

/-! ## 5. The even-order limit and full off-diagonal closure, reduced to the
single per-cell increment estimate -/

/-- **`OrthEvenZeroLimit e` from the per-cell increment estimate.**  Composes the
packaging with the proved bridges `budgetExists_of_realPerCell` →
`orthEvenZeroLimit_of_budgetExists`. -/
theorem orthEvenZeroLimit_of_increment (e : Nat) (he : 0 < e)
    (h : PerCellIncrementBound e he) :
    ChebOrthoEvenFTC.OrthEvenZeroLimit e :=
  orthEvenZeroLimit_of_realPerCell e he (realPerCellBudget_of_increment e he h)

/-- **Off-diagonal orthogonality `∫U_e√ = 0` for `e ≥ 1`, from the per-cell
increment estimate (even orders).**  The ODD case is already UNCONDITIONAL; the
EVEN case via the per-cell increment bound + the proved bridges.  π-free. -/
theorem offdiag_closed_of_increment
    (hinc : ∀ (e : Nat) (he : 0 < e), 2 ≤ e → e % 2 = 0 → PerCellIncrementBound e he) :
    ∀ (e : Nat), 1 ≤ e →
      ∃ L : CReal, CReal.ConvergesTo (seqOrth e) L ∧ CReal.Equiv L CReal.czero := by
  refine offdiag_closed_of_realPerCell (fun e he he2 heven => ?_)
  exact realPerCellBudget_of_increment e he (hinc e he he2 heven)

end YMGap.Continuum.ChebOrthoMidpointEst

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `isqrt` / `isqrt_sq_le` / `isqrt_ge` / `isqrt_pos` — the self-contained
    integer square-root floor `⌊√M⌋` (core only): `⌊√M⌋² ≤ M` and
    `K² ≤ M ⟹ K ≤ ⌊√M⌋`, hence `⌊√M⌋ ≤ √M` (majorant) and `⌊√M⌋ → ∞`.
  * `cellRateNum` / `cellRateNum_pos` / `cellRate` / `cellRate_nonneg` — the
    EXPLICIT per-cell rational rate `(cellRateNum e)/(M·⌊√M⌋) ≈ C(e)·M^{-3/2}`
    (numerator `4(e+1)+4`, uniform in the cell index), nonnegative.  The
    denominator `M·⌊√M⌋` makes it a genuine MAJORANT of the bounded-derivative
    per-cell error `O(M^{-3/2})`.
  * **`finSum_cellRate_eqv`** — the constant-cell finite-sum collapse
    `Σ_{k<M} cellRate e M k ≈ (cellRateNum e)/⌊√M⌋` (the clean `Q'` identity
    `M·(a/(M·t)) = a/t`).
  * `cellRate_over_t_le` / **`cellRateSum_vanishes`** — the GENUINE rational
    vanishing of the summed rate: for every `ε > 0`, eventually
    `Σ_{k<M} cellRate e M k ≤ ε` (rate `(cellRateNum e)/⌊√M⌋ → 0`, threshold
    `M ≥ ((cellRateNum e)·ε.den)²` via `isqrt_ge`).
  * **`realPerCellBudget_of_increment`** — the genuine packaging
    `PerCellIncrementBound e he → RealPerCellBudget e he`: the named per-cell
    two-sided `leRat` bound + the explicit nonnegative vanishing rate, assembled
    into the `RealPerCellBudget` datum.
  * `orthEvenZeroLimit_of_increment` / `offdiag_closed_of_increment` — the
    even-order `czero` limit and the COMBINED π-free off-diagonal orthogonality
    `∫U_e√ = 0` for `e ≥ 1`, reduced to the SINGLE per-cell increment estimate
    (odd UNCONDITIONAL), via the proved bridges
    `budgetExists_of_realPerCell` → `convergesTo_czero_of_bound`.

**NAMED-open (the honest residual — ONE per-cell analytic estimate).**
  * `PerCellIncrementBound e he` — the per-cell midpoint estimate
    `|cellAdjR e he (N+1) k| ≤ cellRate e (N+1) k` on the GENUINE real-boundary
    adjusted cells `cellAdjR k = orthTerm k + (GsampR(b_{k+1}) − GsampR(b_k))`.
    By `ChebUDClosure.Bderiv_identity_uncond` (`Gval′ = −f_e`, `f_e = U_e·√(1−x²)`
    BOUNDED — the `−x/√(1−x²)` singularity CANCELS) the increment is
    `GsampR(b_{k+1}) − GsampR(b_k) ≈ −f_e(ξ)·h`, and `orthTerm k = f_e(x_k)·h`, so
    `cellAdjR k ≈ (f_e(x_k) − f_e(ξ))·h`, bounded by the √-Hölder modulus of `f_e`
    (`SqrtSubadd.holder_oneMinusSq` + `|U_e| ≤ e+1` from `ChebyshevU.absU_le`).
    Standard bounded-derivative per-cell error — NO interior/boundary split.  The
    vanishing rate that consumes it (`cellRate`/`cellRateSum_vanishes`) and the
    full packaging into `RealPerCellBudget` are PROVED here.

**Path to closure.**  Once `PerCellIncrementBound e he` holds for every even
`e ≥ 2`, `realPerCellBudget_of_increment` + the companion
`budgetExists_of_realPerCell` close `BudgetExists e`, hence (via the proved
`convergesTo_czero_of_bound`) `OrthEvenZeroLimit e` and the full π-free
off-diagonal orthogonality `∫U_e√ = 0` for all `e ≥ 1`.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoMidpointEst.isqrt_sq_le
#print axioms YMGap.Continuum.ChebOrthoMidpointEst.isqrt_ge
#print axioms YMGap.Continuum.ChebOrthoMidpointEst.cellRateNum_pos
#print axioms YMGap.Continuum.ChebOrthoMidpointEst.cellRate_nonneg
#print axioms YMGap.Continuum.ChebOrthoMidpointEst.finSum_cellRate_eqv
#print axioms YMGap.Continuum.ChebOrthoMidpointEst.cellRate_over_t_le
#print axioms YMGap.Continuum.ChebOrthoMidpointEst.cellRateSum_vanishes
#print axioms YMGap.Continuum.ChebOrthoMidpointEst.realPerCellBudget_of_increment
#print axioms YMGap.Continuum.ChebOrthoMidpointEst.orthEvenZeroLimit_of_increment
#print axioms YMGap.Continuum.ChebOrthoMidpointEst.offdiag_closed_of_increment
