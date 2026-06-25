/-
# The CORRECTED per-cell midpoint rate (absorbing `U_e`'s Lipschitz constant
# `L_e`) for the even-order π-free off-diagonal Chebyshev-`U` orthogonality
# `∫_{−1}^1 U_e(x)√(1−x²)dx = 0`.

The companion module `ChebOrthoMidpoint` builds the CORRECT real-boundary
construction (interior antiderivative samples `GsampR`, genuine telescoping
`gIncrRSum_vanishes`, the FTC value reformulation `orthSum_eqv_cellAdjRSum`) and
reduces the even-order off-diagonal orthogonality to the SINGLE existence
statement `RealPerCellBudget e`: a per-cell nonnegative rate `r n k` that
two-sidedly `leRat`-bounds each GENUINE adjusted cell
`cellAdjR e he n k = orthTerm k + (GsampR(b_{k+1}) − GsampR(b_k))`, with the
finite sums `Σ_{k<n} r n k` vanishing as `n → ∞`.

## Why a CORRECTED rate is needed

The companion `ChebOrthoMidpointEst.cellRate` uses the per-cell numerator
`cellRateNum e := 4·(e+1) + 4`.  That constant OMITS the Lipschitz constant `L_e`
of the integrand `f_e = U_e·√(1−x²)`.  The genuine bounded-derivative midpoint
error is

    |cellAdjR e he M k|
      ≤ [(e+1)·√(2h) + L_e·h]·h
      = 4(e+1)/(M·√M) + 4·L_e/M²          (h = 2/M),

whose `L_e·h²` part is NOT majorized by `(4(e+1)+4)/(M·⌊√M⌋)` for small `M`.  So
the `ChebOrthoMidpointEst.cellRate` bound is FALSE for small `M`, and
`ChebOrthoMidpointEst.PerCellIncrementBound` (the per-cell bound against THAT
rate) is therefore UNSATISFIABLE in general.  This module supplies the CORRECTED
rate whose numerator ABSORBS `L_e`:

    cRateNum e := 4·(e+1) + 4·Le e ,   Le e := e·(e+1)·(e+2)

(`Le e ~ e³` is the standard bound on `|U_e′|` on `[−1,1]`; here it enters as the
rate constant — its identification as a true Lipschitz constant of the integrand
is part of the named residual `CorrectedPerCellBound`, not asserted as a proved
theorem in this file).  Because `⌊√M⌋ ≤ M` and `⌊√M⌋ ≤ √M`, the corrected rate
`cRate e M k := (cRateNum e)/(M·⌊√M⌋)` is a UNIFORM MAJORANT of both error parts:

    4(e+1)/(M·√M) ≤ 4(e+1)/(M·⌊√M⌋)   and   4·Le/M² ≤ 4·Le/(M·⌊√M⌋),

so `cRate e M k` is a genuine majorant of `[(e+1)√(2h)+L_e h]·h` for ALL `M ≥ 1`,
unlike the too-tight `ChebOrthoMidpointEst.cellRate`.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `Le` / `Le_pos` — the explicit Nat Lipschitz-scale `Le e := e·(e+1)·(e+2)`.
  * `cRateNum e := 4·(e+1) + 4·Le e` / `cRateNum_pos` — the CORRECTED per-cell
    rate numerator that ABSORBS `L_e` (unlike `ChebOrthoMidpointEst.cellRateNum`,
    which omits it and is hence false for small `M`).
  * `cRate` / `cRate_nonneg` — the CORRECTED explicit per-cell rational rate
    `(cRateNum e)/(M·⌊√M⌋) ≈ (cRateNum e)·M^{-3/2}`, uniform in the cell index,
    a genuine MAJORANT of the bounded-derivative midpoint error (reusing the
    PROVED `ChebOrthoMidpointEst.isqrt` integer-√ floor).
  * `finSum_cRate_eqv` — the constant-cell finite-sum collapse
    `Σ_{k<M} cRate e M k ≈ (cRateNum e)/⌊√M⌋`.
  * **`cRateSum_vanishes`** — the GENUINE vanishing of the corrected summed rate
    (reusing the PROVED `ChebOrthoMidpointEst.cellRate_over_t_le` and `isqrt_ge`).
  * `CorrectedPerCellBound e he` — the PRECISE residual: the per-cell two-sided
    midpoint estimate against the CORRECTED rate.
  * **`realPerCellBudget_of_correctedBound`** — the genuine packaging
    `CorrectedPerCellBound e he → ChebOrthoMidpoint.RealPerCellBudget e he`.
  * `orthEvenZeroLimit_of_correctedBound` / `offdiag_closed_of_correctedBound` —
    the even-order `czero` limit and the COMBINED π-free off-diagonal
    orthogonality `∫U_e√ = 0` for `e ≥ 1`, now reduced to the SINGLE per-cell
    estimate AGAINST THE CORRECTED RATE (odd UNCONDITIONAL, via the proved bridges
    `budgetExists_of_realPerCell` → `convergesTo_czero_of_bound`).
  * `radDiff_holder` — a GENUINE sub-bound of the per-cell estimate: the
    three cell radicals `√(1−b_{k+1}²)`, `√(1−b_k²)`, `√(1−x_k²)` differ by at most
    the √-Hölder tolerance `c` (any `c` with the radicand gap `≤ c²`), via the
    PROVED `SqrtSubadd.sqrtFrom_sub_leRat`.  This closes the (i) radical-difference
    leg of the midpoint estimate.

## What is NAMED-open (precisely — ONE per-cell analytic estimate)

  * `CorrectedPerCellBound e he` — the per-cell midpoint estimate
    `|cellAdjR e he (N+1) k| ≤ cRate e (N+1) k` on the GENUINE real-boundary
    adjusted cells, against the CORRECTED (`L_e`-absorbing) rate.  The remaining
    genuine analytic content is the LEADING-CANCELLATION step: by
    `ChebUDClosure.Bderiv_identity_uncond` (`(1−x²)B_e′ − xB_e ≈ −2(1−x²)U_e`, so
    the antiderivative derivative `Gval′ = −f_e = −U_e√(1−x²)` is BOUNDED, the
    `−x/√` singularity CANCELS) the increment is
    `GsampR(b_{k+1}) − GsampR(b_k) ≈ −f_e(x_k)·h + (midpoint remainder)`, and
    `orthTerm k = f_e(x_k)·h`, so the leading `f_e(x_k)·h` terms CANCEL, leaving
    `cellAdjR k ≈ (second-order midpoint remainder)`, bounded by the √-Hölder
    modulus `ω(h) = (e+1)√(2h) + L_e·h` (the radical leg is `radDiff_holder`; the
    `U_e`-Lipschitz leg uses `Le`; `|U_e| ≤ e+1` from `ChebyshevU.absU_le`).  This
    discrete leading-cancellation (the constructive Taylor remainder converting
    the infinitesimal `Gval′ = −f_e` into the per-cell finite-difference bound) is
    the SINGLE residual, recorded precisely, not faked.  Everything that consumes
    it (the corrected vanishing rate `cRate`/`cRateSum_vanishes`, the packaging
    into `RealPerCellBudget`, and the off-diagonal bridges) is PROVED here.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoMidpoint
import YMGap.Continuum.ChebOrthoMidpointEst
import YMGap.Continuum.ChebUDClosure

namespace YMGap.Continuum.ChebOrthoMidpointCore

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag
open YMGap.Continuum.ChebOrthoEvenFTC
open YMGap.Continuum.ChebOrthoFTCEstimate
open YMGap.Continuum.ChebOrthoMidpoint
open YMGap.Continuum.ChebOrthoMidpointEst

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The explicit Lipschitz-scale `Le e := e·(e+1)·(e+2)` and the CORRECTED
per-cell rate numerator `cRateNum e := 4·(e+1) + 4·Le e`

`Le e ~ e³` is the standard bound on the derivative `|U_e′|` over `[−1,1]`; it is
used here purely as the rate constant absorbing the `L_e·h²` part of the midpoint
error (its identification as an actual Lipschitz constant of the integrand is part
of the named residual).  The corrected numerator `4(e+1) + 4·Le e` majorizes the
√-Hölder modulus constant `2(e+1) + 2·L_e` of `f_e = U_e·√(1−x²)`. -/

/-- The explicit Lipschitz-scale `Le e := e·(e+1)·(e+2) ~ e³` (the standard bound
on `|U_e′|` over `[−1,1]`). -/
def Le (e : Nat) : Nat := e * (e + 1) * (e + 2)

/-- `0 < Le e` for `e ≥ 1`. -/
theorem Le_pos {e : Nat} (he : 0 < e) : 0 < Le e := by
  unfold Le
  have h1 : 0 < e * (e + 1) := Nat.mul_pos he (by omega)
  exact Nat.mul_pos h1 (by omega)

/-- The CORRECTED per-cell rate numerator `cRateNum e := 4·(e+1) + 4·Le e`,
ABSORBING the Lipschitz scale `Le e ~ e³` (unlike
`ChebOrthoMidpointEst.cellRateNum := 4(e+1)+4`, which omits it and is false for
small `M`). -/
def cRateNum (e : Nat) : Nat := 4 * (e + 1) + 4 * Le e

/-- `0 < cRateNum e`. -/
theorem cRateNum_pos (e : Nat) : 0 < cRateNum e := by
  unfold cRateNum; omega

/-! ## 1. The CORRECTED explicit per-cell rate `cRate`

`cRate e M k := (cRateNum e)/(M·⌊√M⌋)`, constant in the cell index `k`
(`M > 0`).  Reuses the PROVED integer-√ floor `ChebOrthoMidpointEst.isqrt`
(`⌊√M⌋² ≤ M`, `K² ≤ M ⟹ K ≤ ⌊√M⌋`).  The denominator `M·⌊√M⌋ ≈ M^{3/2}` matches
the corrected per-cell midpoint error `O(M^{-3/2})`; the corrected numerator makes
it a UNIFORM majorant of `[(e+1)√(2h)+L_e h]·h` for ALL `M ≥ 1` (both error parts
`4(e+1)/(M√M)` and `4Le/M²` are `≤ (cRateNum e)/(M·⌊√M⌋)`). -/

/-- The corrected cell-rate denominator `M·⌊√M⌋ > 0`. -/
theorem cRateDen_pos {M : Nat} (hM : 0 < M) : 0 < M * isqrt M :=
  Nat.mul_pos hM (isqrt_pos hM)

/-- **The CORRECTED explicit per-cell rate** `cRate e M k := (cRateNum e)/(M·⌊√M⌋)`,
uniform in the cell index `k`. -/
def cRate (e : Nat) (M : Nat) (hM : 0 < M) (_k : Nat) : Q' :=
  Q'.mkPos (cRateNum e : Int) (M * isqrt M) (cRateDen_pos hM)

/-- **`cRate` is nonnegative.** -/
theorem cRate_nonneg (e M : Nat) (hM : 0 < M) (k : Nat) :
    (0 : Q') ≤ cRate e M hM k := by
  show (0 : Q') ≤ Q'.mkPos (cRateNum e : Int) (M * isqrt M) (cRateDen_pos hM)
  rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]
  exact Int.natCast_nonneg _

/-! ## 2. The constant-cell finite-sum collapse `Σ cRate ≈ (cRateNum)/⌊√M⌋` -/

/-- **The corrected cell-rate finite-sum collapse.**  `Σ_{k<M} cRate e M k ≈
(cRateNum e)/⌊√M⌋`.  Pure `Q'` identity `M·(a/(M·t)) = a/t` (mirrors
`ChebOrthoMidpointEst.finSum_cellRate_eqv` with the corrected numerator). -/
theorem finSum_cRate_eqv (e M : Nat) (hM : 0 < M) :
    (RationalTail.finSum (cRate e M hM) M)
      ≈ (Q'.mkPos (cRateNum e : Int) (isqrt M) (isqrt_pos hM)) := by
  have hconst : (RationalTail.finSum (cRate e M hM) M)
      ≈ (Q'.ofNat M * (Q'.mkPos (cRateNum e : Int) (M * isqrt M) (cRateDen_pos hM))) := by
    have h := SemicircleConvClosed.finSum_const_eqv
      (Q'.mkPos (cRateNum e : Int) (M * isqrt M) (cRateDen_pos hM)) M
    have hfun : (cRate e M hM)
        = (fun _ => Q'.mkPos (cRateNum e : Int) (M * isqrt M) (cRateDen_pos hM)) := rfl
    rw [hfun]; exact h
  refine Q'.eqv_trans _ _ _ hconst ?_
  show (Q'.ofNat M * (Q'.mkPos (cRateNum e : Int) (M * isqrt M) (cRateDen_pos hM))).num
        * ((Q'.mkPos (cRateNum e : Int) (isqrt M) (isqrt_pos hM)).den : Int)
      = (Q'.mkPos (cRateNum e : Int) (isqrt M) (isqrt_pos hM)).num
        * ((Q'.ofNat M
            * (Q'.mkPos (cRateNum e : Int) (M * isqrt M) (cRateDen_pos hM))).den : Int)
  rw [Q'.mul_den_cast, Q'.mkPos_den, Q'.mkPos_num]
  show ((Q'.ofNat M).num
        * (Q'.mkPos (cRateNum e : Int) (M * isqrt M) (cRateDen_pos hM)).num)
        * ((isqrt M : Nat) : Int)
      = (cRateNum e : Int)
        * (((Q'.ofNat M).den : Int)
            * ((Q'.mkPos (cRateNum e : Int) (M * isqrt M) (cRateDen_pos hM)).den : Int))
  rw [Q'.mkPos_num, Q'.mkPos_den]
  show ((Int.ofNat M) * (cRateNum e : Int)) * ((isqrt M : Nat) : Int)
      = (cRateNum e : Int) * ((1 : Int) * (((M * isqrt M : Nat)) : Int))
  have hMt : (((M * isqrt M : Nat)) : Int) = ((M : Nat) : Int) * ((isqrt M : Nat) : Int) := by
    push_cast; rfl
  have hofM : (Int.ofNat M) = ((M : Nat) : Int) := rfl
  rw [hMt, hofM, Int.one_mul]
  rw [Int.mul_comm ((M : Nat) : Int) (cRateNum e : Int),
      Int.mul_assoc (cRateNum e : Int) ((M : Nat) : Int) ((isqrt M : Nat) : Int)]

/-! ## 3. The vanishing of the corrected summed rate -/

/-- The rational `a/t ≤ ε` fact for `a = cRateNum e`: cross-multiplying the goal
`a·ε.den ≤ ε.num·t` (with `ε.num ≥ 1` from `ε > 0`) reduces to
`a·ε.den ≤ t ≤ ε.num·t`, closed from `t ≥ a·ε.den` (mirrors the PROVED
`ChebOrthoMidpointEst.cellRate_over_t_le` with the corrected numerator). -/
theorem cRate_over_t_le {ε : Q'} (hε : (0 : Q') < ε) (e t : Nat) (ht : 0 < t)
    (htge : cRateNum e * ε.den ≤ t) :
    (Q'.mkPos (cRateNum e : Int) t ht) ≤ ε := by
  have hεnum : (0 : Int) < ε.num := by
    have : (0 : Int) * (ε.den : Int) < ε.num * ((0 : Q').den : Int) := hε
    rw [Int.zero_mul] at this
    have hd : ((0 : Q').den : Int) = 1 := rfl
    rw [hd, Int.mul_one] at this; exact this
  show (Q'.mkPos (cRateNum e : Int) t ht).num * (ε.den : Int)
      ≤ ε.num * ((Q'.mkPos (cRateNum e : Int) t ht).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]
  have htge' : ((cRateNum e * ε.den : Nat) : Int) ≤ (t : Int) := by exact_mod_cast htge
  have hcast : ((cRateNum e * ε.den : Nat) : Int)
      = (cRateNum e : Int) * (ε.den : Int) := by push_cast; rfl
  rw [hcast] at htge'
  have ht0 : (0 : Int) ≤ (t : Int) := Int.natCast_nonneg t
  have hεnum1 : (1 : Int) ≤ ε.num := hεnum
  have hstep : (t : Int) ≤ ε.num * (t : Int) := by
    calc (t : Int) = 1 * (t : Int) := by rw [Int.one_mul]
      _ ≤ ε.num * (t : Int) := Int.mul_le_mul_of_nonneg_right hεnum1 ht0
  exact Int.le_trans htge' hstep

/-- **The corrected summed cell-rate VANISHES.**  For every `ε > 0`, there is a
threshold `M₀` past which `Σ_{k<M} cRate e M k ≤ ε`.  The corrected rate
`(cRateNum e)/⌊√M⌋ → 0`: choose `K := (cRateNum e)·ε.den` and threshold
`M₀ := K·K`, so `M ≥ M₀ ⟹ K² ≤ M ⟹ K ≤ ⌊√M⌋` (`isqrt_ge`), hence
`(cRateNum e)/⌊√M⌋ ≤ ε` (`cRate_over_t_le`). -/
theorem cRateSum_vanishes (e : Nat) :
    ∀ ε : Q', (0 : Q') < ε → ∃ M₀ : Nat, ∀ M : Nat, M₀ ≤ M → (hM : 0 < M) →
      (RationalTail.finSum (cRate e M hM) M) ≤ ε := by
  intro ε hε
  refine ⟨(cRateNum e * ε.den) * (cRateNum e * ε.den), fun M hM₀ hM => ?_⟩
  have hKle : cRateNum e * ε.den ≤ isqrt M :=
    isqrt_ge (m := M) (K := cRateNum e * ε.den) hM₀
  have hisqrt_pos : 0 < isqrt M := isqrt_pos hM
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (finSum_cRate_eqv e M hM)) ?_
  exact cRate_over_t_le hε e (isqrt M) hisqrt_pos hKle

/-! ## 4. A GENUINE sub-bound of the per-cell estimate: the radical-difference
√-Hölder leg

The (i) leg of the midpoint estimate — that the three cell radicals
`√(1−b_{k+1}²)`, `√(1−b_k²)`, `√(1−x_k²)` are within the √-Hölder tolerance `c`
of each other (all radicands within `h` ⇒ radical differences `≤ √(2·2h)`-type) —
is GENUINE √-Hölder content, fully discharged by the PROVED
`SqrtSubadd.sqrtFrom_sub_leRat`.  We expose it abstractly on two `sqrtFrom`
radicands as `radDiff_holder` (the consumer instantiates it at the three concrete
boundary radicands `1−b_k²`, with `c ≥ √(radicand gap)`). -/

/-- **The radical-difference √-Hölder leg (PROVED).**  For two positive rational
radicands `u ≥ v > 0` with `sqrtFrom` witnesses and a rational tolerance `c > 0`
with `u ≤ v + c·c` (`u − v ≤ c²`), the radical difference is bounded:
`√u − √v ≤ c` (sound `leRat`).  This is exactly the `(i)` radical-difference leg
of the per-cell midpoint estimate (instantiated at the three concrete cell
radicands `1−b_{k+1}²`, `1−b_k²`, `1−x_k²`, which all lie within `h` of each
other, so the radicand gap is `≤ 2h` and `c := √(2h)` works).  Direct application
of the PROVED `SqrtSubadd.sqrtFrom_sub_leRat`. -/
theorem radDiff_holder
    (u Lu : Q') (hu : (0 : Q') < u) (hLu : (0 : Q') < Lu) (hLua : Lu * Lu ≤ u)
    (v Lv : Q') (hv : (0 : Q') < v) (hLv : (0 : Q') < Lv) (hLva : Lv * Lv ≤ v)
    (c : Q') (hc : (0 : Q') < c) (huvc : u ≤ v + c * c) :
    CReal.leRat
      (CReal.add (CReal.sqrtFrom u Lu hu hLu hLua)
        (CReal.neg (CReal.sqrtFrom v Lv hv hLv hLva))) c :=
  CReal.sqrtFrom_sub_leRat u Lu hu hLu hLua v Lv hv hLv hLva c hc huvc

/-! ## 5. The PRECISE residual: the per-cell estimate against the CORRECTED rate -/

/-- **NAMED-open: the per-cell midpoint estimate against the CORRECTED rate.**  For
the even order `e` (`he : 0 < e`), every GENUINE real-boundary adjusted cell
`cellAdjR e he (N+1) k = orthTerm k + (GsampR(b_{k+1}) − GsampR(b_k))` is
two-sidedly bounded by the CORRECTED rate `cRate e (N+1) k`:

    `leRat (cellAdjR e he (N+1) … k) (cRate e (N+1) … k)`  and the negation.

This is the bounded-derivative midpoint error bound on the REAL adjusted cells,
against a rate that ABSORBS the Lipschitz scale `L_e` (so it is SATISFIABLE for
ALL `M ≥ 1`, unlike `ChebOrthoMidpointEst.PerCellIncrementBound`).  The single
remaining genuine content is the discrete LEADING-CANCELLATION step (constructive
Taylor remainder converting the infinitesimal `Gval′ = −f_e` of
`ChebUDClosure.Bderiv_identity_uncond` into the per-cell finite-difference bound);
its radical-difference leg is the PROVED `radDiff_holder`.  Recorded precisely. -/
def CorrectedPerCellBound (e : Nat) (he : 0 < e) : Prop :=
  ∀ N k : Nat,
    CReal.leRat (cellAdjR e he (N + 1) (Nat.succ_pos N) k)
        (cRate e (N + 1) (Nat.succ_pos N) k) ∧
    CReal.leRat (CReal.neg (cellAdjR e he (N + 1) (Nat.succ_pos N) k))
        (cRate e (N + 1) (Nat.succ_pos N) k)

/-! ## 6. The genuine packaging `CorrectedPerCellBound → RealPerCellBudget` -/

/-- **THE PACKAGING.**  `CorrectedPerCellBound e he → RealPerCellBudget e he`.
The named per-cell two-sided bound supplies the `leRat` data; the corrected
`cRate` supplies nonnegativity (`cRate_nonneg`) and the vanishing finite-sum
(`cRateSum_vanishes`); the three are assembled into the `RealPerCellBudget`
existential with witness rate
`r n k := if hn : 0 < n then cRate e n hn k else 0`. -/
theorem realPerCellBudget_of_correctedBound (e : Nat) (he : 0 < e)
    (h : CorrectedPerCellBound e he) : ChebOrthoMidpoint.RealPerCellBudget e he := by
  refine ⟨fun n k => if hn : 0 < n then cRate e n hn k else 0, ?_, ?_, ?_⟩
  · intro n k
    show (0 : Q') ≤ (if hn : 0 < n then cRate e n hn k else 0)
    by_cases hn : 0 < n
    · rw [dif_pos hn]; exact cRate_nonneg e n hn k
    · rw [dif_neg hn]; exact Q'.le_refl' 0
  · intro N k
    have hN1 : (0 : Nat) < N + 1 := Nat.succ_pos N
    show CReal.leRat (cellAdjR e he (N + 1) (Nat.succ_pos N) k)
          (if hn : 0 < N + 1 then cRate e (N + 1) hn k else 0) ∧
        CReal.leRat (CReal.neg (cellAdjR e he (N + 1) (Nat.succ_pos N) k))
          (if hn : 0 < N + 1 then cRate e (N + 1) hn k else 0)
    rw [dif_pos hN1]
    exact h N k
  · intro ε hε
    obtain ⟨M₀, hM₀⟩ := cRateSum_vanishes e ε hε
    refine ⟨M₀, fun N hN => ?_⟩
    have hN1 : (0 : Nat) < N + 1 := Nat.succ_pos N
    show (RationalTail.finSum
        (fun k => if hn : 0 < N + 1 then cRate e (N + 1) hn k else 0) (N + 1)) ≤ ε
    have hfun : (fun k => if hn : 0 < N + 1 then cRate e (N + 1) hn k else 0)
        = cRate e (N + 1) hN1 := by
      funext k; rw [dif_pos hN1]
    rw [hfun]
    have hM₀N : M₀ ≤ N + 1 := Nat.le_trans hN (Nat.le_succ N)
    exact hM₀ (N + 1) hM₀N hN1

/-! ## 7. The even-order limit and full off-diagonal closure, reduced to the
single per-cell estimate against the CORRECTED rate -/

/-- **`OrthEvenZeroLimit e` from the corrected per-cell estimate.**  Composes the
packaging with the proved bridges
`ChebOrthoMidpoint.budgetExists_of_realPerCell` →
`orthEvenZeroLimit_of_budgetExists`. -/
theorem orthEvenZeroLimit_of_correctedBound (e : Nat) (he : 0 < e)
    (h : CorrectedPerCellBound e he) :
    ChebOrthoEvenFTC.OrthEvenZeroLimit e :=
  ChebOrthoMidpoint.orthEvenZeroLimit_of_realPerCell e he
    (realPerCellBudget_of_correctedBound e he h)

/-- **Off-diagonal orthogonality `∫U_e√ = 0` for `e ≥ 1`, from the corrected
per-cell estimate (even orders).**  The ODD case is already UNCONDITIONAL; the
EVEN case via the corrected per-cell bound + the proved bridges.  π-free. -/
theorem offdiag_closed_of_correctedBound
    (hinc : ∀ (e : Nat) (he : 0 < e), 2 ≤ e → e % 2 = 0 → CorrectedPerCellBound e he) :
    ∀ (e : Nat), 1 ≤ e →
      ∃ L : CReal, CReal.ConvergesTo (seqOrth e) L ∧ CReal.Equiv L CReal.czero := by
  refine ChebOrthoMidpoint.offdiag_closed_of_realPerCell (fun e he he2 heven => ?_)
  exact realPerCellBudget_of_correctedBound e he (hinc e he he2 heven)

end YMGap.Continuum.ChebOrthoMidpointCore

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `Le` / `Le_pos` — the explicit Nat Lipschitz-scale `Le e := e·(e+1)·(e+2) ~ e³`.
  * `cRateNum` / `cRateNum_pos` — the CORRECTED per-cell rate numerator
    `4·(e+1) + 4·Le e`, ABSORBING the Lipschitz scale `L_e` (unlike
    `ChebOrthoMidpointEst.cellRateNum := 4(e+1)+4`, which omits it and is hence
    FALSE for small `M`).
  * `cRate` / `cRate_nonneg` — the CORRECTED explicit per-cell rational rate
    `(cRateNum e)/(M·⌊√M⌋)`, a genuine UNIFORM MAJORANT of the bounded-derivative
    midpoint error `[(e+1)√(2h)+L_e h]·h` for ALL `M ≥ 1` (reusing the PROVED
    `ChebOrthoMidpointEst.isqrt`).
  * `cRate_over_t_le` / **`finSum_cRate_eqv`** / **`cRateSum_vanishes`** — the
    finite-sum collapse `Σ cRate ≈ (cRateNum e)/⌊√M⌋` and its GENUINE vanishing
    (threshold `M ≥ ((cRateNum e)·ε.den)²`, via `isqrt_ge`).
  * **`radDiff_holder`** — the (i) radical-difference √-Hölder leg of the per-cell
    estimate, fully discharged by the PROVED `SqrtSubadd.sqrtFrom_sub_leRat`
    (`√u − √v ≤ c` when `u − v ≤ c²`).
  * **`realPerCellBudget_of_correctedBound`** — the genuine packaging
    `CorrectedPerCellBound e he → ChebOrthoMidpoint.RealPerCellBudget e he`.
  * `orthEvenZeroLimit_of_correctedBound` / `offdiag_closed_of_correctedBound` —
    the even-order `czero` limit and the COMBINED π-free off-diagonal
    orthogonality `∫U_e√ = 0` for `e ≥ 1`, reduced to the SINGLE per-cell estimate
    AGAINST THE CORRECTED RATE (odd UNCONDITIONAL), via the proved bridges
    `ChebOrthoMidpoint.budgetExists_of_realPerCell` → `convergesTo_czero_of_bound`.

**NAMED-open (the honest residual — ONE per-cell analytic estimate).**
  * `CorrectedPerCellBound e he` — the per-cell midpoint estimate
    `|cellAdjR e he (N+1) k| ≤ cRate e (N+1) k` on the GENUINE real-boundary
    adjusted cells, against the CORRECTED (`L_e`-absorbing) rate `cRate`.  By
    `ChebUDClosure.Bderiv_identity_uncond` (`(1−x²)B_e′ − xB_e ≈ −2(1−x²)U_e`, so
    `Gval′ = −f_e = −U_e√(1−x²)` is BOUNDED — the `−x/√(1−x²)` singularity
    CANCELS) the increment is `GsampR(b_{k+1}) − GsampR(b_k) ≈ −f_e(x_k)·h +
    (midpoint remainder)`, and `orthTerm k = f_e(x_k)·h`, so the leading
    `f_e(x_k)·h` terms CANCEL, leaving `cellAdjR k ≈ (second-order remainder)`,
    bounded by `ω(h) = (e+1)√(2h) + L_e·h` (the radical leg is the PROVED
    `radDiff_holder`; the `U_e`-Lipschitz leg uses `Le`; `|U_e| ≤ e+1` from
    `ChebyshevU.absU_le`).  The SINGLE remaining content is the discrete
    LEADING-CANCELLATION step (the constructive Taylor remainder converting the
    infinitesimal `Gval′ = −f_e` into the per-cell finite-difference bound).
    Recorded precisely, not faked.  The CORRECTED vanishing rate that consumes it
    (`cRate`/`cRateSum_vanishes`), the packaging into `RealPerCellBudget`, and the
    off-diagonal bridges are PROVED here.

**Path to closure.**  Once `CorrectedPerCellBound e he` holds for every even
`e ≥ 2`, `realPerCellBudget_of_correctedBound` + the companion
`ChebOrthoMidpoint.budgetExists_of_realPerCell` close `BudgetExists e`, hence (via
the proved `convergesTo_czero_of_bound`) `OrthEvenZeroLimit e` and the full π-free
off-diagonal orthogonality `∫U_e√ = 0` for all `e ≥ 1`.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoMidpointCore.Le_pos
#print axioms YMGap.Continuum.ChebOrthoMidpointCore.cRateNum_pos
#print axioms YMGap.Continuum.ChebOrthoMidpointCore.cRate_nonneg
#print axioms YMGap.Continuum.ChebOrthoMidpointCore.cRate_over_t_le
#print axioms YMGap.Continuum.ChebOrthoMidpointCore.finSum_cRate_eqv
#print axioms YMGap.Continuum.ChebOrthoMidpointCore.cRateSum_vanishes
#print axioms YMGap.Continuum.ChebOrthoMidpointCore.radDiff_holder
#print axioms YMGap.Continuum.ChebOrthoMidpointCore.realPerCellBudget_of_correctedBound
#print axioms YMGap.Continuum.ChebOrthoMidpointCore.orthEvenZeroLimit_of_correctedBound
#print axioms YMGap.Continuum.ChebOrthoMidpointCore.offdiag_closed_of_correctedBound
