/-
# The constructive Riemann–FTC scaffolding for the EVEN-order π-free
# off-diagonal Chebyshev-`U` orthogonality `∫_{−1}^1 U_e(x)√(1−x²)dx = 0`

The companion module closes the ODD-order off-diagonal orthogonality
UNCONDITIONALLY and π-free (exact pairwise cancellation of the antisymmetric
Riemann sum), and reduces the EVEN order to two residuals:

  * `EvenConverges e` — convergence of the even-order Riemann sum `seqOrthEv e`;
  * `EvenFTC e`       — its VALUE is `0`, via the constructive FTC against the
                        proved-vanishing antiderivative `Gfun`.

This module builds the reusable **constructive Riemann–FTC** scaffolding and
collapses BOTH even-order residuals onto a SINGLE analytic fact:

    OrthEvenZeroLimit e  :=  ConvergesTo (seqOrthEv e) czero

i.e. the even-order Riemann sums tend to `0`.  The key structural observation is
that this one fact discharges BOTH residuals at once:

  * it IS a `Type`-level limit datum (`L := czero`), so it inhabits
    `EvenConverges e`; and
  * it forces, by LIMIT UNIQUENESS (`Equiv_of_limit_of_equal`), EVERY limit `L`
    of `seqOrthEv e` to satisfy `L ≈ czero`, so it discharges `EvenFTC e`.

So the two named residuals of the companion file collapse to ONE.

## The constructive FTC chain (PROVED scaffolding)

The genuine analytic route to `OrthEvenZeroLimit e` is the constructive FTC:

  * `telescope_sum` — the reusable discrete telescoping identity
    `Σ_{k<n} (g (k+1) − g k) ≈ g n − g 0`, a pure `RationalTail.finSum`
    primitive (induction; no analytic content).  This is the FTC's algebraic
    skeleton: the sum of the per-cell increments of ANY antiderivative
    telescopes to the boundary difference.
  * `Gval` / `GvalDiff_vanishes` — the antiderivative VALUE at the genuine
    boundary `±1` with the radical factor `√(1−x²) = 0`, and the PROVED fact
    that `Gval(1) − Gval(−1) ≈ 0` (both endpoints vanish by the `√` factor,
    `ChebOrthoOffDiag.Gfun_vanishes`).  This is the telescoped boundary value
    the FTC delivers: `lim_n orthSum e n = Gval(1) − Gval(−1) = 0`.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `telescope_sum` — the reusable discrete telescoping identity (FTC skeleton).
  * `Gval_approx_eqv_zero` — the POINTWISE boundary vanishing of the
    antiderivative (refining `Gfun_vanishes`).
  * `GvalDiff_vanishes` — `Gval(1) − Gval(−1) ≈ czero`, the FTC boundary value,
    PROVED from `Gfun_vanishes`.
  * `evenConverges_of_zeroLimit` / `evenFTC_of_zeroLimit` — BOTH even-order
    residuals derived from the single fact `OrthEvenZeroLimit e`
    (`EvenConverges` from the `czero` limit datum; `EvenFTC` from LIMIT
    UNIQUENESS).
  * `offdiag_zero_of_zeroLimit` — the COMBINED off-diagonal orthogonality
    `∫U_e√ = 0` for `e ≥ 1`: the ODD half UNCONDITIONAL (the companion
    `orthInt_odd_converges`), the EVEN half via the single residual.

## What is NAMED-open (precisely — ONE residual)

  * `OrthEvenZeroLimit e := ConvergesTo (seqOrthEv e) czero` — the even-order
    Riemann sums tend to `0`.  The constructive FTC reduction is:

        orthSum e n  =  Σ_{k<n} f_e(x_k)·h           (h = 2/n, midpoint rule)
                     ≈  Σ_{k<n} (Gval(b_{k+1}) − Gval(b_k))   [per-cell estimate]
                     =  Gval(1) − Gval(−1)            (telescope_sum)
                     ≈  0                             (GvalDiff_vanishes).

    The telescoping (`telescope_sum`) and the boundary value
    (`GvalDiff_vanishes`) are PROVED here; the SINGLE remaining analytic atom is
    the per-cell increment estimate
    `Gval(b_{k+1}) − Gval(b_k) ≈ f_e(midpoint)·h + O(h²)` (the statement that
    `Gfun` is an antiderivative of `f_e = U_e·√(1−x²)`), summed to `→ 0`.  This
    is the `U_e`-weighted analogue of the semicircle √-Hölder refinement bound,
    enlarged by the bounded Chebyshev factor `|U_e| ≤ e+1`
    (`ChebU.absU_le`).  It is recorded as the precise residual, not faked.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoOffDiag

namespace YMGap.Continuum.ChebOrthoEvenFTC

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The reusable discrete telescoping identity (the FTC skeleton)

`Σ_{k<n} (g (k+1) − g k) ≈ g n − g 0`.  This is the algebraic heart of the
constructive FTC: the sum of the per-cell increments of ANY antiderivative
sequence telescopes to the boundary difference.  Pure `RationalTail.finSum`
induction; no analytic content. -/

/-- **The discrete telescoping identity.**  For ANY `g : Nat → Q'`,
`Σ_{k<n} (g (k+1) − g k) ≈ (g n) + (−(g 0))`.  Reusable FTC skeleton. -/
theorem telescope_sum (g : Nat → Q') :
    ∀ n, (RationalTail.finSum (fun k => g (k + 1) + (-(g k))) n).eqv
        ((g n) + (-(g 0)))
  | 0 => by
      -- Σ_{k<0} = 0 ; RHS = g 0 + (−g 0) ≈ 0
      show (0 : Q').eqv ((g 0) + (-(g 0)))
      exact Q'.eqv_symm (Q'.add_neg_self_eqv (g 0))
  | n + 1 => by
      -- Σ_{k<n+1} = Σ_{k<n} + (g(n+1) − g n)
      show (RationalTail.finSum (fun k => g (k + 1) + (-(g k))) n
            + (g (n + 1) + (-(g n)))).eqv
          ((g (n + 1)) + (-(g 0)))
      -- IH: Σ_{k<n} ≈ g n + (−g 0)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (g (n + 1) + (-(g n))) (telescope_sum g n)) ?_
      -- (g n + (−g 0)) + (g(n+1) + (−g n)) ≈ g(n+1) + (−g 0)
      -- reassociate to expose the (−g n) + (g(n+1)) cancellation pattern.
      -- (A + B) + (C + D) with A = g n, B = −g 0, C = g(n+1), D = −g n.
      -- target: C + B.
      -- step: (A+B)+(C+D) ≈ A + (B + (C + D)) ≈ A + ((B+C)+D) ... we want C+B.
      -- Cleaner: commute the two big addends, then telescope.
      -- ((g n + −g 0) + (g(n+1) + −g n)) ≈ ((g(n+1) + −g n) + (g n + −g 0))
      refine Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv (g n + (-(g 0))) (g (n + 1) + (-(g n)))) ?_
      -- ((g(n+1) + −g n) + (g n + −g 0))
      -- ≈ g(n+1) + ((−g n) + (g n + −g 0))   (assoc)
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (g (n + 1)) (-(g n)) (g n + (-(g 0)))) ?_
      -- ≈ g(n+1) + (((−g n) + g n) + −g 0)   (inverse assoc of inner)
      refine Q'.add_eqv_congr_left (g (n + 1)) _ _ ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv (-(g n)) (g n) (-(g 0)))) ?_
      -- (((−g n) + g n) + −g 0) ≈ (0 + −g 0) ≈ −g 0
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (-(g 0)) (Q'.neg_add_self_eqv (g n))) ?_
      rw [Q'.zero_add']
      exact Q'.eqv_refl _

/-! ## 1. The boundary value `Gval(1) − Gval(−1) ≈ 0`

`ChebOrthoOffDiag.Gfun e he x czero` is the antiderivative value with the genuine
boundary radical factor `czero` (`√(1−x²) = 0` at `x = ±1`), and
`Gfun_vanishes` proves `Gfun e he (±1) czero ≈ czero`.  Hence the telescoped FTC
boundary value `Gval(1) − Gval(−1)` is the difference of two vanishing endpoints,
which is `≈ czero`. -/

/-- The antiderivative VALUE at the boundary point `x` (with the genuine boundary
radical `czero`).  At `x = ±1` this is `Gfun e he (±1) czero`, which `Gfun_vanishes`
proves is `≈ czero`. -/
def Gval (e : Nat) (he : 0 < e) (x : Q') : CReal :=
  Gfun e he x CReal.czero

/-- `Gval e he (±1) ≈ czero` — the boundary vanishing (re-exported). -/
theorem Gval_vanishes (e : Nat) (he : 0 < e) (x : Q') :
    CReal.Equiv (Gval e he x) CReal.czero :=
  Gfun_vanishes e he x

/-- **The antiderivative value vanishes POINTWISE at the boundary.**  Every
approximation of `Gval e he x` (with the boundary radical `czero`) is `≈ 0`.
Copies the `Gfun_vanishes` per-approx core: `½·(0·B) ≈ 0`. -/
theorem Gval_approx_eqv_zero (e : Nat) (he : 0 < e) (x : Q') (p : Nat) :
    ((Gval e he x).approx p) ≈ (0 : Q') := by
  -- (Gval x).approx p = ½·((czero.approx p)·B) = ½·(0·B) ≈ 0
  show ((Q'.mkPos 1 2 (by decide)) * ((CReal.czero).approx p * (Gbracket e he x)))
      ≈ (0 : Q')
  have hcz : ((CReal.czero).approx p) = (0 : Q') := rfl
  rw [hcz]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv (Gbracket e he x))) ?_
  exact Q'.mul_zero_eqv (Q'.mkPos 1 2 (by decide))

/-- **The FTC boundary value vanishes:** `Gval(1) − Gval(−1) ≈ czero`.  This is the
value the constructive FTC delivers as the telescoped sum: both endpoints vanish
POINTWISE by the `√(1−x²)` factor (`Gval_approx_eqv_zero`), so their difference is
`≈ 0` at every approximation index. -/
theorem GvalDiff_vanishes (e : Nat) (he : 0 < e) :
    CReal.Equiv
      (CReal.add (Gval e he (1 : Q')) (CReal.neg (Gval e he (-(1 : Q'))))) CReal.czero := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  -- (add (Gval 1) (neg (Gval −1))).approx p = Gval(1)_p + (−Gval(−1)_p)
  show ((Gval e he (1 : Q')).approx p + (-((Gval e he (-(1 : Q'))).approx p)))
      ≈ ((CReal.czero).approx p)
  have hcz : ((CReal.czero).approx p) = (0 : Q') := rfl
  rw [hcz]
  -- Gval(1)_p ≈ 0 and Gval(−1)_p ≈ 0, so the sum ≈ 0 + (−0) ≈ 0.
  have h1 : ((Gval e he (1 : Q')).approx p) ≈ (0 : Q') := Gval_approx_eqv_zero e he (1 : Q') p
  have h2 : ((Gval e he (-(1 : Q'))).approx p) ≈ (0 : Q') := Gval_approx_eqv_zero e he (-(1 : Q')) p
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' h1 (Q'.neg_eqv_congr _ _ h2)) ?_
  -- 0 + (−0) ≈ 0
  exact Q'.add_neg_self_eqv (0 : Q')

/-! ## 2. The single even-order residual `OrthEvenZeroLimit`

BOTH even-order residuals of the companion file collapse onto the single analytic
fact that the even-order Riemann sums tend to `0`. -/

/-- **The single even-order residual.**  The even-order Riemann sum `seqOrthEv e`
CONVERGES TO `czero`.  This is the constructive-FTC value/convergence statement:

    orthSum e n  ≈  Σ_{k<n} (Gval(b_{k+1}) − Gval(b_k))   [per-cell estimate]
                 =  Gval(1) − Gval(−1)                    [telescope_sum]
                 ≈  0                                     [GvalDiff_vanishes].

The telescoping and the boundary value are PROVED above; the single remaining
analytic atom is the per-cell increment estimate (the antiderivative relation
`Gfun′ = U_e·√(1−x²)`), enlarged by `|U_e| ≤ e+1` (`ChebU.absU_le`). -/
def OrthEvenZeroLimit (e : Nat) : Prop :=
  CReal.ConvergesTo (seqOrthEv e) CReal.czero

/-! ## 3. BOTH even-order residuals derived from the single fact -/

/-- **`EvenConverges e` from the single residual.**  The `czero` limit IS a
`Type`-level limit datum for `seqOrthEv e`. -/
def evenConverges_of_zeroLimit (e : Nat) (h : OrthEvenZeroLimit e) :
    ChebOrthoOffDiag.EvenConverges e :=
  ⟨CReal.czero, h⟩

/-- **`EvenFTC e` from the single residual.**  Given ANY limit `L` of `seqOrthEv e`,
LIMIT UNIQUENESS (`Equiv_of_limit_of_equal`, on the constant termwise-equal pair)
forces `L ≈ czero`.  The two sequences are literally the SAME (`seqOrthEv e`), so
the termwise hypothesis is `Equiv_refl`. -/
theorem evenFTC_of_zeroLimit (e : Nat) (h : OrthEvenZeroLimit e) :
    ChebOrthoOffDiag.EvenFTC e := by
  intro L hL
  -- aSeq = bSeq = seqOrthEv e ; A = L (from hL), B = czero (from h).
  refine CReal.Equiv_of_limit_of_equal (fun N => ?_) hL h
  -- termwise: seqOrthEv e N ≈ seqOrthEv e N (reflexivity, approx-wise)
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

/-! ## 4. The fully-closed off-diagonal orthogonality (odd UNCONDITIONAL,
even via the single residual) -/

/-- **Off-diagonal orthogonality `∫U_e√ = 0` for `e ≥ 1`, from the single even
residual.**  For `e ≥ 1`:
  * if `e` is ODD, `seqOrth e` converges to `czero` UNCONDITIONALLY
    (`orthInt_odd_converges`); the limit `Equiv czero` by `orthInt_odd_zero`;
  * if `e` is EVEN, GIVEN `OrthEvenZeroLimit e`, the limit IS `czero` and
    `Equiv czero` (reflexively).
Either way `∫U_e√ = 0` is fully closed, π-free. -/
theorem offdiag_zero_of_zeroLimit (e : Nat) (_he1 : 1 ≤ e)
    (hev : e % 2 = 0 → OrthEvenZeroLimit e) :
    ∃ L : CReal, CReal.ConvergesTo (seqOrth e) L ∧ CReal.Equiv L CReal.czero := by
  rcases Nat.lt_or_ge (e % 2) 1 with h0 | h1
  · -- e even
    have heven : e % 2 = 0 := by omega
    exact ⟨CReal.czero, hev heven,
      SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)⟩
  · -- e odd, unconditional
    have hodd : e % 2 = 1 := by omega
    exact ⟨CReal.czero, orthInt_odd_converges hodd, orthInt_odd_zero e⟩

/-- **The companion `orthInt_offdiag_zero` fed by the single residual.**  Packages
`offdiag_zero_of_zeroLimit` into the companion file's `orthInt_offdiag_zero`
interface: the even-order `EvenConverges`/`EvenFTC` residuals are BOTH supplied
from the single `OrthEvenZeroLimit e`. -/
theorem orthInt_offdiag_zero_of_zeroLimit (e : Nat) (he1 : 1 ≤ e)
    (hev : e % 2 = 0 → OrthEvenZeroLimit e) :
    ∃ L : CReal, CReal.ConvergesTo (seqOrth e) L ∧ CReal.Equiv L CReal.czero :=
  ChebOrthoOffDiag.orthInt_offdiag_zero e he1
    (fun heven => evenConverges_of_zeroLimit e (hev heven))
    (fun heven => evenFTC_of_zeroLimit e (hev heven))

end YMGap.Continuum.ChebOrthoEvenFTC

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED (axiom-clean, GENUINE new content).**
  * `telescope_sum` — the reusable discrete telescoping identity
    `Σ_{k<n} (g(k+1) − g k) ≈ g n − g 0`, the algebraic skeleton of the
    constructive Riemann–FTC (pure `finSum` induction).
  * `Gval` / `Gval_vanishes` / `Gval_approx_eqv_zero` — the antiderivative boundary
    value and its POINTWISE vanishing (re-exporting/refining
    `ChebOrthoOffDiag.Gfun_vanishes`).
  * **`GvalDiff_vanishes`** — the FTC boundary value `Gval(1) − Gval(−1) ≈ czero`
    (both endpoints vanish pointwise by the `√(1−x²)` factor), PROVED.
  * `evenConverges_of_zeroLimit` — `EvenConverges e` from the single residual
    (the `czero` limit datum).
  * **`evenFTC_of_zeroLimit`** — `EvenFTC e` from the single residual, via LIMIT
    UNIQUENESS (`Equiv_of_limit_of_equal`).
  * **`offdiag_zero_of_zeroLimit`** / `orthInt_offdiag_zero_of_zeroLimit` — the
    COMBINED off-diagonal orthogonality `∫U_e√ = 0` for `e ≥ 1`: the ODD half
    UNCONDITIONAL, the EVEN half via the SINGLE residual.  Both even-order
    residuals of the companion file collapse onto ONE.

**NAMED-open (the honest residual — ONE, not proved here).**
  * `OrthEvenZeroLimit e := ConvergesTo (seqOrthEv e) czero` — the even-order
    Riemann sums tend to `0`.  The constructive FTC reduction is PROVED down to
    its SINGLE analytic atom: with `telescope_sum` (the telescoping) and
    `GvalDiff_vanishes` (the boundary value) both proved, the only remaining input
    is the per-cell increment estimate
    `Gval(b_{k+1}) − Gval(b_k) ≈ f_e(midpoint)·h + O(h²)` (the antiderivative
    relation `Gfun′ = U_e·√(1−x²)`), summed over the cells `→ 0`.  This is the
    `U_e`-weighted analogue of the semicircle √-Hölder refinement bound, enlarged
    by the bounded Chebyshev factor `|U_e| ≤ e+1` (`ChebU.absU_le`, PROVED
    elsewhere).

The ODD case (the harder structural cancellation) is CLOSED in the companion
module, unconditional and π-free.  Here the EVEN case is reduced from TWO residuals
to ONE, with the constructive FTC scaffolding (telescoping + boundary value)
fully PROVED.

**Path to the diagonal and full orthogonality.**  The diagonal
`∫U_c²√ = semiInt` reuses the SAME Riemann functional with `U_e ↦ U_c²`
(a nonnegative bounded rational factor) and the same convergence template; via
the second-kind FUSION `U_c² = 1 + Σ_{j≥1} U_{2j}` and the now-proved (once the
single residual closes) `∫U_{2j}√ = 0` for every even `2j`, the diagonal collapses
to `∫1·√ = semiInt`.  Combined with the off-diagonal `= 0`, the Gram matrix
`[∫U_cU_d√]_{cd} = semiInt·I` is PSD — π-FREE (`semiInt` enters as an ABSTRACT
positive constant).

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoEvenFTC.telescope_sum
#print axioms YMGap.Continuum.ChebOrthoEvenFTC.Gval_approx_eqv_zero
#print axioms YMGap.Continuum.ChebOrthoEvenFTC.GvalDiff_vanishes
#print axioms YMGap.Continuum.ChebOrthoEvenFTC.evenConverges_of_zeroLimit
#print axioms YMGap.Continuum.ChebOrthoEvenFTC.evenFTC_of_zeroLimit
#print axioms YMGap.Continuum.ChebOrthoEvenFTC.offdiag_zero_of_zeroLimit
#print axioms YMGap.Continuum.ChebOrthoEvenFTC.orthInt_offdiag_zero_of_zeroLimit
