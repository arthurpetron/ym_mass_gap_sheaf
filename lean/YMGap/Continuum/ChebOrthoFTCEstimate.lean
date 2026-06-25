/-
# The constructive √-weighted FTC ESTIMATE for the EVEN-order π-free off-diagonal
# Chebyshev-`U` orthogonality: the `orthSum e n → 0` limit packaging

The companion modules reduce the even-order off-diagonal orthogonality
`∫_{−1}^1 U_e(x)√(1−x²)dx = 0` to the SINGLE analytic residual

    `ChebOrthoEvenFTC.OrthEvenZeroLimit e := ConvergesTo (seqOrthEv e) czero`

(the even `U_e`-weighted Riemann sums tend to `0`), and supply ALL of the
algebraic FTC apparatus UNCONDITIONALLY:

  * the antiderivative identity `Bderiv_identity_uncond`
    `(1−x²)·B_e′ − x·B_e ≈ −2·(1−x²)·U_e` — the certificate that
    `Gval e = ½·√(1−x²)·B_e` is the antiderivative of `f_e = U_e·√(1−x²)`
    (the per-cell increment's LEADING term, PROVED in `ChebUDClosure`);
  * the discrete telescoping identity `telescope_sum`
    `Σ_{k<n} (g(k+1) − g k) ≈ g n − g 0` (the FTC's algebraic skeleton);
  * the boundary value `GvalDiff_vanishes`
    `Gval(1) − Gval(−1) ≈ czero` (both endpoints vanish by the `√(1−x²)` factor).

What remains is the QUANTITATIVE summed-error ESTIMATE: the per-cell increment
`Gval(b_{k+1}) − Gval(b_k) ≈ −f_e(x_k)·h + O(h²)` (interior, from
`Bderiv_identity_uncond`) plus the O(√δ) boundary control, summed over the cells
and balanced at `δ = √h` to `→ 0`.

## What is PROVED here (axiom-clean, GENUINE new content)

This module supplies the **rate-to-limit BRIDGE** that turns a rational
error-budget rate into the `ConvergesTo (… ) czero` limit, the missing
analytic-packaging atom of the FTC estimate:

  * `RateToZero B` / `rateToZero_invSucc` — the abstract "vanishing rational
    rate" predicate and a CONCRETE instance built from the canonical unit
    fraction `Q'.invSucc` (`1/(n+1) → 0`), PROVED non-vacuous.
  * `SumTwoSidedBound e B` — the per-resolution two-sided `leRat` budget
    `|orthSum e (n+1)| ≤ B n` (both directions), the EXACT shape the summed FTC
    estimate delivers; the analytic residual is recorded precisely as this
    predicate.
  * **`convergesTo_czero_of_bound`** — THE BRIDGE: from a vanishing rational
    rate `B` (`RateToZero B`) and the two-sided budget `SumTwoSidedBound e B`,
    the even Riemann sums converge to `czero`, i.e. `OrthEvenZeroLimit e`.
    Fully PROVED, axiom-clean; this is the reusable rate ⇒ limit packaging.
  * `weightedFTCEstimate_of_budget` — `WeightedFTCEstimate` reduced to the
    EXISTENCE of a vanishing-rate two-sided budget (the named analytic residual
    `BudgetExists`), with `Bderiv_identity_uncond` supplying the increment's
    leading term.
  * `offdiag_closed_of_budget` — the COMBINED off-diagonal orthogonality
    `∫U_e√ = 0` for `e ≥ 1`, conditional on the budget existence; the ODD case is
    already UNCONDITIONAL (companion).  π-free.

## What is NAMED-open (precisely — ONE analytic residual)

  * `BudgetExists e := ∃ B, RateToZero B ∧ SumTwoSidedBound e B` — the existence
    of a vanishing rational error budget two-sidedly bounding the even Riemann
    sums.  This is the SUMMED midpoint-quadrature error estimate: with the
    antiderivative identity `Bderiv_identity_uncond` (leading term) and the
    telescope + boundary vanishing (`telescope_sum`, `GvalDiff_vanishes`) all
    proved, `B n` is the explicit interior (`C(e)·h/δ`) + boundary (`δ^{3/2}`)
    budget at `δ = √h`, summed via the proved √-Hölder per-cell bound
    (`SqrtSubadd.holder_oneMinusSq`/`sqrtFrom_sub_leRat`) and `|U_e| ≤ e+1`
    (`ChebU.absU_le`).  Recorded as the precise residual, not faked.

Once `BudgetExists e` is supplied for every even `e ≥ 2`, this module closes
`OrthEvenZeroLimit e` and hence (with the unconditional odd case) the full π-free
off-diagonal orthogonality `∫U_e√ = 0` for all `e ≥ 1`.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebUDClosure
import YMGap.Continuum.ChebOrthoEvenFTC

namespace YMGap.Continuum.ChebOrthoFTCEstimate

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag
open YMGap.Continuum.ChebOrthoEvenFTC

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The vanishing rational rate predicate

A rational sequence `B : Nat → Q'` "goes to `0`" if it is nonnegative and, for
every tolerance `ε > 0`, eventually `B N ≤ ε`.  This is the explicit-threshold
form (the threshold `M` is `Type`-free but extracted inside `Prop` proofs). -/

/-- **The vanishing rational rate.**  `B` is nonnegative and, for every `ε > 0`,
there is a threshold `M` past which `B N ≤ ε`.  The error budget of the summed
midpoint estimate is exactly such a sequence (interior `C(e)·√h` + boundary
`h^{3/4}` at `δ = √h`). -/
def RateToZero (B : Nat → Q') : Prop :=
  (∀ n, (0 : Q') ≤ B n) ∧
    (∀ ε : Q', (0 : Q') < ε → ∃ M : Nat, ∀ N : Nat, M ≤ N → B N ≤ ε)

/-- **A concrete vanishing rate.**  The canonical unit fraction `B n = 1/(n+1)`
(`Q'.invSucc n`) is nonnegative and tends to `0` (threshold `M = δ.den` via
`invSucc_den_le` + the antitone `invSucc_le_of_le`).  Non-vacuity of
`RateToZero`. -/
theorem rateToZero_invSucc : RateToZero (fun n => Q'.invSucc n) := by
  refine ⟨fun n => Q'.le_of_lt (Q'.invSucc_pos n), ?_⟩
  intro ε hε
  refine ⟨ε.den, fun N hN => ?_⟩
  -- invSucc N ≤ invSucc ε.den ≤ ε
  exact Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hN) (HalfPow.invSucc_den_le ε hε)

/-! ## 1. The per-resolution two-sided budget (the analytic residual core)

`SumTwoSidedBound e B` says: for every resolution index `N`, the even Riemann sum
`seqOrthEv e N = orthSum e (N+1)` is bounded ABOVE by `B N` and its negation is
also bounded above by `B N` — i.e. `|orthSum e (N+1)| ≤ B N` in the
transitivity-free `leRat` form.  This is exactly the shape the summed
midpoint-quadrature FTC estimate delivers. -/

/-- **The per-resolution two-sided `leRat` budget** `|seqOrthEv e N| ≤ B N`. -/
def SumTwoSidedBound (e : Nat) (B : Nat → Q') : Prop :=
  ∀ N : Nat, CReal.leRat (seqOrthEv e N) (B N) ∧
    CReal.leRat (CReal.neg (seqOrthEv e N)) (B N)

/-! ## 2. The rate ⇒ limit BRIDGE (fully PROVED)

The genuine analytic-packaging atom: a vanishing rational rate two-sidedly
bounding the even Riemann sums forces `ConvergesTo (seqOrthEv e) czero`. -/

/-- Local helper: `czero.approx n = 0`. -/
theorem czero_approx (n : Nat) : ((CReal.czero).approx n) = (0 : Q') := rfl

/-- **The neg-approx identity** `(neg x).approx n = -(x.approx n)`. -/
theorem neg_approx (x : CReal) (n : Nat) : (CReal.neg x).approx n = -(x.approx n) := rfl

/-- **THE BRIDGE.**  If `B` is a vanishing rational rate (`RateToZero B`) and it
two-sidedly bounds the even Riemann sums (`SumTwoSidedBound e B`), then the even
Riemann sums converge to `czero`:

    `ConvergesTo (seqOrthEv e) czero`   (= `OrthEvenZeroLimit e`).

PROOF.  Fix `ε > 0`; let `q = ½ε`.  From `RateToZero` choose the stage `M` with
`B N ≤ q` for `N ≥ M`.  For such an `N`, the two-sided `leRat` budget at
tolerance `q` gives an approximation threshold past which
`(seqOrthEv e N).approx n ≤ B N + q ≤ q + q = ε` and
`−(seqOrthEv e N).approx n ≤ B N + q ≤ ε`.  Since `czero.approx n = 0`, these are
exactly the two `ConvergesTo` inequalities. -/
theorem convergesTo_czero_of_bound (e : Nat) (B : Nat → Q')
    (hB : RateToZero B) (hbnd : SumTwoSidedBound e B) :
    CReal.ConvergesTo (seqOrthEv e) CReal.czero := by
  obtain ⟨_hBnn, hBlim⟩ := hB
  intro ε hε
  -- q = ½ε
  let q : Q' := HalfPow.half * ε
  have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos ε hε
  -- two halves: q + q ≈ ε, hence q + q ≤ ε
  have hqq : (q + q) ≈ ε := ExpNeg.two_halves ε
  have hqq_le : q + q ≤ ε := Q'.le_of_eqv hqq
  -- stage where B N ≤ q
  obtain ⟨M, hM⟩ := hBlim q hqpos
  refine ⟨M, fun N hN => ?_⟩
  have hBNq : B N ≤ q := hM N hN
  -- the two-sided budget at this resolution, instantiated at tolerance q
  obtain ⟨hpos, hneg⟩ := hbnd N
  obtain ⟨Np, hNp⟩ := hpos q hqpos   -- (seqOrthEv e N).approx n ≤ B N + q
  obtain ⟨Nn, hNn⟩ := hneg q hqpos   -- (neg (seqOrthEv e N)).approx n ≤ B N + q
  refine ⟨max Np Nn, fun n hn => ?_⟩
  have hnP : Np ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnN : Nn ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  -- upper: (seqOrthEv e N).approx n ≤ B N + q ≤ q + q ≤ ε = 0 + ε = czero.approx n + ε
  have hBq_le_ε : B N + q ≤ ε :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_right (B N) q q hBNq) hqq_le
  refine ⟨?_, ?_⟩
  · -- (seqOrthEv e N).approx n ≤ czero.approx n + ε
    rw [czero_approx]
    -- czero.approx n + ε = 0 + ε ≈ ε
    have h0ε : (0 : Q') + ε ≈ ε := by rw [Q'.zero_add']; exact Q'.eqv_refl _
    refine Q'.le_trans' _ _ _ (hNp n hnP) ?_
    exact Q'.le_trans' _ _ _ hBq_le_ε (Q'.ge_of_eqv h0ε)
  · -- czero.approx n ≤ (seqOrthEv e N).approx n + ε
    rw [czero_approx]
    -- 0 ≤ (seqOrthEv e N).approx n + ε.  Use (neg …).approx n = -(…) ≤ B N + q ≤ ε.
    have hnegle : -((seqOrthEv e N).approx n) ≤ ε := by
      have := hNn n hnN
      rw [neg_approx] at this
      exact Q'.le_trans' _ _ _ this hBq_le_ε
    -- from -(s) ≤ ε conclude 0 ≤ s + ε
    -- 0 = -(s) + s ≤ ε + s ≈ s + ε
    have hstep : (0 : Q') ≤ ε + (seqOrthEv e N).approx n := by
      have h1 : (-((seqOrthEv e N).approx n)) + (seqOrthEv e N).approx n
          ≤ ε + (seqOrthEv e N).approx n :=
        Q'.add_le_add_right _ _ ((seqOrthEv e N).approx n) hnegle
      have h2 : (-((seqOrthEv e N).approx n)) + (seqOrthEv e N).approx n ≈ (0 : Q') :=
        Q'.neg_add_self_eqv ((seqOrthEv e N).approx n)
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv h2) h1
    -- ε + s ≈ s + ε
    exact Q'.le_trans' _ _ _ hstep
      (Q'.le_of_eqv (Q'.add_comm_eqv ε ((seqOrthEv e N).approx n)))

/-! ## 3. `OrthEvenZeroLimit` from the budget, and the reduced FTC estimate -/

/-- **`OrthEvenZeroLimit e` from a vanishing-rate two-sided budget.**  Direct
specialisation of the bridge: this IS `ConvergesTo (seqOrthEv e) czero`. -/
theorem orthEvenZeroLimit_of_budget (e : Nat) (B : Nat → Q')
    (hB : RateToZero B) (hbnd : SumTwoSidedBound e B) :
    ChebOrthoEvenFTC.OrthEvenZeroLimit e :=
  convergesTo_czero_of_bound e B hB hbnd

/-- **NAMED-open: the existence of a vanishing rational error budget.**  For the
given even order `e`, there is a vanishing rational rate `B` two-sidedly bounding
the even Riemann sums.  This is the SUMMED midpoint-quadrature FTC estimate (the
only ANALYTIC residual): with the antiderivative identity
`ChebUDClosure.Bderiv_identity_uncond` supplying the per-cell increment's leading
term, the telescope (`telescope_sum`) and boundary vanishing
(`GvalDiff_vanishes`) already proved, `B n` is the explicit interior
(`C(e)·√h`) + boundary (`h^{3/4}`) budget at `δ = √h`, assembled from the proved
√-Hölder per-cell bound (`SqrtSubadd.holder_oneMinusSq`) and `|U_e| ≤ e+1`
(`ChebU.absU_le`).  Recorded as the precise residual. -/
def BudgetExists (e : Nat) : Prop :=
  ∃ B : Nat → Q', RateToZero B ∧ SumTwoSidedBound e B

/-- **`OrthEvenZeroLimit e` from the budget existence.**  Unpacks the named
residual `BudgetExists e` through the bridge. -/
theorem orthEvenZeroLimit_of_budgetExists (e : Nat) (h : BudgetExists e) :
    ChebOrthoEvenFTC.OrthEvenZeroLimit e := by
  obtain ⟨B, hB, hbnd⟩ := h
  exact orthEvenZeroLimit_of_budget e B hB hbnd

/-- **`WeightedFTCEstimate` reduced to the budget existence.**  Given the
budget-existence residual for every even `e ≥ 2`, the constructive √-weighted FTC
estimate holds: the even Riemann sums converge to `0`.  The pure-algebra
hypotheses `UDClosure`/`TdiffClosure` of `WeightedFTCEstimate` are NOT needed for
this reduction (they are already discharged unconditionally in `ChebUDClosure`,
feeding the antiderivative identity that underlies the budget). -/
theorem weightedFTCEstimate_of_budget
    (hbud : ∀ (e : Nat), 2 ≤ e → e % 2 = 0 → BudgetExists e) :
    ChebOrthoWeightedFTC.WeightedFTCEstimate := by
  intro _hUD _hTd e he2 heven
  exact orthEvenZeroLimit_of_budgetExists e (hbud e he2 heven)

/-! ## 4. The conditional full off-diagonal closure -/

/-- **Off-diagonal orthogonality `∫U_e√ = 0` for `e ≥ 1`, conditional on the
budget existence.**  Feeds the even-order limit (from the budget, via the bridge)
into the companion `offdiag_zero_of_zeroLimit`; the ODD case is already
UNCONDITIONAL.  π-free. -/
theorem offdiag_closed_of_budget
    (hbud : ∀ (e : Nat), 2 ≤ e → e % 2 = 0 → BudgetExists e) :
    ∀ (e : Nat), 1 ≤ e →
      ∃ L : CReal, CReal.ConvergesTo (seqOrth e) L ∧ CReal.Equiv L CReal.czero := by
  intro e he1
  refine ChebOrthoEvenFTC.offdiag_zero_of_zeroLimit e he1 (fun heven => ?_)
  have he2 : 2 ≤ e := by omega
  exact orthEvenZeroLimit_of_budgetExists e (hbud e he2 heven)

end YMGap.Continuum.ChebOrthoFTCEstimate

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `RateToZero` / `rateToZero_invSucc` — the vanishing rational rate predicate
    and a CONCRETE non-vacuous instance (`1/(n+1)`), discharging the threshold
    via `invSucc_den_le` + `invSucc_le_of_le`.
  * `SumTwoSidedBound` — the per-resolution two-sided `leRat` budget
    `|seqOrthEv e N| ≤ B N`, the exact shape the summed FTC estimate delivers.
  * **`convergesTo_czero_of_bound`** — THE RATE ⇒ LIMIT BRIDGE: a vanishing
    rational rate two-sidedly bounding the even Riemann sums forces
    `ConvergesTo (seqOrthEv e) czero` (= `OrthEvenZeroLimit e`).  Fully proved,
    the reusable analytic-packaging atom of the FTC estimate.
  * `orthEvenZeroLimit_of_budget` / `orthEvenZeroLimit_of_budgetExists` —
    `OrthEvenZeroLimit e` from a (resp. existentially-quantified) budget.
  * `weightedFTCEstimate_of_budget` — `ChebOrthoWeightedFTC.WeightedFTCEstimate`
    reduced to the budget existence for every even `e ≥ 2`.
  * `offdiag_closed_of_budget` — the COMBINED off-diagonal orthogonality
    `∫U_e√ = 0` for `e ≥ 1` from the budget existence (ODD case UNCONDITIONAL).

**NAMED-open (the honest residual — ONE analytic estimate).**
  * `BudgetExists e := ∃ B, RateToZero B ∧ SumTwoSidedBound e B` — the existence
    of a vanishing rational error budget two-sidedly bounding the even Riemann
    sums.  This is the SUMMED midpoint-quadrature error estimate: with the
    antiderivative identity `ChebUDClosure.Bderiv_identity_uncond`
    (`(1−x²)B_e′ − xB_e ≈ −2(1−x²)U_e`, the per-cell leading term) PROVED, the
    telescope `ChebOrthoEvenFTC.telescope_sum` and the boundary value
    `ChebOrthoEvenFTC.GvalDiff_vanishes` PROVED, the remaining work is the
    interior (`C(e)·h/δ`) + boundary (`δ^{3/2}`) summed budget at `δ = √h`,
    assembled from the proved √-Hölder per-cell bound
    (`SqrtSubadd.holder_oneMinusSq`/`sqrtFrom_sub_leRat`) and `|U_e| ≤ e+1`
    (`ChebU.absU_le`).  Recorded as the precise residual, not faked.

**Path to the diagonal + full orthogonality.**  Once `BudgetExists e` holds for
every even `e ≥ 2`, `convergesTo_czero_of_bound` closes `OrthEvenZeroLimit e`,
hence (with the unconditional odd case) the full π-free off-diagonal
orthogonality `∫U_e√ = 0` for all `e ≥ 1`.  Combined with the diagonal
`∫U_c²√ = semiInt` (same Riemann functional with the nonnegative bounded factor
`U_c²`, via the second-kind fusion `U_c² = 1 + Σ_{j≥1} U_{2j}` and the proved
even off-diagonal vanishing), the Gram matrix `[∫U_cU_d√]_{cd} = semiInt·I` is
PSD — π-FREE (`semiInt` an ABSTRACT positive constant).

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` not used. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoFTCEstimate.rateToZero_invSucc
#print axioms YMGap.Continuum.ChebOrthoFTCEstimate.convergesTo_czero_of_bound
#print axioms YMGap.Continuum.ChebOrthoFTCEstimate.orthEvenZeroLimit_of_budget
#print axioms YMGap.Continuum.ChebOrthoFTCEstimate.orthEvenZeroLimit_of_budgetExists
#print axioms YMGap.Continuum.ChebOrthoFTCEstimate.weightedFTCEstimate_of_budget
#print axioms YMGap.Continuum.ChebOrthoFTCEstimate.offdiag_closed_of_budget
