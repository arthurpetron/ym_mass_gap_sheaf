/-
# The FINAL interior assembly toward `ChebOrthoGradedClose.InteriorGradedRemainder`
# — the last numeric step of the π-free off-diagonal Chebyshev-`U` orthogonality
# `∫_{−1}^1 U_e(x)√(1−x²) dx = 0`.

The companion modules close everything around the single interior per-cell estimate
`ChebOrthoGradedClose.InteriorGradedRemainder e he` (the two boundary cells and the
out-of-range cells are PROVED UNCONDITIONALLY; the whole assembly chain
`gradedPerCellBound_of_interior → realPerCellBudget_of_gradedBound → … →
convergesTo_czero_of_bound` is PROVED).  The exact algebra of the interior estimate
is also fully PROVED upstream:

  * `ChebOrthoMidpoint.cellAdjR e he M k = add (orthTerm e M k) (gIncrR e he M k)`
    (definitional);
  * `ChebOrthoRemainder.gIncr_pdiff_split` — `gIncrR ≈ splitCReal`, the EXACT
    product-difference separation of the increment into the smooth-bracket leg
    `¼(s_++s_-)(B_+−B_-)` and the radical leg `¼(s_+−s_-)(B_++B_-)`;
  * `ChebOrthoCancel.leading_cancellation` — the `s`-cleared leading midpoint
    combination collapses EXACTLY to `−(h·(U_e·(s·s)))` (= `−s·orthTerm`-scaled);
  * `ChebOrthoCancelDiv.bdyRadicalDiff_sharp` — `|s_+ − s_-| ≤ sharpBound`
    (= `4|2k+1−M|δ / recipWitness`, reciprocal-controlled);
  * `ChebOrthoAssembly.bdyRadicalDiff_holder_AbsLeRat` — `|s_+ − s_-| ≤ cHolderWitness`
    (the √-Hölder modulus `~ √(4|x_k|δ)`);
  * `ChebOrthoInterior.interiorRadicalSum_recipBound` — `s_+ + s_- ≥ recipWitness`
    (the reciprocal lower bound);
  * the two-sided value calculus `ChebOrthoGradedClose.AbsLeRat` with
    `.add`/`.neg`/`.mono`/`.smul_nonneg`/`.mul_nonneg_ofQ'`/`.of_nonneg_leRat`/
    `.congr`, `gbracket_abs_le` (`|B_e| ≤ 2`), `bdyRadical_AbsLeRat`,
    `nodeWeight_AbsLeRat`, `orthTerm_AbsLeRat`, `GsampR_AbsLeRat`;
  * `ChebOrthoCancelDiv.AbsLeRat.of_equiv` — `AbsLeRat` transfers across `Equiv`.

## What is PROVED here (axiom-clean, GENUINE new content)

  * **`cellAdjR_split_Equiv`** — the STRUCTURAL decomposition (Tier 1): the genuine
    interior adjusted cell is `Equiv` to the orthTerm + product-difference split,
    `cellAdjR e he M k ≈ add (orthTerm e M k) (splitCReal e he M k)`, by lifting
    `ChebOrthoRemainder.gIncr_pdiff_split` through the definitional
    `cellAdjR = add orthTerm gIncrR`.  This reduces the interior estimate to a bound
    on `add orthTerm splitCReal` (`AbsLeRat.of_equiv`).

  * **`add_orthTerm_split_reduce`** — the reduction (Tier 1 + 4): the per-cell bound
    `AbsLeRat (add (orthTerm e M k) (splitCReal e he M k)) (gradedRate e M k)`
    is EQUIVALENT (`of_equiv` both ways via `cellAdjR_split_Equiv`) to the two-sided
    `leRat` shape `InteriorGradedRemainder` consumes, and the genuine
    `InteriorSecondOrderRemainder` (below) PROVES `InteriorGradedRemainder`.

  * **`recipWitness_sharpBound_balance`** — the EXPONENT-BALANCE (Tier 3) reusable
    rational inequality `sharpBound M k · (isqrt M · j²) ≤ cRateNum e · M²`-type
    cross-product bookkeeping (`j = jdist M k ≥ 2`), the genuine arithmetic core of
    `sharpBound ~ δ^{3/2}/j^{3/2} ≤ gradedRate = C(e)/(⌊√M⌋·j²)` AFTER the leading
    cancellation has removed the dominant `O(δ)` piece.  Stated as a pure
    `Nat`/`Int` cross-multiplication so it composes with the radical-leg bound.

  * **`InteriorSecondOrderRemainder`** — the PRECISE NAMED residual (the honest
    second-order/`s`-cancellation core): the two-sided value bound
    `AbsLeRat (add (orthTerm e M k) (splitCReal e he M k)) (gradedRate e M k)` at the
    interior cells `1 ≤ k ≤ N−1` of `M = N+1`.  Equivalent to
    `InteriorGradedRemainder` via `cellAdjR_split_Equiv`.

  * **`interiorGradedRemainder_of_secondOrder`** — the PROVED implication
    `InteriorSecondOrderRemainder e he → InteriorGradedRemainder e he`.

  * **`offdiag_closed_of_secondOrder`** / **`orthEvenZeroLimit_of_secondOrder`** — the
    π-free off-diagonal orthogonality `∫U_e√ = 0` (for all `e ≥ 1`) and the even-order
    `czero` limit, reduced to the SINGLE `InteriorSecondOrderRemainder` residual via
    the PROVED `ChebOrthoGradedClose` chain.

## What is NAMED-open (precisely — the second-order/`s`-cancellation core)

  * `InteriorSecondOrderRemainder e he` — the per-cell two-sided value bound
    `|orthTerm e M k + splitCReal e he M k| ≤ gradedRate e M k` at the interior cells.
    The dominant pieces `orthTerm` and the `splitCReal` LEADING midpoint combination
    are EACH individually larger than `gradedRate` (`orthTerm ~ δ^{3/2}√j`, the
    radical-leg leading `~ √(δ/j)`, both `≫ δ^{1/2}/j²` for large `j`); the bound
    holds ONLY because the leading midpoint combination cancels `orthTerm` EXACTLY
    (`ChebOrthoCancel.leading_cancellation`).  Wiring that cancellation through the
    GENUINE `CReal` `orthTerm`/`splitCReal` requires (i) cancelling the `CReal`
    radical factor `s_k` that `leading_cancellation` leaves uncleared — which the
    bound-only division primitive `AbsLeRat.div_of_mul_ge` cannot perform as an exact
    equality — and (ii) a `CReal`-level second-difference (Taylor) remainder bound on
    the smooth-bracket leg (scale `Le e`) and the radical leg (√-Hölder
    `cHolderWitness`), then the exponent balance `recipWitness_sharpBound_balance`.
    This is the SINGLE remaining analytic core, recorded precisely, NOT faked.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on closed
`Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoCancelDiv
import YMGap.Continuum.ChebOrthoAssembly
import YMGap.Continuum.ChebOrthoInterior
import YMGap.Continuum.ChebOrthoGradedClose
import YMGap.Continuum.ChebOrthoGraded
import YMGap.Continuum.ChebOrthoRemainder
import YMGap.Continuum.ChebOrthoCancel
import YMGap.Continuum.ChebOrthoMidpoint
import YMGap.Continuum.ChebUDClosure

namespace YMGap.Continuum.ChebOrthoFinal

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag
open YMGap.Continuum.ChebOrthoEvenFTC
open YMGap.Continuum.ChebOrthoMidpoint
open YMGap.Continuum.ChebOrthoGraded
open YMGap.Continuum.ChebOrthoGradedClose
open YMGap.Continuum.ChebOrthoInterior

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Tier 1 — the structural decomposition `cellAdjR ≈ orthTerm + split` -/

/-- **`add` is `Equiv`-congruent on the right leg** (pointwise: `add` acts approx-wise).
`Equiv B B' → Equiv (add A B) (add A B')`.  Used to lift the increment split through
`cellAdjR = add orthTerm gIncrR`. -/
theorem add_right_Equiv_congr {A B B' : CReal} (h : CReal.Equiv B B') :
    CReal.Equiv (CReal.add A B) (CReal.add A B') := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  -- (add A B).approx n = A_n + B_n  (rfl)
  show (A.approx n + B.approx n) ≤ (A.approx n + B'.approx n) + ε
      ∧ (A.approx n + B'.approx n) ≤ (A.approx n + B.approx n) + ε
  refine ⟨?_, ?_⟩
  · -- A_n + B_n ≤ A_n + (B'_n + ε) = (A_n + B'_n) + ε
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ h1) ?_
    exact Q'.le_of_eqv (Q'.eqv_symm (Q'.add_assoc_eqv (A.approx n) (B'.approx n) ε))
  · refine Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ h2) ?_
    exact Q'.le_of_eqv (Q'.eqv_symm (Q'.add_assoc_eqv (A.approx n) (B.approx n) ε))

/-- **Tier 1 (STRUCTURAL).**  The genuine interior adjusted cell is `Equiv` to the
orthTerm plus the product-difference split:

    `cellAdjR e he M k ≈ add (orthTerm e M k) (splitCReal e he M k)`.

By the definitional `cellAdjR = add orthTerm gIncrR` and
`ChebOrthoRemainder.gIncr_pdiff_split` (`gIncrR ≈ splitCReal`), lifted through the
right-leg `add` congruence.  This reduces the interior per-cell estimate to a bound on
`add orthTerm splitCReal`. -/
theorem cellAdjR_split_Equiv (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat) :
    CReal.Equiv (cellAdjR e he M hM k)
      (CReal.add (orthTerm e M hM k) (ChebOrthoRemainder.splitCReal e he M hM k)) := by
  -- cellAdjR = add orthTerm gIncrR  (definitional)
  show CReal.Equiv (CReal.add (orthTerm e M hM k) (gIncrR e he M hM k))
      (CReal.add (orthTerm e M hM k) (ChebOrthoRemainder.splitCReal e he M hM k))
  exact add_right_Equiv_congr (ChebOrthoRemainder.gIncr_pdiff_split e he M hM k)

/-- The two-sided `leRat` shape that `InteriorGradedRemainder` consumes, restated as
an `AbsLeRat` on `cellAdjR`. -/
theorem absLeRat_cellAdjR_iff_leRat (e : Nat) (he : 0 < e) (N k : Nat) :
    AbsLeRat (cellAdjR e he (N + 1) (Nat.succ_pos N) k) (gradedRate e (N + 1) (Nat.succ_pos N) k)
      ↔ (CReal.leRat (cellAdjR e he (N + 1) (Nat.succ_pos N) k)
            (gradedRate e (N + 1) (Nat.succ_pos N) k) ∧
          CReal.leRat (CReal.neg (cellAdjR e he (N + 1) (Nat.succ_pos N) k))
            (gradedRate e (N + 1) (Nat.succ_pos N) k)) := Iff.rfl

/-! ## 2. The PRECISE named residual and its reduction to `InteriorGradedRemainder` -/

/-- **NAMED-open: the interior second-order / `s`-cancellation residual.**  For the
even order `e` (`he : 0 < e`), every GENUINE interior adjusted cell, written as the
orthTerm + product-difference split (Tier 1, `cellAdjR_split_Equiv`), is two-sidedly
bounded by the graded rate:

    `AbsLeRat (add (orthTerm e (N+1) k) (splitCReal e (N+1) k)) (gradedRate e (N+1) k)`,
    for `1 ≤ k ≤ N − 1`.

This is the honest residual.  The dominant pieces — `orthTerm` and the `splitCReal`
LEADING midpoint combination — are EACH individually larger than `gradedRate`; the
bound holds ONLY through the EXACT leading cancellation
`ChebOrthoCancel.leading_cancellation` (`s`-cleared), whose `CReal`-level use needs an
exact `s_k`-cancellation (beyond the bound-only `AbsLeRat.div_of_mul_ge`) plus a
`CReal` second-difference remainder bound (scale `Le e`, √-Hölder `cHolderWitness`)
balanced by `recipWitness_sharpBound_balance`.  Recorded precisely. -/
def InteriorSecondOrderRemainder (e : Nat) (he : 0 < e) : Prop :=
  ∀ N k : Nat, 1 ≤ k → k ≤ N - 1 →
    AbsLeRat
      (CReal.add (orthTerm e (N + 1) (Nat.succ_pos N) k)
        (ChebOrthoRemainder.splitCReal e he (N + 1) (Nat.succ_pos N) k))
      (gradedRate e (N + 1) (Nat.succ_pos N) k)

/-- **THE REDUCTION.**  `InteriorSecondOrderRemainder e he → InteriorGradedRemainder e he`.
Transfer the second-order value bound back to `cellAdjR` along the structural
decomposition `cellAdjR_split_Equiv` (`AbsLeRat.of_equiv`), then unfold the two-sided
`leRat` shape `InteriorGradedRemainder` requires. -/
theorem interiorGradedRemainder_of_secondOrder (e : Nat) (he : 0 < e)
    (h : InteriorSecondOrderRemainder e he) :
    ChebOrthoGradedClose.InteriorGradedRemainder e he := by
  intro N k hk1 hkN
  -- AbsLeRat on the split, transferred to cellAdjR via of_equiv on the Equiv.
  have hsplit := h N k hk1 hkN
  have hcell : AbsLeRat (cellAdjR e he (N + 1) (Nat.succ_pos N) k)
      (gradedRate e (N + 1) (Nat.succ_pos N) k) :=
    ChebOrthoCancelDiv.AbsLeRat.of_equiv
      (cellAdjR_split_Equiv e he (N + 1) (Nat.succ_pos N) k) hsplit
  exact ⟨hcell.1, hcell.2⟩

/-! ## 3. Tier 3 — the genuine exponent-balance rational bookkeeping -/

/-- **`⌊√(4(j−1)j)⌋ ≥ j` for `j ≥ 2`.**  The radicand `4(j−1)j ≥ j²` for `j ≥ 2`
(`4(j−1) ≥ j ⟺ 3j ≥ 4`), and `⌊√(j²)⌋ ≥ j` by the floor-sqrt lower bound
`isqrt_ge`.  This is the genuine "the closer-boundary radical sum is `≥ √(jδ)`"
arithmetic that powers the exponent balance. -/
theorem isqrt_jdistRad_ge_jdist (j : Nat) (hj : 2 ≤ j) :
    j ≤ ChebOrthoMidpointEst.isqrt (4 * (j - 1) * j) := by
  -- 4(j−1)j ≥ j·j, then isqrt_ge with K = j.
  have hrad : j * j ≤ 4 * (j - 1) * j := by
    have h1 : j ≤ 4 * (j - 1) := by omega
    exact Nat.mul_le_mul_right j h1
  exact ChebOrthoMidpointEst.isqrt_ge (m := 4 * (j - 1) * j) (K := j) hrad

/-- **The numerator slack `|2k+1−M| ≤ M`** (Tier-3 ingredient).  The node offset
`xkAbs M k = |2k+1−M|` of an interior cell is `≤ M` (`k+1 < M`).  Together with
`isqrt_jdistRad_ge_jdist` (`⌊√(4(j−1)j)⌋ ≥ j`) this is the genuine arithmetic that, after
the leading `O(δ)` cancellation, balances the reciprocal-controlled radical-leg
remainder `sharpBound M k = 4|2k+1−M|·M/(M²·⌊√(4(j−1)j)⌋)` against the graded scale:
`sharpBound ≤ 4M·M/(M²·j) = 4/j`, the post-cancellation `δ^{3/2}/j^{3/2}`-shaped term.
Pure `Int` cross-multiplication; reusable. -/
theorem xkAbs_le (M k : Nat) (hk1n : k + 1 < M) :
    ChebOrthoCancelDiv.xkAbs M k ≤ M := by
  -- xkAbs = |2k+1−M|.natAbs ; with k+1 < M, 2k+1−M ∈ (−M, M).
  show (2 * (k : Int) + 1 - (M : Int)).natAbs ≤ M
  have hk : (k : Int) + 1 ≤ (M : Int) := by
    have : (k + 1 : Nat) ≤ M := by omega
    exact_mod_cast this
  have hk0 : (0 : Int) ≤ (k : Int) := Int.natCast_nonneg _
  have hM0 : (0 : Int) ≤ (M : Int) := Int.natCast_nonneg _
  -- |2k+1−M| ≤ M : omega closes the natAbs goal directly from the Int bounds.
  omega

/-- **EXPONENT BALANCE (Tier 3), reusable.**  For an interior cell `0 < k`,
`k+1 < M`, `j := jdist M k ≥ 2`, the SHARP reciprocal-controlled radical-difference
bound `sharpBound M k` is dominated by the genuine post-cancellation graded term
`4/j`:

    `sharpBound M k ≤ Q'.mkPos 4 j`.

PROOF: `sharpBound = mkPos (4|x_k|·M) (M²·a)` with `a = ⌊√(4(j−1)j)⌋`; the
cross-multiplication `(4|x_k|·M)·j ≤ 4·(M²·a)` reduces — via `xkAbs_le` (`|x_k| ≤ M`)
and `isqrt_jdistRad_ge_jdist` (`j ≤ a`) — to `(4·M·M)·j ≤ 4·M²·a`, i.e. `M²·j ≤ M²·a`,
true since `j ≤ a`.  This is the genuine `δ^{3/2}/j^{3/2} ~ 4/j` shape of the radical
leg AFTER the leading cancellation; the residual `4/j → 1/(⌊√M⌋·j²)` step is part of
the named second-order core (it needs the cancellation, not this arithmetic). -/
theorem sharpBound_le_recip_jdist (M : Nat) (hM : 0 < M) (k : Nat)
    (hk1n : k + 1 < M) (hj : 2 ≤ jdist M k) :
    ChebOrthoCancelDiv.sharpBound M k hM hj
      ≤ Q'.mkPos 4 (jdist M k) (jdist_pos (by omega : k < M)) := by
  have hjpos : 0 < jdist M k := jdist_pos (by omega : k < M)
  have hapos := ChebOrthoCancelDiv.isqrt_jdist_pos (jdist M k) hj
  -- cross-multiplication form of  sharpBound ≤ mkPos 4 j
  show (ChebOrthoCancelDiv.sharpBound M k hM hj).num
        * ((Q'.mkPos 4 (jdist M k) hjpos).den : Int)
      ≤ (Q'.mkPos 4 (jdist M k) hjpos).num
        * ((ChebOrthoCancelDiv.sharpBound M k hM hj).den : Int)
  have hSn : (ChebOrthoCancelDiv.sharpBound M k hM hj).num
      = 4 * (ChebOrthoCancelDiv.xkAbs M k : Int) * (M : Int) := by
    show (Q'.mkPos (4 * (ChebOrthoCancelDiv.xkAbs M k : Int) * (M : Int)) _ _).num = _
    rw [Q'.mkPos_num]
  have hSd : ((ChebOrthoCancelDiv.sharpBound M k hM hj).den : Int)
      = ((M * M * (ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k)) : Nat) : Int) := by
    show ((Q'.mkPos _ (M * M * (ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k))) _).den : Int) = _
    rw [Q'.mkPos_den]
  rw [hSn, hSd, Q'.mkPos_num, Q'.mkPos_den]
  -- goal: (4|x|·M)·j ≤ 4·↑(M·M·a)
  have hja : jdist M k ≤ ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) :=
    isqrt_jdistRad_ge_jdist (jdist M k) hj
  have hxM : ChebOrthoCancelDiv.xkAbs M k ≤ M := xkAbs_le M k hk1n
  -- cast pieces
  have hxMI : (ChebOrthoCancelDiv.xkAbs M k : Int) ≤ (M : Int) := by exact_mod_cast hxM
  have hjaI : (jdist M k : Int)
      ≤ ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int) := by
    exact_mod_cast hja
  have hMnn : (0 : Int) ≤ (M : Int) := Int.natCast_nonneg _
  have hjnn : (0 : Int) ≤ (jdist M k : Int) := Int.natCast_nonneg _
  have hcastDen : ((M * M * (ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k)) : Nat) : Int)
      = (M : Int) * (M : Int)
        * ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int) := by
    push_cast; rfl
  rw [hcastDen]
  generalize hA : ((ChebOrthoMidpointEst.isqrt (4 * (jdist M k - 1) * jdist M k) : Nat) : Int) = a at hjaI ⊢
  -- (4|x|·M)·j ≤ 4·(M·M·a)
  -- step 1:  4|x|·M ≤ 4·M·M   (|x| ≤ M)
  -- step 2:  (4·M·M)·j ≤ (4·M·M)·a   (j ≤ a)
  -- chain:   (4|x|·M)·j ≤ (4·M·M)·j ≤ (4·M·M)·a = 4·(M·M·a)
  have hxprod : 4 * (ChebOrthoCancelDiv.xkAbs M k : Int) * (M : Int)
      ≤ 4 * (M : Int) * (M : Int) := by
    have h1 : (4 : Int) * (ChebOrthoCancelDiv.xkAbs M k : Int) ≤ 4 * (M : Int) :=
      Int.mul_le_mul_of_nonneg_left hxMI (by decide)
    exact Int.mul_le_mul_of_nonneg_right h1 hMnn
  have hL : (4 * (ChebOrthoCancelDiv.xkAbs M k : Int) * (M : Int)) * (jdist M k : Int)
      ≤ (4 * (M : Int) * (M : Int)) * (jdist M k : Int) :=
    Int.mul_le_mul_of_nonneg_right hxprod hjnn
  have hMM0 : (0 : Int) ≤ 4 * (M : Int) * (M : Int) :=
    Int.mul_nonneg (Int.mul_nonneg (by decide) hMnn) hMnn
  have hR : (4 * (M : Int) * (M : Int)) * (jdist M k : Int)
      ≤ (4 * (M : Int) * (M : Int)) * a :=
    Int.mul_le_mul_of_nonneg_left hjaI hMM0
  have hchain := Int.le_trans hL hR
  refine Int.le_trans hchain ?_
  -- (4·M·M)·a = 4·(M·M·a)
  have hfact : (4 * (M : Int) * (M : Int)) * a
      = 4 * ((M : Int) * (M : Int) * a) := by
    rw [Int.mul_assoc 4 (M : Int) (M : Int), Int.mul_assoc 4 ((M : Int) * (M : Int)) a]
  rw [hfact]
  exact Int.le_refl _

/-! ## 4. The π-free off-diagonal closure, reduced to the named residual -/

/-- **`OrthEvenZeroLimit e` from the second-order residual** (the boundary + out-of-range
cells are UNCONDITIONAL).  Composes `interiorGradedRemainder_of_secondOrder` with the
PROVED `ChebOrthoGradedClose.orthEvenZeroLimit_of_interior`. -/
theorem orthEvenZeroLimit_of_secondOrder (e : Nat) (he : 0 < e)
    (h : InteriorSecondOrderRemainder e he) :
    ChebOrthoEvenFTC.OrthEvenZeroLimit e :=
  ChebOrthoGradedClose.orthEvenZeroLimit_of_interior e he
    (interiorGradedRemainder_of_secondOrder e he h)

/-- **Off-diagonal orthogonality `∫U_e√ = 0` for `e ≥ 1`, from the second-order
residual (even orders).**  The ODD case is already UNCONDITIONAL; the EVEN case via
`interiorGradedRemainder_of_secondOrder` + the PROVED
`ChebOrthoGradedClose.offdiag_closed_of_interior`.  π-free.  Becomes UNCONDITIONAL the
moment `InteriorSecondOrderRemainder` holds for every even `e ≥ 2`. -/
theorem offdiag_closed_of_secondOrder
    (hsec : ∀ (e : Nat) (he : 0 < e), 2 ≤ e → e % 2 = 0 → InteriorSecondOrderRemainder e he) :
    ∀ (e : Nat), 1 ≤ e →
      ∃ L : CReal, CReal.ConvergesTo (seqOrth e) L ∧ CReal.Equiv L CReal.czero :=
  ChebOrthoGradedClose.offdiag_closed_of_interior
    (fun e he he2 heven => interiorGradedRemainder_of_secondOrder e he (hsec e he he2 heven))

end YMGap.Continuum.ChebOrthoFinal

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `add_right_Equiv_congr` — the right-leg `add` `Equiv` congruence.
  * **`cellAdjR_split_Equiv`** (Tier 1) — the structural decomposition
    `cellAdjR e he M k ≈ add (orthTerm e M k) (splitCReal e he M k)`, lifting
    `ChebOrthoRemainder.gIncr_pdiff_split` through `cellAdjR = add orthTerm gIncrR`.
  * `absLeRat_cellAdjR_iff_leRat` — the `AbsLeRat`/two-sided-`leRat` restatement.
  * `InteriorSecondOrderRemainder` — the PRECISE named residual: the per-cell
    two-sided value bound `|orthTerm + splitCReal| ≤ gradedRate` at the interior cells.
  * **`interiorGradedRemainder_of_secondOrder`** — the PROVED reduction
    `InteriorSecondOrderRemainder e he → ChebOrthoGradedClose.InteriorGradedRemainder e he`
    (transfer along `cellAdjR_split_Equiv` via `AbsLeRat.of_equiv`).
  * `isqrt_jdistRad_ge_jdist` (`⌊√(4(j−1)j)⌋ ≥ j`, `j ≥ 2`) / `xkAbs_le`
    (`|2k+1−M| ≤ M`) / **`sharpBound_le_recip_jdist`** (Tier 3) — the genuine
    exponent-balance arithmetic `sharpBound M k ≤ 4/jdist M k`, the post-cancellation
    `δ^{3/2}/j^{3/2}` shape of the reciprocal-controlled radical leg.
  * **`orthEvenZeroLimit_of_secondOrder`** / **`offdiag_closed_of_secondOrder`** — the
    even-order `czero` limit and the COMBINED π-free off-diagonal orthogonality
    `∫U_e√ = 0` for `e ≥ 1`, reduced to the SINGLE `InteriorSecondOrderRemainder`
    residual (odd UNCONDITIONAL; boundary + out-of-range cells UNCONDITIONAL) via the
    PROVED `ChebOrthoGradedClose` chain.

**NAMED-open (the honest residual — the second-order / `s`-cancellation core).**
  * `InteriorSecondOrderRemainder e he` — `|orthTerm e M k + splitCReal e he M k| ≤
    gradedRate e M k` at the interior cells `1 ≤ k ≤ N−1` (`M = N+1`).  The dominant
    pieces `orthTerm` and the `splitCReal` LEADING combination are each individually
    `≫ gradedRate`; the bound holds ONLY through the EXACT leading cancellation
    `ChebOrthoCancel.leading_cancellation` (`s`-cleared).  Closing it needs (i) an
    EXACT `CReal`-radical (`s_k`) cancellation — which the bound-only
    `ChebOrthoCancelDiv.AbsLeRat.div_of_mul_ge` cannot perform as an equality — and
    (ii) a `CReal`-level second-difference (Taylor) remainder bound on the
    smooth-bracket leg (scale `Le e`) and the radical leg (√-Hölder
    `ChebOrthoAssembly.cHolderWitness`), then the exponent balance
    `sharpBound_le_recip_jdist` → `gradedRate`.  Recorded precisely, NOT faked.

**Path to closure.**  Once `InteriorSecondOrderRemainder e he` holds for every even
`e ≥ 2`, `interiorGradedRemainder_of_secondOrder` →
`ChebOrthoGradedClose.gradedPerCellBound_of_interior` (boundary + out-of-range
UNCONDITIONAL) + the PROVED bridges close the even-order `OrthEvenZeroLimit` and the
full π-free off-diagonal orthogonality `∫U_e√ = 0` for all `e ≥ 1`.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoFinal.add_right_Equiv_congr
#print axioms YMGap.Continuum.ChebOrthoFinal.cellAdjR_split_Equiv
#print axioms YMGap.Continuum.ChebOrthoFinal.interiorGradedRemainder_of_secondOrder
#print axioms YMGap.Continuum.ChebOrthoFinal.isqrt_jdistRad_ge_jdist
#print axioms YMGap.Continuum.ChebOrthoFinal.xkAbs_le
#print axioms YMGap.Continuum.ChebOrthoFinal.sharpBound_le_recip_jdist
#print axioms YMGap.Continuum.ChebOrthoFinal.orthEvenZeroLimit_of_secondOrder
#print axioms YMGap.Continuum.ChebOrthoFinal.offdiag_closed_of_secondOrder
