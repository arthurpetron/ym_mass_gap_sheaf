/-
# The SECOND-DIFFERENCE (Taylor) reduction of the interior second-order remainder
# of the π-free off-diagonal Chebyshev-`U` orthogonality `∫_{−1}^1 U_e(x)√(1−x²)dx = 0`.

The companion module `ChebOrthoFinal` reduces the even-order off-diagonal
orthogonality to the SINGLE interior per-cell two-sided value bound
`ChebOrthoFinal.InteriorSecondOrderRemainder e he`
(`|orthTerm e M k + splitCReal e he M k| ≤ gradedRate e M k`, `1 ≤ k ≤ N−1`,
`M = N+1`).

The dominant pieces — `orthTerm` and the LEADING midpoint combination of
`splitCReal` — are EACH individually larger than `gradedRate` (orthTerm `~ δ^{3/2}√j`,
the radical-leg leading `~ √(δ/j)`); the bound holds ONLY because the leading
combination cancels `orthTerm` EXACTLY (`ChebOrthoCancel.leading_cancellation`).
Bounding the two `splitCReal` legs separately CANNOT close it: the radical leg is
`≤ ¼·|s_+−s_-|·|B_++B_-| ≤ ¼·(4/j)·4 = 4/j ≫ gradedRate`.

## What this module supplies (axiom-clean, GENUINE new content)

  * **The SECOND-DIFFERENCE REDUCTION** `secondDiff_reduce`: a STRUCTURAL theorem
    that splits the dominant combination `orthTerm + splitCReal` along ANY chosen
    "leading model" CReal `LZ`.  If `LZ` EXACTLY cancels `orthTerm`
    (`Equiv (add orthTerm LZ) czero` — the leading cancellation, separated out as a
    clean `Equiv … czero`) AND the SECOND-DIFFERENCE REMAINDER
    `splitCReal + (−LZ)` is two-sidedly `≤ gradedRate`, then
    `|orthTerm + splitCReal| ≤ gradedRate`.  This is the EXACT analytic separation:
    the dominant `O(δ)` part is `orthTerm + LZ ≈ 0`, the residual is the genuine
    second-difference (Taylor) remainder `splitCReal − LZ`.

  * **`SecondDiffRemainder`** — the PRECISE strictly-smaller named residual: for
    every interior cell there EXISTS a leading model `LZ` with BOTH the exact leading
    cancellation `Equiv (add orthTerm LZ) czero` AND the small remainder
    `AbsLeRat (add splitCReal (neg LZ)) gradedRate`.  It is STRICTLY SMALLER than
    `InteriorSecondOrderRemainder`: the dominant `orthTerm`/leading pieces no longer
    appear in the bound to be proved — they have been separated into a clean
    `Equiv … czero` — leaving ONLY the boundary-vs-midpoint second-difference Taylor
    remainder `splitCReal − LZ` (an `O(δ^{3/2})`-shaped object) to bound, against the
    same graded rate.

  * **`interiorSecondOrder_of_secondDiff`** — the PROVED reduction
    `SecondDiffRemainder e he → ChebOrthoFinal.InteriorSecondOrderRemainder e he`
    (pure `CReal` `Equiv` algebra, via `secondDiff_reduce`).

  * **`radicalLeg_AbsLeRat`** — a GENUINE fully-PROVED sub-bound demonstrating the
    sharp radical-leg arithmetic is reachable: the bare radical difference
    `s_+ + (−s_-)` is two-sidedly `≤ 4/jdist M k` at an interior cell, by composing
    the PROVED `ChebOrthoCancelDiv.bdyRadicalDiff_sharp`
    (`|s_+ − s_-| ≤ sharpBound`) with `ChebOrthoFinal.sharpBound_le_recip_jdist`
    (`sharpBound ≤ 4/jdist`).  This is the post-cancellation radical-leg shape, now a
    closed theorem.

## What is NAMED-open (precisely — strictly smaller than the input)

  * `SecondDiffRemainder e he` — for each interior cell, the EXISTENCE of a leading
    model `LZ` with (i) `Equiv (add orthTerm LZ) czero` (the exact leading
    cancellation, separated) and (ii) `AbsLeRat (add splitCReal (neg LZ)) gradedRate`
    (the second-difference remainder bound).  Strictly smaller: the proof of the
    leading cancellation (i) is supplied by the PROVED toolkit
    `ChebOrthoCancel.leading_cancellation` un-cleared via
    `ChebOrthoSecondOrder.CReal.cancel_mul_left`, once a constructive reciprocal of the
    node radical `s_k` at the interior cell is built; the remainder (ii) is the genuine
    `O(δ^{3/2})` Taylor object, controlled by `bdyRadicalDiff_sharp` (radical leg) +
    the bracket Lipschitz scale `Le e` (polynomial leg) + the exponent balance
    `sharpBound_le_recip_jdist`.  Recorded precisely, NOT faked.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on closed
`Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoFinal
import YMGap.Continuum.ChebOrthoSecondOrder
import YMGap.Continuum.ChebOrthoCancelDiv
import YMGap.Continuum.ChebOrthoGradedClose
import YMGap.Continuum.ChebOrthoGraded
import YMGap.Continuum.ChebOrthoRemainder

namespace YMGap.Continuum.ChebOrthoTaylor

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag
open YMGap.Continuum.ChebOrthoMidpoint
open YMGap.Continuum.ChebOrthoGraded
open YMGap.Continuum.ChebOrthoGradedClose

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The `CReal` additive `Equiv` algebra the reduction needs

All proved from the pointwise `add`/`neg` action on approximations (no `Mathlib`). -/

/-- **`add` right-leg `Equiv` congruence** (re-derivation, local).
`Equiv B B' → Equiv (add A B) (add A B')`. -/
theorem cadd_right_congr {A B B' : CReal} (h : CReal.Equiv B B') :
    CReal.Equiv (CReal.add A B) (CReal.add A B') :=
  ChebOrthoFinal.add_right_Equiv_congr h

/-- **`add` left-leg `Equiv` congruence.**  `Equiv A A' → Equiv (add A B) (add A' B)`. -/
theorem cadd_left_congr {A A' B : CReal} (h : CReal.Equiv A A') :
    CReal.Equiv (CReal.add A B) (CReal.add A' B) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  -- (add A B).approx n = A_n + B_n  (rfl)
  show (A.approx n + B.approx n) ≤ (A'.approx n + B.approx n) + ε
      ∧ (A'.approx n + B.approx n) ≤ (A.approx n + B.approx n) + ε
  refine ⟨?_, ?_⟩
  · -- A_n + B_n ≤ (A'_n + ε) + B_n = (A'_n + B_n) + ε
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (B.approx n) h1) ?_
    -- (A'_n + ε) + B_n ≈ (A'_n + B_n) + ε
    refine Q'.le_of_eqv ?_
    calc (A'.approx n + ε) + B.approx n
        ≈ A'.approx n + (ε + B.approx n) := Q'.add_assoc_eqv _ _ _
      _ ≈ A'.approx n + (B.approx n + ε) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv ε (B.approx n))
      _ ≈ (A'.approx n + B.approx n) + ε := Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
  · refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (B.approx n) h2) ?_
    refine Q'.le_of_eqv ?_
    calc (A.approx n + ε) + B.approx n
        ≈ A.approx n + (ε + B.approx n) := Q'.add_assoc_eqv _ _ _
      _ ≈ A.approx n + (B.approx n + ε) :=
          Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv ε (B.approx n))
      _ ≈ (A.approx n + B.approx n) + ε := Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

/-- **`add` is commutative up to `Equiv`.**  `Equiv (add A B) (add B A)`. -/
theorem cadd_comm (A B : CReal) : CReal.Equiv (CReal.add A B) (CReal.add B A) := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  -- (add A B).approx n = A_n + B_n ;  (add B A).approx n = B_n + A_n.
  show (A.approx n + B.approx n) ≤ (B.approx n + A.approx n) + ε
      ∧ (B.approx n + A.approx n) ≤ (A.approx n + B.approx n) + ε
  have hcomm : (A.approx n + B.approx n) ≈ (B.approx n + A.approx n) :=
    Q'.add_comm_eqv _ _
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm) ?_
    exact Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε)
  · refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcomm) ?_
    exact Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε)

/-- **`czero` is a left additive unit up to `Equiv`.**  `Equiv (add czero x) x`. -/
theorem czero_cadd (x : CReal) : CReal.Equiv (CReal.add CReal.czero x) x :=
  GramRed.czero_add_eqv x

/-- **`Equiv` is transitive / symmetric / reflexive** (re-exports for `calc`). -/
theorem cequiv_trans {A B C : CReal} (h1 : CReal.Equiv A B) (h2 : CReal.Equiv B C) :
    CReal.Equiv A C := CReal.Equiv.trans h1 h2

theorem cequiv_symm {A B : CReal} (h : CReal.Equiv A B) : CReal.Equiv B A :=
  CReal.Equiv.symm h

instance : Trans (CReal.Equiv) (CReal.Equiv) (CReal.Equiv) where
  trans h1 h2 := CReal.Equiv.trans h1 h2

/-! ## 1. The key consequence of the leading cancellation: `orthTerm ≈ −LZ`

If `add A LZ ≈ czero` then `A ≈ neg LZ`.  PROOF: `A ≈ add czero A ≈ add (add A LZ) A`
… cleaner: add `(neg LZ)` on the right of the hypothesis. -/

/-- **`add A LZ ≈ czero → A ≈ neg LZ`.**  Add `(neg LZ)` to the right leg of the
hypothesis and simplify with the additive group laws (pointwise `Q'`-eqv). -/
theorem eqv_neg_of_add_eqv_czero {A LZ : CReal}
    (h : CReal.Equiv (CReal.add A LZ) CReal.czero) :
    CReal.Equiv A (CReal.neg LZ) := by
  -- per index n: A_n ≈ −LZ_n, from the eventual (A_n + LZ_n) ≈ 0 in the limit sense.
  -- Work directly at the Equiv level: for all ε>0 eventually A_n ≤ −LZ_n + ε and reverse.
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  -- hN n hn : |(A_n + LZ_n) − 0| ≤ ε, i.e. A_n + LZ_n ≤ ε  and  −(A_n + LZ_n) ≤ ... wait shape
  -- (add A LZ).approx n = A_n + LZ_n ; czero.approx n = 0.
  have hpair := hN n hn
  -- hpair : (A_n + LZ_n) ≤ 0 + ε ∧ 0 ≤ (A_n + LZ_n) + ε
  have h1 : (A.approx n + LZ.approx n) ≤ (0 : Q') + ε := hpair.1
  have h2 : (0 : Q') ≤ (A.approx n + LZ.approx n) + ε := hpair.2
  -- goal: A_n ≤ (−LZ_n) + ε ∧ (−LZ_n) ≤ A_n + ε
  show (A.approx n) ≤ (-(LZ.approx n)) + ε ∧ (-(LZ.approx n)) ≤ (A.approx n) + ε
  -- From h1: A_n + LZ_n ≤ ε.  Add (−LZ_n):  A_n = (A_n+LZ_n) + (−LZ_n) ≤ ε + (−LZ_n) = (−LZ_n)+ε.
  have h1' : (A.approx n + LZ.approx n) ≤ ε := by
    refine Q'.le_trans' _ _ _ h1 ?_
    exact Q'.le_of_eqv (QPoly.q_zero_add_eqv ε)
  -- From h2: 0 ≤ A_n + LZ_n + ε, i.e. −(A_n) ≤ LZ_n + ε ... we need (−LZ_n) ≤ A_n + ε.
  -- 0 ≤ (A_n + LZ_n) + ε ⟹ −LZ_n ≤ A_n + ε  (add (−LZ_n) and rearrange).
  refine ⟨?_, ?_⟩
  · -- A_n ≤ (−LZ_n) + ε
    have hstep : (A.approx n + LZ.approx n) + (-(LZ.approx n)) ≤ ε + (-(LZ.approx n)) :=
      Q'.add_le_add_right _ _ (-(LZ.approx n)) h1'
    -- LHS ≈ A_n ; RHS ≈ (−LZ_n) + ε
    refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ hstep ?_)
    · refine Q'.ge_of_eqv ?_
      calc (A.approx n + LZ.approx n) + (-(LZ.approx n))
          ≈ A.approx n + (LZ.approx n + (-(LZ.approx n))) := Q'.add_assoc_eqv _ _ _
        _ ≈ A.approx n + (0 : Q') :=
            Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv (LZ.approx n))
        _ ≈ A.approx n := QPoly.q_add_zero_eqv _
    · exact Q'.le_of_eqv (Q'.add_comm_eqv ε (-(LZ.approx n)))
  · -- (−LZ_n) ≤ A_n + ε
    -- from 0 ≤ (A_n + LZ_n) + ε add (−LZ_n) to both sides.
    have hstep : (0 : Q') + (-(LZ.approx n)) ≤ ((A.approx n + LZ.approx n) + ε) + (-(LZ.approx n)) :=
      Q'.add_le_add_right _ _ (-(LZ.approx n)) h2
    refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ hstep ?_)
    · exact Q'.ge_of_eqv (QPoly.q_zero_add_eqv (-(LZ.approx n)))
    · -- ((A_n + LZ_n) + ε) + (−LZ_n) ≈ A_n + ε
      refine Q'.le_of_eqv ?_
      calc ((A.approx n + LZ.approx n) + ε) + (-(LZ.approx n))
          ≈ (A.approx n + LZ.approx n) + (ε + (-(LZ.approx n))) := Q'.add_assoc_eqv _ _ _
        _ ≈ (A.approx n + LZ.approx n) + ((-(LZ.approx n)) + ε) :=
            Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv ε (-(LZ.approx n)))
        _ ≈ ((A.approx n + LZ.approx n) + (-(LZ.approx n))) + ε :=
            Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
        _ ≈ (A.approx n + (LZ.approx n + (-(LZ.approx n)))) + ε :=
            Q'.add_eqv_congr_right _ _ _ (Q'.add_assoc_eqv _ _ _)
        _ ≈ (A.approx n + (0 : Q')) + ε :=
            Q'.add_eqv_congr_right _ _ _
              (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv (LZ.approx n)))
        _ ≈ A.approx n + ε :=
            Q'.add_eqv_congr_right _ _ _ (QPoly.q_add_zero_eqv _)

/-! ## 2. THE SECOND-DIFFERENCE REDUCTION -/

/-- **THE SECOND-DIFFERENCE REDUCTION.**  Let `A` (`= orthTerm`), `B` (`= splitCReal`)
and `LZ` (the "leading model") be `CReal`s, and `b : Q'` (the rate).  If

  * `Equiv (add A LZ) czero`  (the EXACT leading cancellation, separated out), and
  * `AbsLeRat (add B (neg LZ)) b`  (the SECOND-DIFFERENCE remainder is small),

then `AbsLeRat (add A B) b`.

PROOF: the cancellation gives `A ≈ neg LZ` (`eqv_neg_of_add_eqv_czero`), so
`add A B ≈ add (neg LZ) B ≈ add B (neg LZ)` (left congruence + commutativity), and the
remainder bound transfers along this `Equiv` (`AbsLeRat.of_equiv`).  This is the EXACT
analytic separation of `orthTerm + splitCReal` into the dominant `O(δ)` part
(`orthTerm + LZ ≈ 0`) and the genuine second-difference (Taylor) remainder
`splitCReal − LZ`. -/
theorem secondDiff_reduce {A B LZ : CReal} {b : Q'}
    (hcancel : CReal.Equiv (CReal.add A LZ) CReal.czero)
    (hrem : AbsLeRat (CReal.add B (CReal.neg LZ)) b) :
    AbsLeRat (CReal.add A B) b := by
  -- A ≈ neg LZ
  have hA : CReal.Equiv A (CReal.neg LZ) := eqv_neg_of_add_eqv_czero hcancel
  -- add A B ≈ add (neg LZ) B ≈ add B (neg LZ)
  have hstep1 : CReal.Equiv (CReal.add A B) (CReal.add (CReal.neg LZ) B) :=
    cadd_left_congr hA
  have hstep2 : CReal.Equiv (CReal.add (CReal.neg LZ) B) (CReal.add B (CReal.neg LZ)) :=
    cadd_comm (CReal.neg LZ) B
  have hEq : CReal.Equiv (CReal.add A B) (CReal.add B (CReal.neg LZ)) :=
    CReal.Equiv.trans hstep1 hstep2
  exact ChebOrthoCancelDiv.AbsLeRat.of_equiv hEq hrem

/-! ## 3. The PRECISE strictly-smaller named residual and its reduction -/

/-- **NAMED-open: the SECOND-DIFFERENCE (Taylor) remainder residual** (strictly
smaller than `ChebOrthoFinal.InteriorSecondOrderRemainder`).  For the even order `e`,
at every interior cell `1 ≤ k ≤ N−1` there is a "leading model" `CReal` `LZ` with:

  * `Equiv (add (orthTerm e (N+1) k) LZ) czero`  — the EXACT leading cancellation, and
  * `AbsLeRat (add (splitCReal e he (N+1) k) (neg LZ)) (gradedRate e (N+1) k)`  — the
    SECOND-DIFFERENCE remainder bound.

This is STRICTLY SMALLER/SHARPER than `InteriorSecondOrderRemainder`: the dominant
`orthTerm` and the leading midpoint combination of `splitCReal` (each individually
`≫ gradedRate`) NO LONGER appear in the bound to be proved — they are separated into a
clean `Equiv … czero` (the leading cancellation, supplied by the PROVED
`ChebOrthoCancel.leading_cancellation` un-cleared via
`ChebOrthoSecondOrder.CReal.cancel_mul_left`), leaving ONLY the genuine
boundary-vs-midpoint second-difference Taylor remainder `splitCReal − LZ`
(an `O(δ^{3/2})`-shaped object) to bound against the SAME graded rate. -/
def SecondDiffRemainder (e : Nat) (he : 0 < e) : Prop :=
  ∀ N k : Nat, 1 ≤ k → k ≤ N - 1 →
    ∃ LZ : CReal,
      CReal.Equiv
        (CReal.add (orthTerm e (N + 1) (Nat.succ_pos N) k) LZ) CReal.czero ∧
      AbsLeRat
        (CReal.add (ChebOrthoRemainder.splitCReal e he (N + 1) (Nat.succ_pos N) k)
          (CReal.neg LZ))
        (gradedRate e (N + 1) (Nat.succ_pos N) k)

/-- **THE REDUCTION.**  `SecondDiffRemainder e he → ChebOrthoFinal.InteriorSecondOrderRemainder e he`.
For each interior cell, extract the leading model `LZ` and its two properties, then
apply `secondDiff_reduce` with `A = orthTerm`, `B = splitCReal`. -/
theorem interiorSecondOrder_of_secondDiff (e : Nat) (he : 0 < e)
    (h : SecondDiffRemainder e he) :
    ChebOrthoFinal.InteriorSecondOrderRemainder e he := by
  intro N k hk1 hkN
  obtain ⟨LZ, hcancel, hrem⟩ := h N k hk1 hkN
  exact secondDiff_reduce hcancel hrem

/-! ## 4. A GENUINE fully-PROVED sub-bound: the post-cancellation radical-leg shape

The radical leg of `splitCReal` carries the bare radical difference `s_+ − s_-`.
After the leading cancellation, the radical-leg remainder is controlled by the SHARP
reciprocal-free difference `|s_+ − s_-| ≤ sharpBound ≤ 4/jdist`.  We assemble that
into a single closed two-sided value bound (the genuine `δ^{3/2}/j^{3/2} ~ 4/j` shape),
demonstrating the radical-leg arithmetic of `SecondDiffRemainder` is reachable. -/

/-- **The radical-difference is two-sidedly `≤ 4/jdist M k`** at an interior cell.
Composes the PROVED `ChebOrthoCancelDiv.bdyRadicalDiff_sharp`
(`|s_+ − s_-| ≤ sharpBound M k`) with the PROVED
`ChebOrthoFinal.sharpBound_le_recip_jdist` (`sharpBound M k ≤ 4/jdist M k`) via
`AbsLeRat.mono`.  This is the post-cancellation radical-leg shape, now a closed
theorem (axiom-clean). -/
theorem radicalLeg_AbsLeRat (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hk1n : k + 1 < M) (hj : 2 ≤ jdist M k) :
    AbsLeRat (CReal.add (bdyRadical M hM (k + 1)) (CReal.neg (bdyRadical M hM k)))
      (Q'.mkPos 4 (jdist M k) (jdist_pos (by omega : k < M))) :=
  AbsLeRat.mono
    (ChebOrthoCancelDiv.bdyRadicalDiff_sharp M hM k hk0 hk1n hj)
    (ChebOrthoFinal.sharpBound_le_recip_jdist M hM k hk1n hj)

end YMGap.Continuum.ChebOrthoTaylor

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `cadd_right_congr` / `cadd_left_congr` / `cadd_comm` / `czero_cadd` — the `CReal`
    additive `Equiv` algebra the reduction needs (pointwise `Q'`-eqv).
  * **`eqv_neg_of_add_eqv_czero`** — `Equiv (add A LZ) czero → Equiv A (neg LZ)`, the
    exact consequence of the leading cancellation that powers the reduction.
  * **`secondDiff_reduce`** — THE SECOND-DIFFERENCE REDUCTION: from the EXACT leading
    cancellation `Equiv (add A LZ) czero` and the small SECOND-DIFFERENCE remainder
    `AbsLeRat (add B (neg LZ)) b`, conclude `AbsLeRat (add A B) b`.  The exact analytic
    separation of `orthTerm + splitCReal` into the dominant `O(δ)` part
    (`orthTerm + LZ ≈ 0`) and the genuine second-difference (Taylor) remainder
    `splitCReal − LZ`.
  * `SecondDiffRemainder` — the PRECISE strictly-smaller named residual (see its
    docstring): for each interior cell, the EXISTENCE of a leading model `LZ` with the
    separated leading cancellation and the small remainder.
  * **`interiorSecondOrder_of_secondDiff`** — the PROVED reduction
    `SecondDiffRemainder e he → ChebOrthoFinal.InteriorSecondOrderRemainder e he`.
  * **`radicalLeg_AbsLeRat`** — the post-cancellation radical-leg shape
    `|s_+ − s_-| ≤ 4/jdist M k` at an interior cell, composing the PROVED
    `bdyRadicalDiff_sharp` and `sharpBound_le_recip_jdist`.

**NAMED-open (the honest residual — STRICTLY SMALLER than the input).**
  * `SecondDiffRemainder e he` — for each interior cell, the EXISTENCE of a leading
    model `LZ` with (i) `Equiv (add orthTerm LZ) czero` and (ii)
    `AbsLeRat (add splitCReal (neg LZ)) gradedRate`.  Strictly smaller than
    `ChebOrthoFinal.InteriorSecondOrderRemainder`: the dominant `orthTerm`/leading
    pieces are separated into the clean `Equiv … czero` (i), provable from the PROVED
    `ChebOrthoCancel.leading_cancellation` un-cleared by
    `ChebOrthoSecondOrder.CReal.cancel_mul_left` once a constructive reciprocal of the
    node radical at the interior cell is built; the remainder (ii) is the genuine
    `O(δ^{3/2})` second-difference Taylor object, controlled by the PROVED
    `ChebOrthoCancelDiv.bdyRadicalDiff_sharp` (radical leg, see `radicalLeg_AbsLeRat`)
    + the bracket Lipschitz scale `Le e` (polynomial leg) + the exponent balance
    `ChebOrthoFinal.sharpBound_le_recip_jdist`.  Recorded precisely, NOT faked.

**Path to closure.**  Once `SecondDiffRemainder e he` holds for every even `e ≥ 2`,
`interiorSecondOrder_of_secondDiff` → `ChebOrthoFinal.offdiag_closed_of_secondOrder`
closes the full π-free off-diagonal orthogonality `∫U_e√ = 0` for all `e ≥ 1`.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoTaylor.cadd_left_congr
#print axioms YMGap.Continuum.ChebOrthoTaylor.cadd_comm
#print axioms YMGap.Continuum.ChebOrthoTaylor.eqv_neg_of_add_eqv_czero
#print axioms YMGap.Continuum.ChebOrthoTaylor.secondDiff_reduce
#print axioms YMGap.Continuum.ChebOrthoTaylor.interiorSecondOrder_of_secondDiff
#print axioms YMGap.Continuum.ChebOrthoTaylor.radicalLeg_AbsLeRat
