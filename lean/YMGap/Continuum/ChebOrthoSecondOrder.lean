/-
# The EXACT `CReal` left-cancellation primitive `CReal.cancel_mul_left`
# and its use toward the interior second-order remainder of the π-free
# off-diagonal Chebyshev-`U` orthogonality `∫_{−1}^1 U_e(x)√(1−x²) dx = 0`.

The companion module `ChebOrthoFinal` reduces the even-order off-diagonal
orthogonality to the SINGLE interior per-cell two-sided value bound
`InteriorSecondOrderRemainder e he`
(`|orthTerm e M k + splitCReal e he M k| ≤ gradedRate e M k`, `1 ≤ k ≤ N−1`,
`M = N+1`), via the PROVED chain `interiorGradedRemainder_of_secondOrder →
offdiag_closed_of_secondOrder`.

The dominant pieces `orthTerm` and the LEADING midpoint combination of
`splitCReal` are EACH individually larger than `gradedRate`; the bound holds
ONLY because the leading midpoint combination cancels `orthTerm` EXACTLY
(`ChebOrthoCancel.leading_cancellation`).  Wiring that cancellation through the
GENUINE `CReal`s needs ONE missing limit-level primitive that the bound-only
`ChebOrthoCancelDiv.AbsLeRat.div_of_mul_ge` cannot perform as an EXACT equality:
the cancellation of a positive `CReal` factor from BOTH sides of an `Equiv`.
That primitive is what this module supplies.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `Q'.le_of_not_le` — `¬ (a ≤ b) → b ≤ a` (rational order is total; the `Q'`-`≤`
    unfolds to `Int`-`≤`, where `Int.le_total`/`omega` closes it).  A constructive
    case-companion (the order is DECIDABLE, so `by_cases` on it is intuitionistic).

  * `Q'.le_of_mul_le_mul_left_pos` — the LEFT rational cancellation
    `c·a ≤ c·b → 0 < c → a ≤ b` (commute to the right form
    `ChebOrthoCancelDiv.Q'.le_of_mul_le_mul_right_pos`).

  * `Q'.sub_nonneg_of_le` / `Q'.mul_sub_distrib_le` — the two `Q'`-algebra helpers:
    `b ≤ a → 0 ≤ a + (−b)`, and the distributed difference monotonicity
    `L ≤ S → b ≤ a → L·a + (−(L·b)) ≤ S·a + (−(S·b))` (multiply the nonnegative
    difference `a + (−b)` by `L ≤ S`, then distribute `mul_add`/`mul_neg`).

  * **`CReal.cancel_mul_left`** — THE EXACT CReal left-cancellation primitive.
    From `Equiv (mul S a) (mul S b)`, a POINTWISE lower bound `L ≤ S.approx n`, and
    `0 < L`, conclude `Equiv a b`.  PROOF (per direction `a_n ≤ b_n + ε`, per index
    `n`, using the product tolerance `L·ε`): sign-case on `a_n ≤ b_n` (DECIDABLE).
    The `a_n ≤ b_n` case is free (`a_n ≤ b_n ≤ b_n + ε`).  In the `b_n ≤ a_n` case,
    the difference `d := a_n + (−b_n) ≥ 0`, so `L·a_n + (−(L·b_n)) = L·d ≤ S·d =
    S·a_n + (−(S·b_n)) ≤ L·ε` (the `Equiv` hypothesis at tolerance `L·ε`), whence
    `L·a_n ≤ L·(b_n + ε)`; cancelling `L > 0` on the LEFT
    (`Q'.le_of_mul_le_mul_left_pos`) gives `a_n ≤ b_n + ε`.  The second direction is
    the symmetric application with `a`, `b` swapped.  NO `CReal` reciprocal is ever
    formed; the only "division" is the exact left-cancellation of `L`.

This is the precise primitive (i) named in `ChebOrthoFinal`'s honest ledger as the
exact `s_k`-cancellation that `div_of_mul_ge` cannot supply.  It UN-CLEARS the
leading cancellation: with it, `ChebOrthoCancel.leading_cancellation`'s
`s`-cleared identity `s·(leadingCombo) ≈ s·(−orthTerm-form)` upgrades to the EXACT
`leadingCombo ≈ −orthTerm-form` (cancelling the `CReal` radical factor `s`).

## What is NAMED-open (precisely — the second-order assembly)

  * `ChebOrthoFinal.InteriorSecondOrderRemainder e he` — the per-cell two-sided
    value bound at the interior cells.  With the EXACT left-cancellation primitive
    now PROVED, the residual is the SECOND-DIFFERENCE REMAINDER ASSEMBLY: decompose
    each `splitCReal` factor into its midpoint value plus a second difference
    (radical `s_++s_-`, smooth `B_++B_-` even legs; radical `s_+−s_-`, smooth
    `B_+−B_-` odd legs), use the EXACT `leadingCombo ≈ −orthTerm` to cancel the
    dominant `O(δ)` part, and bound the remainder by `AbsLeRat` additivity with the
    SHARP radical-difference bound `ChebOrthoCancelDiv.bdyRadicalDiff_sharp` and the
    exponent balance `ChebOrthoFinal.sharpBound_le_recip_jdist` against
    `gradedRate`.  This needs (a) the LEADING combination of `splitCReal` matched
    structurally to `ChebOrthoCancel.leading_cancellation`'s midpoint form (the
    split is at the cell BOUNDARIES `b_{k±}`, the cancellation lemma at the cell
    MIDPOINT `x_k`; the second-difference Taylor matching of the two is the genuine
    remaining content), and (b) the `CReal`-level second-difference bracket-leg
    bound (Lipschitz scale `Le e`).  Recorded precisely, NOT faked.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoFinal

namespace YMGap.Continuum.ChebOrthoSecondOrder

open YMGap.Constructive
open YMGap.Continuum

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The `Q'` algebra the cancellation needs -/

/-- **Rational order is total.**  `¬ (a ≤ b) → b ≤ a`.  The `Q'`-`≤` unfolds to the
`Int`-`≤` on the cross-products `a.num·b.den ≤ b.num·a.den`, where `omega` (Int
totality) closes the contrapositive.  (The order is DECIDABLE, so case-splitting on
it via `by_cases` is intuitionistic — no `Classical`.) -/
theorem Q'.le_of_not_le {a b : Q'} (h : ¬ (a ≤ b)) : b ≤ a := by
  -- a ≤ b   ⟺   a.num * b.den ≤ b.num * a.den
  -- b ≤ a   ⟺   b.num * a.den ≤ a.num * b.den
  have h' : ¬ (a.num * (b.den : Int) ≤ b.num * (a.den : Int)) := h
  show b.num * (a.den : Int) ≤ a.num * (b.den : Int)
  omega

/-- **LEFT rational cancellation by a positive factor.**  `c·a ≤ c·b` and `0 < c`
give `a ≤ b`.  Commute both products to the right form and apply
`ChebOrthoCancelDiv.Q'.le_of_mul_le_mul_right_pos`. -/
theorem Q'.le_of_mul_le_mul_left_pos (a b c : Q') (hc : (0 : Q') < c)
    (h : c * a ≤ c * b) : a ≤ b := by
  have h' : a * c ≤ b * c := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv a c)) ?_
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv c b))
  exact ChebOrthoCancelDiv.Q'.le_of_mul_le_mul_right_pos a b c hc h'

/-- `b ≤ a → 0 ≤ a + (−b)` (`Q'`). -/
theorem Q'.sub_nonneg_of_le {a b : Q'} (h : b ≤ a) : (0 : Q') ≤ a + (-b) := by
  -- b + (−b) ≤ a + (−b), and b + (−b) ≈ 0.
  have h1 : b + (-b) ≤ a + (-b) := Q'.add_le_add_right b a (-b) h
  refine Q'.le_trans' _ _ _ ?_ h1
  exact Q'.ge_of_eqv (Q'.add_neg_self_eqv b)

/-- **The distributed difference monotonicity.**  For `L ≤ S` and `b ≤ a`,
`L·a + (−(L·b)) ≤ S·a + (−(S·b))`.  Multiply the nonnegative difference
`d = a + (−b)` by `L ≤ S` (`mul_le_mul_of_nonneg_right`), then distribute both
products `(·)·d ≈ (·)·a + (−((·)·b))` (`add_mul`/`mul_neg`). -/
theorem Q'.mul_sub_distrib_le {L S a b : Q'} (hLS : L ≤ S) (hba : b ≤ a) :
    L * a + (-(L * b)) ≤ S * a + (-(S * b)) := by
  have hd0 : (0 : Q') ≤ a + (-b) := Q'.sub_nonneg_of_le hba
  -- L·d ≤ S·d  (right-monotonicity: L ≤ S, d ≥ 0)
  have hmul : L * (a + (-b)) ≤ S * (a + (-b)) :=
    Q'.mul_le_mul_of_nonneg_right L S (a + (-b)) hLS hd0
  -- distribute each side:  X·(a + (−b)) ≈ X·a + (−(X·b))
  have hdist : ∀ X : Q', (X * (a + (-b))) ≈ (X * a + (-(X * b))) := by
    intro X
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv X a (-b)) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv X b)
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (hdist L)) ?_
  exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (hdist S))

/-! ## 1. THE EXACT `CReal` left-cancellation primitive -/

/-- **THE EXACT `CReal` LEFT-CANCELLATION PRIMITIVE.**  From an `Equiv` of two
products with a common LEFT factor `S`, a POINTWISE lower bound `L ≤ S.approx n`
at every index, and `0 < L`, conclude the `Equiv` of the two right factors:

    `Equiv (mul S a) (mul S b)`, `(∀ n, L ≤ S.approx n)`, `0 < L`  ⟹  `Equiv a b`.

PROOF (per direction, per index `n`, at product tolerance `L·ε`):  sign-case on
`a_n ≤ b_n` (DECIDABLE rational order).  The `a_n ≤ b_n` case is free
(`a_n ≤ b_n ≤ b_n + ε`).  In the complementary `b_n ≤ a_n` case the difference
`d = a_n + (−b_n) ≥ 0`, so by the distributed difference monotonicity
`L·a_n + (−(L·b_n)) ≤ S·a_n + (−(S·b_n))`; the `Equiv` hypothesis at tolerance
`L·ε` bounds `S·a_n ≤ S·b_n + L·ε`, i.e. `S·a_n + (−(S·b_n)) ≤ L·ε`, whence
`L·a_n ≤ L·b_n + L·ε ≈ L·(b_n + ε)`; cancelling `L > 0` on the LEFT
(`Q'.le_of_mul_le_mul_left_pos`) gives `a_n ≤ b_n + ε`.  The second direction is the
symmetric application with `a`, `b` swapped (the hypothesis is symmetric).  NO
`CReal` reciprocal is ever formed. -/
theorem CReal.cancel_mul_left {S a b : CReal} {L : Q'}
    (h : CReal.Equiv (CReal.mul S a) (CReal.mul S b))
    (hSL : ∀ n, L ≤ S.approx n) (hL : (0 : Q') < L) :
    CReal.Equiv a b := by
  -- A reusable per-direction core:  given the product bound `S·x ≤ S·y + L·ε`
  -- eventually (one half of `h` at tolerance `L·ε`), conclude `x ≤ y + ε` eventually.
  -- We phrase the core abstractly in the two CReals (x, y) so it serves both
  -- directions of `h`.
  have core : ∀ x y : CReal,
      (∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
        (CReal.mul S x).approx n ≤ (CReal.mul S y).approx n + ε) →
      (∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
        x.approx n ≤ y.approx n + ε) := by
    intro x y hxy ε hε
    -- product tolerance  L·ε > 0
    have hLε : (0 : Q') < L * ε := by
      have hLn : (0 : Int) < L.num := Q'.num_pos_of_pos hL
      have hεn : (0 : Int) < ε.num := Q'.num_pos_of_pos hε
      show (0 : Q').num * ((L * ε).den : Int) < (L * ε).num * ((0 : Q').den : Int)
      show (0 : Q').num * ((L * ε).den : Int) < (L.num * ε.num) * ((0 : Q').den : Int)
      have h0n : (0 : Q').num = 0 := rfl
      have hd1 : ((0 : Q').den : Int) = 1 := rfl
      rw [h0n, hd1, Int.zero_mul, Int.mul_one]
      exact Int.mul_pos hLn hεn
    obtain ⟨N, hN⟩ := hxy (L * ε) hLε
    refine ⟨N, fun n hn => ?_⟩
    -- the product bound at index n:  S_n·x_n ≤ S_n·y_n + L·ε
    have hprod : S.approx n * x.approx n
        ≤ S.approx n * y.approx n + L * ε := hN n hn
    -- sign-case on x_n ≤ y_n (decidable order)
    by_cases hxyle : x.approx n ≤ y.approx n
    · -- x_n ≤ y_n ≤ y_n + ε
      refine Q'.le_trans' _ _ _ hxyle ?_
      exact Q'.add_le_self_of_nonneg (y.approx n) ε (Q'.le_of_lt hε)
    · -- y_n ≤ x_n :  the genuine cancellation case
      have hyx : y.approx n ≤ x.approx n := Q'.le_of_not_le hxyle
      -- S_n·x_n + (−(S_n·y_n)) ≤ L·ε  (from hprod, shuffle the additive form)
      have hSdiff : S.approx n * x.approx n + (-(S.approx n * y.approx n)) ≤ L * ε := by
        -- add (−(S_n·y_n)) to both sides of hprod
        have h1 : (S.approx n * x.approx n) + (-(S.approx n * y.approx n))
            ≤ (S.approx n * y.approx n + L * ε) + (-(S.approx n * y.approx n)) :=
          Q'.add_le_add_right _ _ (-(S.approx n * y.approx n)) hprod
        refine Q'.le_trans' _ _ _ h1 ?_
        -- (S_n·y_n + L·ε) + (−(S_n·y_n)) ≈ L·ε
        refine Q'.le_of_eqv ?_
        calc (S.approx n * y.approx n + L * ε) + (-(S.approx n * y.approx n))
            ≈ (L * ε + S.approx n * y.approx n) + (-(S.approx n * y.approx n)) :=
              Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv (S.approx n * y.approx n) (L * ε))
          _ ≈ L * ε + (S.approx n * y.approx n + (-(S.approx n * y.approx n))) :=
              Q'.add_assoc_eqv _ _ _
          _ ≈ L * ε + (0 : Q') :=
              Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv (S.approx n * y.approx n))
          _ ≈ L * ε := QPoly.q_add_zero_eqv _
      -- L·x_n + (−(L·y_n)) ≤ S_n·x_n + (−(S_n·y_n))  (distributed diff monotonicity)
      have hLdiff : L * x.approx n + (-(L * y.approx n))
          ≤ S.approx n * x.approx n + (-(S.approx n * y.approx n)) :=
        Q'.mul_sub_distrib_le (hSL n) hyx
      -- so L·x_n + (−(L·y_n)) ≤ L·ε
      have hLb : L * x.approx n + (-(L * y.approx n)) ≤ L * ε :=
        Q'.le_trans' _ _ _ hLdiff hSdiff
      -- L·x_n ≤ L·y_n + L·ε = L·(y_n + ε)
      have hLx : L * x.approx n ≤ L * (y.approx n + ε) := by
        -- from L·x_n + (−(L·y_n)) ≤ L·ε add (L·y_n) and rewrite
        have h2 : (L * x.approx n + (-(L * y.approx n))) + L * y.approx n
            ≤ L * ε + L * y.approx n :=
          Q'.add_le_add_right _ _ (L * y.approx n) hLb
        -- LHS ≈ L·x_n ; RHS ≈ L·(y_n + ε)
        refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ h2 ?_)
        · -- L·x_n ≈ (L·x_n + (−(L·y_n))) + (L·y_n)
          refine Q'.ge_of_eqv ?_
          calc (L * x.approx n + (-(L * y.approx n))) + L * y.approx n
              ≈ L * x.approx n + ((-(L * y.approx n)) + L * y.approx n) :=
                Q'.add_assoc_eqv _ _ _
            _ ≈ L * x.approx n + (0 : Q') :=
                Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv (L * y.approx n))
            _ ≈ L * x.approx n := QPoly.q_add_zero_eqv _
        · -- L·ε + L·y_n ≈ L·(y_n + ε)
          refine Q'.le_of_eqv ?_
          calc L * ε + L * y.approx n
              ≈ L * y.approx n + L * ε := Q'.add_comm_eqv _ _
            _ ≈ L * (y.approx n + ε) := Q'.eqv_symm (Q'.mul_add_eqv L (y.approx n) ε)
      -- cancel L > 0 on the left
      exact Q'.le_of_mul_le_mul_left_pos (x.approx n) (y.approx n + ε) L hL hLx
  -- assemble both directions of Equiv a b from `core` on (a,b) and (b,a)
  intro ε hε
  -- direction a_n ≤ b_n + ε
  obtain ⟨N1, hN1⟩ := core a b (fun e he => by
    obtain ⟨M, hM⟩ := h e he
    exact ⟨M, fun n hn => (hM n hn).1⟩) ε hε
  -- direction b_n ≤ a_n + ε  (use Equiv.symm of h, then core on (b,a))
  have hsym : CReal.Equiv (CReal.mul S b) (CReal.mul S a) := CReal.Equiv.symm h
  obtain ⟨N2, hN2⟩ := core b a (fun e he => by
    obtain ⟨M, hM⟩ := hsym e he
    exact ⟨M, fun n hn => (hM n hn).1⟩) ε hε
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  exact ⟨hN1 n hn1, hN2 n hn2⟩

/-! ## 2. The interior second-order remainder (NAMED-open, reduced to the
second-difference assembly) -/

/-- **NAMED-open: the interior second-order remainder.**  The per-cell two-sided
value bound `ChebOrthoFinal.InteriorSecondOrderRemainder e he` at the interior
cells.  With the EXACT left-cancellation primitive `CReal.cancel_mul_left` now
PROVED — un-clearing `ChebOrthoCancel.leading_cancellation`'s `s`-cleared identity
to the exact `leadingCombo ≈ −orthTerm` form — the residual is the SECOND-DIFFERENCE
remainder assembly: structurally match the LEADING combination of `splitCReal`
(at the cell BOUNDARIES `b_{k±}`) to the cancellation lemma's MIDPOINT form (at
`x_k`) via the second-difference Taylor decomposition, then bound the remainder by
`AbsLeRat` additivity with the SHARP radical-difference bound
`ChebOrthoCancelDiv.bdyRadicalDiff_sharp` and the exponent balance
`ChebOrthoFinal.sharpBound_le_recip_jdist`.  Recorded precisely. -/
def InteriorSecondOrderRemainderResidual (e : Nat) (he : 0 < e) : Prop :=
  ChebOrthoFinal.InteriorSecondOrderRemainder e he

end YMGap.Continuum.ChebOrthoSecondOrder

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * `Q'.le_of_not_le` — rational order totality `¬ (a ≤ b) → b ≤ a` (decidable
    order; `by_cases` on it is intuitionistic).
  * `Q'.le_of_mul_le_mul_left_pos` — LEFT rational cancellation by a positive factor
    `c·a ≤ c·b → 0 < c → a ≤ b`.
  * `Q'.sub_nonneg_of_le` / `Q'.mul_sub_distrib_le` — the nonnegative difference and
    its distributed monotonicity `L ≤ S → b ≤ a → L·a + (−(L·b)) ≤ S·a + (−(S·b))`.
  * **`CReal.cancel_mul_left`** — THE EXACT CReal left-cancellation primitive:
    `Equiv (mul S a) (mul S b)`, `(∀ n, L ≤ S.approx n)`, `0 < L` ⟹ `Equiv a b`.
    Reciprocal-free; the two directions use a constructive sign split on `a_n ≤ b_n`
    (the negative case multiplies the nonnegative difference by the pointwise lower
    bound `L ≤ S_n` and cancels `L > 0` on the left).  This is the exact
    `s_k`-cancellation that the bound-only `ChebOrthoCancelDiv.AbsLeRat.div_of_mul_ge`
    cannot supply, and it UN-CLEARS `ChebOrthoCancel.leading_cancellation`.

**NAMED-open (the honest residual — the second-difference assembly).**
  * `ChebOrthoFinal.InteriorSecondOrderRemainder e he` — the per-cell two-sided value
    bound at the interior cells.  With `CReal.cancel_mul_left` PROVED, the residual is
    the SECOND-DIFFERENCE REMAINDER ASSEMBLY: match the LEADING combination of
    `splitCReal` (at the cell BOUNDARIES `b_{k±}`) to
    `ChebOrthoCancel.leading_cancellation`'s MIDPOINT form (at `x_k`) by a
    second-difference Taylor decomposition, cancel the dominant `O(δ)` piece via the
    exact `leadingCombo ≈ −orthTerm`, then bound the remainder by `AbsLeRat`
    additivity with the SHARP radical-difference bound
    `ChebOrthoCancelDiv.bdyRadicalDiff_sharp` and the exponent balance
    `ChebOrthoFinal.sharpBound_le_recip_jdist` against `gradedRate`.  Recorded
    precisely, NOT faked.

**Path to closure.**  Once `ChebOrthoFinal.InteriorSecondOrderRemainder e he` holds
for every even `e ≥ 2`, `ChebOrthoFinal.interiorGradedRemainder_of_secondOrder` →
`ChebOrthoFinal.offdiag_closed_of_secondOrder` closes the full π-free off-diagonal
orthogonality `∫U_e√ = 0` for all `e ≥ 1` UNCONDITIONALLY.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoSecondOrder.Q'.le_of_not_le
#print axioms YMGap.Continuum.ChebOrthoSecondOrder.Q'.le_of_mul_le_mul_left_pos
#print axioms YMGap.Continuum.ChebOrthoSecondOrder.Q'.sub_nonneg_of_le
#print axioms YMGap.Continuum.ChebOrthoSecondOrder.Q'.mul_sub_distrib_le
#print axioms YMGap.Continuum.ChebOrthoSecondOrder.CReal.cancel_mul_left
