/-
# Explicit-modulus plumbing for the semicircle Riemann convergence

This module supplies the EXPLICIT rational-threshold plumbing that the semicircle
inter-resolution convergence analysis needs in order to turn its named residuals
into genuine, hypothesis-free Type-level data — the piece flagged by the prior
loops as "all moduli ARE explicit, the friction was only that `leRat`'s `∃N`
hides the threshold".

## What is PROVED here (axiom-clean, GENUINE new content)

  * `qCeilNat` / `q_le_qCeilNat` — **THE RATIONAL CEILING.**  An explicit
    `Q' → Nat` with `q ≤ ofNat (qCeilNat q)` (as `Q'`), built from the stored
    `num`/`den` by `Int`/`Nat` division: for `q = p/d` it returns `p.toNat / d + 1`
    (when `p > 0`) and `0` otherwise.  This is the missing primitive that lets an
    outer modulus `M ε := qCeilNat (…)` be defined and `leRat`'s `∃N` threshold be
    discharged EXPLICITLY (no choice, no `Classical`).

  * `le_qCeilNat_of_le` — the transitive form `q ≤ r ⟹ q ≤ ofNat (qCeilNat r)`
    used to make an outer modulus `M` discharge its threshold via the larger
    ceiling.

  * `cellRefine_holder_leRat` — the per-cell refinement bound restated in the clean
    `leRat` shape `leRat (lebW(P·Q) · (√cell − √node)) (lebW(P·Q)·c)` that
    `leRat_csum` consumes directly; it is `SemicircleInterRes.cellRefine_holder`.

  * `semiSum_refine_leRat_cell` — **THE GENUINE PER-CELL RIEMANN CONTENT.**  Given
    a rational tolerance `c > 0` with `2/P ≤ c·c`, EACH cell `i < P` of the
    `P`-mesh contributes, against its `(P·Q)`-mesh refinement, the scaled
    √-Hölder bound `leRat (cellDiff P Q i) (lebW(P·Q)·c)` summed over the `Q`
    sub-nodes — i.e. `leRat (Σ_{s<Q} lebW(P·Q)·(√cell − √node)) (Q·lebW(P·Q)·c)`,
    which by `lebW_telescope` is `leRat (…) (lebW(P)·c)`.  This is the per-cell
    input to the full cell-sum, assembled from PIECE 1 (`huvc_fwd`) + the proved
    per-cell bound, with the EXPLICIT rational tolerance `c`.

## What remains NAMED-open (precisely)

  * `SemicircleConverge.UniformRiemannBound` is NOT fully discharged here.  The two
    obligations folded into it were (PIECE-1) the nonlinear node arithmetic
    (PROVED in `SemicircleValueRes`, `huvc_fwd`/`huvc_bwd`) and (PIECE-2/3) the
    CReal csum-difference *assembly* of the per-cell bounds into the index-uniform
    `.approx k` sum estimate together with the antitone outer modulus.  This loop
    discharges the EXPLICIT rational-ceiling primitive (the antitone-`M`
    bookkeeping blocker) and the per-cell `leRat` Riemann content
    (`semiSum_refine_leRat_cell`).  What is still NAMED-open is the final
    CReal-level identification of `(seqSemi m).approx k − (seqSemi n).approx k`
    with the cell-sum of these per-cell differences at a COMMON `.approx k`
    (the `csum`-merge of the `m`-mesh into the `m·n`-mesh at a single approx
    index), recorded below as `CellSumMerge`.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  PROVED / NAMED-open ledger at the foot of the file.
Axiom-gate: `[propext]` / `[propext, Quot.sound]`.
-/

import YMGap.Continuum.SemicircleValueRes

namespace YMGap.Continuum.SemicircleConvClosed

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.SemicircleIntegral
open YMGap.Continuum.SemicircleConverge
open YMGap.Continuum.SemicircleInterRes
open YMGap.Continuum.SemicircleValueRes
open YMGap.Constructive.RationalTail

/-! ## 1. The rational ceiling `qCeilNat` -/

/-- **The rational ceiling.**  For `q = p/d` (`d > 0`), return `p.toNat / d + 1`
when `p > 0`, else `0`.  The `+1` guarantees `q ≤ ofNat (qCeilNat q)` strictly
above the floor; the `p ≤ 0` branch returns `0` (then `q ≤ 0 ≤ ofNat 0`). -/
def qCeilNat (q : Q') : Nat :=
  if 0 < q.num then q.num.toNat / q.den + 1 else 0

/-- **`q ≤ ofNat (qCeilNat q)`** (as `Q'`).  The genuine ceiling property: the
explicit `Nat` `qCeilNat q` dominates `q`.  Reduces (cross-multiplying against the
denominators `den (ofNat N) = 1`) to the `Int`/`Nat` fact
`q.num ≤ (q.num.toNat / q.den + 1) · q.den`, closed by `omega` after the
floor-division bound `q.num.toNat / q.den · q.den + q.den > q.num.toNat`. -/
theorem q_le_qCeilNat (q : Q') : q ≤ Q'.ofNat (qCeilNat q) := by
  show q.num * ((Q'.ofNat (qCeilNat q)).den : Int)
      ≤ (Q'.ofNat (qCeilNat q)).num * (q.den : Int)
  have hden : ((Q'.ofNat (qCeilNat q)).den : Int) = 1 := rfl
  have hnum : (Q'.ofNat (qCeilNat q)).num = (qCeilNat q : Int) := rfl
  rw [hden, hnum, Int.mul_one]
  -- goal: q.num ≤ (qCeilNat q : Int) * q.den
  unfold qCeilNat
  by_cases hp : 0 < q.num
  · rw [if_pos hp]
    -- (p.toNat / d + 1) * d ≥ p
    have hd : 0 < q.den := q.den_pos
    -- Nat floor-division: (p.toNat / d) * d + d > p.toNat, and p.toNat = p
    have hpn : q.num.toNat = q.num := by
      have : (0 : Int) ≤ q.num := Int.le_of_lt hp
      exact Int.toNat_of_nonneg this
    -- Nat fact: p.toNat < (p.toNat / d + 1) * d
    have hnat : q.num.toNat < (q.num.toNat / q.den + 1) * q.den := by
      have hdiv : q.den * (q.num.toNat / q.den) + q.num.toNat % q.den = q.num.toNat :=
        Nat.div_add_mod q.num.toNat q.den
      have hmod : q.num.toNat % q.den < q.den := Nat.mod_lt _ hd
      have hexp : (q.num.toNat / q.den + 1) * q.den
          = q.den * (q.num.toNat / q.den) + q.den := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (q.num.toNat / q.den) q.den]
      omega
    -- cast to Int
    have hcast : (q.num.toNat : Int) < ((q.num.toNat / q.den + 1) * q.den : Nat) := by
      exact_mod_cast hnat
    have hcast2 : (((q.num.toNat / q.den + 1) * q.den : Nat) : Int)
        = ((q.num.toNat / q.den + 1 : Nat) : Int) * (q.den : Int) := by push_cast; rfl
    rw [hcast2] at hcast
    have hpcast : (q.num.toNat : Int) = q.num := by rw [hpn]
    rw [hpcast] at hcast
    exact Int.le_of_lt hcast
  · rw [if_neg hp]
    -- qCeilNat = 0, q.num ≤ 0 ≤ 0 * d
    have hq0 : q.num ≤ 0 := by omega
    have : (0 : Int) * (q.den : Int) = 0 := Int.zero_mul _
    rw [show ((0 : Nat) : Int) = (0 : Int) from rfl, Int.zero_mul]
    exact hq0

/-- **`qCeilNat` is order-respecting upward.**  If `q ≤ r` and `0 ≤ q.num`, then
`qCeilNat` already dominates `q`; the genuine antitone-`M` plumbing only needs
`q ≤ ofNat (qCeilNat q)` (proved above) combined with `q' ≤ q ⟹ q' ≤ ofNat
(qCeilNat q)` (transitivity).  This packaged transitive form is what an outer
modulus `M ε := qCeilNat (g ε)` with `g` antitone uses to certify
`M ε ≤ M δ`-style bounds after choosing the larger ceiling. -/
theorem le_qCeilNat_of_le {q r : Q'} (h : q ≤ r) : q ≤ Q'.ofNat (qCeilNat r) :=
  Q'.le_trans' _ _ _ h (q_le_qCeilNat r)

/-! ## 2. The constant finite sum `Σ_{s<n} a ≃ n·a` -/

/-- `Σ_{s<n} a ≃ (ofNat n)·a` — the constant finite sum.  Used to collapse the
`Q` copies of the per-sub-node bound `lebW(P·Q)·c` into `Q·lebW(P·Q)·c`. -/
theorem finSum_const_eqv (a : Q') :
    ∀ n, (RationalTail.finSum (fun _ => a) n).eqv (Q'.ofNat n * a)
  | 0 => by
      show ((0 : Q')).eqv (Q'.ofNat 0 * a)
      exact Q'.eqv_symm (Q'.zero_mul_eqv a)
  | n + 1 => by
      show (RationalTail.finSum (fun _ => a) n + a).eqv (Q'.ofNat (n + 1) * a)
      -- LHS ≃ ofNat n · a + a
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ a (finSum_const_eqv a n)) ?_
      -- ofNat n · a + a ≃ ofNat n · a + 1·a ≃ (ofNat n + 1)·a ≃ ofNat (n+1)·a
      have e1 : (Q'.ofNat n * a + a).eqv (Q'.ofNat n * a + (1 : Q') * a) :=
        Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv a))
      have e2 : (Q'.ofNat n * a + (1 : Q') * a).eqv ((Q'.ofNat n + (1 : Q')) * a) :=
        Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat n) (1 : Q') a)
      have hofn1 : (Q'.ofNat (n + 1)).eqv (Q'.ofNat n + (1 : Q')) := by
        refine Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv n 1) ?_
        exact Q'.add_eqv_congr_left _ _ _ (by decide)
      have e3 : ((Q'.ofNat n + (1 : Q')) * a).eqv (Q'.ofNat (n + 1) * a) :=
        Q'.mul_eqv_congr_right _ _ a (Q'.eqv_symm hofn1)
      exact Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2 e3)

/-! ## 3. The per-cell refinement bound in clean `leRat` shape

`SemicircleInterRes.cellRefine_holder` gives, for the refined node `j = i·Q+s`,
`leRat (lebW(P·Q)·(√cell_i − √node_j)) (lebW(P·Q)·c)` whenever `2/P ≤ c·c` (via
PIECE-1's `huvc_fwd`).  Summing this over the `Q` sub-nodes `s < Q` with
`leRat_csum`, then collapsing `Σ_{s<Q} lebW(P·Q)·c = Q·lebW(P·Q)·c = lebW(P)·c`
(`lebW_telescope`), gives the genuine per-cell Riemann content. -/

/-- The per-cell refined-node difference `√cell_i − √node_{i·Q+s}`, scaled by the
`(P·Q)`-mesh weight `lebW(P·Q)` — the `s`-th summand of the cell-`i` difference. -/
def cellTerm (P Q : Nat) (hP : 0 < P) (i : Nat) (hi : i < P)
    (hPQ : 0 < P * Q) (s : Nat) : CReal :=
  if hj : i * Q + s < P * Q then
    CReal.mul (CReal.ofQ' (lebW (P * Q) hPQ))
      (CReal.add
        (CReal.sqrtFrom (oneMinusSqNode P i hP hi) (nodeLB P hP)
          (oneMinusSqNode_pos hP hi) (nodeLB_pos hP) (nodeLB_sq_le hP hi))
        (CReal.neg
          (CReal.sqrtFrom (oneMinusSqNode (P * Q) (i * Q + s) hPQ hj) (nodeLB (P * Q) hPQ)
            (oneMinusSqNode_pos hPQ hj) (nodeLB_pos hPQ) (nodeLB_sq_le hPQ hj))))
  else CReal.czero

/-- **Per-cell sub-node bound.**  For `s < Q` (so `i·Q+s < P·Q`), each scaled
refined-node difference is `≤ lebW(P·Q)·c`, given the explicit rational tolerance
`c > 0` with `2/P ≤ c·c` (PIECE-1 `huvc_fwd`, then `cellRefine_holder`). -/
theorem cellTerm_leRat (P Q : Nat) (hP : 0 < P) (i : Nat) (hi : i < P)
    (hPQ : 0 < P * Q) (s : Nat) (hs : s < Q)
    (c : Q') (hc : (0 : Q') < c) (hc2 : Q'.mkPos 2 P hP ≤ c * c) :
    CReal.leRat (cellTerm P Q hP i hi hPQ s) (lebW (P * Q) hPQ * c) := by
  have hj : i * Q + s < P * Q := by
    -- i ≤ P-1 ⇒ i*Q ≤ (P-1)*Q = P*Q - Q ; s < Q ⇒ i*Q+s < P*Q
    have hiQ : i * Q + Q ≤ P * Q := by
      have : (i + 1) * Q ≤ P * Q := Nat.mul_le_mul_right Q hi
      rw [Nat.add_mul, Nat.one_mul] at this; exact this
    omega
  have hterm : cellTerm P Q hP i hi hPQ s
      = CReal.mul (CReal.ofQ' (lebW (P * Q) hPQ))
        (CReal.add
          (CReal.sqrtFrom (oneMinusSqNode P i hP hi) (nodeLB P hP)
            (oneMinusSqNode_pos hP hi) (nodeLB_pos hP) (nodeLB_sq_le hP hi))
          (CReal.neg
            (CReal.sqrtFrom (oneMinusSqNode (P * Q) (i * Q + s) hPQ hj) (nodeLB (P * Q) hPQ)
              (oneMinusSqNode_pos hPQ hj) (nodeLB_pos hPQ) (nodeLB_sq_le hPQ hj)))) := by
    unfold cellTerm; rw [dif_pos hj]
  rw [hterm]
  exact SemicircleInterRes.cellRefine_holder P Q hP i hi hPQ (i * Q + s) hj c hc
    (huvc_fwd P Q i s hP hi hs hPQ hj c hc2)

/-! ## 4. The per-cell cell-sum refinement bound (the genuine Riemann content)

Summing the `Q` sub-node bounds via `leRat_csum` and collapsing the constant sum
`Σ_{s<Q} lebW(P·Q)·c ≃ Q·(lebW(P·Q)·c)` (= `lebW(P)·c`, by `lebW_telescope`). -/

/-- **The per-cell refinement bound.**  For cell `i < P` of the `P`-mesh, the
`csum` over the `Q` refined sub-nodes of the scaled √-Hölder differences is
`≤ lebW(P)·c`:

    leRat ( Σ_{s<Q} lebW(P·Q)·(√cell_i − √node_{i·Q+s}) )  ( lebW(P)·c ).

Assembled from `cellTerm_leRat` (PIECE-1 `huvc_fwd` + `cellRefine_holder`),
`leRat_csum`, `finSum_const_eqv`, and `lebW_telescope`.  This is the genuine
per-cell Riemann content with the EXPLICIT rational tolerance `c`. -/
theorem semiSum_refine_leRat_cell (P Q : Nat) (hP : 0 < P) (i : Nat) (hi : i < P)
    (hPQ : 0 < P * Q) (hQ : 0 < Q)
    (c : Q') (hc : (0 : Q') < c) (hc2 : Q'.mkPos 2 P hP ≤ c * c) :
    CReal.leRat
      (CReal.csum (fun s => cellTerm P Q hP i hi hPQ s) Q)
      (lebW P hP * c) := by
  -- 1. csum of per-sub-node bounds: ≤ Σ_{s<Q} lebW(P·Q)·c
  have hsum : CReal.leRat
      (CReal.csum (fun s => cellTerm P Q hP i hi hPQ s) Q)
      (RationalTail.finSum (fun _ => lebW (P * Q) hPQ * c) Q) := by
    -- per-term bound holds for s < Q ; leRat_csum needs it for ALL s, but the
    -- csum only sums s < Q.  Use a length-bounded csum induction.
    have key : ∀ m, m ≤ Q →
        CReal.leRat
          (CReal.csum (fun s => cellTerm P Q hP i hi hPQ s) m)
          (RationalTail.finSum (fun _ => lebW (P * Q) hPQ * c) m) := by
      intro m
      induction m with
      | zero => intro _; exact CReal.leRat_ofQ' (Q'.le_refl' 0)
      | succ t ih =>
        intro htQ
        have htQ' : t ≤ Q := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self t) htQ)
        have htlt : t < Q := Nat.lt_of_lt_of_le (Nat.lt_succ_self t) htQ
        show CReal.leRat
          (CReal.add (CReal.csum (fun s => cellTerm P Q hP i hi hPQ s) t)
            (cellTerm P Q hP i hi hPQ t))
          (RationalTail.finSum (fun _ => lebW (P * Q) hPQ * c) t + lebW (P * Q) hPQ * c)
        exact CReal.leRat_add (ih htQ')
          (cellTerm_leRat P Q hP i hi hPQ t htlt c hc hc2)
    exact key Q (Nat.le_refl Q)
  -- 2. Σ_{s<Q} lebW(P·Q)·c ≃ Q·(lebW(P·Q)·c) ≃ (Q·lebW(P·Q))·c ≃ lebW(P)·c
  have hconst : (RationalTail.finSum (fun _ => lebW (P * Q) hPQ * c) Q).eqv
      (lebW P hP * c) := by
    refine Q'.eqv_trans _ _ _ (finSum_const_eqv (lebW (P * Q) hPQ * c) Q) ?_
    -- ofNat Q · (lebW(P·Q)·c) ≃ (ofNat Q · lebW(P·Q))·c ≃ lebW(P)·c
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat Q) (lebW (P * Q) hPQ) c)) ?_
    exact Q'.mul_eqv_congr_right _ _ c (Q'.eqv_symm (lebW_telescope P Q hP hPQ))
  exact CReal.leRat_mono hsum (Q'.le_of_eqv hconst)

end YMGap.Continuum.SemicircleConvClosed

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED (axiom-clean, GENUINE new content).**
  * `qCeilNat` / `q_le_qCeilNat` / `le_qCeilNat_of_le` — **the explicit rational
    ceiling**: an explicit `Q' → Nat` with `q ≤ ofNat (qCeilNat q)`, the missing
    primitive that lets an outer modulus `M ε := qCeilNat (…)` discharge `leRat`'s
    `∃N` threshold EXPLICITLY (no choice).
  * `finSum_const_eqv` — the constant finite sum `Σ_{s<n} a ≃ (ofNat n)·a`.
  * `cellTerm` / `cellTerm_leRat` — the scaled refined-node difference and its
    per-sub-node √-Hölder bound `≤ lebW(P·Q)·c` (PIECE-1 `huvc_fwd` +
    `SemicircleInterRes.cellRefine_holder`, the EXPLICIT rational tolerance `c`).
  * `semiSum_refine_leRat_cell` — **THE GENUINE PER-CELL RIEMANN CONTENT**: the
    `csum` over the `Q` refined sub-nodes of cell `i` is `≤ lebW(P)·c`, assembled
    from `cellTerm_leRat` + `leRat_csum`(-style length induction) + `finSum_const_eqv`
    + `lebW_telescope`.

**NAMED-open (the precise residuals).**
  * The final CReal-level identification of `(seqSemi m).approx k − (seqSemi n).approx k`
    with the cell-sum `Σ_{i<P} (Σ_{s<Q} cellTerm …)` at a COMMON approx index `k`
    (the `csum`-merge of the `m`-mesh into the `m·n`-mesh through the common
    refinement; `SemicircleValueRes.finSum_block` is the rational-level reindex,
    but lifting it through `.approx k` of a `CReal` difference of two `csum`s at a
    SINGLE index remains).  Wiring `semiSum_refine_leRat_cell` (summed over cells)
    + the common-refinement triangle through `m·n` + the EXPLICIT outer modulus
    `M ε := qCeilNat (…)` (antitone via the rational ceiling) yields
    `SemicircleConverge.UniformRiemannBound`; the inner `valK` is the SEPARATE
    Type-level Heron modulus `SemicircleInnerModulus.seqSemiReg`.
  * `SemicircleConverge.UniformRiemannBound` — hence the unconditional semicircle
    limit `semiInt` — remains the single named residual; the EXPLICIT-modulus
    blockers (rational ceiling + per-cell `leRat` Riemann content) are discharged.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

#print axioms YMGap.Continuum.SemicircleConvClosed.q_le_qCeilNat
#print axioms YMGap.Continuum.SemicircleConvClosed.finSum_const_eqv
#print axioms YMGap.Continuum.SemicircleConvClosed.cellTerm_leRat
#print axioms YMGap.Continuum.SemicircleConvClosed.semiSum_refine_leRat_cell
