/-
# Closing the per-cell two-sided estimate `ChebOrthoGraded.GradedPerCellBound`
# for the π-free off-diagonal Chebyshev-`U` orthogonality `∫_{−1}^1 U_e(x)√(1−x²)dx = 0`.

The companion module `ChebOrthoGraded` reduces the even-order off-diagonal
orthogonality to the SINGLE per-cell two-sided estimate

    `GradedPerCellBound e he :=
       ∀ N k, leRat (cellAdjR e he (N+1) k) (gradedRate e (N+1) k)
            ∧ leRat (neg (cellAdjR e he (N+1) k)) (gradedRate e (N+1) k)`

against the CORRECTED NON-UNIFORM GRADED rate `gradedRate e M k =
C(e)/(⌊√M⌋·jdist(M,k)²)` (`jdist M k = min(k+1, M−k)`, `C(e) = 4(e+1)+4·Le e`).
Everything that CONSUMES this estimate — the graded rate, its nonnegativity, the
p-series majorant, the vanishing finite sum, the packaging into
`RealPerCellBudget`, and the off-diagonal bridges — is PROVED in `ChebOrthoGraded`.

This module supplies the GENUINE per-cell content in two cases.

## What is PROVED here (axiom-clean, GENUINE new content)

  * A reusable **two-sided value-bound calculus** `AbsLeRat x b := leRat x b ∧
    leRat (neg x) b` (`|lim x| ≤ b`) with constructors:
      - `AbsLeRat.ofQ'` (`|q| ≤ b`), `AbsLeRat.add`, `AbsLeRat.mono`,
      - `AbsLeRat.smul_nonneg` (scale by a NONNEGATIVE rational),
      - `AbsLeRat.of_nonneg_leRat` (a NONNEGATIVE `CReal` with `leRat r b`,
        `0 ≤ b`, is two-sidedly `≤ b`),
      - `AbsLeRat.mul_ofQ'_nonneg` (product of a NONNEGATIVE `CReal` `≤ Br` with a
        rational `c`, `|c| ≤ Bc`, is two-sidedly `≤ Br·Bc`).
    These are the transitivity-free sound building blocks for value-level bounds.

  * `bdyRadical_AbsLeRat` / `nodeWeight_AbsLeRat` — the genuine cell radicals
    `√(1−b_k²)`, `√(1−x_k²)` are two-sidedly `≤ c` for any rational `c > 0` with the
    radicand `≤ c²` (they are NONNEGATIVE, so the lower side is free).

  * `gbracket_abs_le` — the rational bracket bound `|B_e(x)| ≤ 2` on `[−1,1]`
    (`|U_{e−1}/e| ≤ 1`, `|U_{e+1}/(e+2)| ≤ 1` via `ChebyshevU.absU_le`).

  * **`boundary_cell_bound`** — the DIRECT two-sided per-cell estimate at the two
    BOUNDARY cells `k ∈ {0, M−1}` (where `jdist = 1`, rate `= C(e)/⌊√M⌋`).  At
    `k = M−1` the right endpoint `b_M = 1` kills `GsampR(M)` (`czero` radical), so
    `cellAdjR = orthTerm(M−1) + (0 − GsampR(M−1))`; both surviving pieces live near
    `±1` where the radicand is `≤ 4/M ≤ (2/⌊√M⌋)²`, giving
    `|orthTerm| ≤ (2/M)(e+1)(2/⌊√M⌋)` and `|GsampR(M−1)| ≤ ½(2/⌊√M⌋)·2 = 2/⌊√M⌋`,
    hence `|cellAdjR| ≤ (4(e+1)+2)/⌊√M⌋ ≤ C(e)/⌊√M⌋`.  Fully rigorous, NO
    interior cancellation needed.  The `k = 0` boundary cell is symmetric.

## What is NAMED-open (precisely — the INTERIOR second-order graded remainder)

  * `InteriorGradedRemainder e he` — the per-cell two-sided estimate at the INTERIOR
    cells `1 ≤ k ≤ M−2`, against `gradedRate = C(e)/(⌊√M⌋·j²)`, `j = jdist`.  Its
    EXACT structure is fully assembled from the PROVED pieces
    `cellAdjR = orthTerm + gIncrR`, `ChebOrthoRemainder.gIncr_pdiff_split`
    (product-difference split into the two finite-difference legs),
    `ChebOrthoRemainder.radSq_diff_equiv` (`s_+²−s_-² = ofQ'(1−b_{k+1}²) −
    ofQ'(1−b_k²)`, exact `= −4x_kδ`), and `ChebOrthoCancel.leading_cancellation`
    (the leading midpoint combination EXACTLY cancels `orthTerm`).  After the exact
    cancellation `cellAdjR` is the SECOND-ORDER centered-difference remainder; the
    SINGLE remaining genuine content is the NUMERIC assembly bounding it by
    `C(e)·δ^{3/2}/j^{3/2} ≤ C(e)/(⌊√M⌋·j²)`, which needs (i) the √-Hölder modulus
    `SqrtSubadd.holder_oneMinusSq` for the radical leg, (ii) the Lipschitz scale
    `Le e` for the bracket leg, and (iii) a CONSTRUCTIVE LOWER bound on `s_++s_-`
    (`≥ √(jδ)`-type) to control the reciprocal in the `s_+−s_- = −4x_kδ/(s_++s_-)`
    radical leg.  Recorded precisely, NOT faked.

The combined per-cell estimate `GradedPerCellBound` is then `boundary_cell_bound`
on the two boundary cells and `InteriorGradedRemainder` on the interior; the
even-order limit + the full off-diagonal closure are stated CONDITIONAL on the
single interior remainder (`offdiag_closed_of_interior`), and become UNCONDITIONAL
the moment `InteriorGradedRemainder` holds.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file
(`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoGraded
import YMGap.Continuum.ChebOrthoRemainder
import YMGap.Continuum.ChebOrthoCancel
import YMGap.Continuum.ChebOrthoMidpoint
import YMGap.Continuum.ChebUDClosure

namespace YMGap.Continuum.ChebOrthoGradedClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ChebOrthoOffDiag
open YMGap.Continuum.ChebOrthoEvenFTC
open YMGap.Continuum.ChebOrthoMidpoint
open YMGap.Continuum.ChebOrthoMidpointCore
open YMGap.Continuum.ChebOrthoMidpointEst
open YMGap.Continuum.ChebOrthoGraded

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The two-sided value-bound calculus `AbsLeRat` -/

/-- **Two-sided value bound** `AbsLeRat x b := leRat x b ∧ leRat (neg x) b`,
i.e. `−b ≤ lim x ≤ b` (`|lim x| ≤ b`).  The transitivity-free sound packaging of a
symmetric value bound. -/
def AbsLeRat (x : CReal) (b : Q') : Prop :=
  CReal.leRat x b ∧ CReal.leRat (CReal.neg x) b

/-- Monotone in the bound. -/
theorem AbsLeRat.mono {x : CReal} {a b : Q'} (h : AbsLeRat x a) (hab : a ≤ b) :
    AbsLeRat x b :=
  ⟨CReal.leRat_mono h.1 hab, CReal.leRat_mono h.2 hab⟩

/-- `AbsLeRat` is symmetric under negation. -/
theorem AbsLeRat.neg {x : CReal} {b : Q'} (h : AbsLeRat x b) : AbsLeRat (CReal.neg x) b := by
  refine ⟨h.2, ?_⟩
  -- neg (neg x) ≈ x pointwise
  have hcong : ∀ n, ((CReal.neg (CReal.neg x)).approx n) ≈ (x.approx n) := by
    intro n
    show (-(-(x.approx n))) ≈ (x.approx n)
    exact Q'.neg_neg_eqv (x.approx n)
  exact CReal.leRat_congr hcong h.1

/-- A rational embeds with its own absolute value as a two-sided bound. -/
theorem AbsLeRat.ofQ' {q b : Q'} (hb1 : q ≤ b) (hb2 : (-q) ≤ b) :
    AbsLeRat (CReal.ofQ' q) b := by
  refine ⟨CReal.leRat_ofQ' hb1, ?_⟩
  -- neg (ofQ' q) = ofQ' (−q)
  have h : CReal.neg (CReal.ofQ' q) = CReal.ofQ' (-q) := CReal.ofQ'_neg q
  rw [h]; exact CReal.leRat_ofQ' hb2

/-- Additivity: `AbsLeRat x a → AbsLeRat y b → AbsLeRat (x+y) (a+b)`. -/
theorem AbsLeRat.add {x y : CReal} {a b : Q'}
    (hx : AbsLeRat x a) (hy : AbsLeRat y b) :
    AbsLeRat (CReal.add x y) (a + b) := by
  refine ⟨CReal.leRat_add hx.1 hy.1, ?_⟩
  -- neg (add x y) ≈ add (neg x) (neg y) (pointwise)
  have hcong : ∀ n, ((CReal.neg (CReal.add x y)).approx n)
      ≈ ((CReal.add (CReal.neg x) (CReal.neg y)).approx n) := by
    intro n
    show (-(x.approx n + y.approx n)) ≈ ((-(x.approx n)) + (-(y.approx n)))
    exact Q'.neg_add_eqv (x.approx n) (y.approx n)
  exact CReal.leRat_congr hcong (CReal.leRat_add hx.2 hy.2)

/-- Scale by a NONNEGATIVE rational: `0 ≤ c → AbsLeRat y b → AbsLeRat (c·y) (c·b)`. -/
theorem AbsLeRat.smul_nonneg {c : Q'} (hc : (0 : Q') ≤ c) {y : CReal} {b : Q'}
    (h : AbsLeRat y b) :
    AbsLeRat (CReal.mul (CReal.ofQ' c) y) (c * b) := by
  refine ⟨CReal.leRat_smul_nonneg hc h.1, ?_⟩
  -- neg (c·y) ≈ c·(neg y) (pointwise, c·(−y_n) = −(c·y_n))
  have hcong : ∀ n, ((CReal.neg (CReal.mul (CReal.ofQ' c) y)).approx n)
      ≈ ((CReal.mul (CReal.ofQ' c) (CReal.neg y)).approx n) := by
    intro n
    show (-(c * y.approx n)) ≈ (c * (-(y.approx n)))
    exact Q'.eqv_symm (Q'.mul_neg_eqv c (y.approx n))
  exact CReal.leRat_congr hcong (CReal.leRat_smul_nonneg hc h.2)

/-- **Lower-control helper.**  From `−B ≤ a + ε` deduce `−a ≤ B + ε` (`Q'`).  The
`neg`-reflection of an additive bound (used to turn a `geRat` lower bound into a
`leRat`-style upper bound on `−a`). -/
theorem neg_le_of_negB_le {a B ε : Q'} (h : (-B) ≤ a + ε) : (-a) ≤ B + ε := by
  -- −(a+ε) ≤ −(−B) = B, then shuffle the ε.
  have h1 : (-(a + ε)) ≤ (-(- B)) := Q'.neg_le_neg h
  have h2 : (-(a + ε)) ≈ ((-a) + (-ε)) := Q'.neg_add_eqv a ε
  have h3 : (-(- B)) ≈ B := Q'.neg_neg_eqv B
  have h4 : ((-a) + (-ε)) ≤ B :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv h2) (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv h3))
  -- (−a) + (−ε) ≤ B  ⟹  −a ≤ B + ε
  have h5 : ((-a) + (-ε)) + ε ≤ B + ε := Q'.add_le_add_right _ _ ε h4
  refine Q'.le_trans' _ _ _ ?_ h5
  -- −a ≈ ((−a) + (−ε)) + ε
  refine Q'.ge_of_eqv ?_
  calc ((-a) + (-ε)) + ε
      ≈ (-a) + ((-ε) + ε) := Q'.add_assoc_eqv _ _ _
    _ ≈ (-a) + (0 : Q') := Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv ε)
    _ ≈ (-a) := QPoly.q_add_zero_eqv _

/-- From `0 ≤ a + d` deduce `−d ≤ a` (`Q'`). -/
theorem neg_le_of_add_nonneg {a d : Q'} (h : (0 : Q') ≤ a + d) : (-d) ≤ a := by
  have h1 : (0 : Q') + (-d) ≤ (a + d) + (-d) := Q'.add_le_add_right _ _ (-d) h
  refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ h1 ?_)
  · exact Q'.ge_of_eqv (QPoly.q_zero_add_eqv (-d))
  · refine Q'.le_of_eqv ?_
    calc (a + d) + (-d)
        ≈ a + (d + (-d)) := Q'.add_assoc_eqv _ _ _
      _ ≈ a + (0 : Q') := Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv d)
      _ ≈ a := QPoly.q_add_zero_eqv _

/-- A NONNEGATIVE `CReal` with a `leRat`-upper bound `b ≥ 0` is two-sidedly `≤ b`:
the lower side `−r ≤ 0 ≤ b` is free from `geRat r 0`. -/
theorem AbsLeRat.of_nonneg_leRat {r : CReal} {b : Q'}
    (hr0 : ExpPos.geRat r 0) (hrb : CReal.leRat r b) (hb : (0 : Q') ≤ b) :
    AbsLeRat r b := by
  refine ⟨hrb, ?_⟩
  -- leRat (neg r) b : eventually −r_n ≤ b + ε.
  intro ε hε
  obtain ⟨N, hN⟩ := hr0 ε hε
  refine ⟨N, fun n hn => ?_⟩
  -- 0 ≤ r_n + ε  ⟹  −r_n ≤ 0 + ε  (neg_le_of_negB_le with B = 0), then ≤ b + ε.
  have h0 : (0 : Q') ≤ r.approx n + ε := hN n hn
  have hnegzero : (-(0 : Q')) ≈ (0 : Q') := by decide
  have hB0 : (-(0 : Q')) ≤ r.approx n + ε :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hnegzero) h0
  have hneg : (-(r.approx n)) ≤ (0 : Q') + ε := neg_le_of_negB_le hB0
  show (-(r.approx n)) ≤ b + ε
  refine Q'.le_trans' _ _ _ hneg ?_
  exact Q'.add_le_add_right (0 : Q') b ε hb

/-- **Product of a NONNEGATIVE `CReal` (`≤ Br`) with a rational (`|c| ≤ Bc`).**
`mul r (ofQ' c)` is two-sidedly `≤ Br·Bc` (`Br, Bc ≥ 0`).  Reduces to the
nonnegative-scale lemma after commuting the product: `r·c = c·r` pointwise; we
bound `|c|·r ≤ Bc·Br`.  Used for `GsampR = ½·s·B`. -/
theorem AbsLeRat.mul_nonneg_ofQ' {r : CReal} {c Br Bc : Q'}
    (hr0 : ExpPos.geRat r 0) (hrB : CReal.leRat r Br)
    (hc1 : c ≤ Bc) (hc2 : (-c) ≤ Bc)
    (hBr : (0 : Q') ≤ Br) (hBc : (0 : Q') ≤ Bc) :
    AbsLeRat (CReal.mul r (CReal.ofQ' c)) (Br * Bc) := by
  -- mul r (ofQ' c) ≈ mul (ofQ' |c|-bounded) ... we bound via approx directly.
  -- r·c two-sided: −(Br·Bc) ≤ r_n·c_n ≤ Br·Bc eventually.
  -- We use: for r ≥ 0 with r ≤ Br, and −Bc ≤ c ≤ Bc, the product r·c ∈ [−Br·Bc, Br·Bc].
  constructor
  · -- leRat (r·c) (Br·Bc)
    intro ε hε
    -- choose δ for the r-slack: need δ with Bc·δ ≤ ε (Bc ≥ 0)
    obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le hBc hε
    obtain ⟨N1, hN1⟩ := hrB δ hδpos
    obtain ⟨N2, hN2⟩ := hr0 δ hδpos
    refine ⟨max N1 N2, fun n hn => ?_⟩
    have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
    have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
    have hub : r.approx n ≤ Br + δ := hN1 n hn1
    have hlb : (0 : Q') ≤ r.approx n + δ := hN2 n hn2
    show (r.approx n * c) ≤ Br * Bc + ε
    -- r_n·c ≤ r_n·Bc (since c ≤ Bc, r_n ≥ −δ … but we need r_n ≥ 0; use 0 ≤ r_n+δ).
    -- Cleaner: r_n·c ≤ (Br+δ)·Bc when 0 ≤ r_n ≤ Br+δ and c ≤ Bc, Bc ≥ 0.
    -- but r_n might be slightly negative (≥ −δ). Use r_n ≤ Br+δ and c ≤ Bc, plus
    -- a lower control. We bound via |r_n·c| ≤ (Br+δ)·Bc using two-sided c.
    -- Use Q'.mul_le_of_bounds: −(Br+δ) ≤ r_n ≤ Br+δ and −Bc ≤ c ≤ Bc.
    have hrlow : (-(Br + δ)) ≤ r.approx n := by
      -- 0 ≤ r_n + δ ⟹ −δ ≤ r_n ⟹ −(Br+δ) ≤ −δ ≤ r_n
      have hmδ : (-δ) ≤ r.approx n := neg_le_of_add_nonneg hlb
      refine Q'.le_trans' _ _ _ ?_ hmδ
      -- −(Br+δ) ≤ −δ since Br ≥ 0
      have hBrδ : δ ≤ Br + δ := by
        refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_zero_add_eqv δ)) ?_
        exact Q'.add_le_add_right (0 : Q') Br δ hBr
      exact Q'.neg_le_neg hBrδ
    have hBrδ0 : (0 : Q') ≤ Br + δ :=
      Q'.le_trans' _ _ _ hBr (Q'.add_le_self_of_nonneg Br δ (Q'.le_of_lt hδpos))
    have hvlow : (-Bc) ≤ c := by
      have := Q'.neg_le_neg hc2  -- −Bc ≤ −(−c)
      exact Q'.le_trans' _ _ _ this (Q'.le_of_eqv (Q'.neg_neg_eqv c))
    have hbnd := Q'.mul_le_of_bounds hBrδ0 hBc hrlow hub hvlow hc1
    -- hbnd : r_n·c ≤ (Br+δ)·Bc
    refine Q'.le_trans' _ _ _ hbnd ?_
    -- (Br+δ)·Bc = Br·Bc + δ·Bc ≤ Br·Bc + ε
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Cheb.add_mul_eqv Br δ Bc)) ?_
    refine Q'.add_le_add_left (Br * Bc) (δ * Bc) ε ?_
    -- δ·Bc ≤ ε  (from Bc·δ ≤ ε)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv δ Bc)) hδ
  · -- leRat (neg (r·c)) (Br·Bc) :  −(r_n·c) ≤ Br·Bc + ε
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le hBc hε
    obtain ⟨N1, hN1⟩ := hrB δ hδpos
    obtain ⟨N2, hN2⟩ := hr0 δ hδpos
    refine ⟨max N1 N2, fun n hn => ?_⟩
    have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
    have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
    have hub : r.approx n ≤ Br + δ := hN1 n hn1
    have hlb : (0 : Q') ≤ r.approx n + δ := hN2 n hn2
    show (-(r.approx n * c)) ≤ Br * Bc + ε
    have hrlow : (-(Br + δ)) ≤ r.approx n := by
      have hmδ : (-δ) ≤ r.approx n := neg_le_of_add_nonneg hlb
      refine Q'.le_trans' _ _ _ ?_ hmδ
      have hBrδ : δ ≤ Br + δ := by
        refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_zero_add_eqv δ)) ?_
        exact Q'.add_le_add_right (0 : Q') Br δ hBr
      exact Q'.neg_le_neg hBrδ
    -- −(r_n·c) = r_n·(−c) ; bound r_n·(−c) ≤ (Br+δ)·Bc with −Bc ≤ −c (=neg hc1) and −c ≤ Bc (hc2).
    have hBrδ0 : (0 : Q') ≤ Br + δ :=
      Q'.le_trans' _ _ _ hBr (Q'.add_le_self_of_nonneg Br δ (Q'.le_of_lt hδpos))
    have hvlow : (-Bc) ≤ (-c) := Q'.neg_le_neg hc1
    have hbnd := Q'.mul_le_of_bounds hBrδ0 hBc hrlow hub hvlow hc2
    -- hbnd : r_n·(−c) ≤ (Br+δ)·Bc
    have hrewrite : (-(r.approx n * c)) ≈ (r.approx n * (-c)) :=
      Q'.eqv_symm (Q'.mul_neg_eqv (r.approx n) c)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hrewrite) ?_
    refine Q'.le_trans' _ _ _ hbnd ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Cheb.add_mul_eqv Br δ Bc)) ?_
    refine Q'.add_le_add_left (Br * Bc) (δ * Bc) ε ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv δ Bc)) hδ

/-- `AbsLeRat` transfers across pointwise-`eqv` approximations. -/
theorem AbsLeRat.congr {x y : CReal} {b : Q'}
    (h : ∀ n, (x.approx n) ≈ (y.approx n)) (hy : AbsLeRat y b) : AbsLeRat x b := by
  refine ⟨CReal.leRat_congr h hy.1, ?_⟩
  have hneg : ∀ n, ((CReal.neg x).approx n) ≈ ((CReal.neg y).approx n) := by
    intro n
    show (-(x.approx n)) ≈ (-(y.approx n))
    exact Q'.neg_eqv_congr _ _ (h n)
  exact CReal.leRat_congr hneg hy.2

/-- Product `mul (ofQ' c) r` (rational first) of a NONNEGATIVE `CReal` `r ≤ Br`:
two-sidedly `≤ Bc·Br`.  Commutes to `mul_nonneg_ofQ'`. -/
theorem AbsLeRat.ofQ'_mul_nonneg {r : CReal} {c Br Bc : Q'}
    (hr0 : ExpPos.geRat r 0) (hrB : CReal.leRat r Br)
    (hc1 : c ≤ Bc) (hc2 : (-c) ≤ Bc)
    (hBr : (0 : Q') ≤ Br) (hBc : (0 : Q') ≤ Bc) :
    AbsLeRat (CReal.mul (CReal.ofQ' c) r) (Bc * Br) := by
  -- mul (ofQ' c) r ≈ mul r (ofQ' c) pointwise
  have hcomm : ∀ n, ((CReal.mul (CReal.ofQ' c) r).approx n)
      ≈ ((CReal.mul r (CReal.ofQ' c)).approx n) := by
    intro n
    show (c * r.approx n) ≈ (r.approx n * c)
    exact Q'.mul_comm_eqv c (r.approx n)
  -- Bc·Br = Br·Bc
  have hb : (Bc * Br) ≈ (Br * Bc) := Q'.mul_comm_eqv Bc Br
  refine AbsLeRat.mono ?_ (Q'.ge_of_eqv hb)
  exact AbsLeRat.congr hcomm
    (AbsLeRat.mul_nonneg_ofQ' hr0 hrB hc1 hc2 hBr hBc)

/-! ## 1. The rational bracket bound `|B_e(x)| ≤ 2` on `[−1,1]` -/

/-- A single bracket term `U_m(x)/d ≤ 1` and `≥ −1` (`d ≥ m+1 > 0`) when
`|U_m(x)| ≤ m+1 ≤ d`.  We use it with `m = e−1, d = e` and `m = e+1, d = e+2`:
`mkPos (U_m.num) (U_m.den · d) = U_m(x)/d`, two-sidedly `≤ 1` since `|U_m| ≤ d`. -/
theorem bracketTerm_abs_le (m d : Nat) (hd : 0 < d) (x : Q')
    (hx1 : x ≤ 1) (hxm1 : (-1 : Q') ≤ x) (hdm : m + 1 ≤ d) :
    Q'.mkPos (Cheb.U m x).num ((Cheb.U m x).den * d)
        (Nat.mul_pos (Cheb.U m x).den_pos hd) ≤ (1 : Q')
      ∧ (-(1 : Q')) ≤ Q'.mkPos (Cheb.U m x).num ((Cheb.U m x).den * d)
        (Nat.mul_pos (Cheb.U m x).den_pos hd) := by
  obtain ⟨hub, hlb⟩ := ChebU.absU_le m x hx1 hxm1
  -- hub : U_m(x) ≤ ofNat (m+1) ;  i.e. U.num · 1 ≤ (m+1) · U.den
  -- hlb : −ofNat(m+1) ≤ U_m(x)
  -- cross-mult of U ≤ ofNat(m+1):
  have hub' : (Cheb.U m x).num ≤ ((m + 1 : Nat) : Int) * ((Cheb.U m x).den : Int) := by
    have hh : (Cheb.U m x).num * ((Q'.ofNat (m + 1)).den : Int)
        ≤ (Q'.ofNat (m + 1)).num * ((Cheb.U m x).den : Int) := hub
    have hd1 : ((Q'.ofNat (m + 1)).den : Int) = 1 := rfl
    have hn1 : (Q'.ofNat (m + 1)).num = ((m + 1 : Nat) : Int) := rfl
    rw [hd1, hn1, Int.mul_one] at hh; exact hh
  have hlb' : (-(((m + 1 : Nat) : Int))) * ((Cheb.U m x).den : Int) ≤ (Cheb.U m x).num := by
    have hh : (Q'.ofNat (m + 1) |> Neg.neg).num * ((Cheb.U m x).den : Int)
        ≤ (Cheb.U m x).num * ((Q'.ofNat (m + 1) |> Neg.neg).den : Int) := hlb
    have hd1 : ((Q'.ofNat (m + 1) |> Neg.neg).den : Int) = 1 := rfl
    have hn1 : (Q'.ofNat (m + 1) |> Neg.neg).num = -(((m + 1 : Nat) : Int)) := rfl
    rw [hd1, hn1, Int.mul_one] at hh; exact hh
  have hdmI : ((m + 1 : Nat) : Int) ≤ (d : Int) := by exact_mod_cast hdm
  have hdenpos : (0 : Int) ≤ ((Cheb.U m x).den : Int) := Int.natCast_nonneg _
  constructor
  · -- mkPos p (q·d) ≤ 1  ⟺  p · 1 ≤ 1 · (q·d) = q·d   (p = U.num, q = U.den)
    show (Q'.mkPos (Cheb.U m x).num ((Cheb.U m x).den * d)
        (Nat.mul_pos (Cheb.U m x).den_pos hd)).num * ((1 : Q').den : Int)
      ≤ (1 : Q').num * ((Q'.mkPos (Cheb.U m x).num ((Cheb.U m x).den * d)
        (Nat.mul_pos (Cheb.U m x).den_pos hd)).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]
    have hd1 : ((1 : Q').den : Int) = 1 := rfl
    have hn1 : (1 : Q').num = 1 := rfl
    rw [hd1, hn1, Int.mul_one, Int.one_mul]
    have hcast : (((Cheb.U m x).den * d : Nat) : Int)
        = ((Cheb.U m x).den : Int) * (d : Int) := by push_cast; rfl
    rw [hcast]
    -- U.num ≤ (m+1)·U.den ≤ d·U.den = U.den·d
    refine Int.le_trans hub' ?_
    rw [Int.mul_comm ((Cheb.U m x).den : Int) (d : Int)]
    exact Int.mul_le_mul_of_nonneg_right hdmI hdenpos
  · -- −1 ≤ mkPos p (q·d)  ⟺  (−1)·(q·d) ≤ p · 1
    show ((-(1 : Q')).num) * ((Q'.mkPos (Cheb.U m x).num ((Cheb.U m x).den * d)
        (Nat.mul_pos (Cheb.U m x).den_pos hd)).den : Int)
      ≤ (Q'.mkPos (Cheb.U m x).num ((Cheb.U m x).den * d)
        (Nat.mul_pos (Cheb.U m x).den_pos hd)).num * ((-(1 : Q')).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]
    have hd1 : ((-(1 : Q')).den : Int) = 1 := rfl
    have hn1 : (-(1 : Q')).num = -1 := rfl
    rw [hd1, hn1, Int.mul_one]
    have hcast : (((Cheb.U m x).den * d : Nat) : Int)
        = ((Cheb.U m x).den : Int) * (d : Int) := by push_cast; rfl
    rw [hcast]
    -- (−1)·(U.den·d) ≤ U.num.  We have −(m+1)·U.den ≤ U.num and (m+1) ≤ d.
    refine Int.le_trans ?_ hlb'
    -- −1·(U.den·d) = −(U.den·d) ≤ −((m+1)·U.den) = −(m+1)·U.den
    have hge : ((m + 1 : Nat) : Int) * ((Cheb.U m x).den : Int)
        ≤ (d : Int) * ((Cheb.U m x).den : Int) :=
      Int.mul_le_mul_of_nonneg_right hdmI hdenpos
    -- so −(d·U.den) ≤ −((m+1)·U.den)
    have hneg : -((d : Int) * ((Cheb.U m x).den : Int))
        ≤ -(((m + 1 : Nat) : Int) * ((Cheb.U m x).den : Int)) := Int.neg_le_neg hge
    -- rewrite LHS  (−1)·(U.den·d) = −(U.den·d) = −(d·U.den)
    have hL : (-1 : Int) * (((Cheb.U m x).den : Int) * (d : Int))
        = -((d : Int) * ((Cheb.U m x).den : Int)) := by
      rw [Int.neg_one_mul, Int.mul_comm ((Cheb.U m x).den : Int) (d : Int)]
    -- rewrite RHS  −(m+1)·U.den = −((m+1)·U.den)
    have hR : (-(((m + 1 : Nat) : Int))) * ((Cheb.U m x).den : Int)
        = -(((m + 1 : Nat) : Int) * ((Cheb.U m x).den : Int)) := by
      rw [Int.neg_mul]
    rw [hL, hR]; exact hneg

/-- **The rational bracket bound `|B_e(x)| ≤ 2` on `[−1,1]`** (for `e ≥ 1`).
`B_e(x) = U_{e−1}(x)/e − U_{e+1}(x)/(e+2)`; each term is `≤ 1` and `≥ −1`
(`bracketTerm_abs_le`, `|U_{e−1}| ≤ e`, `|U_{e+1}| ≤ e+2`), so the bracket is two
-sidedly bounded by `2`. -/
theorem gbracket_abs_le (e : Nat) (he : 0 < e) (x : Q')
    (hx1 : x ≤ 1) (hxm1 : (-1 : Q') ≤ x) :
    Gbracket e he x ≤ (2 : Q') ∧ (-(Gbracket e he x)) ≤ (2 : Q') := by
  -- e ≥ 1 ⟹ e−1+1 = e ; (e+1)+1 = e+2.
  have hT1 := bracketTerm_abs_le (e - 1) e he x hx1 hxm1 (by omega)
  have hT2 := bracketTerm_abs_le (e + 1) (e + 2) (by omega) x hx1 hxm1 (by omega)
  -- Gbracket = T1 + (−T2)
  unfold Gbracket
  -- name the two bracket terms (hT1/hT2 refer to them).
  generalize hT1def : Q'.mkPos (Cheb.U (e - 1) x).num ((Cheb.U (e - 1) x).den * e)
    (Nat.mul_pos (Cheb.U (e - 1) x).den_pos he) = T1 at hT1 ⊢
  generalize hT2def : Q'.mkPos (Cheb.U (e + 1) x).num ((Cheb.U (e + 1) x).den * (e + 2))
    (Nat.mul_pos (Cheb.U (e + 1) x).den_pos (by omega)) = T2 at hT2 ⊢
  constructor
  · -- T1 + (−T2) ≤ 1 + 1 = 2 ;  from −1 ≤ T2 deduce −T2 ≤ 1.
    have hnegT2 : (-T2) ≤ (1 : Q') := by
      have := Q'.neg_le_neg hT2.2  -- −T2 ≤ −(−1)
      exact Q'.le_trans' _ _ _ this (Q'.le_of_eqv (Q'.neg_neg_eqv (1 : Q')))
    have hstep : T1 + (-T2) ≤ (1 : Q') + (1 : Q') := Q'.add_le_add hT1.1 hnegT2
    refine Q'.le_trans' _ _ _ hstep ?_
    exact Q'.le_of_eqv (by decide : ((1 : Q') + (1 : Q')) ≈ (2 : Q'))
  · -- −(T1 + (−T2)) = (−T1) + T2 ≤ 1 + 1 = 2
    have hrw : (-(T1 + (-T2))) ≈ ((-T1) + T2) := by
      refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv T1 (-T2)) ?_
      exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv T2)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hrw) ?_
    have hnegT1 : (-T1) ≤ (1 : Q') := by
      have := Q'.neg_le_neg hT1.2  -- −T1 ≤ −(−1)
      exact Q'.le_trans' _ _ _ this (Q'.le_of_eqv (Q'.neg_neg_eqv (1 : Q')))
    have hstep : (-T1) + T2 ≤ (1 : Q') + (1 : Q') := Q'.add_le_add hnegT1 hT2.1
    refine Q'.le_trans' _ _ _ hstep ?_
    exact Q'.le_of_eqv (by decide : ((1 : Q') + (1 : Q')) ≈ (2 : Q'))

/-! ## 2. The genuine cell radicals as two-sided value bounds -/

/-- **`bdyRadical n k ≥ 0`** (nonnegative): it is a `sqrtFrom` (≥ lower witness `> 0`)
for interior `0 < k < n`, and `czero` at the endpoints. -/
theorem bdyRadical_geRat0 (n : Nat) (hn : 0 < n) (k : Nat) :
    ExpPos.geRat (bdyRadical n hn k) 0 := by
  unfold bdyRadical
  by_cases hk0 : 0 < k
  · rw [dif_pos hk0]
    by_cases hkn : k < n
    · rw [dif_pos hkn]
      refine ExpPos.geRat_of_eventually ⟨0, fun m _ => ?_⟩
      show (0 : Q') ≤ (CReal.sqrtFrom (bdyOneMinusSq n k hn hk0 hkn)
        (SemicircleIntegral.nodeLB n hn) (bdyOneMinusSq_pos hn hk0 hkn)
        (SemicircleIntegral.nodeLB_pos hn) (bdyLB_sq_le hn hk0 hkn)).approx m
      rw [CReal.sqrtFrom_approx]
      exact Q'.le_trans' _ _ _ (Q'.le_of_lt (SemicircleIntegral.nodeLB_pos hn))
        (CReal.heronSeq_lb (bdyOneMinusSq n k hn hk0 hkn) (SemicircleIntegral.nodeLB n hn)
          (bdyOneMinusSq_pos hn hk0 hkn) (SemicircleIntegral.nodeLB_pos hn)
          (bdyLB_sq_le hn hk0 hkn) m)
    · rw [dif_neg hkn]; exact SumOfSquares.geRat_czero
  · rw [dif_neg hk0]; exact SumOfSquares.geRat_czero

/-- **The cell radical as a two-sided value bound.**  For an INTERIOR cell
`0 < k < n` and any rational `c > 0` with `1 − b_k² ≤ c²`, the genuine radical
`√(1 − b_k²)` is two-sidedly `≤ c` (nonnegative, so the lower side is free). -/
theorem bdyRadical_AbsLeRat (n : Nat) (hn : 0 < n) (k : Nat) (hk0 : 0 < k) (hkn : k < n)
    (c : Q') (hc : (0 : Q') < c) (hac : bdyOneMinusSq n k hn hk0 hkn ≤ c * c) :
    AbsLeRat (bdyRadical n hn k) c :=
  AbsLeRat.of_nonneg_leRat (bdyRadical_geRat0 n hn k)
    (ChebOrthoCancel.bdyRadical_leRat n hn k hk0 hkn c hc hac)
    (Q'.le_of_lt hc)

/-- **The node weight as a two-sided value bound.**  For `k < n` and any rational
`c > 0` with `1 − x_k² ≤ c²`, the genuine node weight `√(1 − x_k²)` is two-sidedly
`≤ c` (nonnegative). -/
theorem nodeWeight_AbsLeRat (n : Nat) (hn : 0 < n) (k : Nat) (hk : k < n)
    (c : Q') (hc : (0 : Q') < c)
    (hac : SemicircleIntegral.oneMinusSqNode n k hn hk ≤ c * c) :
    AbsLeRat (SemicircleIntegral.nodeWeight n hn k) c := by
  refine AbsLeRat.of_nonneg_leRat (SemicircleIntegral.nodeWeight_nonneg n hn k) ?_
    (Q'.le_of_lt hc)
  -- leRat (nodeWeight) c via sqrtFrom_leRat_of_sq
  unfold SemicircleIntegral.nodeWeight
  rw [dif_pos hk]
  exact CReal.sqrtFrom_leRat_of_sq (SemicircleIntegral.oneMinusSqNode n k hn hk)
    (SemicircleIntegral.nodeLB n hn) (SemicircleIntegral.oneMinusSqNode_pos hn hk)
    (SemicircleIntegral.nodeLB_pos hn) (SemicircleIntegral.nodeLB_sq_le hn hk) c hc hac

/-- Square expansion `(a − b)·(a − b) = a·a − 2·(a·b) + b·b` over `Int` (core ring
lemmas; used to make the boundary radicand bounds `omega`-closable with `a·b`,
`a·a`, `b·b` as opaque atoms). -/
theorem int_sq_expand (a b : Int) :
    (a - b) * (a - b) = a * a - 2 * (a * b) + b * b := by
  have h1 : (a - b) * (a - b) = a * (a - b) - b * (a - b) := Int.sub_mul a b (a - b)
  have h2 : a * (a - b) = a * a - a * b := Int.mul_sub a a b
  have h3 : b * (a - b) = b * a - b * b := Int.mul_sub b a b
  have h4 : b * a = a * b := Int.mul_comm b a
  rw [h1, h2, h3, h4]; omega

/-! ## 2b. Boundary radicand bound: `mkPos N (M²) ≤ (2/⌊√M⌋)²` when `N ≤ 4M` -/

/-- The boundary radical-bound witness `cBdy M := 2/⌊√M⌋`. -/
def cBdy (M : Nat) (hM : 0 < M) : Q' := Q'.mkPos 2 (isqrt M) (isqrt_pos hM)

theorem cBdy_pos (M : Nat) (hM : 0 < M) : (0 : Q') < cBdy M hM := by
  show (0 : Int) * ((cBdy M hM).den : Int) < (cBdy M hM).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  show (0 : Int) < (Q'.mkPos 2 (isqrt M) (isqrt_pos hM)).num
  rw [Q'.mkPos_num]; decide

/-- **The boundary radicand bound.**  Any radicand `mkPos N (M·M)` with
`0 ≤ N ≤ 4·M` is `≤ (cBdy M)² = (2/⌊√M⌋)²`.  Cross-multiplying:
`N · ⌊√M⌋² ≤ 4 · M²`, from `N ≤ 4M` and `⌊√M⌋² ≤ M`. -/
theorem radicand_le_cBdy_sq (M : Nat) (hM : 0 < M) (N : Int)
    (hN0 : (0 : Int) ≤ N) (hN : N ≤ 4 * (M : Int)) :
    Q'.mkPos N (M * M) (Nat.mul_pos hM hM) ≤ cBdy M hM * cBdy M hM := by
  -- cBdy·cBdy = mkPos 2 t · mkPos 2 t : num = 4, den (cast) = t·t  (t = isqrt M)
  show (Q'.mkPos N (M * M) (Nat.mul_pos hM hM)).num * ((cBdy M hM * cBdy M hM).den : Int)
      ≤ (cBdy M hM * cBdy M hM).num * ((Q'.mkPos N (M * M) (Nat.mul_pos hM hM)).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]
  have hcnum : (cBdy M hM * cBdy M hM).num = (4 : Int) := by
    show (cBdy M hM).num * (cBdy M hM).num = 4
    show (Q'.mkPos 2 (isqrt M) (isqrt_pos hM)).num * (Q'.mkPos 2 (isqrt M) (isqrt_pos hM)).num = 4
    rw [Q'.mkPos_num]; decide
  have hcden : ((cBdy M hM * cBdy M hM).den : Int)
      = ((isqrt M : Nat) : Int) * ((isqrt M : Nat) : Int) := by
    rw [Q'.mul_den_cast]
    show ((cBdy M hM).den : Int) * ((cBdy M hM).den : Int)
        = ((isqrt M : Nat) : Int) * ((isqrt M : Nat) : Int)
    show ((Q'.mkPos 2 (isqrt M) (isqrt_pos hM)).den : Int)
          * ((Q'.mkPos 2 (isqrt M) (isqrt_pos hM)).den : Int)
        = ((isqrt M : Nat) : Int) * ((isqrt M : Nat) : Int)
    rw [Q'.mkPos_den]
  rw [hcnum, hcden]
  -- goal: N · (t·t) ≤ 4 · (M·M)   (t = isqrt M)
  have hMMcast : (((M * M : Nat)) : Int) = (M : Int) * (M : Int) := by push_cast; rfl
  rw [hMMcast]
  -- t² ≤ M  and  N ≤ 4M, N ≥ 0
  have htsq : ((isqrt M : Nat) : Int) * ((isqrt M : Nat) : Int) ≤ (M : Int) := by
    have := isqrt_sq_le M
    exact_mod_cast this
  have ht0 : (0 : Int) ≤ ((isqrt M : Nat) : Int) * ((isqrt M : Nat) : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  -- N · t² ≤ N · M  (N ≥ 0)   and  N · M ≤ 4M · M = 4·(M·M)
  calc N * (((isqrt M : Nat) : Int) * ((isqrt M : Nat) : Int))
      ≤ N * (M : Int) := Int.mul_le_mul_of_nonneg_left htsq hN0
    _ ≤ (4 * (M : Int)) * (M : Int) :=
        Int.mul_le_mul_of_nonneg_right hN (Int.natCast_nonneg M)
    _ = 4 * ((M : Int) * (M : Int)) := Int.mul_assoc 4 (M : Int) (M : Int)

/-! ## 3. Two-sided value bounds on `orthTerm` and `GsampR` -/

/-- `|U_e(x_k)| ≤ ofNat (e+1)` at the midpoint node (two-sided, rational). -/
theorem uNode_abs_le (e M : Nat) (hM : 0 < M) (k : Nat) (hk : k < M) :
    uNode e M hM k ≤ Q'.ofNat (e + 1) ∧ (-(Q'.ofNat (e + 1))) ≤ uNode e M hM k := by
  have hx1 := RiemannSOS.node_hi M hM k hk
  have hxm1 := RiemannSOS.node_lo M hM k
  exact ChebOrthoCancel.uNode_abs_le e (RiemannSOS.uniformMidpoint M hM k) hx1 hxm1

/-- **Two-sided value bound on `orthTerm`.**  For `k < M`, with a rational
`cw > 0` bounding the node weight (`1 − x_k² ≤ cw²`),
`AbsLeRat (orthTerm e M k) (lebW M · (ofNat(e+1) · cw))`. -/
theorem orthTerm_AbsLeRat (e M : Nat) (hM : 0 < M) (k : Nat) (hk : k < M)
    (cw : Q') (hcw : (0 : Q') < cw)
    (haw : SemicircleIntegral.oneMinusSqNode M k hM hk ≤ cw * cw) :
    AbsLeRat (orthTerm e M hM k) (SemicircleIntegral.lebW M hM * (Q'.ofNat (e + 1) * cw)) := by
  -- orthTerm = ofQ'(lebW) · (ofQ'(uNode) · nodeWeight)
  -- inner : AbsLeRat (ofQ'(uNode) · nodeWeight) (ofNat(e+1) · cw)
  have hw := nodeWeight_AbsLeRat M hM k hk cw hcw haw
  obtain ⟨hu1, hu2⟩ := uNode_abs_le e M hM k hk
  have hofNatpos : (0 : Q') ≤ Q'.ofNat (e + 1) := by
    rw [Q'.zero_le_iff_num_nonneg]
    show (0 : Int) ≤ (Q'.ofNat (e + 1)).num
    exact Int.natCast_nonneg _
  have hinner : AbsLeRat (CReal.mul (CReal.ofQ' (uNode e M hM k))
      (SemicircleIntegral.nodeWeight M hM k)) (Q'.ofNat (e + 1) * cw) := by
    -- ofQ'_mul_nonneg with c = uNode, r = nodeWeight, Bc = ofNat(e+1), Br = cw
    -- need hc2 : −uNode ≤ ofNat(e+1)  from hu2 : −ofNat(e+1) ≤ uNode
    have hu2' : (-(uNode e M hM k)) ≤ Q'.ofNat (e + 1) := by
      have := Q'.neg_le_neg hu2  -- −uNode ≤ −(−ofNat)
      exact Q'.le_trans' _ _ _ this (Q'.le_of_eqv (Q'.neg_neg_eqv (Q'.ofNat (e + 1))))
    refine AbsLeRat.ofQ'_mul_nonneg (SemicircleIntegral.nodeWeight_nonneg M hM k) ?_
      hu1 hu2' (Q'.le_of_lt hcw) hofNatpos
    -- leRat (nodeWeight) cw
    exact (nodeWeight_AbsLeRat M hM k hk cw hcw haw).1
  -- scale by lebW ≥ 0
  show AbsLeRat (CReal.mul (CReal.ofQ' (SemicircleIntegral.lebW M hM))
      (CReal.mul (CReal.ofQ' (uNode e M hM k)) (SemicircleIntegral.nodeWeight M hM k)))
      (SemicircleIntegral.lebW M hM * (Q'.ofNat (e + 1) * cw))
  exact AbsLeRat.smul_nonneg (SemicircleIntegral.lebW_nonneg hM) hinner

/-- **Two-sided value bound on `GsampR`.**  For an INTERIOR sample `0 < k < M`,
with a rational `cs > 0` bounding the cell radical (`1 − b_k² ≤ cs²`),
`AbsLeRat (GsampR e he M k) (½ · (cs · 2))`.  (The bracket is `|B_e| ≤ 2`.) -/
theorem GsampR_AbsLeRat (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat)
    (hk0 : 0 < k) (hkn : k < M)
    (cs : Q') (hcs : (0 : Q') < cs)
    (hac : bdyOneMinusSq M k hM hk0 hkn ≤ cs * cs) :
    AbsLeRat (GsampR e he M hM k) (Q'.mkPos 1 2 (by decide) * (cs * (2 : Q'))) := by
  -- GsampR = ofQ'(½) · (bdyRadical · ofQ'(Gbracket))
  -- bdyPoint M k is in [−1,1]? we only need the bracket bound which needs x∈[−1,1].
  -- b_k = (2k − M)/M ∈ [−1,1] for 0 ≤ k ≤ M.
  have hb1 : bdyPoint M hM k ≤ (1 : Q') := by
    show (bdyPoint M hM k).num * ((1 : Q').den : Int) ≤ (1 : Q').num * ((bdyPoint M hM k).den : Int)
    show (Q'.mkPos (2 * (k : Int) - (M : Int)) M hM).num * ((1 : Q').den : Int)
        ≤ (1 : Q').num * ((Q'.mkPos (2 * (k : Int) - (M : Int)) M hM).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]
    have hd1 : ((1 : Q').den : Int) = 1 := rfl
    have hn1 : (1 : Q').num = 1 := rfl
    rw [hd1, hn1, Int.mul_one, Int.one_mul]
    have hkM : (k : Int) ≤ (M : Int) := by exact_mod_cast (Nat.le_of_lt hkn)
    have : (0 : Int) ≤ (M : Int) := Int.natCast_nonneg _
    omega
  have hbm1 : (-1 : Q') ≤ bdyPoint M hM k := by
    show ((-1 : Q').num) * ((bdyPoint M hM k).den : Int)
        ≤ (bdyPoint M hM k).num * ((-1 : Q').den : Int)
    show ((-1 : Q').num) * ((Q'.mkPos (2 * (k : Int) - (M : Int)) M hM).den : Int)
        ≤ (Q'.mkPos (2 * (k : Int) - (M : Int)) M hM).num * ((-1 : Q').den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]
    have hd1 : ((-1 : Q').den : Int) = 1 := rfl
    have hn1 : (-1 : Q').num = -1 := rfl
    rw [hd1, hn1, Int.mul_one]
    have hk0' : (0 : Int) ≤ (k : Int) := Int.natCast_nonneg _
    omega
  obtain ⟨hB1, hB2⟩ := gbracket_abs_le e he (bdyPoint M hM k) hb1 hbm1
  -- inner : AbsLeRat (bdyRadical · ofQ'(Gbracket)) (cs · 2)
  have hrad0 := bdyRadical_geRat0 M hM k
  have hradB := (bdyRadical_AbsLeRat M hM k hk0 hkn cs hcs hac).1
  have hinner : AbsLeRat (CReal.mul (bdyRadical M hM k)
      (CReal.ofQ' (Gbracket e he (bdyPoint M hM k)))) (cs * (2 : Q')) := by
    refine AbsLeRat.mul_nonneg_ofQ' hrad0 hradB hB1 hB2 (Q'.le_of_lt hcs) (by decide)
  -- scale by ½ ≥ 0
  show AbsLeRat (CReal.mul (CReal.ofQ' (Q'.mkPos 1 2 (by decide)))
      (CReal.mul (bdyRadical M hM k) (CReal.ofQ' (Gbracket e he (bdyPoint M hM k)))))
      (Q'.mkPos 1 2 (by decide) * (cs * (2 : Q')))
  refine AbsLeRat.smul_nonneg ?_ hinner
  show (0 : Q') ≤ Q'.mkPos 1 2 (by decide)
  decide

/-- A `CReal` whose approximations are all `≈ 0` is two-sidedly `≤ 0`. -/
theorem AbsLeRat_zero_of_approx_zero {x : CReal} (h : ∀ p, (x.approx p) ≈ (0 : Q')) :
    AbsLeRat x 0 := by
  constructor
  · refine CReal.leRat_of_eventually ⟨0, fun n _ => ?_⟩
    exact Q'.le_of_eqv (h n)
  · refine CReal.leRat_of_eventually ⟨0, fun n _ => ?_⟩
    show (-(x.approx n)) ≤ (0 : Q')
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (h n)) ?_
    decide

/-- **The endpoint sample is two-sidedly `≤ 0`.**  For `k = 0` or `k = M`, the cell
radical is `czero`, so `GsampR ≈ 0` pointwise (`GsampR_endpoint_approx_zero`). -/
theorem GsampR_endpoint_AbsLeRat (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat)
    (hk : k = 0 ∨ k = M) : AbsLeRat (GsampR e he M hM k) 0 :=
  AbsLeRat_zero_of_approx_zero (fun p => GsampR_endpoint_approx_zero e he M hM k hk p)

/-! ## 4. The boundary-cell per-cell rate comparisons (pure `Q'`) -/

/-- The `orthTerm` boundary bound simplifies: `lebW·(ofNat(e+1)·cBdy) ≤
4(e+1)/⌊√M⌋`.  `lebW·(ofNat(e+1)·cBdy) = 4(e+1)/(M·⌊√M⌋) ≤ 4(e+1)/⌊√M⌋` (`M ≥ 1`). -/
theorem orthBound_le (e M : Nat) (hM : 0 < M) :
    SemicircleIntegral.lebW M hM * (Q'.ofNat (e + 1) * cBdy M hM)
      ≤ Q'.mkPos ((4 * (e + 1) : Nat) : Int) (isqrt M) (isqrt_pos hM) := by
  -- LHS num = 4(e+1), den (cast) = M·isqrt M.
  have htpos : 0 < isqrt M := isqrt_pos hM
  show (SemicircleIntegral.lebW M hM * (Q'.ofNat (e + 1) * cBdy M hM)).num
        * ((Q'.mkPos ((4 * (e + 1) : Nat) : Int) (isqrt M) htpos).den : Int)
      ≤ (Q'.mkPos ((4 * (e + 1) : Nat) : Int) (isqrt M) htpos).num
        * ((SemicircleIntegral.lebW M hM * (Q'.ofNat (e + 1) * cBdy M hM)).den : Int)
  -- numerator: 2·((e+1)·2) = 4(e+1)
  have hLnum : (SemicircleIntegral.lebW M hM * (Q'.ofNat (e + 1) * cBdy M hM)).num
      = (4 : Int) * ((e + 1 : Nat) : Int) := by
    show (SemicircleIntegral.lebW M hM).num * (Q'.ofNat (e + 1) * cBdy M hM).num
        = (4 : Int) * ((e + 1 : Nat) : Int)
    show (Q'.mkPos 2 M hM).num * ((Q'.ofNat (e + 1)).num * (cBdy M hM).num)
        = (4 : Int) * ((e + 1 : Nat) : Int)
    rw [Q'.mkPos_num]
    show (2 : Int) * ((Q'.ofNat (e + 1)).num * (Q'.mkPos 2 (isqrt M) htpos).num)
        = (4 : Int) * ((e + 1 : Nat) : Int)
    rw [Q'.mkPos_num]
    have hof : (Q'.ofNat (e + 1)).num = ((e + 1 : Nat) : Int) := rfl
    rw [hof]
    -- 2·(a·2) = 4·a
    rw [Int.mul_comm ((e + 1 : Nat) : Int) (2 : Int),
        ← Int.mul_assoc (2 : Int) (2 : Int) ((e + 1 : Nat) : Int)]
    show ((2 : Int) * (2 : Int)) * ((e + 1 : Nat) : Int) = (4 : Int) * ((e + 1 : Nat) : Int)
    have h22 : (2 : Int) * (2 : Int) = (4 : Int) := by decide
    rw [h22]
  have hLden : ((SemicircleIntegral.lebW M hM * (Q'.ofNat (e + 1) * cBdy M hM)).den : Int)
      = (M : Int) * (isqrt M : Int) := by
    rw [Q'.mul_den_cast]
    show ((SemicircleIntegral.lebW M hM).den : Int) * ((Q'.ofNat (e + 1) * cBdy M hM).den : Int)
        = (M : Int) * (isqrt M : Int)
    show ((Q'.mkPos 2 M hM).den : Int) * ((Q'.ofNat (e + 1) * cBdy M hM).den : Int)
        = (M : Int) * (isqrt M : Int)
    rw [Q'.mkPos_den, Q'.mul_den_cast]
    show (M : Int) * (((Q'.ofNat (e + 1)).den : Int) * ((cBdy M hM).den : Int))
        = (M : Int) * (isqrt M : Int)
    have hd1 : ((Q'.ofNat (e + 1)).den : Int) = 1 := rfl
    show (M : Int) * (((Q'.ofNat (e + 1)).den : Int) * ((Q'.mkPos 2 (isqrt M) htpos).den : Int))
        = (M : Int) * (isqrt M : Int)
    rw [Q'.mkPos_den, hd1, Int.one_mul]
  rw [hLnum, hLden, Q'.mkPos_num, Q'.mkPos_den]
  -- goal: (4(e+1)) · isqrt M ≤ (4(e+1)) · (M · isqrt M)
  have hc4 : (((4 * (e + 1) : Nat)) : Int) = (4 : Int) * ((e + 1 : Nat) : Int) := by push_cast; rfl
  rw [hc4]
  have hM1 : (1 : Int) ≤ (M : Int) := by exact_mod_cast hM
  have ht0 : (0 : Int) ≤ (isqrt M : Int) := Int.natCast_nonneg _
  have he0 : (0 : Int) ≤ (4 : Int) * ((e + 1 : Nat) : Int) :=
    Int.mul_nonneg (by decide) (Int.natCast_nonneg _)
  -- 4(e+1)·t ≤ 4(e+1)·(M·t)  via  t ≤ M·t
  have htMt : (isqrt M : Int) ≤ (M : Int) * (isqrt M : Int) := by
    calc (isqrt M : Int) = 1 * (isqrt M : Int) := (Int.one_mul _).symm
      _ ≤ (M : Int) * (isqrt M : Int) := Int.mul_le_mul_of_nonneg_right hM1 ht0
  exact Int.mul_le_mul_of_nonneg_left htMt he0

/-- The `GsampR` boundary bound simplifies: `½·(cBdy·2) ≤ 2/⌊√M⌋`. -/
theorem gsampBound_le (M : Nat) (hM : 0 < M) :
    Q'.mkPos 1 2 (by decide) * (cBdy M hM * (2 : Q'))
      ≤ Q'.mkPos (2 : Int) (isqrt M) (isqrt_pos hM) := by
  have htpos : 0 < isqrt M := isqrt_pos hM
  -- LHS = ½·((2/t)·2) = (½·2·2)/t = 2/t.  num = 4, den = 2t.
  show (Q'.mkPos 1 2 (by decide) * (cBdy M hM * (2 : Q'))).num
        * ((Q'.mkPos (2 : Int) (isqrt M) htpos).den : Int)
      ≤ (Q'.mkPos (2 : Int) (isqrt M) htpos).num
        * ((Q'.mkPos 1 2 (by decide) * (cBdy M hM * (2 : Q'))).den : Int)
  have hLnum : (Q'.mkPos 1 2 (by decide) * (cBdy M hM * (2 : Q'))).num = (4 : Int) := by
    show (Q'.mkPos 1 2 (by decide)).num * (cBdy M hM * (2 : Q')).num = (4 : Int)
    rw [Q'.mkPos_num]
    show (1 : Int) * ((cBdy M hM).num * (2 : Q').num) = (4 : Int)
    show (1 : Int) * ((Q'.mkPos 2 (isqrt M) htpos).num * (2 : Q').num) = (4 : Int)
    rw [Q'.mkPos_num]; decide
  have hLden : ((Q'.mkPos 1 2 (by decide) * (cBdy M hM * (2 : Q'))).den : Int)
      = (2 : Int) * (isqrt M : Int) := by
    rw [Q'.mul_den_cast]
    show ((Q'.mkPos 1 2 (by decide)).den : Int) * ((cBdy M hM * (2 : Q')).den : Int)
        = (2 : Int) * (isqrt M : Int)
    rw [Q'.mkPos_den, Q'.mul_den_cast]
    show (2 : Int) * (((cBdy M hM).den : Int) * ((2 : Q').den : Int))
        = (2 : Int) * (isqrt M : Int)
    show (2 : Int) * (((Q'.mkPos 2 (isqrt M) htpos).den : Int) * ((2 : Q').den : Int))
        = (2 : Int) * (isqrt M : Int)
    rw [Q'.mkPos_den]
    show (2 : Int) * ((isqrt M : Int) * (1 : Int)) = (2 : Int) * (isqrt M : Int)
    rw [Int.mul_one]
  rw [hLnum, hLden, Q'.mkPos_num, Q'.mkPos_den]
  -- goal: 4 · isqrt M ≤ 2 · (2 · isqrt M)
  rw [← Int.mul_assoc (2 : Int) (2 : Int) (isqrt M : Int)]
  show (4 : Int) * (isqrt M : Int) ≤ ((2 : Int) * (2 : Int)) * (isqrt M : Int)
  have h22 : (2 : Int) * (2 : Int) = (4 : Int) := by decide
  rw [h22]
  exact Int.le_refl _

/-- `mkPos a t + mkPos b t ≤ mkPos c t` when `a + b ≤ c` (common denominator `t`). -/
theorem mkPos_add_le (a b c : Int) (t : Nat) (ht : 0 < t) (h : a + b ≤ c) :
    Q'.mkPos a t ht + Q'.mkPos b t ht ≤ Q'.mkPos c t ht := by
  show (Q'.mkPos a t ht + Q'.mkPos b t ht).num * ((Q'.mkPos c t ht).den : Int)
      ≤ (Q'.mkPos c t ht).num * ((Q'.mkPos a t ht + Q'.mkPos b t ht).den : Int)
  have hnum : (Q'.mkPos a t ht + Q'.mkPos b t ht).num
      = a * (t : Int) + b * (t : Int) := by
    show (Q'.mkPos a t ht).num * ((Q'.mkPos b t ht).den : Int)
        + (Q'.mkPos b t ht).num * ((Q'.mkPos a t ht).den : Int)
        = a * (t : Int) + b * (t : Int)
    rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  have hden : ((Q'.mkPos a t ht + Q'.mkPos b t ht).den : Int) = (t : Int) * (t : Int) := by
    rw [Q'.add_den_cast, Q'.mkPos_den, Q'.mkPos_den]
  rw [hnum, hden, Q'.mkPos_num, Q'.mkPos_den]
  -- (a·t + b·t)·t ≤ c·(t·t)  ⟺ (a+b)·t² ≤ c·t²
  have hfact : (a * (t : Int) + b * (t : Int)) * (t : Int)
      = (a + b) * ((t : Int) * (t : Int)) := by
    rw [← Int.add_mul a b (t : Int), Int.mul_assoc (a + b) (t : Int) (t : Int)]
  rw [hfact]
  have ht2 : (0 : Int) ≤ (t : Int) * (t : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  exact Int.mul_le_mul_of_nonneg_right h ht2

/-! ## 5. The DIRECT boundary-cell two-sided estimate -/

/-- Connect a radicand `oneMinusSqNode`/`bdyOneMinusSq` (denominator `M·M`) to the
`cBdy` square bound from a numerator inequality `0 ≤ N ≤ 4M`. -/
theorem radicand_node_le_cBdy (M : Nat) (hM : 0 < M) (k : Nat) (hk : k < M)
    (hN0 : (0 : Int) ≤ SemicircleIntegral.omsNum M k)
    (hN : SemicircleIntegral.omsNum M k ≤ 4 * (M : Int)) :
    SemicircleIntegral.oneMinusSqNode M k hM hk ≤ cBdy M hM * cBdy M hM :=
  radicand_le_cBdy_sq M hM (SemicircleIntegral.omsNum M k) hN0 hN

theorem radicand_bdy_le_cBdy (M : Nat) (hM : 0 < M) (k : Nat) (hk0 : 0 < k) (hkn : k < M)
    (hN0 : (0 : Int) ≤ bdyNum M k) (hN : bdyNum M k ≤ 4 * (M : Int)) :
    bdyOneMinusSq M k hM hk0 hkn ≤ cBdy M hM * cBdy M hM :=
  radicand_le_cBdy_sq M hM (bdyNum M k) hN0 hN

/-- The combined boundary bound `B(e,M) := 4(e+1)/⌊√M⌋ + 2/⌊√M⌋ ≤ gradedRate` at a
boundary cell (`jdist = 1`), i.e. `4(e+1)+2 ≤ cRateNum e = 4(e+1)+4·Le e`
(`4 ≤ 4·Le e`, `Le e ≥ 1`). -/
theorem boundaryRate_le_graded (e M : Nat) (he : 0 < e) (hM : 0 < M) :
    Q'.mkPos ((4 * (e + 1) : Nat) : Int) (isqrt M) (isqrt_pos hM)
        + Q'.mkPos (2 : Int) (isqrt M) (isqrt_pos hM)
      ≤ Q'.mkPos (cRateNum e : Int) (isqrt M) (isqrt_pos hM) := by
  refine mkPos_add_le _ _ _ (isqrt M) (isqrt_pos hM) ?_
  -- 4(e+1) + 2 ≤ cRateNum e = 4(e+1) + 4·Le e
  have hLe : 1 ≤ Le e := by
    unfold Le
    have hp : 0 < e * (e + 1) * (e + 2) :=
      Nat.mul_pos (Nat.mul_pos he (by omega)) (by omega)
    omega
  have h2 : 2 ≤ 4 * Le e := by omega
  have hcN : 4 * (e + 1) + 2 ≤ cRateNum e := by
    unfold cRateNum; omega
  have hc : (cRateNum e : Int) = ((4 * (e + 1) : Nat) : Int) + (2 : Int)
      + ((4 * Le e - 2 : Nat) : Int) := by
    show ((4 * (e + 1) + 4 * Le e : Nat) : Int)
        = ((4 * (e + 1) : Nat) : Int) + (2 : Int) + ((4 * Le e - 2 : Nat) : Int)
    have hcastsub : ((4 * Le e - 2 : Nat) : Int) = (4 * (Le e : Int)) - 2 := by
      have : (2 : Nat) ≤ 4 * Le e := h2
      omega
    rw [hcastsub]
    push_cast
    omega
  rw [hc]
  have hge : (0 : Int) ≤ ((4 * Le e - 2 : Nat) : Int) := Int.natCast_nonneg _
  -- a ≤ a + nonneg
  have := Int.add_le_add_left hge (((4 * (e + 1) : Nat) : Int) + (2 : Int))
  -- rewrite (x) ≤ (x) + nonneg  with x = 4(e+1)+2
  refine Int.le_trans ?_ this
  omega

/-- `jdist M 0 = 1` (`M ≥ 1`). -/
theorem jdist_zero (M : Nat) (hM : 0 < M) : jdist M 0 = 1 := by
  have h : jdist M 0 = (0 + 1) := Nat.min_eq_left (by omega : 0 + 1 ≤ M - 0)
  omega

/-- `jdist M (M−1) = 1` (`M ≥ 1`). -/
theorem jdist_top (M : Nat) (hM : 0 < M) : jdist M (M - 1) = 1 := by
  have h : jdist M (M - 1) = (M - (M - 1)) :=
    Nat.min_eq_right (by omega : M - (M - 1) ≤ (M - 1) + 1)
  omega

/-- `gradedRate` at a boundary cell (`jdist = 1`) is `cRateNum e / ⌊√M⌋`. -/
theorem gradedRate_boundary (e M : Nat) (hM : 0 < M) (k : Nat) (hj : jdist M k = 1) :
    gradedRate e M hM k = Q'.mkPos (cRateNum e : Int) (isqrt M) (isqrt_pos hM) := by
  show scaledTerm e M hM (jdist M k) = Q'.mkPos (cRateNum e : Int) (isqrt M) (isqrt_pos hM)
  rw [hj]
  show (if hj : 0 < 1 then
      Q'.mkPos (cRateNum e : Int) (isqrt M * (1 * 1)) (Nat.mul_pos (isqrt_pos hM) (Nat.mul_pos hj hj))
    else 0) = Q'.mkPos (cRateNum e : Int) (isqrt M) (isqrt_pos hM)
  rw [dif_pos (by decide : 0 < 1)]
  -- isqrt M * (1*1) = isqrt M ; rewrite the denominator
  have hden : isqrt M * (1 * 1) = isqrt M := by omega
  -- mkPos depends on the den only through the value (proof irrelevant): rewrite den.
  congr 1

/-- **THE BOUNDARY-CELL TWO-SIDED ESTIMATE.**  At the two boundary cells
`k ∈ {0, M−1}` (`jdist = 1`, rate `= C(e)/⌊√M⌋`), the genuine adjusted cell is
two-sidedly bounded by the graded rate.  At `k = M−1` the right endpoint `b_M = 1`
kills `GsampR(M)`; at `k = 0` the left endpoint `b_0 = −1` kills `GsampR(0)`.  The
surviving interior sample lives near `±1` where the radicand is `≤ 4/M ≤
(2/⌊√M⌋)²`, and the node weight likewise, giving the boundary scale. -/
theorem boundary_cell_bound (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat)
    (hk : k = 0 ∨ k = M - 1) :
    AbsLeRat (cellAdjR e he M hM k) (gradedRate e M hM k) := by
  -- common: jdist = 1, so gradedRate = mkPos cRateNum (isqrt M)
  have hj : jdist M k = 1 := by
    rcases hk with h0 | htop
    · rw [h0]; exact jdist_zero M hM
    · rw [htop]; exact jdist_top M hM
  rw [gradedRate_boundary e M hM k hj]
  -- abbreviations for the bound targets
  have hcBdypos := cBdy_pos M hM
  -- cellAdjR = add orthTerm (add GsampR(k+1) (neg GsampR(k)))
  show AbsLeRat (CReal.add (orthTerm e M hM k)
      (CReal.add (GsampR e he M hM (k + 1)) (CReal.neg (GsampR e he M hM k))))
      (Q'.mkPos (cRateNum e : Int) (isqrt M) (isqrt_pos hM))
  rcases hk with h0 | htop
  · -- k = 0 : node 0 (interior weight), GsampR(1) interior, GsampR(0) endpoint.
    subst h0
    have hk0lt : (0 : Nat) < M := hM
    -- orthTerm bound (node k=0, radicand omsNum M 0 = 2M-1 ≤ 4M)
    have homsN0 : (0 : Int) ≤ SemicircleIntegral.omsNum M 0 :=
      Int.le_of_lt (SemicircleIntegral.omsNum_pos hM hk0lt)
    have homsB0 : SemicircleIntegral.omsNum M 0 ≤ 4 * (M : Int) := by
      show (M : Int) * (M : Int) - (2 * (0 : Int) + 1 - (M : Int)) * (2 * (0 : Int) + 1 - (M : Int))
          ≤ 4 * (M : Int)
      have hs : (2 * (0 : Int) + 1 - (M : Int)) = (1 : Int) - (M : Int) := by omega
      rw [hs, int_sq_expand 1 (M : Int)]
      have hMpos : (0 : Int) ≤ (M : Int) := Int.natCast_nonneg _
      have h1M : (1 : Int) * (M : Int) = (M : Int) := Int.one_mul _
      rw [h1M]; omega
    have hOrth := orthTerm_AbsLeRat e M hM 0 hk0lt (cBdy M hM) hcBdypos
      (radicand_node_le_cBdy M hM 0 hk0lt homsN0 homsB0)
    have hOrth' : AbsLeRat (orthTerm e M hM 0)
        (Q'.mkPos ((4 * (e + 1) : Nat) : Int) (isqrt M) (isqrt_pos hM)) :=
      AbsLeRat.mono hOrth (orthBound_le e M hM)
    -- GsampR(1): interior iff 1 < M.  Split.
    have hGp : AbsLeRat (GsampR e he M hM 1)
        (Q'.mkPos (2 : Int) (isqrt M) (isqrt_pos hM)) := by
      by_cases h1M : 1 < M
      · -- interior: radicand bdyNum M 1 = 4M-4 ≤ 4M
        have hb0 : (0 : Int) ≤ bdyNum M 1 := Int.le_of_lt (bdyNum_pos (by decide) h1M)
        have hbB : bdyNum M 1 ≤ 4 * (M : Int) := by
          show (M : Int) * (M : Int)
              - (2 * ((1 : Nat) : Int) - (M : Int)) * (2 * ((1 : Nat) : Int) - (M : Int))
              ≤ 4 * (M : Int)
          have hs : (2 * ((1 : Nat) : Int) - (M : Int)) = (2 : Int) - (M : Int) := by
            push_cast; omega
          rw [hs, int_sq_expand 2 (M : Int)]
          have hMpos : (0 : Int) ≤ (M : Int) := Int.natCast_nonneg _
          have h2M : (2 : Int) * (M : Int) = (M : Int) + (M : Int) := by omega
          omega
        have hG := GsampR_AbsLeRat e he M hM 1 (by decide) h1M (cBdy M hM) hcBdypos
          (radicand_bdy_le_cBdy M hM 1 (by decide) h1M hb0 hbB)
        exact AbsLeRat.mono hG (gsampBound_le M hM)
      · -- M = 1 so 1 = M, endpoint, bound 0 ≤ mkPos 2
        have hM1 : M = 1 := by omega
        have := GsampR_endpoint_AbsLeRat e he M hM 1 (Or.inr (by omega))
        refine AbsLeRat.mono this ?_
        show (0 : Q') ≤ Q'.mkPos (2 : Int) (isqrt M) (isqrt_pos hM)
        rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide
    -- GsampR(0): endpoint, bound 0
    have hGm0 : AbsLeRat (GsampR e he M hM 0) (0 : Q') :=
      GsampR_endpoint_AbsLeRat e he M hM 0 (Or.inl rfl)
    have hGmNeg : AbsLeRat (CReal.neg (GsampR e he M hM 0)) (0 : Q') := AbsLeRat.neg hGm0
    -- assemble: orthTerm + (GsampR(1) + neg GsampR(0))
    have hSum := AbsLeRat.add hOrth' (AbsLeRat.add hGp hGmNeg)
    -- bound = mkPos(4(e+1)) + (mkPos 2 + 0)
    refine AbsLeRat.mono hSum ?_
    -- mkPos(4(e+1)) + (mkPos 2 + 0) ≤ mkPos cRateNum (isqrt M)
    refine Q'.le_trans' _ _ _ ?_ (boundaryRate_le_graded e M he hM)
    -- mkPos(4(e+1)) + (mkPos2 + 0) ≤ mkPos(4(e+1)) + mkPos2
    refine Q'.add_le_add_left _ _ _ ?_
    exact Q'.le_of_eqv (QPoly.q_add_zero_eqv (Q'.mkPos (2 : Int) (isqrt M) (isqrt_pos hM)))
  · -- k = M-1 : node M-1 (interior weight for M≥1), GsampR(M) endpoint, GsampR(M-1) interior.
    subst htop
    have hk0lt : (M - 1 : Nat) < M := by omega
    -- orthTerm bound (node k=M-1, radicand omsNum M (M-1) = 2M-1 ≤ 4M)
    have homsN0 : (0 : Int) ≤ SemicircleIntegral.omsNum M (M - 1) :=
      Int.le_of_lt (SemicircleIntegral.omsNum_pos hM hk0lt)
    have homsB0 : SemicircleIntegral.omsNum M (M - 1) ≤ 4 * (M : Int) := by
      show (M : Int) * (M : Int)
          - (2 * ((M - 1 : Nat) : Int) + 1 - (M : Int)) * (2 * ((M - 1 : Nat) : Int) + 1 - (M : Int))
          ≤ 4 * (M : Int)
      have hcast : ((M - 1 : Nat) : Int) = (M : Int) - 1 := by
        omega
      have hs : (2 * ((M - 1 : Nat) : Int) + 1 - (M : Int)) = (M : Int) - 1 := by
        rw [hcast]; omega
      rw [hs, int_sq_expand (M : Int) 1]
      have hMpos : (0 : Int) ≤ (M : Int) := Int.natCast_nonneg _
      have hM1 : (M : Int) * 1 = (M : Int) := Int.mul_one _
      rw [hM1]; omega
    have hOrth := orthTerm_AbsLeRat e M hM (M - 1) hk0lt (cBdy M hM) hcBdypos
      (radicand_node_le_cBdy M hM (M - 1) hk0lt homsN0 homsB0)
    have hOrth' : AbsLeRat (orthTerm e M hM (M - 1))
        (Q'.mkPos ((4 * (e + 1) : Nat) : Int) (isqrt M) (isqrt_pos hM)) :=
      AbsLeRat.mono hOrth (orthBound_le e M hM)
    -- GsampR(M): endpoint (k+1 = M-1+1 = M for M≥1), bound 0
    have hksucc : (M - 1) + 1 = M := by omega
    have hGp : AbsLeRat (GsampR e he M hM ((M - 1) + 1)) (0 : Q') := by
      rw [hksucc]
      exact GsampR_endpoint_AbsLeRat e he M hM M (Or.inr rfl)
    -- GsampR(M-1): interior iff 0 < M-1.  Split.
    have hGm : AbsLeRat (GsampR e he M hM (M - 1))
        (Q'.mkPos (2 : Int) (isqrt M) (isqrt_pos hM)) := by
      by_cases hMm : 0 < M - 1
      · -- interior: radicand bdyNum M (M-1) = 4M-4 ≤ 4M
        have hb0 : (0 : Int) ≤ bdyNum M (M - 1) := Int.le_of_lt (bdyNum_pos hMm hk0lt)
        have hbB : bdyNum M (M - 1) ≤ 4 * (M : Int) := by
          show (M : Int) * (M : Int)
              - (2 * ((M - 1 : Nat) : Int) - (M : Int)) * (2 * ((M - 1 : Nat) : Int) - (M : Int))
              ≤ 4 * (M : Int)
          have hcast : ((M - 1 : Nat) : Int) = (M : Int) - 1 := by
            omega
          have hs : (2 * ((M - 1 : Nat) : Int) - (M : Int)) = (M : Int) - 2 := by
            rw [hcast]; omega
          rw [hs, int_sq_expand (M : Int) 2]
          have hMpos : (0 : Int) ≤ (M : Int) := Int.natCast_nonneg _
          omega
        have hG := GsampR_AbsLeRat e he M hM (M - 1) hMm hk0lt (cBdy M hM) hcBdypos
          (radicand_bdy_le_cBdy M hM (M - 1) hMm hk0lt hb0 hbB)
        exact AbsLeRat.mono hG (gsampBound_le M hM)
      · -- M = 1 so M-1 = 0, endpoint, bound 0 ≤ mkPos 2
        have hM1 : M = 1 := by omega
        have := GsampR_endpoint_AbsLeRat e he M hM (M - 1) (Or.inl (by omega))
        refine AbsLeRat.mono this ?_
        show (0 : Q') ≤ Q'.mkPos (2 : Int) (isqrt M) (isqrt_pos hM)
        rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]; decide
    have hGmNeg : AbsLeRat (CReal.neg (GsampR e he M hM (M - 1)))
        (Q'.mkPos (2 : Int) (isqrt M) (isqrt_pos hM)) := AbsLeRat.neg hGm
    -- assemble: orthTerm + (GsampR(M) + neg GsampR(M-1))
    have hSum := AbsLeRat.add hOrth' (AbsLeRat.add hGp hGmNeg)
    -- bound = mkPos(4(e+1)) + (0 + mkPos 2)
    refine AbsLeRat.mono hSum ?_
    refine Q'.le_trans' _ _ _ ?_ (boundaryRate_le_graded e M he hM)
    -- mkPos(4(e+1)) + (0 + mkPos2) ≤ mkPos(4(e+1)) + mkPos2
    refine Q'.add_le_add_left _ _ _ ?_
    exact Q'.le_of_eqv (QPoly.q_zero_add_eqv (Q'.mkPos (2 : Int) (isqrt M) (isqrt_pos hM)))

/-! ## 6. The boundary cells in `GradedPerCellBound` shape, the interior residual,
and the assembly -/

/-- **The boundary cells in the `leRat` two-sided shape of `GradedPerCellBound`.**
For `M = N+1` and a boundary cell `k ∈ {0, M−1}`, both
`leRat (cellAdjR e he M k) (gradedRate e M k)` and the negation hold. -/
theorem boundary_cell_leRat (e : Nat) (he : 0 < e) (N k : Nat)
    (hk : k = 0 ∨ k = (N + 1) - 1) :
    CReal.leRat (cellAdjR e he (N + 1) (Nat.succ_pos N) k)
        (gradedRate e (N + 1) (Nat.succ_pos N) k) ∧
    CReal.leRat (CReal.neg (cellAdjR e he (N + 1) (Nat.succ_pos N) k))
        (gradedRate e (N + 1) (Nat.succ_pos N) k) :=
  boundary_cell_bound e he (N + 1) (Nat.succ_pos N) k hk

/-- **NAMED-open: the INTERIOR second-order graded remainder.**  For the even order
`e` (`he : 0 < e`), every GENUINE real-boundary INTERIOR adjusted cell
`cellAdjR e he (N+1) k` (`1 ≤ k ≤ N−1`, i.e. NOT a boundary cell) is two-sidedly
bounded by the graded rate `gradedRate e (N+1) k = C(e)/(⌊√(N+1)⌋·jdist²)`.

This is the SINGLE remaining analytic core.  Its EXACT structure is supplied by the
PROVED pieces: `cellAdjR = orthTerm + gIncrR` (`ChebOrthoMidpoint.cellAdjR`),
`ChebOrthoRemainder.gIncr_pdiff_split` (the product-difference split of `gIncrR`
into the smooth-bracket and radical finite-difference legs),
`ChebOrthoRemainder.radSq_diff_equiv` (the exact `s_+²−s_-² = ofQ'(1−b_{k+1}²) −
ofQ'(1−b_k²) = −4x_kδ`), and `ChebOrthoCancel.leading_cancellation` (the leading
midpoint combination EXACTLY cancels `orthTerm`).  After the exact cancellation
`cellAdjR` is the SECOND-ORDER centered-difference remainder `~ C(e)·δ^{3/2}/j^{3/2}
≤ C(e)/(⌊√(N+1)⌋·j²)`; the residual NUMERIC assembly needs (i) the √-Hölder modulus
`SqrtSubadd.holder_oneMinusSq` for the radical leg, (ii) the Lipschitz scale `Le e`
for the bracket leg, and (iii) a CONSTRUCTIVE LOWER bound `s_++s_- ≥ √(jδ)` on the
sum of the two cell radicals (to control the reciprocal in `s_+−s_- = −4x_kδ/(s_++s_-)`).
Recorded precisely, NOT faked. -/
def InteriorGradedRemainder (e : Nat) (he : 0 < e) : Prop :=
  ∀ N k : Nat, 1 ≤ k → k ≤ N - 1 →
    CReal.leRat (cellAdjR e he (N + 1) (Nat.succ_pos N) k)
        (gradedRate e (N + 1) (Nat.succ_pos N) k) ∧
    CReal.leRat (CReal.neg (cellAdjR e he (N + 1) (Nat.succ_pos N) k))
        (gradedRate e (N + 1) (Nat.succ_pos N) k)

/-- The cell radical vanishes off range (`k ≥ M`): `bdyRadical M k = czero`. -/
theorem bdyRadical_outrange (M : Nat) (hM : 0 < M) (k : Nat) (hk : M ≤ k) :
    bdyRadical M hM k = CReal.czero := by
  unfold bdyRadical
  by_cases hk0 : 0 < k
  · rw [dif_pos hk0, dif_neg (by omega : ¬ k < M)]
  · rw [dif_neg hk0]

/-- **The out-of-range cell is two-sidedly `≤ 0`.**  For `k ≥ M` the node weight and
both cell radicals are `czero`, so `cellAdjR ≈ 0` pointwise; and `gradedRate = 0`
there (`jdist = 0`).  Hence the per-cell bound holds trivially off range. -/
theorem outOfRange_cell_bound (e : Nat) (he : 0 < e) (M : Nat) (hM : 0 < M) (k : Nat)
    (hk : M ≤ k) :
    AbsLeRat (cellAdjR e he M hM k) (gradedRate e M hM k) := by
  -- gradedRate = scaledTerm e M (jdist M k) ; jdist M k = min(k+1, M-k) = min(k+1, 0) = 0.
  have hjd : jdist M k = 0 := by
    have h : jdist M k = (M - k) := Nat.min_eq_right (by omega : M - k ≤ k + 1)
    omega
  have hgr : gradedRate e M hM k = (0 : Q') := by
    show scaledTerm e M hM (jdist M k) = 0
    rw [hjd]
    show (if hj : 0 < 0 then _ else (0 : Q')) = 0
    rw [dif_neg (by decide : ¬ 0 < 0)]
  rw [hgr]
  -- cellAdjR ≈ 0 pointwise
  refine AbsLeRat_zero_of_approx_zero (fun p => ?_)
  -- cellAdjR = orthTerm + (GsampR(k+1) + neg GsampR(k)) ; all three ≈ 0.
  show ((CReal.add (orthTerm e M hM k)
      (CReal.add (GsampR e he M hM (k + 1)) (CReal.neg (GsampR e he M hM k)))).approx p) ≈ 0
  show ((orthTerm e M hM k).approx p
      + ((GsampR e he M hM (k + 1)).approx p + (-((GsampR e he M hM k).approx p)))) ≈ 0
  -- orthTerm.approx p ≈ 0 : nodeWeight czero (k ≥ M)
  have horth : ((orthTerm e M hM k).approx p) ≈ 0 := by
    show ((SemicircleIntegral.lebW M hM)
        * ((uNode e M hM k) * ((SemicircleIntegral.nodeWeight M hM k).approx p))) ≈ 0
    have hnw : SemicircleIntegral.nodeWeight M hM k = CReal.czero := by
      unfold SemicircleIntegral.nodeWeight; rw [dif_neg (by omega : ¬ k < M)]
    rw [hnw]
    have hcz : ((CReal.czero).approx p) = (0 : Q') := rfl
    rw [hcz]
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv (uNode e M hM k))) ?_
    exact Q'.mul_zero_eqv (SemicircleIntegral.lebW M hM)
  -- GsampR(k) ≈ 0 and GsampR(k+1) ≈ 0 : bdyRadical czero off range.
  have hgsamp : ∀ j, M ≤ j → ((GsampR e he M hM j).approx p) ≈ 0 := by
    intro j hj
    show ((Q'.mkPos 1 2 (by decide))
        * ((bdyRadical M hM j).approx p * (Gbracket e he (bdyPoint M hM j)))) ≈ 0
    rw [bdyRadical_outrange M hM j hj]
    have hcz : ((CReal.czero).approx p) = (0 : Q') := rfl
    rw [hcz]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv (Gbracket e he (bdyPoint M hM j)))) ?_
    exact Q'.mul_zero_eqv (Q'.mkPos 1 2 (by decide))
  have hGp : ((GsampR e he M hM (k + 1)).approx p) ≈ 0 := hgsamp (k + 1) (by omega)
  have hGm : ((GsampR e he M hM k).approx p) ≈ 0 := hgsamp k hk
  -- assemble: 0 + (0 + (−0)) ≈ 0
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' horth
      (Q'.add_eqv_congr' hGp (Q'.neg_eqv_congr _ _ hGm))) ?_
  decide

/-- **Assembly: `GradedPerCellBound` from the interior remainder.**  Every cell is
either a boundary cell `k ∈ {0, M−1}` (closed UNCONDITIONALLY by
`boundary_cell_bound`) or an interior cell `1 ≤ k ≤ M−2` (the named
`InteriorGradedRemainder`).  So the interior remainder is the ONLY residual for the
full per-cell bound. -/
theorem gradedPerCellBound_of_interior (e : Nat) (he : 0 < e)
    (h : InteriorGradedRemainder e he) :
    ChebOrthoGraded.GradedPerCellBound e he := by
  intro N k
  -- case split: k = 0, k = N (= M-1 for M=N+1 only if k=N which is out of range, so
  -- the top boundary is k = N (= (N+1)-1)), or interior 1 ≤ k ≤ N-1.
  by_cases hkr : N + 1 ≤ k
  · -- out of range k ≥ M = N+1 : trivial (cellAdjR ≈ 0, gradedRate = 0).
    exact outOfRange_cell_bound e he (N + 1) (Nat.succ_pos N) k hkr
  · by_cases hk0 : k = 0
    · exact boundary_cell_leRat e he N k (Or.inl hk0)
    · by_cases hktop : k = (N + 1) - 1
      · exact boundary_cell_leRat e he N k (Or.inr hktop)
      · -- interior: 1 ≤ k (since k ≠ 0) and k ≤ N-1 (k ≠ N = (N+1)-1, k < N+1).
        have hk1 : 1 ≤ k := by omega
        have hkN1 : k ≤ N - 1 := by omega
        exact h N k hk1 hkN1

/-- **`OrthEvenZeroLimit e` from the interior remainder** (the boundary cells are
UNCONDITIONAL).  Composes the assembly with the PROVED bridge
`ChebOrthoGraded.orthEvenZeroLimit_of_gradedBound`. -/
theorem orthEvenZeroLimit_of_interior (e : Nat) (he : 0 < e)
    (h : InteriorGradedRemainder e he) :
    ChebOrthoEvenFTC.OrthEvenZeroLimit e :=
  ChebOrthoGraded.orthEvenZeroLimit_of_gradedBound e he
    (gradedPerCellBound_of_interior e he h)

/-- **Off-diagonal orthogonality `∫U_e√ = 0` for `e ≥ 1`, from the interior
remainder (even orders).**  The ODD case is already UNCONDITIONAL; the EVEN case via
the assembly `gradedPerCellBound_of_interior` (boundary cells unconditional) + the
PROVED bridges.  π-free. -/
theorem offdiag_closed_of_interior
    (hint : ∀ (e : Nat) (he : 0 < e), 2 ≤ e → e % 2 = 0 → InteriorGradedRemainder e he) :
    ∀ (e : Nat), 1 ≤ e →
      ∃ L : CReal, CReal.ConvergesTo (seqOrth e) L ∧ CReal.Equiv L CReal.czero := by
  refine ChebOrthoGraded.offdiag_closed_of_gradedBound (fun e he he2 heven => ?_)
  exact gradedPerCellBound_of_interior e he (hint e he he2 heven)

end YMGap.Continuum.ChebOrthoGradedClose

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (axiom-clean, GENUINE new content).**
  * The two-sided value-bound calculus `AbsLeRat` with `AbsLeRat.mono` /
    `AbsLeRat.neg` / `AbsLeRat.ofQ'` / `AbsLeRat.add` / `AbsLeRat.smul_nonneg` /
    `AbsLeRat.of_nonneg_leRat` / `AbsLeRat.mul_nonneg_ofQ'` / `AbsLeRat.congr` /
    `AbsLeRat.ofQ'_mul_nonneg` (+ the `Q'` helpers `neg_le_of_negB_le`,
    `neg_le_of_add_nonneg`) — reusable transitivity-free symmetric value bounds.
  * `bracketTerm_abs_le` / **`gbracket_abs_le`** — the rational bracket bound
    `|B_e(x)| ≤ 2` on `[−1,1]` (via `ChebyshevU.absU_le`, `|U_{e−1}/e| ≤ 1`,
    `|U_{e+1}/(e+2)| ≤ 1`).
  * `bdyRadical_geRat0` / `bdyRadical_AbsLeRat` / `nodeWeight_AbsLeRat` — the genuine
    cell radicals `√(1−b_k²)`, `√(1−x_k²)` as two-sided value bounds against any
    rational `c` with radicand `≤ c²` (via `sqrtFrom_leRat_of_sq`, nonnegativity).
  * `int_sq_expand` / `cBdy` / `radicand_le_cBdy_sq` / `radicand_node_le_cBdy` /
    `radicand_bdy_le_cBdy` — the boundary radical-bound witness `cBdy M = 2/⌊√M⌋`
    and the radicand bound `mkPos N (M²) ≤ (2/⌊√M⌋)²` for `0 ≤ N ≤ 4M` (`⌊√M⌋² ≤ M`).
  * `uNode_abs_le` / `orthTerm_AbsLeRat` / `GsampR_endpoint_AbsLeRat` /
    `GsampR_AbsLeRat` — the two-sided value bounds on `orthTerm` and the
    antiderivative samples `GsampR` (interior and endpoint cases).
  * `orthBound_le` / `gsampBound_le` / `mkPos_add_le` / `boundaryRate_le_graded` /
    `jdist_zero` / `jdist_top` / `gradedRate_boundary` — the boundary-cell rate
    comparisons (`4(e+1)/⌊√M⌋ + 2/⌊√M⌋ ≤ C(e)/⌊√M⌋`, `C(e) = 4(e+1)+4·Le e`).
  * **`boundary_cell_bound`** / `boundary_cell_leRat` — the DIRECT two-sided per-cell
    estimate `|cellAdjR e he M k| ≤ gradedRate e M k` at the BOUNDARY cells
    `k ∈ {0, M−1}` (`jdist = 1`, rate `C(e)/⌊√M⌋`).  At `k = M−1` (resp `k = 0`) the
    endpoint sample `GsampR(M)` (resp `GsampR(0)`) vanishes (`czero` radical); the
    surviving interior sample + the node weight live near `±1` where the radicand is
    `≤ 4/M ≤ (2/⌊√M⌋)²`.  Fully rigorous, NO interior cancellation needed.
  * `bdyRadical_outrange` / **`outOfRange_cell_bound`** — the out-of-range cells
    `k ≥ M` are trivially `≤ 0` (`cellAdjR ≈ 0`, `gradedRate = 0`).
  * **`gradedPerCellBound_of_interior`** — the assembly:
    `InteriorGradedRemainder e he → ChebOrthoGraded.GradedPerCellBound e he`
    (boundary + out-of-range cells UNCONDITIONAL; interior is the named residual).
  * `orthEvenZeroLimit_of_interior` / `offdiag_closed_of_interior` — the even-order
    `czero` limit and the COMBINED π-free off-diagonal orthogonality `∫U_e√ = 0` for
    `e ≥ 1`, reduced to the SINGLE INTERIOR residual (odd UNCONDITIONAL), via the
    PROVED `ChebOrthoGraded` bridges.

**NAMED-open (the honest residual — the INTERIOR second-order graded remainder).**
  * `InteriorGradedRemainder e he` — the per-cell two-sided estimate
    `|cellAdjR e he (N+1) k| ≤ gradedRate e (N+1) k` at the INTERIOR cells
    `1 ≤ k ≤ N−1` only (the boundary cells `k ∈ {0, N}` and out-of-range cells are
    PROVED above).  Its EXACT structure is the second-order centered-difference
    remainder, fully assembled from the PROVED exact pieces
    `ChebOrthoMidpoint.cellAdjR` (`= orthTerm + gIncrR`),
    `ChebOrthoRemainder.gIncr_pdiff_split` (product-difference split into the two
    finite-difference legs), `ChebOrthoRemainder.radSq_diff_equiv`
    (`s_+²−s_-² = ofQ'(1−b_{k+1}²) − ofQ'(1−b_k²) = −4x_kδ`), and
    `ChebOrthoCancel.leading_cancellation` (the leading midpoint combination cancels
    `orthTerm` EXACTLY).  The SINGLE remaining content is the NUMERIC assembly
    bounding the resulting second-order remainder by `C(e)·δ^{3/2}/j^{3/2} ≤
    C(e)/(⌊√(N+1)⌋·j²)`, needing (i) the √-Hölder modulus
    `SqrtSubadd.holder_oneMinusSq` (radical leg), (ii) the Lipschitz scale `Le e`
    (bracket leg), and (iii) a CONSTRUCTIVE LOWER bound `s_++s_- ≥ √(jδ)` on the sum
    of the two cell radicals (reciprocal in `s_+−s_- = −4x_kδ/(s_++s_-)`).  Recorded
    precisely, NOT faked.

**Path to closure.**  Once `InteriorGradedRemainder e he` holds for every even
`e ≥ 2`, `gradedPerCellBound_of_interior` (boundary + out-of-range UNCONDITIONAL)
closes `ChebOrthoGraded.GradedPerCellBound`, hence (via the PROVED chain
`realPerCellBudget_of_gradedBound` → `budgetExists_of_realPerCell` →
`convergesTo_czero_of_bound`) `OrthEvenZeroLimit e` and the full π-free off-diagonal
orthogonality `∫U_e√ = 0` for all `e ≥ 1`.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` only on closed
`Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthoGradedClose.AbsLeRat.add
#print axioms YMGap.Continuum.ChebOrthoGradedClose.AbsLeRat.smul_nonneg
#print axioms YMGap.Continuum.ChebOrthoGradedClose.AbsLeRat.of_nonneg_leRat
#print axioms YMGap.Continuum.ChebOrthoGradedClose.AbsLeRat.mul_nonneg_ofQ'
#print axioms YMGap.Continuum.ChebOrthoGradedClose.gbracket_abs_le
#print axioms YMGap.Continuum.ChebOrthoGradedClose.bdyRadical_AbsLeRat
#print axioms YMGap.Continuum.ChebOrthoGradedClose.nodeWeight_AbsLeRat
#print axioms YMGap.Continuum.ChebOrthoGradedClose.radicand_le_cBdy_sq
#print axioms YMGap.Continuum.ChebOrthoGradedClose.orthTerm_AbsLeRat
#print axioms YMGap.Continuum.ChebOrthoGradedClose.GsampR_AbsLeRat
#print axioms YMGap.Continuum.ChebOrthoGradedClose.boundaryRate_le_graded
#print axioms YMGap.Continuum.ChebOrthoGradedClose.gradedRate_boundary
#print axioms YMGap.Continuum.ChebOrthoGradedClose.boundary_cell_bound
#print axioms YMGap.Continuum.ChebOrthoGradedClose.outOfRange_cell_bound
#print axioms YMGap.Continuum.ChebOrthoGradedClose.gradedPerCellBound_of_interior
#print axioms YMGap.Continuum.ChebOrthoGradedClose.orthEvenZeroLimit_of_interior
#print axioms YMGap.Continuum.ChebOrthoGradedClose.offdiag_closed_of_interior
