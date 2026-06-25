/-
# The unconditional constructive semicircle Riemann integral

This module discharges the two residuals that block the semicircle integral's
convergence from being FULLY UNCONDITIONAL:

  * the antitone rate predicate `CReal.MmonoPred` for the outer Cauchy rate, and
  * the `leRat` outer Cauchy bound `SemicircleRate.SemiLeRatBound` (the common
    refinement assembly of the proved per-cell Riemann content).

Together with the already-proved completeness backbone
(`CReal.completeLimitFromRate`), the per-cell Riemann content
(`SemicircleConvClosed.semiSum_refine_leRat_cell`), and the enclosure-passers in
`SemicircleRate`, these yield the FIRST fully-rigorous constructive Riemann
integral in the library: an UNCONDITIONAL `semiInt : CReal` with a proved
convergence certificate and the proved enclosure `0 ≤ semiInt ≤ 2`.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `qCeilNat_mono` — the rational ceiling `SemicircleConvClosed.qCeilNat` is
    monotone (`q ≤ r ⟹ qCeilNat q ≤ qCeilNat r`), from `Int`/`Nat` floor-division
    monotonicity on the cross-multiplied comparison.
  * `recipSq` / `recipSq_anti` — the explicit antitone rational `128/ε²`
    (`= 128·den²/num²`), with `0 < δ ≤ ε ⟹ recipSq ε ≤ recipSq δ` (the positive
    reciprocal-square anti-monotonicity, a pure cross-multiplied `Int` fact).
  * `semiRateB` / `semiRateB_mono` — the concrete antitone outer rate
    `semiRateB ε := qCeilNat (recipSq ε)` and its `CReal.MmonoPred`.

  * `semiSum_refine_leRat` / `semiSum_refine_rev_leRat` — **THE GENUINE RIEMANN
    CONVERGENCE CONTENT** (both directions): the nested refinement bound
    `leRat (semiSum P + (−semiSum (P·Q))) (2·c)` (and its reverse), assembled from
    the proved per-cell content via the `CReal`-level `leRat_congr` identification
    of the value difference `(semiSum P).approx k − (semiSum (P·Q)).approx k` with
    the block-reindexed cell-sum (`value_diff_eqv` / `cell_value_eqv`).
  * `semiLeRatBound` — TARGET 2: the `leRat` outer Cauchy bound
    `SemicircleRate.SemiLeRatBound semiRateB`, the two-sided common-refinement
    assembly (telescope through `semiSum (P·N)`, both refinement bounds, the
    `2c + 2c ≤ ε` collapse with `c = ε/8`).
  * `semiInt` / `semiInt_converges` / `semiInt_nonneg` / `semiInt_leRat_two` —
    the FULLY UNCONDITIONAL semicircle Riemann integral `∫_{−1}^1 √(1−x²)`, its
    hypothesis-free convergence certificate, and its proved enclosure
    `0 ≤ semiInt ≤ 2`.  This is the first fully-rigorous constructive Riemann
    integral in the library.

## What is NAMED-open (precisely)

  * NOTHING for the semicircle convergence: both residuals are discharged here and
    `semiInt` carries no remaining hypothesis.  (The VALUE identity
    `semiInt ≃ π/2` is a SEPARATE, untouched named-open obligation living in
    `SemicircleIntegral.SemicircleValue`; it is not in scope of this module.)

See the foot-of-file ledger for the precise PROVED accounting.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Int`/`Q'`.  Axiom-gate at the foot of the file.
-/

import YMGap.Continuum.SemicircleRate

namespace YMGap.Continuum.SemicircleBoundClosed

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SemicircleIntegral
open YMGap.Continuum.SemicircleConvClosed
open YMGap.Continuum.SemicircleValueRes

/-! ## 0. A shared positivity helper -/

/-- **Positive numerator is preserved upward.**  If `0 < q.num` and `q ≤ r` then
`0 < r.num` (the cross-product `q.num·r.den ≤ r.num·q.den` with positive
denominators forces `r.num > 0`).  Constructive case split (no `by_contra`). -/
theorem posNum_of_le {q r : Q'} (hq : 0 < q.num) (h : q ≤ r) : 0 < r.num := by
  have hcross : q.num * (r.den : Int) ≤ r.num * (q.den : Int) := h
  have hqd : (0 : Int) < (q.den : Int) := by exact_mod_cast q.den_pos
  have hrd : (0 : Int) < (r.den : Int) := by exact_mod_cast r.den_pos
  rcases Int.lt_or_le 0 r.num with hr | hr
  · exact hr
  · -- r.num ≤ 0 : RHS ≤ 0 < LHS, contradiction
    have hLpos : (0 : Int) < q.num * (r.den : Int) := Int.mul_pos hq hrd
    have hRnonpos : r.num * (q.den : Int) ≤ 0 :=
      Int.mul_nonpos_of_nonpos_of_nonneg hr (Int.le_of_lt hqd)
    omega

/-! ## 1. Monotonicity of the rational ceiling `qCeilNat` -/

/-- **Nat floor-division monotonicity from a cross-multiplied bound.**  For
positive denominators `b, d`, if `a·d ≤ c·b` then `a / b ≤ c / d`. -/
theorem nat_div_le_div_of_cross {a b c d : Nat} (hb : 0 < b) (hd : 0 < d)
    (h : a * d ≤ c * b) : a / b ≤ c / d := by
  -- a / b ≤ c / d  ⟺  (a/b) * d ≤ c   (via `Nat.le_div_iff_mul_le`)
  rw [Nat.le_div_iff_mul_le hd]
  -- (a/b)*d ≤ c : multiply by b>0 and cancel.  (a/b)*b ≤ a, so (a/b)*d*b ≤ a*d ≤ c*b.
  have hdiv : a / b * b ≤ a := Nat.div_mul_le_self a b
  have hstep : (a / b * d) * b ≤ c * b := by
    -- (a/b*d)*b = (a/b*b)*d ≤ a*d ≤ c*b
    have he : (a / b * d) * b = (a / b * b) * d := by
      rw [Nat.mul_right_comm]
    rw [he]
    exact Nat.le_trans (Nat.mul_le_mul_right d hdiv) h
  exact Nat.le_of_mul_le_mul_right hstep hb

/-- **The rational ceiling is monotone.**  `q ≤ r ⟹ qCeilNat q ≤ qCeilNat r`.
If `q.num ≤ 0` the left ceiling is `0`; otherwise `0 < q.num` forces `0 < r.num`
(from the cross-multiplied `q ≤ r`), and both ceilings reduce to the
floor-division `num.toNat / den + 1`, monotone by `nat_div_le_div_of_cross`. -/
theorem qCeilNat_mono {q r : Q'} (h : q ≤ r) : qCeilNat q ≤ qCeilNat r := by
  unfold qCeilNat
  by_cases hq : 0 < q.num
  · -- 0 < q.num ⟹ 0 < r.num (else the cross-product fails)
    have hcross : q.num * (r.den : Int) ≤ r.num * (q.den : Int) := h
    have hr : 0 < r.num := posNum_of_le hq h
    rw [if_pos hq, if_pos hr]
    -- reduce to Nat floor-div monotonicity
    refine Nat.add_le_add_right ?_ 1
    -- cross-product in Nat: q.num.toNat · r.den ≤ r.num.toNat · q.den
    have hqtoNat : (q.num.toNat : Int) = q.num := Int.toNat_of_nonneg (Int.le_of_lt hq)
    have hrtoNat : (r.num.toNat : Int) = r.num := Int.toNat_of_nonneg (Int.le_of_lt hr)
    have hnatcross : q.num.toNat * r.den ≤ r.num.toNat * q.den := by
      have hI : (q.num.toNat : Int) * (r.den : Int) ≤ (r.num.toNat : Int) * (q.den : Int) := by
        rw [hqtoNat, hrtoNat]; exact hcross
      have hI' : ((q.num.toNat * r.den : Nat) : Int) ≤ ((r.num.toNat * q.den : Nat) : Int) := by
        push_cast; exact hI
      exact_mod_cast hI'
    exact nat_div_le_div_of_cross q.den_pos r.den_pos hnatcross
  · -- q.num ≤ 0 ⟹ qCeilNat q = 0 ≤ anything
    rw [if_neg hq]
    exact Nat.zero_le _

/-! ## 2. The antitone outer rate `semiRateB ε := qCeilNat (128/ε²)`

The completeness backbone needs an antitone rate `M : Q' → Nat` (`MmonoPred`).
The stored shape `qCeilNat ((16·ε)·(16·ε)) = qCeilNat (256·ε²)` is the WRONG
shape — it DECREASES as `ε → 0`, so it is neither antitone nor a usable Cauchy
rate.  We supply the correct antitone shape `qCeilNat (128/ε²)`, where `128/ε²`
is expressed without a division operator as the explicit rational
`128·den(ε)² / num(ε)²` (positive for `ε > 0`). -/

/-- `0 < n ⟹ 0 < n.toNat` for `n : Int`. -/
theorem toNat_pos_of_pos {n : Int} (h : 0 < n) : 0 < n.toNat := by
  have hcast : (n.toNat : Int) = n := Int.toNat_of_nonneg (Int.le_of_lt h)
  have : (0 : Int) < (n.toNat : Int) := by rw [hcast]; exact h
  exact_mod_cast this

/-- The explicit rational `128/ε² = 128·den(ε)² / num(ε)²` (for `ε > 0`, so
`num(ε) > 0` and `num(ε).toNat > 0`).  Built with `mkPos` over the positive
denominator `num(ε).toNat²`. -/
def recipSq (ε : Q') : Q' :=
  if h : 0 < ε.num then
    Q'.mkPos (128 * (ε.den : Int) * (ε.den : Int))
      (ε.num.toNat * ε.num.toNat)
      (Nat.mul_pos (toNat_pos_of_pos h) (toNat_pos_of_pos h))
  else Q'.ofNat 0

/-- **`recipSq` is antitone for positive arguments.**  For `0 < δ ≤ ε`,
`recipSq ε ≤ recipSq δ` (the positive reciprocal-square anti-monotonicity:
`(1/ε)² ≤ (1/δ)²` from `δ ≤ ε`).  Pure cross-multiplied `Int` inequality. -/
theorem recipSq_anti {δ ε : Q'} (hδ : (0 : Q') < δ) (hδε : δ ≤ ε) :
    recipSq ε ≤ recipSq δ := by
  -- 0 < δ and δ ≤ ε give 0 < ε ; extract num/den positivity
  have hδnum : 0 < δ.num := by
    have hraw : (0 : Q').num * (δ.den : Int) < δ.num * ((0 : Q').den : Int) := hδ
    have h0n : (0 : Q').num = 0 := by decide
    have h0d : ((0 : Q').den : Int) = 1 := by decide
    rw [h0n, h0d, Int.zero_mul, Int.mul_one] at hraw
    exact hraw
  have hεnum : 0 < ε.num := posNum_of_le hδnum hδε
  unfold recipSq
  rw [dif_pos hεnum, dif_pos hδnum]
  -- goal: mkPos (128·dε²) (nε²) ≤ mkPos (128·dδ²) (nδ²)
  -- cross product: 128·dε²·nδ² ≤ 128·dδ²·nε²   (Int)
  show (Q'.mkPos (128 * (ε.den : Int) * (ε.den : Int))
        (ε.num.toNat * ε.num.toNat) _).num
      * ((Q'.mkPos (128 * (δ.den : Int) * (δ.den : Int))
          (δ.num.toNat * δ.num.toNat) _).den : Int)
    ≤ (Q'.mkPos (128 * (δ.den : Int) * (δ.den : Int))
        (δ.num.toNat * δ.num.toNat) _).num
      * ((Q'.mkPos (128 * (ε.den : Int) * (ε.den : Int))
          (ε.num.toNat * ε.num.toNat) _).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_num, Q'.mkPos_den, Q'.mkPos_den]
  -- cast toNat back to num
  have hεtoNat : (ε.num.toNat : Int) = ε.num := Int.toNat_of_nonneg (Int.le_of_lt hεnum)
  have hδtoNat : (δ.num.toNat : Int) = δ.num := Int.toNat_of_nonneg (Int.le_of_lt hδnum)
  have hεsq : ((ε.num.toNat * ε.num.toNat : Nat) : Int) = ε.num * ε.num := by
    push_cast [hεtoNat]; rfl
  have hδsq : ((δ.num.toNat * δ.num.toNat : Nat) : Int) = δ.num * δ.num := by
    push_cast [hδtoNat]; rfl
  rw [hεsq, hδsq]
  -- goal: 128·dε²·(nδ²) ≤ 128·dδ²·(nε²)
  -- from δ ≤ ε i.e. nδ·dε ≤ nε·dδ ; square both sides (both nonneg).
  have hcross : δ.num * (ε.den : Int) ≤ ε.num * (δ.den : Int) := hδε
  have hδd : (0 : Int) ≤ (δ.den : Int) := Int.natCast_nonneg _
  have hεd : (0 : Int) ≤ (ε.den : Int) := Int.natCast_nonneg _
  have hδn0 : (0 : Int) ≤ δ.num := Int.le_of_lt hδnum
  have hεn0 : (0 : Int) ≤ ε.num := Int.le_of_lt hεnum
  -- both products nonneg
  have hL0 : (0 : Int) ≤ δ.num * (ε.den : Int) := Int.mul_nonneg hδn0 hεd
  have hR0 : (0 : Int) ≤ ε.num * (δ.den : Int) := Int.mul_nonneg hεn0 hδd
  -- square the inequality: (nδ·dε)² ≤ (nε·dδ)²
  have hsq : (δ.num * (ε.den : Int)) * (δ.num * (ε.den : Int))
      ≤ (ε.num * (δ.den : Int)) * (ε.num * (δ.den : Int)) :=
    Int.mul_le_mul hcross hcross hL0 (Int.le_trans hL0 hcross)
  -- LHS² = nδ²·dε² ; RHS² = nε²·dδ²
  have hLexp : (δ.num * (ε.den : Int)) * (δ.num * (ε.den : Int))
      = (ε.den : Int) * (ε.den : Int) * (δ.num * δ.num) := by ac_rfl
  have hRexp : (ε.num * (δ.den : Int)) * (ε.num * (δ.den : Int))
      = (δ.den : Int) * (δ.den : Int) * (ε.num * ε.num) := by ac_rfl
  rw [hLexp, hRexp] at hsq
  -- multiply both by 128 ≥ 0 and reshape to match the goal
  have h128 : (0 : Int) ≤ 128 := by decide
  have hscaled : 128 * ((ε.den : Int) * (ε.den : Int) * (δ.num * δ.num))
      ≤ 128 * ((δ.den : Int) * (δ.den : Int) * (ε.num * ε.num)) :=
    Int.mul_le_mul_of_nonneg_left hsq h128
  -- goal shape: 128·dε·dε·(nδ·nδ) ≤ 128·dδ·dδ·(nε·nε)
  have hLgoal : 128 * (ε.den : Int) * (ε.den : Int) * (δ.num * δ.num)
      = 128 * ((ε.den : Int) * (ε.den : Int) * (δ.num * δ.num)) := by ac_rfl
  have hRgoal : 128 * (δ.den : Int) * (δ.den : Int) * (ε.num * ε.num)
      = 128 * ((δ.den : Int) * (δ.den : Int) * (ε.num * ε.num)) := by ac_rfl
  rw [hLgoal, hRgoal]
  exact hscaled

/-- **The concrete antitone outer rate** `semiRateB ε := qCeilNat (128/ε²)`. -/
def semiRateB (ε : Q') : Nat := qCeilNat (recipSq ε)

/-- **`semiRateB` is antitone** (`CReal.MmonoPred`): for `0 < δ ≤ ε`,
`semiRateB ε ≤ semiRateB δ`, by `recipSq_anti` then `qCeilNat_mono`. -/
theorem semiRateB_mono : CReal.MmonoPred semiRateB := by
  intro ε δ hδ hδε
  exact qCeilNat_mono (recipSq_anti hδ hδε)

/-! ## 3. The nested refinement bound (the genuine Riemann convergence content)

The genuine content of Riemann convergence is the inter-resolution refinement
bound: the gap `semiSum P − semiSum (P·Q)` between a mesh and its `Q`-fold
refinement is `≤ refBound P := 2·c` (for any rational `c > 0` with `2/P ≤ c·c`),
because regrouping by cells turns it into the cell-sum of the per-cell √-Hölder
differences, each `≤ lebW(P)·c` (`SemicircleConvClosed.semiSum_refine_leRat_cell`),
summed over the `P` cells to `Σ_{i<P} lebW(P)·c = P·(2/P)·c = 2·c`.

### The total per-cell family (dependent-`hi` removed) -/

/-- The cell-`i` refinement sum as a TOTAL `Nat → CReal` (no `i < P`
side-condition): `Σ_{s<Q} cellTerm P Q hP i hi hPQ s` when `i < P`, else `czero`.
This packages `SemicircleConvClosed.semiSum_refine_leRat_cell` into a uniform
family that `leRat_csum` can sum over all `i`. -/
def cellSum (P Q : Nat) (hP : 0 < P) (hPQ : 0 < P * Q) (i : Nat) : CReal :=
  if hi : i < P then CReal.csum (fun s => cellTerm P Q hP i hi hPQ s) Q
  else CReal.czero

/-- **Per-cell bound, uniform in `i`.**  Each `cellSum i` is `≤ lebW(P)·c`.  For
`i < P` this is `SemicircleConvClosed.semiSum_refine_leRat_cell`; for `i ≥ P` the
term is `czero ≤ lebW(P)·c` (the bound is nonnegative: `lebW P ≥ 0`, `c > 0`). -/
theorem cellSum_leRat (P Q : Nat) (hP : 0 < P) (hPQ : 0 < P * Q) (hQ : 0 < Q)
    (c : Q') (hc : (0 : Q') < c) (hc2 : Q'.mkPos 2 P hP ≤ c * c) (i : Nat) :
    CReal.leRat (cellSum P Q hP hPQ i) (lebW P hP * c) := by
  unfold cellSum
  by_cases hi : i < P
  · rw [dif_pos hi]
    exact semiSum_refine_leRat_cell P Q hP i hi hPQ hQ c hc hc2
  · rw [dif_neg hi]
    -- czero ≤ lebW P · c  (the bound is ≥ 0)
    have hwc : (0 : Q') ≤ lebW P hP * c :=
      Q'.mul_nonneg _ _ (lebW_nonneg hP) (Q'.le_of_lt hc)
    exact CReal.leRat_of_eventually ⟨0, fun n _ =>
      (by exact hwc : (CReal.czero.approx n) ≤ lebW P hP * c)⟩

/-! ### The bound-side collapse `Σ_{i<P} lebW(P)·c ≃ 2·c` -/

/-- **`P·(2/P) ≃ 2`** (the Lebesgue total mass).  `ofNat P · lebW P ≃ ofNat 2`,
cross-multiplied: `(P·2)·1 = 2·P`. -/
theorem nat_mul_lebW (P : Nat) (hP : 0 < P) :
    (Q'.ofNat P * lebW P hP).eqv (Q'.ofNat 2) := by
  show (Q'.ofNat P * lebW P hP).num * ((Q'.ofNat 2).den : Int)
      = (Q'.ofNat 2).num * ((Q'.ofNat P * lebW P hP).den : Int)
  rw [show (Q'.ofNat P * lebW P hP).num = (Q'.ofNat P).num * (lebW P hP).num from rfl,
    show ((Q'.ofNat P * lebW P hP).den : Int)
        = ((Q'.ofNat P).den : Int) * ((lebW P hP).den : Int) from Q'.mul_den_cast _ _,
    show (lebW P hP).num = (2 : Int) from Q'.mkPos_num _ _ _,
    show (lebW P hP).den = P from Q'.mkPos_den _ _ _]
  have hPnum : (Q'.ofNat P).num = (P : Int) := rfl
  have hPden : ((Q'.ofNat P).den : Int) = 1 := rfl
  have h2num : (Q'.ofNat 2).num = (2 : Int) := rfl
  have h2den : ((Q'.ofNat 2).den : Int) = 1 := rfl
  rw [hPnum, hPden, h2num, h2den, Int.one_mul, Int.mul_one]
  -- goal: (P * 2) = 2 * P
  exact Int.mul_comm (P : Int) 2

/-- **The bound side `Σ_{i<P} lebW(P)·c ≃ 2·c`.** -/
theorem finSum_cellBound_eqv (P : Nat) (hP : 0 < P) (c : Q') :
    (RationalTail.finSum (fun _ => lebW P hP * c) P).eqv (Q'.ofNat 2 * c) := by
  refine Q'.eqv_trans _ _ _ (finSum_const_eqv (lebW P hP * c) P) ?_
  -- ofNat P · (lebW P · c) ≃ (ofNat P · lebW P)·c ≃ ofNat 2 · c
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat P) (lebW P hP) c)) ?_
  exact Q'.mul_eqv_congr_right _ _ c (nat_mul_lebW P hP)

/-- **The cell-sum is `≤ 2·c`.**  Sum the per-cell bounds `cellSum_leRat` over the
`P` cells via `leRat_csum`, then collapse `Σ_{i<P} lebW(P)·c ≃ 2·c`. -/
theorem csum_cellSum_leRat (P Q : Nat) (hP : 0 < P) (hPQ : 0 < P * Q) (hQ : 0 < Q)
    (c : Q') (hc : (0 : Q') < c) (hc2 : Q'.mkPos 2 P hP ≤ c * c) :
    CReal.leRat (CReal.csum (cellSum P Q hP hPQ) P) (Q'.ofNat 2 * c) := by
  have hsum : CReal.leRat (CReal.csum (cellSum P Q hP hPQ) P)
      (RationalTail.finSum (fun _ => lebW P hP * c) P) :=
    CReal.leRat_csum (cellSum P Q hP hPQ) (fun _ => lebW P hP * c)
      (fun i => cellSum_leRat P Q hP hPQ hQ c hc hc2 i) P
  exact CReal.leRat_mono hsum (Q'.le_of_eqv (finSum_cellBound_eqv P hP c))

/-! ### The approx-level identification of the value difference with the cell-sum

The genuine Riemann content is the identification
`semiSum P − semiSum (P·Q) ≃ Σ_{i<P} cellSum i` at every approximation index `k`.
Both sides are finite rational sums of the SAME `heronSeq` atoms (the per-node
square roots), so the identity is a pure `Q'`-level `finSum` rearrangement:
block-reindex the refined sum by cells (`SemicircleValueRes.finSum_block`), pull
the cell weight through the telescoping `lebW P = Q·lebW(P·Q)`
(`SemicircleValueRes.lebW_telescope`), and split each cell. -/

/-- Negation of a finite sum: `-(Σ f) ≃ Σ (−f)`. -/
theorem finSum_neg (f : RationalTail.QSeq) :
    ∀ n, (-(RationalTail.finSum f n)).eqv (RationalTail.finSum (fun i => -(f i)) n)
  | 0 => by
      show (-(0 : Q')).eqv (0 : Q')
      decide
  | n + 1 => by
      show (-(RationalTail.finSum f n + f n)).eqv
          (RationalTail.finSum (fun i => -(f i)) n + -(f n))
      refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (RationalTail.finSum f n) (f n)) ?_
      exact Q'.add_eqv_congr_right _ _ (-(f n)) (finSum_neg f n)

/-- The per-node heron value at approx index `k`: `(nodeWeight n hn j).approx k`
for `j < n`, which is `heronSeq (oneMinusSqNode n j ..) k`, the same atom the
`cellTerm` square roots use. -/
theorem nodeWeight_approx_dif (n : Nat) (hn : 0 < n) (j : Nat) (hj : j < n) (k : Nat) :
    (nodeWeight n hn j).approx k =
      (CReal.sqrtFrom (oneMinusSqNode n j hn hj) (nodeLB n hn)
        (oneMinusSqNode_pos hn hj) (nodeLB_pos hn) (nodeLB_sq_le hn hj)).approx k := by
  unfold nodeWeight
  rw [dif_pos hj]

/-- **The per-cell value identity.**  For `i < P`, the cell-`i` contribution to the
value difference,
`lebW(P)·√cell_i + (−Σ_{s<Q} lebW(P·Q)·√node_{iQ+s})`, equals the cell-sum atom
`(cellSum i).approx k = Σ_{s<Q} lebW(P·Q)·(√cell_i − √node_{iQ+s})`.  Pure `Q'`
`finSum` rearrangement: telescope the weight `lebW(P) = Q·lebW(P·Q)` and split the
constant cell value across the `Q` sub-nodes. -/
theorem cell_value_eqv (P Q : Nat) (hP : 0 < P) (hPQ : 0 < P * Q) (hQ : 0 < Q)
    (i : Nat) (hi : i < P) (k : Nat) :
    ((lebW P hP * (nodeWeight P hP i).approx k)
        + (-(RationalTail.finSum
              (fun s => lebW (P * Q) hPQ * (nodeWeight (P * Q) hPQ (i * Q + s)).approx k) Q))).eqv
      ((cellSum P Q hP hPQ i).approx k) := by
  -- RHS: (cellSum i).approx k = finSum (fun s => (cellTerm ... s).approx k) Q
  have hcellSum_approx : (cellSum P Q hP hPQ i).approx k
      = RationalTail.finSum (fun s => (cellTerm P Q hP i hi hPQ s).approx k) Q := by
    unfold cellSum
    rw [dif_pos hi]
    exact CReal.csum_approx (fun s => cellTerm P Q hP i hi hPQ s) Q k
  rw [hcellSum_approx]
  -- (cellTerm ... s).approx k = lebW PQ * (((nodeWeight P hP i).approx k) + -(nodeWeight PQ (iQ+s)).approx k)  for s < Q
  have hterm : ∀ s, s < Q →
      (cellTerm P Q hP i hi hPQ s).approx k
        = lebW (P * Q) hPQ * (((nodeWeight P hP i).approx k) + -((nodeWeight (P * Q) hPQ (i * Q + s)).approx k)) := by
    intro s hs
    have hj : i * Q + s < P * Q := by
      have hiQ : i * Q + Q ≤ P * Q := by
        have : (i + 1) * Q ≤ P * Q := Nat.mul_le_mul_right Q hi
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      omega
    have hct : cellTerm P Q hP i hi hPQ s
        = CReal.mul (CReal.ofQ' (lebW (P * Q) hPQ))
          (CReal.add
            (CReal.sqrtFrom (oneMinusSqNode P i hP hi) (nodeLB P hP)
              (oneMinusSqNode_pos hP hi) (nodeLB_pos hP) (nodeLB_sq_le hP hi))
            (CReal.neg
              (CReal.sqrtFrom (oneMinusSqNode (P * Q) (i * Q + s) hPQ hj) (nodeLB (P * Q) hPQ)
                (oneMinusSqNode_pos hPQ hj) (nodeLB_pos hPQ) (nodeLB_sq_le hPQ hj)))) := by
      unfold cellTerm; rw [dif_pos hj]
    rw [hct]
    -- approx of mul/add/neg/ofQ' are definitional
    show lebW (P * Q) hPQ
        * ((CReal.sqrtFrom (oneMinusSqNode P i hP hi) (nodeLB P hP)
              (oneMinusSqNode_pos hP hi) (nodeLB_pos hP) (nodeLB_sq_le hP hi)).approx k
            + -((CReal.sqrtFrom (oneMinusSqNode (P * Q) (i * Q + s) hPQ hj) (nodeLB (P * Q) hPQ)
                (oneMinusSqNode_pos hPQ hj) (nodeLB_pos hPQ) (nodeLB_sq_le hPQ hj)).approx k))
      = lebW (P * Q) hPQ * (((nodeWeight P hP i).approx k) + -((nodeWeight (P * Q) hPQ (i * Q + s)).approx k))
    rw [nodeWeight_approx_dif P hP i hi k, nodeWeight_approx_dif (P * Q) hPQ (i * Q + s) hj k]
  -- RHS finSum ≃ finSum (fun s => lebW PQ * (((nodeWeight P hP i).approx k) + -(nwPQ_{iQ+s}))) Q
  have hRHS : (RationalTail.finSum (fun s => (cellTerm P Q hP i hi hPQ s).approx k) Q).eqv
      (RationalTail.finSum
        (fun s => lebW (P * Q) hPQ * (((nodeWeight P hP i).approx k) + -((nodeWeight (P * Q) hPQ (i * Q + s)).approx k))) Q) := by
    -- equality on a Q-truncated sum (the atoms agree for s < Q)
    have key : ∀ m, m ≤ Q →
        (RationalTail.finSum (fun s => (cellTerm P Q hP i hi hPQ s).approx k) m).eqv
        (RationalTail.finSum
          (fun s => lebW (P * Q) hPQ * (((nodeWeight P hP i).approx k) + -((nodeWeight (P * Q) hPQ (i * Q + s)).approx k))) m) := by
      intro m
      induction m with
      | zero => intro _; exact Q'.eqv_refl 0
      | succ t ih =>
        intro htQ
        have htlt : t < Q := Nat.lt_of_lt_of_le (Nat.lt_succ_self t) htQ
        have htQ' : t ≤ Q := Nat.le_of_lt htlt
        show (RationalTail.finSum (fun s => (cellTerm P Q hP i hi hPQ s).approx k) t
              + (cellTerm P Q hP i hi hPQ t).approx k).eqv
            (RationalTail.finSum
              (fun s => lebW (P * Q) hPQ * (((nodeWeight P hP i).approx k) + -((nodeWeight (P * Q) hPQ (i * Q + s)).approx k))) t
              + lebW (P * Q) hPQ * (((nodeWeight P hP i).approx k) + -((nodeWeight (P * Q) hPQ (i * Q + t)).approx k)))
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ ((cellTerm P Q hP i hi hPQ t).approx k) (ih htQ')) ?_
        refine Q'.add_eqv_congr_left _ _ _ ?_
        rw [hterm t htlt]
        exact Q'.eqv_refl _
    exact key Q (Nat.le_refl Q)
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hRHS)
  -- Now show LHS ≃ finSum (fun s => lebW PQ * (((nodeWeight P hP i).approx k) + -nwPQ)) Q
  -- LHS = (lebW P * ((nodeWeight P hP i).approx k)) + (- finSum (fun s => lebW PQ * nwPQ) Q)
  -- Step 1: lebW P * ((nodeWeight P hP i).approx k) ≃ finSum (fun s => lebW PQ * ((nodeWeight P hP i).approx k)) Q
  have hA : (lebW P hP * ((nodeWeight P hP i).approx k)).eqv
      (RationalTail.finSum (fun _ => lebW (P * Q) hPQ * ((nodeWeight P hP i).approx k)) Q) := by
    -- lebW P * ((nodeWeight P hP i).approx k) ≃ (ofNat Q * lebW PQ) * ((nodeWeight P hP i).approx k) ≃ ofNat Q * (lebW PQ * ((nodeWeight P hP i).approx k)) ≃ Σ (lebW PQ * ((nodeWeight P hP i).approx k))
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ ((nodeWeight P hP i).approx k) (lebW_telescope P Q hP hPQ)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (Q'.ofNat Q) (lebW (P * Q) hPQ) ((nodeWeight P hP i).approx k)) ?_
    exact Q'.eqv_symm (finSum_const_eqv (lebW (P * Q) hPQ * ((nodeWeight P hP i).approx k)) Q)
  -- Step 2: - finSum (fun s => lebW PQ * nwPQ) Q ≃ finSum (fun s => -(lebW PQ * nwPQ)) Q
  have hB := finSum_neg
    (fun s => lebW (P * Q) hPQ * (nodeWeight (P * Q) hPQ (i * Q + s)).approx k) Q
  -- LHS ≃ Σ (lebW PQ * ((nodeWeight P hP i).approx k)) + Σ (-(lebW PQ * nwPQ)) ≃ Σ ((lebW PQ*((nodeWeight P hP i).approx k)) + -(lebW PQ*nwPQ))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hA hB) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (RationalTail.finSum_add
      (fun _ => lebW (P * Q) hPQ * ((nodeWeight P hP i).approx k))
      (fun s => -(lebW (P * Q) hPQ * (nodeWeight (P * Q) hPQ (i * Q + s)).approx k)) Q)) ?_
  -- termwise: (lebW PQ * ((nodeWeight P hP i).approx k)) + -(lebW PQ * nwPQ) ≃ lebW PQ * (((nodeWeight P hP i).approx k) + -nwPQ)
  refine RationalTail.finSum_eqv_congr _ _ (fun s => ?_) Q
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _
    (Q'.mul_add_eqv (lebW (P * Q) hPQ) ((nodeWeight P hP i).approx k) (-((nodeWeight (P * Q) hPQ (i * Q + s)).approx k))) ?_)
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.mul_neg_eqv (lebW (P * Q) hPQ) ((nodeWeight (P * Q) hPQ (i * Q + s)).approx k))

/-- The approx form of `semiSum`: `(semiSum n hn).approx k = Σ_{i<n} lebW(n)·√node_i`. -/
theorem semiSum_approx (n : Nat) (hn : 0 < n) (k : Nat) :
    (semiSum n hn).approx k
      = RationalTail.finSum (fun i => lebW n hn * (nodeWeight n hn i).approx k) n := by
  show (CReal.csum (fun i => CReal.mul (CReal.ofQ' (lebW n hn)) (nodeWeight n hn i)) n).approx k
      = RationalTail.finSum (fun i => lebW n hn * (nodeWeight n hn i).approx k) n
  exact CReal.csum_approx (fun i => CReal.mul (CReal.ofQ' (lebW n hn)) (nodeWeight n hn i)) n k

/-- **The full value-difference identity.**  At every approx index `k`,
`(semiSum P − semiSum (P·Q)).approx k ≃ (csum (cellSum) P).approx k` — the
block-reindexed cell-sum of the per-cell √-Hölder differences.  Assembled from
`finSum_block` (refined-sum reindex), `finSum_neg`/`finSum_add` (linearity), and
the per-cell identity `cell_value_eqv`. -/
theorem value_diff_eqv (P Q : Nat) (hP : 0 < P) (hPQ : 0 < P * Q) (hQ : 0 < Q) (k : Nat) :
    ((CReal.add (semiSum P hP) (CReal.neg (semiSum (P * Q) hPQ))).approx k).eqv
      ((CReal.csum (cellSum P Q hP hPQ) P).approx k) := by
  -- RHS = finSum (fun i => (cellSum i).approx k) P
  have hRHS : (CReal.csum (cellSum P Q hP hPQ) P).approx k
      = RationalTail.finSum (fun i => (cellSum P Q hP hPQ i).approx k) P :=
    CReal.csum_approx (cellSum P Q hP hPQ) P k
  rw [hRHS]
  -- LHS = (semiSum P).approx k + -((semiSum PQ).approx k)
  show ((semiSum P hP).approx k + -((semiSum (P * Q) hPQ).approx k)).eqv
      (RationalTail.finSum (fun i => (cellSum P Q hP hPQ i).approx k) P)
  rw [semiSum_approx P hP k, semiSum_approx (P * Q) hPQ k]
  -- reindex the refined sum by blocks: Σ_{j<PQ} g j ≃ Σ_{i<P} Σ_{s<Q} g (iQ+s)
  have hblock := finSum_block
    (fun j => lebW (P * Q) hPQ * (nodeWeight (P * Q) hPQ j).approx k) Q P
  -- rewrite the negated refined sum via the block identity
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hblock)) ?_
  -- now: Σ_i A_i + -(Σ_i B_i)  with A_i = lebW P · nwP_i, B_i = Σ_s lebW PQ · nwPQ_{iQ+s}
  -- push the neg inside, then merge the two outer sums
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (finSum_neg
      (fun i => RationalTail.finSum
        (fun s => lebW (P * Q) hPQ * (nodeWeight (P * Q) hPQ (i * Q + s)).approx k) Q) P)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (RationalTail.finSum_add
      (fun i => lebW P hP * (nodeWeight P hP i).approx k)
      (fun i => -(RationalTail.finSum
        (fun s => lebW (P * Q) hPQ * (nodeWeight (P * Q) hPQ (i * Q + s)).approx k) Q)) P)) ?_
  -- termwise: A_i + -(B_i) ≃ (cellSum i).approx k  — BUT cell_value_eqv needs i < P.
  -- Use a length-P-truncated induction so each term carries its `i < P`.
  have key : ∀ m, m ≤ P →
      (RationalTail.finSum (fun i =>
        lebW P hP * (nodeWeight P hP i).approx k
          + -(RationalTail.finSum
              (fun s => lebW (P * Q) hPQ * (nodeWeight (P * Q) hPQ (i * Q + s)).approx k) Q)) m).eqv
      (RationalTail.finSum (fun i => (cellSum P Q hP hPQ i).approx k) m) := by
    intro m
    induction m with
    | zero => intro _; exact Q'.eqv_refl 0
    | succ t ih =>
      intro htP
      have htlt : t < P := Nat.lt_of_lt_of_le (Nat.lt_succ_self t) htP
      have htP' : t ≤ P := Nat.le_of_lt htlt
      show (RationalTail.finSum (fun i =>
            lebW P hP * (nodeWeight P hP i).approx k
              + -(RationalTail.finSum
                  (fun s => lebW (P * Q) hPQ * (nodeWeight (P * Q) hPQ (i * Q + s)).approx k) Q)) t
            + (lebW P hP * (nodeWeight P hP t).approx k
              + -(RationalTail.finSum
                  (fun s => lebW (P * Q) hPQ * (nodeWeight (P * Q) hPQ (t * Q + s)).approx k) Q))).eqv
          (RationalTail.finSum (fun i => (cellSum P Q hP hPQ i).approx k) t
            + (cellSum P Q hP hPQ t).approx k)
      exact Q'.add_eqv_congr' (ih htP') (cell_value_eqv P Q hP hPQ hQ t htlt k)
  exact key P (Nat.le_refl P)

/-- **The nested refinement bound** (the genuine Riemann convergence content).
`leRat (semiSum P + (−semiSum (P·Q))) (2·c)` for any rational `c > 0` with
`2/P ≤ c·c`.  By `value_diff_eqv` the value difference agrees, at every approx
index, with the cell-sum `csum (cellSum) P`, whose `leRat` bound `2·c` is
`csum_cellSum_leRat`; transport via `leRat_congr`. -/
theorem semiSum_refine_leRat (P Q : Nat) (hP : 0 < P) (hPQ : 0 < P * Q) (hQ : 0 < Q)
    (c : Q') (hc : (0 : Q') < c) (hc2 : Q'.mkPos 2 P hP ≤ c * c) :
    CReal.leRat (CReal.add (semiSum P hP) (CReal.neg (semiSum (P * Q) hPQ)))
      (Q'.ofNat 2 * c) :=
  CReal.leRat_congr (value_diff_eqv P Q hP hPQ hQ) (csum_cellSum_leRat P Q hP hPQ hQ c hc hc2)

/-! ## 4. The REVERSE refinement bound `semiSum (P·Q) − semiSum P ≤ 2·c`

`SemiLeRatBound` is two-sided, so we also need the gap in the OTHER direction.
By symmetry of `SemicircleConverge.nodeWeight_holder` (which bounds `√u − √v`
for ANY two nodes `u, v` with `u ≤ v + c·c`) and the backward node gap
`SemicircleValueRes.huvc_bwd` (`oneMinusSqNode(P·Q) j ≤ oneMinusSqNode P i + c·c`),
the reverse per-cell difference `√node_{iQ+s} − √cell_i` is `≤ c`; the whole
construction mirrors the forward one with the cell/node roles swapped. -/

open YMGap.Continuum.SemicircleConverge in
/-- The REVERSE per-cell scaled difference `lebW(P·Q)·(√node_{iQ+s} − √cell_i)`. -/
def cellTermRev (P Q : Nat) (hP : 0 < P) (i : Nat) (hi : i < P)
    (hPQ : 0 < P * Q) (s : Nat) : CReal :=
  if hj : i * Q + s < P * Q then
    CReal.mul (CReal.ofQ' (lebW (P * Q) hPQ))
      (CReal.add
        (CReal.sqrtFrom (oneMinusSqNode (P * Q) (i * Q + s) hPQ hj) (nodeLB (P * Q) hPQ)
          (oneMinusSqNode_pos hPQ hj) (nodeLB_pos hPQ) (nodeLB_sq_le hPQ hj))
        (CReal.neg
          (CReal.sqrtFrom (oneMinusSqNode P i hP hi) (nodeLB P hP)
            (oneMinusSqNode_pos hP hi) (nodeLB_pos hP) (nodeLB_sq_le hP hi))))
  else CReal.czero

/-- **Per-sub-node REVERSE bound.**  `cellTermRev … s ≤ lebW(P·Q)·c` for `s < Q`,
via `nodeWeight_holder` (cell/node roles swapped) + `huvc_bwd` + the nonneg
weight scaling. -/
theorem cellTermRev_leRat (P Q : Nat) (hP : 0 < P) (i : Nat) (hi : i < P)
    (hPQ : 0 < P * Q) (s : Nat) (hs : s < Q)
    (c : Q') (hc : (0 : Q') < c) (hc2 : Q'.mkPos 2 P hP ≤ c * c) :
    CReal.leRat (cellTermRev P Q hP i hi hPQ s) (lebW (P * Q) hPQ * c) := by
  have hj : i * Q + s < P * Q := by
    have hiQ : i * Q + Q ≤ P * Q := by
      have : (i + 1) * Q ≤ P * Q := Nat.mul_le_mul_right Q hi
      rw [Nat.add_mul, Nat.one_mul] at this; exact this
    omega
  have hterm : cellTermRev P Q hP i hi hPQ s
      = CReal.mul (CReal.ofQ' (lebW (P * Q) hPQ))
        (CReal.add
          (CReal.sqrtFrom (oneMinusSqNode (P * Q) (i * Q + s) hPQ hj) (nodeLB (P * Q) hPQ)
            (oneMinusSqNode_pos hPQ hj) (nodeLB_pos hPQ) (nodeLB_sq_le hPQ hj))
          (CReal.neg
            (CReal.sqrtFrom (oneMinusSqNode P i hP hi) (nodeLB P hP)
              (oneMinusSqNode_pos hP hi) (nodeLB_pos hP) (nodeLB_sq_le hP hi)))) := by
    unfold cellTermRev; rw [dif_pos hj]
  rw [hterm]
  -- inner √node − √cell ≤ c  (nodeWeight_holder swapped + huvc_bwd)
  have hcell : CReal.leRat
      (CReal.add
        (CReal.sqrtFrom (oneMinusSqNode (P * Q) (i * Q + s) hPQ hj) (nodeLB (P * Q) hPQ)
          (oneMinusSqNode_pos hPQ hj) (nodeLB_pos hPQ) (nodeLB_sq_le hPQ hj))
        (CReal.neg
          (CReal.sqrtFrom (oneMinusSqNode P i hP hi) (nodeLB P hP)
            (oneMinusSqNode_pos hP hi) (nodeLB_pos hP) (nodeLB_sq_le hP hi))))
      c :=
    SemicircleConverge.nodeWeight_holder (P * Q) (i * Q + s) hPQ hj P i hP hi c hc
      (huvc_bwd P Q i s hP hi hs hPQ hj c hc2)
  exact CReal.leRat_smul_nonneg (lebW_nonneg hPQ) hcell

/-- The REVERSE per-cell sum `Σ_{s<Q} cellTermRev … s`, total in `i`. -/
def cellSumRev (P Q : Nat) (hP : 0 < P) (hPQ : 0 < P * Q) (i : Nat) : CReal :=
  if hi : i < P then CReal.csum (fun s => cellTermRev P Q hP i hi hPQ s) Q
  else CReal.czero

/-- **Per-cell REVERSE bound, uniform in `i`.**  `cellSumRev i ≤ lebW(P)·c`. -/
theorem cellSumRev_leRat (P Q : Nat) (hP : 0 < P) (hPQ : 0 < P * Q) (hQ : 0 < Q)
    (c : Q') (hc : (0 : Q') < c) (hc2 : Q'.mkPos 2 P hP ≤ c * c) (i : Nat) :
    CReal.leRat (cellSumRev P Q hP hPQ i) (lebW P hP * c) := by
  unfold cellSumRev
  by_cases hi : i < P
  · rw [dif_pos hi]
    -- Σ_{s<Q} cellTermRev ≤ Σ_{s<Q} lebW(PQ)·c ≃ lebW(P)·c  (length-Q induction)
    have hsum : CReal.leRat
        (CReal.csum (fun s => cellTermRev P Q hP i hi hPQ s) Q)
        (RationalTail.finSum (fun _ => lebW (P * Q) hPQ * c) Q) := by
      have key : ∀ m, m ≤ Q →
          CReal.leRat
            (CReal.csum (fun s => cellTermRev P Q hP i hi hPQ s) m)
            (RationalTail.finSum (fun _ => lebW (P * Q) hPQ * c) m) := by
        intro m
        induction m with
        | zero => intro _; exact CReal.leRat_ofQ' (Q'.le_refl' 0)
        | succ t ih =>
          intro htQ
          have htlt : t < Q := Nat.lt_of_lt_of_le (Nat.lt_succ_self t) htQ
          have htQ' : t ≤ Q := Nat.le_of_lt htlt
          show CReal.leRat
            (CReal.add (CReal.csum (fun s => cellTermRev P Q hP i hi hPQ s) t)
              (cellTermRev P Q hP i hi hPQ t))
            (RationalTail.finSum (fun _ => lebW (P * Q) hPQ * c) t + lebW (P * Q) hPQ * c)
          exact CReal.leRat_add (ih htQ')
            (cellTermRev_leRat P Q hP i hi hPQ t htlt c hc hc2)
      exact key Q (Nat.le_refl Q)
    have hconst : (RationalTail.finSum (fun _ => lebW (P * Q) hPQ * c) Q).eqv
        (lebW P hP * c) := by
      refine Q'.eqv_trans _ _ _ (finSum_const_eqv (lebW (P * Q) hPQ * c) Q) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat Q) (lebW (P * Q) hPQ) c)) ?_
      exact Q'.mul_eqv_congr_right _ _ c (Q'.eqv_symm (lebW_telescope P Q hP hPQ))
    exact CReal.leRat_mono hsum (Q'.le_of_eqv hconst)
  · rw [dif_neg hi]
    have hwc : (0 : Q') ≤ lebW P hP * c :=
      Q'.mul_nonneg _ _ (lebW_nonneg hP) (Q'.le_of_lt hc)
    exact CReal.leRat_of_eventually ⟨0, fun n _ =>
      (by exact hwc : (CReal.czero.approx n) ≤ lebW P hP * c)⟩

/-- **The REVERSE cell-sum is `≤ 2·c`.** -/
theorem csum_cellSumRev_leRat (P Q : Nat) (hP : 0 < P) (hPQ : 0 < P * Q) (hQ : 0 < Q)
    (c : Q') (hc : (0 : Q') < c) (hc2 : Q'.mkPos 2 P hP ≤ c * c) :
    CReal.leRat (CReal.csum (cellSumRev P Q hP hPQ) P) (Q'.ofNat 2 * c) := by
  have hsum : CReal.leRat (CReal.csum (cellSumRev P Q hP hPQ) P)
      (RationalTail.finSum (fun _ => lebW P hP * c) P) :=
    CReal.leRat_csum (cellSumRev P Q hP hPQ) (fun _ => lebW P hP * c)
      (fun i => cellSumRev_leRat P Q hP hPQ hQ c hc hc2 i) P
  exact CReal.leRat_mono hsum (Q'.le_of_eqv (finSum_cellBound_eqv P hP c))

/-- The REVERSE per-cell value identity: for `i < P`,
`(−lebW(P)·√cell_i) + Σ_{s<Q} lebW(P·Q)·√node_{iQ+s} ≃ (cellSumRev i).approx k`. -/
theorem cell_value_rev_eqv (P Q : Nat) (hP : 0 < P) (hPQ : 0 < P * Q) (hQ : 0 < Q)
    (i : Nat) (hi : i < P) (k : Nat) :
    ((RationalTail.finSum
        (fun s => lebW (P * Q) hPQ * (nodeWeight (P * Q) hPQ (i * Q + s)).approx k) Q)
        + (-(lebW P hP * (nodeWeight P hP i).approx k))).eqv
      ((cellSumRev P Q hP hPQ i).approx k) := by
  have hcellSum_approx : (cellSumRev P Q hP hPQ i).approx k
      = RationalTail.finSum (fun s => (cellTermRev P Q hP i hi hPQ s).approx k) Q := by
    unfold cellSumRev
    rw [dif_pos hi]
    exact CReal.csum_approx (fun s => cellTermRev P Q hP i hi hPQ s) Q k
  rw [hcellSum_approx]
  have hterm : ∀ s, s < Q →
      (cellTermRev P Q hP i hi hPQ s).approx k
        = lebW (P * Q) hPQ * ((nodeWeight (P * Q) hPQ (i * Q + s)).approx k
            + -((nodeWeight P hP i).approx k)) := by
    intro s hs
    have hj : i * Q + s < P * Q := by
      have hiQ : i * Q + Q ≤ P * Q := by
        have : (i + 1) * Q ≤ P * Q := Nat.mul_le_mul_right Q hi
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      omega
    have hct : cellTermRev P Q hP i hi hPQ s
        = CReal.mul (CReal.ofQ' (lebW (P * Q) hPQ))
          (CReal.add
            (CReal.sqrtFrom (oneMinusSqNode (P * Q) (i * Q + s) hPQ hj) (nodeLB (P * Q) hPQ)
              (oneMinusSqNode_pos hPQ hj) (nodeLB_pos hPQ) (nodeLB_sq_le hPQ hj))
            (CReal.neg
              (CReal.sqrtFrom (oneMinusSqNode P i hP hi) (nodeLB P hP)
                (oneMinusSqNode_pos hP hi) (nodeLB_pos hP) (nodeLB_sq_le hP hi)))) := by
      unfold cellTermRev; rw [dif_pos hj]
    rw [hct]
    show lebW (P * Q) hPQ
        * ((CReal.sqrtFrom (oneMinusSqNode (P * Q) (i * Q + s) hPQ hj) (nodeLB (P * Q) hPQ)
              (oneMinusSqNode_pos hPQ hj) (nodeLB_pos hPQ) (nodeLB_sq_le hPQ hj)).approx k
            + -((CReal.sqrtFrom (oneMinusSqNode P i hP hi) (nodeLB P hP)
                (oneMinusSqNode_pos hP hi) (nodeLB_pos hP) (nodeLB_sq_le hP hi)).approx k))
      = lebW (P * Q) hPQ * ((nodeWeight (P * Q) hPQ (i * Q + s)).approx k
            + -((nodeWeight P hP i).approx k))
    rw [nodeWeight_approx_dif P hP i hi k, nodeWeight_approx_dif (P * Q) hPQ (i * Q + s) hj k]
  -- RHS finSum ≃ finSum (fun s => lebW PQ * (nwPQ + -nwP)) Q
  have hRHS : (RationalTail.finSum (fun s => (cellTermRev P Q hP i hi hPQ s).approx k) Q).eqv
      (RationalTail.finSum
        (fun s => lebW (P * Q) hPQ * ((nodeWeight (P * Q) hPQ (i * Q + s)).approx k
            + -((nodeWeight P hP i).approx k))) Q) := by
    have key : ∀ m, m ≤ Q →
        (RationalTail.finSum (fun s => (cellTermRev P Q hP i hi hPQ s).approx k) m).eqv
        (RationalTail.finSum
          (fun s => lebW (P * Q) hPQ * ((nodeWeight (P * Q) hPQ (i * Q + s)).approx k
              + -((nodeWeight P hP i).approx k))) m) := by
      intro m
      induction m with
      | zero => intro _; exact Q'.eqv_refl 0
      | succ t ih =>
        intro htQ
        have htlt : t < Q := Nat.lt_of_lt_of_le (Nat.lt_succ_self t) htQ
        have htQ' : t ≤ Q := Nat.le_of_lt htlt
        show (RationalTail.finSum (fun s => (cellTermRev P Q hP i hi hPQ s).approx k) t
              + (cellTermRev P Q hP i hi hPQ t).approx k).eqv
            (RationalTail.finSum
              (fun s => lebW (P * Q) hPQ * ((nodeWeight (P * Q) hPQ (i * Q + s)).approx k
                  + -((nodeWeight P hP i).approx k))) t
              + lebW (P * Q) hPQ * ((nodeWeight (P * Q) hPQ (i * Q + t)).approx k
                  + -((nodeWeight P hP i).approx k)))
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ ((cellTermRev P Q hP i hi hPQ t).approx k) (ih htQ')) ?_
        refine Q'.add_eqv_congr_left _ _ _ ?_
        rw [hterm t htlt]
        exact Q'.eqv_refl _
    exact key Q (Nat.le_refl Q)
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hRHS)
  -- LHS = Σ (lebW PQ · nwPQ) + -(lebW P · nwP)
  -- Step: lebW P · nwP ≃ Σ_{s<Q} (lebW PQ · nwP)
  have hA : (lebW P hP * (nodeWeight P hP i).approx k).eqv
      (RationalTail.finSum (fun _ => lebW (P * Q) hPQ * (nodeWeight P hP i).approx k) Q) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ ((nodeWeight P hP i).approx k) (lebW_telescope P Q hP hPQ)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat Q) (lebW (P * Q) hPQ) ((nodeWeight P hP i).approx k)) ?_
    exact Q'.eqv_symm (finSum_const_eqv (lebW (P * Q) hPQ * (nodeWeight P hP i).approx k) Q)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hA)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (finSum_neg
      (fun _ => lebW (P * Q) hPQ * (nodeWeight P hP i).approx k) Q)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (RationalTail.finSum_add
      (fun s => lebW (P * Q) hPQ * (nodeWeight (P * Q) hPQ (i * Q + s)).approx k)
      (fun _ => -(lebW (P * Q) hPQ * (nodeWeight P hP i).approx k)) Q)) ?_
  refine RationalTail.finSum_eqv_congr _ _ (fun s => ?_) Q
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _
    (Q'.mul_add_eqv (lebW (P * Q) hPQ) ((nodeWeight (P * Q) hPQ (i * Q + s)).approx k)
      (-((nodeWeight P hP i).approx k))) ?_)
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.mul_neg_eqv (lebW (P * Q) hPQ) ((nodeWeight P hP i).approx k))

/-- **The REVERSE full value-difference identity.**
`(semiSum (P·Q) − semiSum P).approx k ≃ (csum cellSumRev P).approx k`. -/
theorem value_diff_rev_eqv (P Q : Nat) (hP : 0 < P) (hPQ : 0 < P * Q) (hQ : 0 < Q) (k : Nat) :
    ((CReal.add (semiSum (P * Q) hPQ) (CReal.neg (semiSum P hP))).approx k).eqv
      ((CReal.csum (cellSumRev P Q hP hPQ) P).approx k) := by
  have hRHS : (CReal.csum (cellSumRev P Q hP hPQ) P).approx k
      = RationalTail.finSum (fun i => (cellSumRev P Q hP hPQ i).approx k) P :=
    CReal.csum_approx (cellSumRev P Q hP hPQ) P k
  rw [hRHS]
  show ((semiSum (P * Q) hPQ).approx k + -((semiSum P hP).approx k)).eqv
      (RationalTail.finSum (fun i => (cellSumRev P Q hP hPQ i).approx k) P)
  rw [semiSum_approx P hP k, semiSum_approx (P * Q) hPQ k]
  have hblock := finSum_block
    (fun j => lebW (P * Q) hPQ * (nodeWeight (P * Q) hPQ j).approx k) Q P
  -- rewrite the refined sum (positive, first summand) via the block identity
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ hblock) ?_
  -- now: (Σ_i B_i) + -(Σ_i A_i)  with A_i = lebW P · nwP_i, B_i = Σ_s ...
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (finSum_neg
      (fun i => lebW P hP * (nodeWeight P hP i).approx k) P)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (RationalTail.finSum_add
      (fun i => RationalTail.finSum
        (fun s => lebW (P * Q) hPQ * (nodeWeight (P * Q) hPQ (i * Q + s)).approx k) Q)
      (fun i => -(lebW P hP * (nodeWeight P hP i).approx k)) P)) ?_
  have key : ∀ m, m ≤ P →
      (RationalTail.finSum (fun i =>
        RationalTail.finSum
          (fun s => lebW (P * Q) hPQ * (nodeWeight (P * Q) hPQ (i * Q + s)).approx k) Q
          + -(lebW P hP * (nodeWeight P hP i).approx k)) m).eqv
      (RationalTail.finSum (fun i => (cellSumRev P Q hP hPQ i).approx k) m) := by
    intro m
    induction m with
    | zero => intro _; exact Q'.eqv_refl 0
    | succ t ih =>
      intro htP
      have htlt : t < P := Nat.lt_of_lt_of_le (Nat.lt_succ_self t) htP
      have htP' : t ≤ P := Nat.le_of_lt htlt
      show (RationalTail.finSum (fun i =>
            RationalTail.finSum
              (fun s => lebW (P * Q) hPQ * (nodeWeight (P * Q) hPQ (i * Q + s)).approx k) Q
              + -(lebW P hP * (nodeWeight P hP i).approx k)) t
            + (RationalTail.finSum
                (fun s => lebW (P * Q) hPQ * (nodeWeight (P * Q) hPQ (t * Q + s)).approx k) Q
              + -(lebW P hP * (nodeWeight P hP t).approx k))).eqv
          (RationalTail.finSum (fun i => (cellSumRev P Q hP hPQ i).approx k) t
            + (cellSumRev P Q hP hPQ t).approx k)
      exact Q'.add_eqv_congr' (ih htP') (cell_value_rev_eqv P Q hP hPQ hQ t htlt k)
  exact key P (Nat.le_refl P)

/-- **The REVERSE nested refinement bound.**
`leRat (semiSum (P·Q) + (−semiSum P)) (2·c)` for `c > 0`, `2/P ≤ c·c`. -/
theorem semiSum_refine_rev_leRat (P Q : Nat) (hP : 0 < P) (hPQ : 0 < P * Q) (hQ : 0 < Q)
    (c : Q') (hc : (0 : Q') < c) (hc2 : Q'.mkPos 2 P hP ≤ c * c) :
    CReal.leRat (CReal.add (semiSum (P * Q) hPQ) (CReal.neg (semiSum P hP)))
      (Q'.ofNat 2 * c) :=
  CReal.leRat_congr (value_diff_rev_eqv P Q hP hPQ hQ)
    (csum_cellSumRev_leRat P Q hP hPQ hQ c hc hc2)

/-! ## 5. The common-refinement assembly ⇒ `SemiLeRatBound semiRateB`

For `m, n ≥ semiRateB ε`, the value gap `seqSemi m − seqSemi n` is bridged through
the common refinement mesh `(m+1)·(n+1)`: telescope
`X − Y = (X − Z) + (Z − Y)`, bound each leg by the (forward / reverse) refinement
bounds at tolerance `2·c` with `c = ε/8`, and collapse `2c + 2c = ε/2 ≤ ε`.  The
tolerance condition `2/P ≤ c·c` follows from `P > 128/ε² = recipSq ε` (the rate
`semiRateB`), a pure rational cross-multiplication. -/

/-- Rational telescope: `x + (−y) ≃ (x + (−z)) + (z + (−y))`. -/
theorem telescope_eqv (x y z : Q') :
    (x + (-y)).eqv ((x + (-z)) + (z + (-y))) := by
  refine Q'.eqv_symm ?_
  -- ((x+-z)+(z+-y)) ≃ (((x+-z)+z)+-y)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (x + (-z)) z (-y))) ?_
  -- (x+-z)+z ≃ x
  have hxz : ((x + (-z)) + z).eqv x := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv x (-z) z) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left x _ _ (Q'.neg_add_self_eqv z)) ?_
    rw [Q'.add_zero']
    exact Q'.eqv_refl x
  exact Q'.add_eqv_congr_right _ _ (-y) hxz

/-- **CReal telescope at the value level.**  `add X (neg Y)` agrees, at every approx
index, with `add (add X (neg Z)) (add Z (neg Y))`. -/
theorem cTelescope_leRat {X Y Z : CReal} {b : Q'}
    (h : CReal.leRat (CReal.add (CReal.add X (CReal.neg Z)) (CReal.add Z (CReal.neg Y))) b) :
    CReal.leRat (CReal.add X (CReal.neg Y)) b := by
  refine CReal.leRat_congr (fun k => ?_) h
  show ((X.approx k) + (-(Y.approx k))).eqv
    (((X.approx k) + (-(Z.approx k))) + ((Z.approx k) + (-(Y.approx k))))
  exact telescope_eqv (X.approx k) (Y.approx k) (Z.approx k)

/-- **`semiSum` is congruent in its `Nat` argument.**  For `a = b`, the two
`semiSum` (at any positivity proofs) agree at every approx index. -/
theorem semiSum_nat_congr {a b : Nat} (hab : a = b) (ha : 0 < a) (hb : 0 < b) (k : Nat) :
    ((semiSum a ha).approx k).eqv ((semiSum b hb).approx k) := by
  subst hab
  exact Q'.eqv_refl _

/-- `ofNat` is monotone from `Nat.le`. -/
theorem ofNat_le_ofNat {a b : Nat} (h : a ≤ b) : Q'.ofNat a ≤ Q'.ofNat b := by
  show (Q'.ofNat a).num * ((Q'.ofNat b).den : Int) ≤ (Q'.ofNat b).num * ((Q'.ofNat a).den : Int)
  have ha : (Q'.ofNat a).num = (a : Int) := rfl
  have hb : (Q'.ofNat b).num = (b : Int) := rfl
  have hda : ((Q'.ofNat a).den : Int) = 1 := rfl
  have hdb : ((Q'.ofNat b).den : Int) = 1 := rfl
  rw [ha, hb, hda, hdb, Int.mul_one, Int.mul_one]
  exact_mod_cast h

/-- The tolerance value `c = ε/8 = ε.num/(8·ε.den)`. -/
def cVal (ε : Q') : Q' := Q'.mkPos ε.num (8 * ε.den) (by
  have := ε.den_pos; omega)

/-- `0 < cVal ε` for `0 < ε`. -/
theorem cVal_pos {ε : Q'} (hε : (0 : Q') < ε) : (0 : Q') < cVal ε := by
  have hεnum : 0 < ε.num := by
    have hraw : (0 : Q').num * (ε.den : Int) < ε.num * ((0 : Q').den : Int) := hε
    have h0n : (0 : Q').num = 0 := by decide
    have h0d : ((0 : Q').den : Int) = 1 := by decide
    rw [h0n, h0d, Int.zero_mul, Int.mul_one] at hraw
    exact hraw
  show (0 : Int) * ((cVal ε).den : Int) < (cVal ε).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  show (0 : Int) < (Q'.mkPos ε.num (8 * ε.den) _).num
  rw [Q'.mkPos_num]; exact hεnum

/-- **`4·cVal ε ≤ ε`** (i.e. `ε/2 ≤ ε`), as `ofNat 2 · cVal + ofNat 2 · cVal ≤ ε`. -/
theorem fourC_le {ε : Q'} (hε : (0 : Q') < ε) :
    Q'.ofNat 2 * cVal ε + Q'.ofNat 2 * cVal ε ≤ ε := by
  have hεnum : 0 < ε.num := by
    have hraw : (0 : Q').num * (ε.den : Int) < ε.num * ((0 : Q').den : Int) := hε
    have h0n : (0 : Q').num = 0 := by decide
    have h0d : ((0 : Q').den : Int) = 1 := by decide
    rw [h0n, h0d, Int.zero_mul, Int.mul_one] at hraw
    exact hraw
  -- LHS = (2·ε.num)/(8 ε.den) + (2·ε.num)/(8 ε.den) ; reduce cross product to Int
  show (Q'.ofNat 2 * cVal ε + Q'.ofNat 2 * cVal ε).num * (ε.den : Int)
      ≤ ε.num * ((Q'.ofNat 2 * cVal ε + Q'.ofNat 2 * cVal ε).den : Int)
  -- num and den of (2·cVal):  num = 2·ε.num, den = 8 ε.den
  have hcnum : (Q'.ofNat 2 * cVal ε).num = 2 * ε.num := by
    show (Q'.ofNat 2).num * (cVal ε).num = 2 * ε.num
    rw [show (Q'.ofNat 2).num = (2 : Int) from rfl]
    show (2 : Int) * (Q'.mkPos ε.num (8 * ε.den) _).num = 2 * ε.num
    rw [Q'.mkPos_num]
  have hcden : ((Q'.ofNat 2 * cVal ε).den : Int) = (8 * ε.den : Nat) := by
    rw [Q'.mul_den_cast]
    show ((Q'.ofNat 2).den : Int) * ((cVal ε).den : Int) = ((8 * ε.den : Nat) : Int)
    rw [show ((Q'.ofNat 2).den : Int) = 1 from rfl,
      show (cVal ε).den = 8 * ε.den from Q'.mkPos_den _ _ _, Int.one_mul]
  -- sum num = (2ε.num)·(8 ε.den) + (2ε.num)·(8 ε.den) over den (8 ε.den)·(8 ε.den)
  have hsumnum : (Q'.ofNat 2 * cVal ε + Q'.ofNat 2 * cVal ε).num
      = (2 * ε.num) * ((8 * ε.den : Nat) : Int) + (2 * ε.num) * ((8 * ε.den : Nat) : Int) := by
    show (Q'.ofNat 2 * cVal ε).num * ((Q'.ofNat 2 * cVal ε).den : Int)
        + (Q'.ofNat 2 * cVal ε).num * ((Q'.ofNat 2 * cVal ε).den : Int)
      = (2 * ε.num) * ((8 * ε.den : Nat) : Int) + (2 * ε.num) * ((8 * ε.den : Nat) : Int)
    rw [hcnum, hcden]
  have hsumden : ((Q'.ofNat 2 * cVal ε + Q'.ofNat 2 * cVal ε).den : Int)
      = ((8 * ε.den : Nat) : Int) * ((8 * ε.den : Nat) : Int) := by
    rw [Q'.add_den_cast, hcden]
  rw [hsumnum, hsumden]
  -- goal: ((2ε.num)·D + (2ε.num)·D)·ε.den ≤ ε.num·(D·D)  where D = 8 ε.den
  have hD : ((8 * ε.den : Nat) : Int) = 8 * (ε.den : Int) := by push_cast; rfl
  rw [hD]
  -- ((2 ε.num)(8 ed) + (2 ε.num)(8 ed))·ed = 32 ε.num ed² ; RHS ε.num·(8ed·8ed)=64 ε.num ed²
  have hed : (0 : Int) ≤ (ε.den : Int) := Int.natCast_nonneg _
  have hednn : (0 : Int) ≤ ε.num := Int.le_of_lt hεnum
  have hbase : (0 : Int) ≤ ε.num * ((ε.den : Int) * (ε.den : Int)) :=
    Int.mul_nonneg hednn (Int.mul_nonneg hed hed)
  -- LHS ≃ (2·2·8)·base, RHS ≃ (8·8)·base  (ac only; no numeric eval)
  -- first collapse A + A = 2·A
  have hAA : (2 * ε.num * (8 * (ε.den : Int)) + 2 * ε.num * (8 * (ε.den : Int)))
      = 2 * (2 * ε.num * (8 * (ε.den : Int))) := (Int.two_mul _).symm
  rw [hAA]
  have hLHS : (2 * (2 * ε.num * (8 * (ε.den : Int)))) * (ε.den : Int)
      = (2 * 2 * 8) * (ε.num * ((ε.den : Int) * (ε.den : Int))) := by ac_rfl
  have hRHS : ε.num * (8 * (ε.den : Int) * (8 * (ε.den : Int)))
      = (8 * 8) * (ε.num * ((ε.den : Int) * (ε.den : Int))) := by ac_rfl
  rw [hLHS, hRHS]
  have h3264 : (2 * 2 * 8 : Int) ≤ 8 * 8 := by decide
  exact Int.mul_le_mul_of_nonneg_right h3264 hbase

/-- `cVal ε * cVal ε` has `num = ε.num²`, `den = (8 ε.den)·(8 ε.den)`. -/
private theorem cVal_sq_num (ε : Q') : (cVal ε * cVal ε).num = ε.num * ε.num := by
  show (cVal ε).num * (cVal ε).num = ε.num * ε.num
  rw [show (cVal ε).num = ε.num from Q'.mkPos_num _ _ _]

private theorem cVal_sq_den (ε : Q') :
    ((cVal ε * cVal ε).den : Int) = (8 * (ε.den : Int)) * (8 * (ε.den : Int)) := by
  rw [Q'.mul_den_cast]
  rw [show (cVal ε).den = 8 * ε.den from Q'.mkPos_den _ _ _]
  push_cast; rfl

/-- **The tolerance condition from the rate.**  If `recipSq ε ≤ ofNat P` (which
holds when `P ≥ semiRateB ε`), then `2/P ≤ cVal ε · cVal ε`. -/
theorem tol_of_recipSq_le {ε : Q'} (hε : (0 : Q') < ε) {P : Nat} (hP : 0 < P)
    (hle : recipSq ε ≤ Q'.ofNat P) :
    Q'.mkPos 2 P hP ≤ cVal ε * cVal ε := by
  have hεnum : 0 < ε.num := by
    have hraw : (0 : Q').num * (ε.den : Int) < ε.num * ((0 : Q').den : Int) := hε
    have h0n : (0 : Q').num = 0 := by decide
    have h0d : ((0 : Q').den : Int) = 1 := by decide
    rw [h0n, h0d, Int.zero_mul, Int.mul_one] at hraw
    exact hraw
  have hrs : recipSq ε = Q'.mkPos (128 * (ε.den : Int) * (ε.den : Int))
      (ε.num.toNat * ε.num.toNat)
      (Nat.mul_pos (toNat_pos_of_pos hεnum) (toNat_pos_of_pos hεnum)) := by
    unfold recipSq; rw [dif_pos hεnum]
  rw [hrs] at hle
  have hcross : (128 * (ε.den : Int) * (ε.den : Int)) * ((Q'.ofNat P).den : Int)
      ≤ (Q'.ofNat P).num * ((ε.num.toNat * ε.num.toNat : Nat) : Int) := by
    have hexpand :
        (Q'.mkPos (128 * (ε.den : Int) * (ε.den : Int)) (ε.num.toNat * ε.num.toNat)
            (Nat.mul_pos (toNat_pos_of_pos hεnum) (toNat_pos_of_pos hεnum))).num
          * ((Q'.ofNat P).den : Int)
        ≤ (Q'.ofNat P).num
          * ((Q'.mkPos (128 * (ε.den : Int) * (ε.den : Int)) (ε.num.toNat * ε.num.toNat)
              (Nat.mul_pos (toNat_pos_of_pos hεnum) (toNat_pos_of_pos hεnum))).den : Int) := hle
    rw [Q'.mkPos_num, Q'.mkPos_den] at hexpand
    exact hexpand
  have hPnum : (Q'.ofNat P).num = (P : Int) := rfl
  have hPden : ((Q'.ofNat P).den : Int) = 1 := rfl
  rw [hPnum, hPden, Int.mul_one] at hcross
  have htoNat : (ε.num.toNat : Int) = ε.num := Int.toNat_of_nonneg (Int.le_of_lt hεnum)
  have hsq : ((ε.num.toNat * ε.num.toNat : Nat) : Int) = ε.num * ε.num := by
    push_cast [htoNat]; rfl
  rw [hsq] at hcross
  show (Q'.mkPos 2 P hP).num * ((cVal ε * cVal ε).den : Int)
      ≤ (cVal ε * cVal ε).num * ((Q'.mkPos 2 P hP).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den, cVal_sq_num, cVal_sq_den]
  have hgoalL : (2 : Int) * ((8 * (ε.den : Int)) * (8 * (ε.den : Int)))
      = (2 * 8 * 8) * ((ε.den : Int) * (ε.den : Int)) := by ac_rfl
  have hcrossL : 128 * (ε.den : Int) * (ε.den : Int)
      = 128 * ((ε.den : Int) * (ε.den : Int)) := by ac_rfl
  rw [hgoalL]
  rw [hcrossL] at hcross
  have h128 : (2 * 8 * 8 : Int) = 128 := by decide
  rw [h128]
  have hcomm : (P : Int) * (ε.num * ε.num) = (ε.num * ε.num) * (P : Int) := Int.mul_comm _ _
  rw [hcomm] at hcross
  exact hcross

/-- **`recipSq ε ≤ ofNat P` when `P ≥ semiRateB ε`.** -/
theorem recipSq_le_ofNat_of_rate {ε : Q'} {P : Nat} (h : semiRateB ε ≤ P) :
    recipSq ε ≤ Q'.ofNat P :=
  Q'.le_trans' _ _ _ (q_le_qCeilNat (recipSq ε)) (ofNat_le_ofNat h)

/-- **The forward common-refinement bound.**  For `P, N` with `recipSq ε ≤ ofNat P`
and `recipSq ε ≤ ofNat N`, the value gap `semiSum P − semiSum N` is `leRat`-`≤ ε`,
via the telescope through `semiSum (P·N)` and the two refinement bounds at
tolerance `2·cVal ε` (each `≤ ε/2`). -/
theorem semiSum_common_leRat {ε : Q'} (hε : (0 : Q') < ε) {P N : Nat}
    (hP : 0 < P) (hN : 0 < N) (hPr : recipSq ε ≤ Q'.ofNat P) (hNr : recipSq ε ≤ Q'.ofNat N) :
    CReal.leRat (CReal.add (semiSum P hP) (CReal.neg (semiSum N hN))) ε := by
  have hPN : 0 < P * N := Nat.mul_pos hP hN
  have hNP : 0 < N * P := Nat.mul_pos hN hP
  have hc : (0 : Q') < cVal ε := cVal_pos hε
  have htP : Q'.mkPos 2 P hP ≤ cVal ε * cVal ε := tol_of_recipSq_le hε hP hPr
  have htN : Q'.mkPos 2 N hN ≤ cVal ε * cVal ε := tol_of_recipSq_le hε hN hNr
  have hleg1 : CReal.leRat
      (CReal.add (semiSum P hP) (CReal.neg (semiSum (P * N) hPN))) (Q'.ofNat 2 * cVal ε) :=
    semiSum_refine_leRat P N hP hPN hN (cVal ε) hc htP
  have hleg2NP : CReal.leRat
      (CReal.add (semiSum (N * P) hNP) (CReal.neg (semiSum N hN))) (Q'.ofNat 2 * cVal ε) :=
    semiSum_refine_rev_leRat N P hN hNP hP (cVal ε) hc htN
  have hleg2 : CReal.leRat
      (CReal.add (semiSum (P * N) hPN) (CReal.neg (semiSum N hN))) (Q'.ofNat 2 * cVal ε) := by
    refine CReal.leRat_congr (fun k => ?_) hleg2NP
    show ((semiSum (P * N) hPN).approx k + -((semiSum N hN).approx k)).eqv
      ((semiSum (N * P) hNP).approx k + -((semiSum N hN).approx k))
    exact Q'.add_eqv_congr_right _ _ (-((semiSum N hN).approx k))
      (semiSum_nat_congr (Nat.mul_comm P N) hPN hNP k)
  have hcomb : CReal.leRat
      (CReal.add (CReal.add (semiSum P hP) (CReal.neg (semiSum (P * N) hPN)))
        (CReal.add (semiSum (P * N) hPN) (CReal.neg (semiSum N hN))))
      (Q'.ofNat 2 * cVal ε + Q'.ofNat 2 * cVal ε) :=
    CReal.leRat_add hleg1 hleg2
  exact CReal.leRat_mono (cTelescope_leRat hcomb) (fourC_le hε)

/-- **TARGET 2 — the `leRat` outer Cauchy bound** `SemicircleRate.SemiLeRatBound
semiRateB`: for `m, n ≥ semiRateB ε`, the value gap `seqSemi m − seqSemi n` (and
its symmetric) is `leRat`-`≤ ε`.  The common-refinement assembly of the two proved
refinement bounds. -/
theorem semiLeRatBound : SemicircleRate.SemiLeRatBound semiRateB := by
  intro ε hε m n hm hn
  have hPpos : 0 < m + 1 := Nat.succ_pos m
  have hNpos : 0 < n + 1 := Nat.succ_pos n
  have hPr : recipSq ε ≤ Q'.ofNat (m + 1) :=
    Q'.le_trans' _ _ _ (recipSq_le_ofNat_of_rate hm) (ofNat_le_ofNat (Nat.le_succ m))
  have hNr : recipSq ε ≤ Q'.ofNat (n + 1) :=
    Q'.le_trans' _ _ _ (recipSq_le_ofNat_of_rate hn) (ofNat_le_ofNat (Nat.le_succ n))
  refine ⟨?_, ?_⟩
  · show CReal.leRat (CReal.add (seqSemi m) (CReal.neg (seqSemi n))) ε
    exact semiSum_common_leRat hε hPpos hNpos hPr hNr
  · show CReal.leRat (CReal.add (seqSemi n) (CReal.neg (seqSemi m))) ε
    exact semiSum_common_leRat hε hNpos hPpos hNr hPr

/-! ## 6. The UNCONDITIONAL constructive semicircle Riemann integral

With `semiRateB_mono` (TARGET 1) and `semiLeRatBound` (TARGET 2) BOTH proved, the
semicircle integral and its convergence + enclosure become hypothesis-free —
the first fully-rigorous constructive Riemann integral in the library. -/

/-- **The unconditional semicircle integral** `∫_{−1}^1 √(1−x²)` as a constructive
real — from the proved outer rate `semiRateB` and the proved `leRat` outer Cauchy
bound `semiLeRatBound`, with NO remaining hypothesis. -/
def semiInt : CReal :=
  SemicircleRate.semiIntClosed semiRateB semiLeRatBound

/-- **Convergence is hypothesis-free.** -/
theorem semiInt_converges : CReal.ConvergesTo seqSemi semiInt :=
  SemicircleRate.semiIntClosed_converges semiRateB semiLeRatBound semiRateB_mono

/-- **`0 ≤ semiInt`** (hypothesis-free). -/
theorem semiInt_nonneg : ExpPos.geRat semiInt 0 :=
  SemicircleRate.semiIntClosed_nonneg semiRateB semiLeRatBound semiRateB_mono

/-- **`semiInt ≤ 2`** (hypothesis-free). -/
theorem semiInt_leRat_two : CReal.leRat semiInt (2 : Q') :=
  SemicircleRate.semiIntClosed_leRat_two semiRateB semiLeRatBound semiRateB_mono

end YMGap.Continuum.SemicircleBoundClosed

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED (axiom-clean, GENUINE new content).**

  * TARGET 1 — `qCeilNat_mono` (rational-ceiling monotonicity via `Int`/`Nat`
    floor-division), `recipSq` + `recipSq_anti` (the explicit antitone `128/ε²`),
    `semiRateB` + `semiRateB_mono : CReal.MmonoPred semiRateB`.

  * The genuine Riemann content — `cell_value_eqv` / `value_diff_eqv` (the
    `finSum_block`-reindexed identification of the value difference with the
    cell-sum of per-cell √-Hölder differences, at every approx index), and the
    nested refinement bounds `semiSum_refine_leRat` (forward) and
    `semiSum_refine_rev_leRat` (reverse, via `nodeWeight_holder` with cell/node
    roles swapped + `huvc_bwd`).

  * TARGET 2 — `semiLeRatBound : SemicircleRate.SemiLeRatBound semiRateB`, the
    two-sided common-refinement assembly (telescope through `semiSum (P·N)`, both
    refinement bounds at tolerance `2·(ε/8)`, the `2c + 2c ≤ ε` collapse).

  * The UNCONDITIONAL integral — `semiInt`, `semiInt_converges`, `semiInt_nonneg`,
    `semiInt_leRat_two`: ALL hypothesis-free.  The semicircle Riemann integral
    `∫_{−1}^1 √(1−x²)` now exists as a constructive real with a proved convergence
    certificate and the proved enclosure `0 ≤ semiInt ≤ 2`.

**Note on the stored `SemicircleRate.semiRate`.**  The existing
`SemicircleRate.semiRate ε = qCeilNat ((16·ε)·(16·ε)) = qCeilNat (256·ε²)` is the
WRONG shape for a Cauchy rate (it DECREASES as `ε → 0`, so it is not antitone and
not usable).  This module supplies the correct antitone `semiRateB ε =
qCeilNat (128/ε²)` and proves both residuals for IT; `semiInt` is built on
`semiRateB`.  No existing file was edited.

**NAMED-open.**  None for the semicircle CONVERGENCE.  The VALUE identity
`semiInt ≃ π/2` (`SemicircleIntegral.SemicircleValue`) is a separate, untouched
obligation outside this module's scope.

**Path for the general `U_a·U_b·R` integrand.**  The pattern reuses verbatim:
the rate machinery (`qCeilNat_mono` / `recipSq_anti`) is integrand-agnostic; the
cell/value identities (`cell_value_eqv` / `value_diff_eqv`) and the common-
refinement assembly only need the per-cell √-Hölder bound enlarged by the QPoly
Lipschitz factor of `U_a·U_b` at the rational node (the per-cell input the existing
`nodeWeight_holder` / `cellRefine_holder` already abstract over).

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide`/`ac_rfl` only on
closed `Nat`/`Int`/`Q'`. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SemicircleBoundClosed.nat_div_le_div_of_cross
#print axioms YMGap.Continuum.SemicircleBoundClosed.qCeilNat_mono
#print axioms YMGap.Continuum.SemicircleBoundClosed.recipSq_anti
#print axioms YMGap.Continuum.SemicircleBoundClosed.semiRateB_mono
#print axioms YMGap.Continuum.SemicircleBoundClosed.cell_value_eqv
#print axioms YMGap.Continuum.SemicircleBoundClosed.semiSum_refine_leRat
#print axioms YMGap.Continuum.SemicircleBoundClosed.semiSum_refine_rev_leRat
#print axioms YMGap.Continuum.SemicircleBoundClosed.semiSum_common_leRat
#print axioms YMGap.Continuum.SemicircleBoundClosed.semiLeRatBound
#print axioms YMGap.Continuum.SemicircleBoundClosed.semiInt
#print axioms YMGap.Continuum.SemicircleBoundClosed.semiInt_converges
#print axioms YMGap.Continuum.SemicircleBoundClosed.semiInt_nonneg
#print axioms YMGap.Continuum.SemicircleBoundClosed.semiInt_leRat_two
