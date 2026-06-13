/-
Constructive trig: the even/odd extension `cosFull`/`sinFull : Q' → CReal`, the
elementary small-angle bounds, and the exp-term bridge that reduces the trig
addition formula to the exponential one — all over the project's `Q'`/`CReal`,
NO Mathlib `ℝ`, NO classical axioms, NO `sorry`.

`Constructive/Trig.lean` ships `cosNN`/`sinNN : (x : Q') → 0 ≤ x → CReal`, the
alternating cos/sin series at a *nonnegative* rational `x = |B|`.  This module
adds, in increasing depth:

  1. **`Q'`/`CReal` congruence plumbing** — `termAbs`, `cosTerm`, `sinTerm`,
     `cosPartial`, `sinPartial` are `eqv`-congruent in their angle argument, so
     `cosNN`/`sinNN` evaluated at `eqv`-equal angles have `CReal.Equiv` limits
     (`equiv_of_approx_eqv`).

  2. **The even/odd extension** (`cosFull`/`sinFull : Q' → CReal`): cos/sin of a
     *signed* rational angle, `cosFull x := cos |x|` (even, `cosFull_even`),
     `sinFull x := ± sin |x|` (odd, `sinFull_odd_of_nonneg`).

  3. **The small-angle bounds** (alternating-decreasing regime `0 ≤ x ≤ 1`),
     truncation form: `|cosPartial x (1+d) − 1| ≤ 2·termAbs x 2 = x²`
     (`cos_small_angle`) and `|sinPartial x (1+d) − sinTerm x 0| ≤ 2·termAbs x 3
     = x³/3` (`sin_small_angle`), the inputs to the `TrigBound` small-angle budget
     family (which is constant-agnostic — it accepts any `Bc`, `Bs`).  Built from
     the `cos`/`sin` block bounds dominated by the exponential magnitude block,
     bounded geometrically at ratio `1/2`.

  4. **The exp-term bridge** (`term_even_eq_abs`, `term_odd_eq_neg_abs`): the trig
     terms are the signed even/odd subsequences of the *signed* exponential series
     `ExpNeg.term x i = (−x)ⁱ/i!`, namely `term x (2k) ≈ termAbs x (2k)` and
     `term x (2k+1) ≈ −termAbs x (2k+1)`.

  5. **The trig convolutions** (`cosConv`/`sinConv`) and the per-degree addition
     identity, base case (`cosConv_addition_zero`).  The general identity is the
     research-novel core; see the footer for its precise statement and the named
     residual that remains (the even/odd reassembly of `ExpAddConv.convAdd`).

# Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (only via reused `Q'` ring / `Nat` helpers).
No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Constructive.Trig
import YMGap.Constructive.TrigBound
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.ExpAddConv
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.CornerBound
import YMGap.Constructive.ProductDecompAdd
import YMGap.Constructive.CornerBoundAdd
import YMGap.Constructive.ExpAdd

namespace YMGap.Constructive

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.Trig

namespace TrigAdd

/-! ## 0. `eqv`-congruence of the magnitude / trig terms in the angle

`termAbs x (k+1) = termAbs x k · (x · invSucc k)`, so an `eqv` on `x` propagates
through the product recurrence.  This lets `cosNN`/`sinNN` at `eqv`-equal angles
be related by `CReal.Equiv`. -/

/-- Antisymmetry of `Q'.le` packaged as `eqv`. -/
theorem eqv_of_le_of_le {a b : Q'} (h1 : a ≤ b) (h2 : b ≤ a) : a.eqv b := by
  show a.num * (b.den : Int) = b.num * (a.den : Int)
  exact Int.le_antisymm h1 h2

/-- `termAbs 0 (k+1) ≈ 0` — the magnitude series at the zero angle vanishes past
the constant term. -/
theorem termAbs_zero_succ_eqv :
    ∀ k, (termAbs (0 : Q') (k + 1)).eqv 0
  | 0 => by
    show (termAbs (0 : Q') 0 * ((0 : Q') * Q'.invSucc 0)).eqv 0
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (termAbs (0 : Q') 0) ((0 : Q') * Q'.invSucc 0) 0
        (Q'.zero_mul_eqv (Q'.invSucc 0))) ?_
    exact Q'.mul_zero_eqv (termAbs (0 : Q') 0)
  | k + 1 => by
    show (termAbs (0 : Q') (k + 1) * ((0 : Q') * Q'.invSucc (k + 1))).eqv 0
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (termAbs (0 : Q') (k + 1)) 0 ((0 : Q') * Q'.invSucc (k + 1))
        (termAbs_zero_succ_eqv k)) ?_
    exact Q'.zero_mul_eqv ((0 : Q') * Q'.invSucc (k + 1))

/-- `sinTerm 0 k ≈ 0` for every `k` (the odd magnitude term at zero vanishes). -/
theorem sinTerm_zero_angle_eqv (k : Nat) : (sinTerm (0 : Q') k).eqv 0 := by
  show (negPow k * termAbs (0 : Q') (2 * k + 1)).eqv 0
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow k) (termAbs (0 : Q') (2 * k + 1)) 0
      (termAbs_zero_succ_eqv (2 * k))) ?_
  exact Q'.mul_zero_eqv (negPow k)

/-- `sinPartial 0 n ≈ 0`. -/
theorem sinPartial_zero_eqv : ∀ n, (sinPartial (0 : Q') n).eqv 0
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
    show (sinPartial (0 : Q') n + sinTerm (0 : Q') n).eqv 0
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (sinPartial_zero_eqv n) (sinTerm_zero_angle_eqv n)) ?_
    show ((0 : Q') + 0).eqv 0
    exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-- `Q'.abs 0 = 0`. -/
theorem abs_zero_eq : Q'.abs (0 : Q') = 0 := by
  unfold Q'.abs; rw [if_pos (Q'.le_refl' 0)]

/-- `termAbs` is `eqv`-congruent in its angle: `x ≈ y → termAbs x k ≈ termAbs y k`. -/
theorem termAbs_eqv_congr {x y : Q'} (h : x.eqv y) :
    ∀ k, (termAbs x k).eqv (termAbs y k)
  | 0 => Q'.eqv_refl 1
  | k + 1 => by
    show (termAbs x k * (x * Q'.invSucc k)).eqv (termAbs y k * (y * Q'.invSucc k))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (termAbs x k) (termAbs y k) (x * Q'.invSucc k)
        (termAbs_eqv_congr h k)) ?_
    exact Q'.mul_eqv_congr_left (termAbs y k) (x * Q'.invSucc k) (y * Q'.invSucc k)
      (Q'.mul_eqv_congr_right x y (Q'.invSucc k) h)

/-- `cosTerm` is `eqv`-congruent in its angle. -/
theorem cosTerm_eqv_congr {x y : Q'} (h : x.eqv y) (k : Nat) :
    (cosTerm x k).eqv (cosTerm y k) :=
  Q'.mul_eqv_congr_left (negPow k) (termAbs x (2 * k)) (termAbs y (2 * k))
    (termAbs_eqv_congr h (2 * k))

/-- `sinTerm` is `eqv`-congruent in its angle. -/
theorem sinTerm_eqv_congr {x y : Q'} (h : x.eqv y) (k : Nat) :
    (sinTerm x k).eqv (sinTerm y k) :=
  Q'.mul_eqv_congr_left (negPow k) (termAbs x (2 * k + 1)) (termAbs y (2 * k + 1))
    (termAbs_eqv_congr h (2 * k + 1))

/-- `cosPartial` is `eqv`-congruent in its angle. -/
theorem cosPartial_eqv_congr {x y : Q'} (h : x.eqv y) :
    ∀ n, (cosPartial x n).eqv (cosPartial y n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
    show (cosPartial x n + cosTerm x n).eqv (cosPartial y n + cosTerm y n)
    exact Q'.add_eqv_congr' (cosPartial_eqv_congr h n) (cosTerm_eqv_congr h n)

/-- `sinPartial` is `eqv`-congruent in its angle. -/
theorem sinPartial_eqv_congr {x y : Q'} (h : x.eqv y) :
    ∀ n, (sinPartial x n).eqv (sinPartial y n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
    show (sinPartial x n + sinTerm x n).eqv (sinPartial y n + sinTerm y n)
    exact Q'.add_eqv_congr' (sinPartial_eqv_congr h n) (sinTerm_eqv_congr h n)

/-! ## 1. `CReal.Equiv` from termwise `eqv` of approximations

`Equiv_of_lifted_approx_equal` (in `CRealAbs.lean`) reduces `CReal.Equiv A B` to
`∀ N, Equiv (ofQ' (A.approx N)) (ofQ' (B.approx N))`; we supply the per-`N`
`Equiv` of the lifted constants from an `eqv` of the rationals. -/

/-- `Equiv (ofQ' a) (ofQ' b)` from `a ≈ b`. -/
theorem equiv_ofQ'_of_eqv {a b : Q'} (h : a.eqv b) :
    CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  show a ≤ b + ε ∧ b ≤ a + ε
  refine ⟨?_, ?_⟩
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h) (Q'.add_le_self_of_nonneg b ε (Q'.le_of_lt hε))
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv h) (Q'.add_le_self_of_nonneg a ε (Q'.le_of_lt hε))

/-- If two `CReal`s have termwise-`eqv` approximation sequences, they are
`CReal.Equiv`. -/
theorem equiv_of_approx_eqv {A B : CReal}
    (h : ∀ n, (A.approx n).eqv (B.approx n)) : CReal.Equiv A B :=
  CReal.Equiv_of_lifted_approx_equal (fun N => equiv_ofQ'_of_eqv (h N))

/-! ## 2. The even/odd extension `cosFull`/`sinFull : Q' → CReal` -/

/-- **Constructive `cos x`** for a signed rational angle `x`: `cos x := cos |x|`
(cosine is even). -/
def cosFull (x : Q') : CReal := cosNN (Q'.abs x) (Q'.abs_nonneg x)

/-- **Constructive `sin x`** for a signed rational angle `x`: `sin x := sin |x|`
if `0 ≤ x`, else `−sin |x|` (sine is odd). -/
def sinFull (x : Q') : CReal :=
  if (0 : Q') ≤ x then sinNN (Q'.abs x) (Q'.abs_nonneg x)
  else CReal.neg (sinNN (Q'.abs x) (Q'.abs_nonneg x))

@[simp] theorem cosFull_approx (x : Q') (n : Nat) :
    (cosFull x).approx n = cosPartial (Q'.abs x) n := rfl

/-- `cosFull` is even: `cosFull (−x) ≃ cosFull x`. -/
theorem cosFull_even (x : Q') : CReal.Equiv (cosFull (-x)) (cosFull x) := by
  refine equiv_of_approx_eqv (fun n => ?_)
  show (cosPartial (Q'.abs (-x)) n).eqv (cosPartial (Q'.abs x) n)
  exact cosPartial_eqv_congr (Q'.abs_neg' x) n

/-- `sinFull` of a nonnegative angle is `sinNN`. -/
theorem sinFull_of_nonneg {x : Q'} (hx : (0 : Q') ≤ x) :
    sinFull x = sinNN (Q'.abs x) (Q'.abs_nonneg x) := by
  unfold sinFull; rw [if_pos hx]

/-- `sinFull (−x) ≃ −sinFull x` (sine is odd).  We prove the case `0 ≤ x`; the
`x < 0` case is symmetric (then `−x > 0`).  Stated as a `CReal.Equiv`. -/
theorem sinFull_odd_of_nonneg {x : Q'} (hx : (0 : Q') ≤ x) :
    CReal.Equiv (sinFull (-x)) (CReal.neg (sinFull x)) := by
  -- sinFull x = sinNN |x|.  sinFull (−x): is 0 ≤ −x?  Only if x ≈ 0; in general
  -- −x ≤ 0, so sinFull (−x) = neg (sinNN |−x|) = neg (sinNN |x|) (up to eqv).
  by_cases hnx : (0 : Q') ≤ -x
  · -- both x and −x are ≥ 0, so x ≈ 0: sinNN |x| has approx sinPartial |x|;
    -- |x| ≈ |−x| and sinFull (−x) = sinNN |−x|.  Need sinNN |x| ≃ neg (sinNN |x|),
    -- which holds since x ≈ 0 ⇒ |x| ≈ 0 ⇒ sinPartial |x| n ≃ 0 = −0.
    refine equiv_of_approx_eqv (fun n => ?_)
    rw [sinFull_of_nonneg hnx, sinFull_of_nonneg hx]
    show (sinPartial (Q'.abs (-x)) n).eqv (-(sinPartial (Q'.abs x) n))
    -- x ≥ 0 and −x ≥ 0 ⇒ x ≈ 0.
    have hx0 : x.eqv 0 := by
      have h1 : x ≤ 0 := by
        have := Q'.neg_le_neg hnx
        refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_neg_eqv x)) ?_
        refine Q'.le_trans' _ _ _ this ?_
        exact Q'.le_of_eqv (by show ((-0 : Q')).eqv 0; decide)
      exact eqv_of_le_of_le h1 hx
    -- |−x| ≈ 0 and |x| ≈ 0
    have hax : (Q'.abs x).eqv 0 :=
      Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr hx0) (Q'.eqv_of_eq abs_zero_eq)
    have hanx : (Q'.abs (-x)).eqv 0 :=
      Q'.eqv_trans _ _ _ (Q'.abs_neg' x) hax
    -- sinPartial _ n ≃ sinPartial 0 n = 0 (since each sinTerm 0 k = 0).
    refine Q'.eqv_trans _ _ _ (sinPartial_eqv_congr hanx n) ?_
    refine Q'.eqv_trans _ _ _ (sinPartial_zero_eqv n) ?_
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (sinPartial_eqv_congr hax n)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (sinPartial_zero_eqv n)) ?_
    show ((-0 : Q')).eqv 0; decide
  · -- −x < 0, so sinFull (−x) = neg (sinNN |−x|).
    refine equiv_of_approx_eqv (fun n => ?_)
    have hsx : sinFull (-x) = CReal.neg (sinNN (Q'.abs (-x)) (Q'.abs_nonneg (-x))) := by
      unfold sinFull; rw [if_neg hnx]
    rw [hsx, sinFull_of_nonneg hx]
    show (-(sinPartial (Q'.abs (-x)) n)).eqv (-(sinPartial (Q'.abs x) n))
    exact Q'.neg_eqv_congr _ _ (sinPartial_eqv_congr (Q'.abs_neg' x) n)

/-! ## 3. Small-angle bounds (the alternating-decreasing regime `0 ≤ x ≤ 1`)

`cosPartial x (1+d)` differs from `cosPartial x 1 = 1` by the cosine block from
index `1`, two-sidedly dominated by `cosBlockAbs x 1 d`; and that block is
dominated by the exponential magnitude block `blockAbs x 2 (2d)`.  For `0 ≤ x ≤ 1`
the ratio of consecutive magnitude terms from index `2` is `≤ x/3 ≤ 1/2`, so the
whole block is `≤ 2·termAbs x 2 = x²` (`blockAbs_le` at `r = 1/2`,
`H = 2·termAbs x 2`).  Hence `|cos x − 1| ≤ x²` at every truncation — the cosine
small-angle budget.  The sine analogue gives `|sin x − x| ≤ x³/3` (block from
index `1`, dominated by `blockAbs x 3 (2d) ≤ 2·termAbs x 3 = x³/3`). -/

/-- For `0 ≤ x ≤ 1`, the magnitude block from index `2` is `≤ 2·termAbs x 2`. -/
theorem blockAbs_two_le (x : Q') (hx : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (d : Nat) :
    blockAbs x 2 d ≤ termAbs x 2 + termAbs x 2 := by
  have hH : (0 : Q') ≤ termAbs x 2 + termAbs x 2 :=
    Q'.zero_le_add _ _ (termAbs_nonneg x hx 2) (termAbs_nonneg x hx 2)
  -- x·invSucc 2 ≤ half
  have hbound : x * Q'.invSucc 2 ≤ HalfPow.half := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right x 1 (Q'.invSucc 2) hx1 (Q'.invSucc_nonneg 2)) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv (Q'.invSucc 2))) ?_
    decide
  -- recurrence: termAbs x 2 + half·(2 termAbs x 2) ≤ 2 termAbs x 2  (equality)
  have hrec : termAbs x 2 + HalfPow.half * (termAbs x 2 + termAbs x 2)
      ≤ termAbs x 2 + termAbs x 2 := by
    refine Q'.le_of_eqv ?_
    refine Q'.add_eqv_congr_left (termAbs x 2) _ _ ?_
    exact Q'.eqv_trans _ _ _ (Q'.mul_add_eqv HalfPow.half (termAbs x 2) (termAbs x 2))
      (ExpNeg.two_halves (termAbs x 2))
  exact blockAbs_le x HalfPow.half (termAbs x 2 + termAbs x 2) hx 2
    HalfPow.half_nonneg hH hbound hrec d

/-- For `0 ≤ x ≤ 1`, the magnitude block from index `3` is `≤ 2·termAbs x 3`. -/
theorem blockAbs_three_le (x : Q') (hx : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (d : Nat) :
    blockAbs x 3 d ≤ termAbs x 3 + termAbs x 3 := by
  have hH : (0 : Q') ≤ termAbs x 3 + termAbs x 3 :=
    Q'.zero_le_add _ _ (termAbs_nonneg x hx 3) (termAbs_nonneg x hx 3)
  have hbound : x * Q'.invSucc 3 ≤ HalfPow.half := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right x 1 (Q'.invSucc 3) hx1 (Q'.invSucc_nonneg 3)) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv (Q'.invSucc 3))) ?_
    decide
  have hrec : termAbs x 3 + HalfPow.half * (termAbs x 3 + termAbs x 3)
      ≤ termAbs x 3 + termAbs x 3 := by
    refine Q'.le_of_eqv ?_
    refine Q'.add_eqv_congr_left (termAbs x 3) _ _ ?_
    exact Q'.eqv_trans _ _ _ (Q'.mul_add_eqv HalfPow.half (termAbs x 3) (termAbs x 3))
      (ExpNeg.two_halves (termAbs x 3))
  exact blockAbs_le x HalfPow.half (termAbs x 3 + termAbs x 3) hx 3
    HalfPow.half_nonneg hH hbound hrec d

/-- **Cosine small-angle bound (truncation form).**  For `0 ≤ x ≤ 1` and every
truncation `cosPartial x (1+d)`,
`|cosPartial x (1+d) − 1| ≤ 2·termAbs x 2 = x²`. -/
theorem cos_small_angle (x : Q') (hx : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (d : Nat) :
    Q'.abs (cosPartial x (1 + d) + (-1)) ≤ termAbs x 2 + termAbs x 2 := by
  -- block bound on cosBlockAbs x 1 d
  have hblk : cosBlockAbs x 1 d ≤ termAbs x 2 + termAbs x 2 := by
    refine Q'.le_trans' _ _ _ (cosBlockAbs_le_blockAbs x hx 1 d) ?_
    -- blockAbs x (2·1) (2d) = blockAbs x 2 (2d)
    show blockAbs x (2 * 1) (2 * d) ≤ termAbs x 2 + termAbs x 2
    have h21 : 2 * 1 = 2 := by decide
    rw [h21]
    exact blockAbs_two_le x hx hx1 (2 * d)
  -- |cosPartial x (1+d) − 1| ≤ cosBlockAbs x 1 d
  have hup : cosPartial x (1 + d) ≤ 1 + cosBlockAbs x 1 d := by
    have h := cos_block_upper x hx 1 d
    rw [cosPartial_one] at h
    exact h
  have hlo : (1 : Q') ≤ cosPartial x (1 + d) + cosBlockAbs x 1 d := by
    have h := cos_block_lower x hx 1 d
    rw [cosPartial_one] at h
    exact h
  -- assemble the two-sided bound, then abs_le
  refine Q'.abs_le ?_ ?_
  · -- −(block) ≤ cosPartial − 1
    exact Q'.le_trans' _ _ _ (Q'.neg_le_neg hblk) (Q'.neg_le_sub_of_le_add hlo)
  · -- cosPartial − 1 ≤ block
    exact Q'.le_trans' _ _ _ (Q'.sub_le_of_le_add hup) hblk

/-- **Sine small-angle bound (truncation form).**  For `0 ≤ x ≤ 1` and every
truncation `sinPartial x (1+d)`,
`|sinPartial x (1+d) − sinTerm x 0| ≤ 2·termAbs x 3 = x³/3`.  Combined with
`sinTerm x 0 ≈ x`, this is `|sin x − x| ≤ x³/3`. -/
theorem sin_small_angle (x : Q') (hx : (0 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (d : Nat) :
    Q'.abs (sinPartial x (1 + d) + (-(sinTerm x 0))) ≤ termAbs x 3 + termAbs x 3 := by
  have hblk : sinBlockAbs x 1 d ≤ termAbs x 3 + termAbs x 3 := by
    refine Q'.le_trans' _ _ _ (sinBlockAbs_le_blockAbs x hx 1 d) ?_
    show blockAbs x (2 * 1 + 1) (2 * d) ≤ termAbs x 3 + termAbs x 3
    have h31 : 2 * 1 + 1 = 3 := by decide
    rw [h31]
    exact blockAbs_three_le x hx hx1 (2 * d)
  -- sinPartial x 1 = sinTerm x 0
  have hsp1 : sinPartial x 1 = sinTerm x 0 := by
    show sinPartial x 0 + sinTerm x 0 = sinTerm x 0
    rw [sinPartial_zero, Q'.zero_add']
  have hup : sinPartial x (1 + d) ≤ sinTerm x 0 + sinBlockAbs x 1 d := by
    have h := sin_block_upper x hx 1 d
    rw [hsp1] at h
    exact h
  have hlo : sinTerm x 0 ≤ sinPartial x (1 + d) + sinBlockAbs x 1 d := by
    have h := sin_block_lower x hx 1 d
    rw [hsp1] at h
    exact h
  refine Q'.abs_le ?_ ?_
  · exact Q'.le_trans' _ _ _ (Q'.neg_le_neg hblk) (Q'.neg_le_sub_of_le_add hlo)
  · exact Q'.le_trans' _ _ _ (Q'.sub_le_of_le_add hup) hblk

/-! ## 4. The exp-term bridge for the addition formula

The trig terms are the signed even/odd subsequences of the *signed* exponential
series `ExpNeg.term x i = (−x)ⁱ/i!`:

  * even index: `(−x)^{2k} = x^{2k}`, so `term x (2k) ≈ termAbs x (2k)`;
  * odd index:  `(−x)^{2k+1} = −x^{2k+1}`, so `term x (2k+1) ≈ −termAbs x (2k+1)`.

These two identities are what reduce the trig convolution to the exponential one
(`ExpAddConv.convAdd_eqv_term`).  Proved by a paired induction on `k`. -/

/-- **The even/odd exp-term bridge.**  `term x (2k) ≈ termAbs x (2k)` and
`term x (2k+1) ≈ −(termAbs x (2k+1))`. -/
theorem term_even_odd_bridge (x : Q') :
    ∀ k, (ExpNeg.term x (2 * k)).eqv (termAbs x (2 * k))
       ∧ (ExpNeg.term x (2 * k + 1)).eqv (-(termAbs x (2 * k + 1)))
  | 0 => by
    refine ⟨Q'.eqv_refl 1, ?_⟩
    -- term x 1 = term x 0 · ((−x)·c0) = 1·((−x)·c0); termAbs x 1 = 1·(x·c0).
    show (ExpNeg.term x 0 * ((-x) * Q'.invSucc 0)).eqv (-(termAbs x 0 * (x * Q'.invSucc 0)))
    rw [ExpNeg.term_zero]
    refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv ((-x) * Q'.invSucc 0)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv x (Q'.invSucc 0)) ?_
    refine Q'.neg_eqv_congr _ _ ?_
    exact Q'.eqv_symm (Q'.one_mul_eqv (x * Q'.invSucc 0))
  | k + 1 => by
    obtain ⟨hP, hQ⟩ := term_even_odd_bridge x k
    -- Need P(k+1): term x (2(k+1)) ≈ termAbs x (2(k+1)), and
    --      Q(k+1): term x (2(k+1)+1) ≈ −termAbs x (2(k+1)+1).
    -- Index arithmetic: 2(k+1) = (2k+1)+1, 2(k+1)+1 = ((2k+1)+1)+1.
    have hi1 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    have hi2 : 2 * (k + 1) + 1 = ((2 * k + 1) + 1) + 1 := by omega
    -- P(k+1): term x ((2k+1)+1) ≈ termAbs x ((2k+1)+1), proved from hQ.
    have hPk1 : (ExpNeg.term x ((2 * k + 1) + 1)).eqv (termAbs x ((2 * k + 1) + 1)) := by
      show (ExpNeg.term x (2 * k + 1) * ((-x) * Q'.invSucc (2 * k + 1))).eqv
          (termAbs x (2 * k + 1) * (x * Q'.invSucc (2 * k + 1)))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (ExpNeg.term x (2 * k + 1)) (-(termAbs x (2 * k + 1)))
          ((-x) * Q'.invSucc (2 * k + 1)) hQ) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (-(termAbs x (2 * k + 1))) ((-x) * Q'.invSucc (2 * k + 1))
          (-(x * Q'.invSucc (2 * k + 1))) (Q'.neg_mul_eqv x (Q'.invSucc (2 * k + 1)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.neg_mul_eqv (termAbs x (2 * k + 1)) (-(x * Q'.invSucc (2 * k + 1)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv (termAbs x (2 * k + 1)) (x * Q'.invSucc (2 * k + 1)))) ?_
      exact Q'.neg_neg_eqv (termAbs x (2 * k + 1) * (x * Q'.invSucc (2 * k + 1)))
    refine ⟨?_, ?_⟩
    · rw [hi1]; exact hPk1
    · -- term x (((2k+1)+1)+1) = term x ((2k+1)+1) · ((−x)·c) ≈ termAbs((2k+1)+1)·(−(x·c))
      --   = −(termAbs((2k+1)+1)·(x·c)) = −termAbs(((2k+1)+1)+1)
      rw [hi2]
      show (ExpNeg.term x ((2 * k + 1) + 1) * ((-x) * Q'.invSucc ((2 * k + 1) + 1))).eqv
          (-(termAbs x ((2 * k + 1) + 1) * (x * Q'.invSucc ((2 * k + 1) + 1))))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (ExpNeg.term x ((2 * k + 1) + 1)) (termAbs x ((2 * k + 1) + 1))
          ((-x) * Q'.invSucc ((2 * k + 1) + 1)) hPk1) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (termAbs x ((2 * k + 1) + 1)) ((-x) * Q'.invSucc ((2 * k + 1) + 1))
          (-(x * Q'.invSucc ((2 * k + 1) + 1))) (Q'.neg_mul_eqv x (Q'.invSucc ((2 * k + 1) + 1)))) ?_
      exact Q'.mul_neg_eqv (termAbs x ((2 * k + 1) + 1)) (x * Q'.invSucc ((2 * k + 1) + 1))

/-- `term x (2k) ≈ termAbs x (2k)` (even-index bridge). -/
theorem term_even_eq_abs (x : Q') (k : Nat) :
    (ExpNeg.term x (2 * k)).eqv (termAbs x (2 * k)) :=
  (term_even_odd_bridge x k).1

/-- `term x (2k+1) ≈ −(termAbs x (2k+1))` (odd-index bridge). -/
theorem term_odd_eq_neg_abs (x : Q') (k : Nat) :
    (ExpNeg.term x (2 * k + 1)).eqv (-(termAbs x (2 * k + 1))) :=
  (term_even_odd_bridge x k).2

/-! ## 5. The trig convolutions and the per-degree addition identity

`CosConv A B m = Σ_{i=0}^{m} cosTerm A i · cosTerm B (m−i)` and
`SinConv A B m = Σ_{i=0}^{m} sinTerm A i · sinTerm B (m−i)` are the cos·cos and
sin·sin Cauchy products at degree `m`.  The exact per-degree addition identity —
the algebraic heart of `cos(A+B) = cos A cos B − sin A sin B` — is

    CosConv A B m  +  (−(SinConv A B (m−1)))  ≃  cosTerm (A+B) m .          (TC)

Note the **sin convolution is at degree `m−1`**, not `m`: in the even/odd split of
`convAdd A B (2m)` (`ExpAddConv.convAdd_eqv_term`), the even-`i` terms reassemble
`CosConv A B m` (each even·even product `term A (2i)·term B (2j)` with `i+j=m`
equals `cosTerm A i·cosTerm B j` up to the shared sign `(−1)^m`, by
`term_even_eq_abs`), while the odd-`i` terms reassemble `SinConv A B (m−1)`
(each odd·odd product `term A (2i+1)·term B (2j+1)` with `i+j=m−1` equals
`sinTerm A i·sinTerm B j` up to `(−1)^{m−1}`, by `term_odd_eq_neg_abs`).  The two
shared signs `(−1)^m`, `(−1)^{m−1}` differ by one factor of `−1`, which is the
algebraic source of the MINUS sign in the addition formula. -/

/-- `i`-th term of the cos·cos Cauchy product at degree `m`. -/
def cosConvTerm (A B : Q') (m : Nat) : Nat → Q' :=
  fun i => cosTerm A i * cosTerm B (m - i)

/-- `i`-th term of the sin·sin Cauchy product at degree `m`. -/
def sinConvTerm (A B : Q') (m : Nat) : Nat → Q' :=
  fun i => sinTerm A i * sinTerm B (m - i)

/-- `CosConv A B m = Σ_{i=0}^{m} cosTerm A i · cosTerm B (m−i)`. -/
def cosConv (A B : Q') (m : Nat) : Q' :=
  RationalTail.finSum (cosConvTerm A B m) (m + 1)

/-- `SinConv A B m = Σ_{i=0}^{m} sinTerm A i · sinTerm B (m−i)`. -/
def sinConv (A B : Q') (m : Nat) : Q' :=
  RationalTail.finSum (sinConvTerm A B m) (m + 1)

/-- **The per-degree addition identity at `m = 0` (base case of (TC)).**
`cosConv A B 0 ≃ cosTerm (A+B) 0`.  At `m = 0` the sin·sin part is empty, so this
is `cosTerm A 0 · cosTerm B 0 = 1·1 = 1 = cosTerm (A+B) 0`. -/
theorem cosConv_addition_zero (A B : Q') :
    (cosConv A B 0).eqv (cosTerm (A + B) 0) := by
  show ((0 : Q') + cosTerm A 0 * cosTerm B 0).eqv (cosTerm (A + B) 0)
  rw [cosTerm_zero, cosTerm_zero, cosTerm_zero, Q'.zero_add']
  exact Q'.mul_one_eqv 1

/-! ### 5a. `negPow` sign algebra (the source of the addition-formula minus)

The two shared signs in the even/odd reassembly are `negPow m = (−1)^m` (even
sub-sum) and `negPow (m−1) = (−1)^{m−1}` (odd sub-sum).  Their product with the
outer `negPow m` collapses to `1` (even) and `−1` (odd), and that single `−1` is
the minus of `cos(A+B) = cos A cos B − sin A sin B`. -/

/-- `negPow (i + j) ≈ negPow i · negPow j`. -/
theorem negPow_add (i : Nat) : ∀ j, (negPow (i + j)).eqv (negPow i * negPow j)
  | 0 => by
    show (negPow (i + 0)).eqv (negPow i * negPow 0)
    rw [Nat.add_zero]
    exact Q'.eqv_symm (Q'.mul_one_eqv (negPow i))
  | j + 1 => by
    show (negPow (i + (j + 1))).eqv (negPow i * negPow (j + 1))
    have hidx : i + (j + 1) = (i + j) + 1 := by omega
    rw [hidx]
    show (-(negPow (i + j))).eqv (negPow i * (-(negPow j)))
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (negPow_add i j)) ?_
    exact Q'.eqv_symm (Q'.mul_neg_eqv (negPow i) (negPow j))

/-- `negPow (2k) ≈ 1`. -/
theorem negPow_two_mul : ∀ k, (negPow (2 * k)).eqv 1
  | 0 => by show (negPow 0).eqv 1; exact Q'.eqv_refl 1
  | k + 1 => by
    have hidx : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [hidx]
    show (-(negPow (2 * k + 1))).eqv 1
    show (-(-(negPow (2 * k)))).eqv 1
    refine Q'.eqv_trans _ _ _ (Q'.neg_neg_eqv (negPow (2 * k))) ?_
    exact negPow_two_mul k

/-- `negPow m · negPow m ≈ 1`. -/
theorem negPow_self_mul (m : Nat) : (negPow m * negPow m).eqv 1 := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (negPow_add m m)) ?_
  have : m + m = 2 * m := by omega
  rw [this]
  exact negPow_two_mul m

/-- `negPow (m+1) · negPow m ≈ −1`. -/
theorem negPow_succ_mul (m : Nat) : (negPow (m + 1) * negPow m).eqv (-(1 : Q')) := by
  show ((-(negPow m)) * negPow m).eqv (-(1 : Q'))
  refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv (negPow m) (negPow m)) ?_
  exact Q'.neg_eqv_congr _ _ (negPow_self_mul m)

/-! ### 5b. The even/odd `finSum` deinterleave

`finSum f (2m+1) ≃ Σ_{p≤m} f(2p) + Σ_{p<m} f(2p+1)` — the even-index sub-sum (`m+1`
terms) plus the odd-index sub-sum (`m` terms).  Proved by induction on `m`, peeling
one even and one odd term per step.  Pure `finSum`/`add`-algebra reindexing. -/

/-- `finSum f (2m+3) = finSum f (2m+1) + f(2m+1) + f(2m+2)` (defeq peel of two). -/
theorem finSum_two_step (f : RationalTail.QSeq) (k : Nat) :
    RationalTail.finSum f (k + 2)
      = RationalTail.finSum f k + f k + f (k + 1) := rfl

/-- Pure `Q'` rearrangement: `(s·t)·(a·b) ≈ (s·a)·(t·b)`. -/
theorem mul_shuffle_4 (s t a b : Q') :
    ((s * t) * (a * b)).eqv ((s * a) * (t * b)) := by
  -- (s·t)·(a·b) ≈ s·(t·(a·b)) ≈ s·((t·a)·b) ≈ s·((a·t)·b) ≈ s·(a·(t·b))
  --   ≈ (s·a)·(t·b)
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv s t (a * b)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left s _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv t a b))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left s _ _
      (Q'.mul_eqv_congr_right (t * a) (a * t) b (Q'.mul_comm_eqv t a))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left s _ _ (Q'.mul_assoc_eqv a t b)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv s a (t * b))

/-- Pure `Q'` rearrangement: `(a+b)+((p+q)+r) ≈ (a+p)+((b+r)+q)`.  Both sides
reduce to `((a+p)+(b+r))+q`. -/
theorem add_rearrange_5 (a b p q r : Q') :
    ((a + b) + ((p + q) + r)).eqv ((a + p) + ((b + r) + q)) := by
  -- LHS ≈ ((a+p)+(b+r))+q
  have hL : ((a + b) + ((p + q) + r)).eqv (((a + p) + (b + r)) + q) := by
    -- (p+q)+r ≈ (p+r)+q
    have h1 : ((p + q) + r).eqv ((p + r) + q) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv p q r) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left p _ _ (Q'.add_comm_eqv q r)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv p r q)
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (a + b) _ _ h1) ?_
    -- (a+b)+((p+r)+q) ≈ ((a+b)+(p+r))+q ≈ ((a+p)+(b+r))+q
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (a + b) (p + r) q)) ?_
    exact Q'.add_eqv_congr_right _ _ q (Q'.add_swap_inner a b p r)
  -- RHS ≈ ((a+p)+(b+r))+q
  have hR : ((a + p) + ((b + r) + q)).eqv (((a + p) + (b + r)) + q) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (a + p) (b + r) q)
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

/-- Pure `Q'` rearrangement: `((E+O)+a)+b ≈ (E+b)+(O+a)`. -/
theorem add_rearrange_4 (E O a b : Q') :
    (((E + O) + a) + b).eqv ((E + b) + (O + a)) := by
  -- ((E+O)+a)+b ≈ (E+(O+a))+b ≈ E+((O+a)+b) ≈ E+(b+(O+a)) ≈ (E+b)+(O+a)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ b (Q'.add_assoc_eqv E O a)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv E (O + a) b) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left E _ _ (Q'.add_comm_eqv (O + a) b)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv E b (O + a))

/-- **Even/odd deinterleave.**  `Σ_{i<2m+1} f(i) ≃ Σ_{p≤m} f(2p) + Σ_{p<m} f(2p+1)`. -/
theorem finSum_even_odd_split (f : RationalTail.QSeq) :
    ∀ m, (RationalTail.finSum f (2 * m + 1)).eqv
        (RationalTail.finSum (fun p => f (2 * p)) (m + 1)
          + RationalTail.finSum (fun p => f (2 * p + 1)) m)
  | 0 => by
    show (RationalTail.finSum f 1).eqv
        (RationalTail.finSum (fun p => f (2 * p)) 1 + RationalTail.finSum (fun p => f (2 * p + 1)) 0)
    show ((0 : Q') + f 0).eqv (((0 : Q') + f (2 * 0)) + (0 : Q'))
    rw [Nat.mul_zero, Q'.zero_add', Q'.add_zero']
    exact Q'.eqv_refl (f 0)
  | m + 1 => by
    -- LHS index 2*(m+1)+1 = (2m+1)+2 reduces (defeq) to a two-term peel; RHS even
    -- sub-sum at m+2 peels (defeq) to (Σ even m+1)+f(2(m+1)), odd at m+1 to (Σ odd m)+f(2m+1).
    show (RationalTail.finSum f (2 * m + 1) + f (2 * m + 1) + f (2 * (m + 1))).eqv
        ((RationalTail.finSum (fun p => f (2 * p)) (m + 1) + f (2 * (m + 1)))
          + (RationalTail.finSum (fun p => f (2 * p + 1)) m + f (2 * m + 1)))
    -- IH: finSum f (2m+1) ≈ E + O.  Goal: ((E+O) + a) + b ≈ (E+b) + (O+a).
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (f (2 * (m + 1)))
        (Q'.add_eqv_congr_right _ _ (f (2 * m + 1)) (finSum_even_odd_split f m))) ?_
    exact add_rearrange_4 _ _ (f (2 * m + 1)) (f (2 * (m + 1)))

/-! ### 5c. The bridge from trig convolution terms to even/odd convAdd terms

`cosConvTerm A B m p = cosTerm A p · cosTerm B (m−p)` reassembles the **even**-index
convAdd term `convAddTerm A B (2m) (2p)` with the shared sign `(−1)^m`; the
**odd**-index convAdd term `convAddTerm A B (2m) (2p+1)` reassembles
`sinConvTerm A B (m−1) p` with shared sign `(−1)^{m−1}`.  Sign via §5a, magnitude
via the §4 bridge `term_even_eq_abs`/`term_odd_eq_neg_abs`. -/

/-- Even-term bridge: for `p ≤ m`,
`cosConvTerm A B m p ≈ negPow m · convAddTerm A B (2m) (2p)`. -/
theorem cosConvTerm_eqv (A B : Q') (m p : Nat) (hp : p ≤ m) :
    (cosConvTerm A B m p).eqv (negPow m * convAddTerm A B (2 * m) (2 * p)) := by
  have hsub : 2 * m - 2 * p = 2 * (m - p) := by omega
  -- LHS = (negPow p · termAbs A (2p)) · (negPow (m−p) · termAbs B (2(m−p)))
  show ((negPow p * termAbs A (2 * p)) * (negPow (m - p) * termAbs B (2 * (m - p)))).eqv
      (negPow m * (ExpNeg.term A (2 * p) * ExpNeg.term B (2 * m - 2 * p)))
  rw [hsub]
  -- RHS: replace term A (2p) ≈ termAbs A (2p), term B (2(m−p)) ≈ termAbs B (2(m−p)).
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow m) _ _
      (Q'.mul_eqv_congr_right (ExpNeg.term A (2 * p)) (termAbs A (2 * p)) _
        (term_even_eq_abs A p))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow m) _ _
      (Q'.mul_eqv_congr_left (termAbs A (2 * p)) (ExpNeg.term B (2 * (m - p)))
        (termAbs B (2 * (m - p))) (term_even_eq_abs B (m - p)))) ?_
  -- Now: negPow m · (termAbs A (2p) · termAbs B (2(m−p)))  ≈  LHS.
  -- LHS = (negPow p · tA) · (negPow (m−p) · tB).  Rearrange to negPow m · (tA · tB).
  -- First collapse the sign: negPow m ≈ negPow p · negPow (m−p)  (p + (m−p) = m).
  have hsign : (negPow m).eqv (negPow p * negPow (m - p)) := by
    have hpm : p + (m - p) = m := by omega
    refine Q'.eqv_trans _ _ _ ?_ (negPow_add p (m - p))
    rw [hpm]
    exact Q'.eqv_refl (negPow m)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (negPow m) (negPow p * negPow (m - p))
      (termAbs A (2 * p) * termAbs B (2 * (m - p))) hsign) ?_
  -- Goal: (negPow p · negPow (m−p)) · (tA · tB) ≈ (negPow p · tA) · (negPow (m−p) · tB)
  -- Pure mul-comm/assoc shuffle: (s·t)·(a·b) ≈ (s·a)·(t·b).
  exact mul_shuffle_4 (negPow p) (negPow (m - p)) (termAbs A (2 * p)) (termAbs B (2 * (m - p)))

/-- `(-a)·(-b) ≈ a·b`. -/
theorem neg_mul_neg (a b : Q') : ((-a) * (-b)).eqv (a * b) := by
  refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv a (-b)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv a b)) ?_
  exact Q'.neg_neg_eqv (a * b)

/-- Odd-term bridge: for `p ≤ m`,
`sinConvTerm A B m p ≈ negPow m · convAddTerm A B (2(m+1)) (2p+1)`.
The convAdd partner index is `(2m+2)−(2p+1) = 2(m−p)+1` (odd), so both factors
flip sign and the product is positive; the shared sign is `negPow m`. -/
theorem sinConvTerm_eqv (A B : Q') (m p : Nat) (hp : p ≤ m) :
    (sinConvTerm A B m p).eqv (negPow m * convAddTerm A B (2 * (m + 1)) (2 * p + 1)) := by
  have hsub : 2 * (m + 1) - (2 * p + 1) = 2 * (m - p) + 1 := by omega
  show ((negPow p * termAbs A (2 * p + 1)) * (negPow (m - p) * termAbs B (2 * (m - p) + 1))).eqv
      (negPow m * (ExpNeg.term A (2 * p + 1) * ExpNeg.term B (2 * (m + 1) - (2 * p + 1))))
  rw [hsub]
  refine Q'.eqv_symm ?_
  -- Replace term A (2p+1) ≈ −termAbs A (2p+1), term B (2(m−p)+1) ≈ −termAbs B (2(m−p)+1).
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow m) _ _
      (Q'.mul_eqv_congr_right (ExpNeg.term A (2 * p + 1)) (-(termAbs A (2 * p + 1))) _
        (term_odd_eq_neg_abs A p))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow m) _ _
      (Q'.mul_eqv_congr_left (-(termAbs A (2 * p + 1))) (ExpNeg.term B (2 * (m - p) + 1))
        (-(termAbs B (2 * (m - p) + 1))) (term_odd_eq_neg_abs B (m - p)))) ?_
  -- (−tA)·(−tB) ≈ tA·tB
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow m) _ _
      (neg_mul_neg (termAbs A (2 * p + 1)) (termAbs B (2 * (m - p) + 1)))) ?_
  -- sign collapse negPow m ≈ negPow p · negPow (m−p)
  have hsign : (negPow m).eqv (negPow p * negPow (m - p)) := by
    have hpm : p + (m - p) = m := by omega
    refine Q'.eqv_trans _ _ _ ?_ (negPow_add p (m - p))
    rw [hpm]; exact Q'.eqv_refl (negPow m)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (negPow m) (negPow p * negPow (m - p))
      (termAbs A (2 * p + 1) * termAbs B (2 * (m - p) + 1)) hsign) ?_
  exact mul_shuffle_4 (negPow p) (negPow (m - p)) (termAbs A (2 * p + 1)) (termAbs B (2 * (m - p) + 1))

/-! ### 5d. Sum-level even/odd bridges and the per-degree addition identity (TC) -/

/-- The even sub-sum of `convAdd A B (2(m+1))` (the `m+2` even-index terms). -/
def evenSub (A B : Q') (m : Nat) : Q' :=
  RationalTail.finSum (fun p => convAddTerm A B (2 * (m + 1)) (2 * p)) (m + 2)

/-- The odd sub-sum of `convAdd A B (2(m+1))` (the `m+1` odd-index terms). -/
def oddSub (A B : Q') (m : Nat) : Q' :=
  RationalTail.finSum (fun p => convAddTerm A B (2 * (m + 1)) (2 * p + 1)) (m + 1)

/-- `cosConv A B (m+1) ≈ negPow (m+1) · evenSub A B m`. -/
theorem cosConv_eqv_evenSub (A B : Q') (m : Nat) :
    (cosConv A B (m + 1)).eqv (negPow (m + 1) * evenSub A B m) := by
  -- cosConv (m+1) = finSum (cosConvTerm A B (m+1)) (m+2)
  show (RationalTail.finSum (cosConvTerm A B (m + 1)) (m + 2)).eqv
      (negPow (m + 1) * RationalTail.finSum
        (fun p => convAddTerm A B (2 * (m + 1)) (2 * p)) (m + 2))
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr_lt (cosConvTerm A B (m + 1))
      (fun p => negPow (m + 1) * convAddTerm A B (2 * (m + 1)) (2 * p)) (m + 2)
      (fun p hp => cosConvTerm_eqv A B (m + 1) p (by omega))) ?_
  exact Q'.eqv_symm
    (RationalTail.const_mul_finSum
      (fun p => convAddTerm A B (2 * (m + 1)) (2 * p)) (negPow (m + 1)) (m + 2))

/-- `sinConv A B m ≈ negPow m · oddSub A B m`. -/
theorem sinConv_eqv_oddSub (A B : Q') (m : Nat) :
    (sinConv A B m).eqv (negPow m * oddSub A B m) := by
  show (RationalTail.finSum (sinConvTerm A B m) (m + 1)).eqv
      (negPow m * RationalTail.finSum
        (fun p => convAddTerm A B (2 * (m + 1)) (2 * p + 1)) (m + 1))
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr_lt (sinConvTerm A B m)
      (fun p => negPow m * convAddTerm A B (2 * (m + 1)) (2 * p + 1)) (m + 1)
      (fun p hp => sinConvTerm_eqv A B m p (by omega))) ?_
  exact Q'.eqv_symm
    (RationalTail.const_mul_finSum
      (fun p => convAddTerm A B (2 * (m + 1)) (2 * p + 1)) (negPow m) (m + 1))

/-- `convAdd A B (2(m+1)) ≈ evenSub A B m + oddSub A B m` (even/odd deinterleave at
the convAdd degree). -/
theorem convAdd_eqv_even_odd (A B : Q') (m : Nat) :
    (convAdd A B (2 * (m + 1))).eqv (evenSub A B m + oddSub A B m) := by
  -- convAdd A B D = finSum (convAddTerm A B D) (D+1), D = 2(m+1); D+1 = 2(m+1)+1.
  show (RationalTail.finSum (convAddTerm A B (2 * (m + 1))) (2 * (m + 1) + 1)).eqv
      (RationalTail.finSum (fun p => convAddTerm A B (2 * (m + 1)) (2 * p)) (m + 2)
        + RationalTail.finSum (fun p => convAddTerm A B (2 * (m + 1)) (2 * p + 1)) (m + 1))
  exact finSum_even_odd_split (convAddTerm A B (2 * (m + 1))) (m + 1)

/-- `cosTerm (A+B) (m+1) ≈ negPow (m+1) · term (A+B) (2(m+1))` (even-index magnitude
bridge applied at the sum angle). -/
theorem cosTerm_eqv_negPow_term (A B : Q') (m : Nat) :
    (cosTerm (A + B) (m + 1)).eqv (negPow (m + 1) * ExpNeg.term (A + B) (2 * (m + 1))) := by
  show (negPow (m + 1) * termAbs (A + B) (2 * (m + 1))).eqv
      (negPow (m + 1) * ExpNeg.term (A + B) (2 * (m + 1)))
  exact Q'.mul_eqv_congr_left (negPow (m + 1)) _ _
    (Q'.eqv_symm (term_even_eq_abs (A + B) (m + 1)))

/-- **The per-degree trig addition identity (TC), inductive degrees `m+1`.**
`cosConv A B (m+1) + (−(sinConv A B m)) ≃ cosTerm (A+B) (m+1)`.

This is the algebraic heart of `cos(A+B) = cos A cos B − sin A sin B`: the even
sub-sum of the exponential Cauchy coefficient `convAdd A B (2(m+1))` reassembles
`cosConv` with sign `(−1)^{m+1}`, the odd sub-sum reassembles `sinConv` with sign
`(−1)^m`, and the single `(−1)^{m+1}·(−1)^m = −1` discrepancy is the MINUS sign. -/
theorem cosConv_addition (A B : Q') (m : Nat) :
    (cosConv A B (m + 1) + (-(sinConv A B m))).eqv (cosTerm (A + B) (m + 1)) := by
  -- Step 1: substitute (C) and (Sn).
  -- cosConv(m+1) ≈ negPow(m+1)·even ; sinConv m ≈ negPow m·odd.
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (cosConv_eqv_evenSub A B m)
      (Q'.neg_eqv_congr _ _ (sinConv_eqv_oddSub A B m))) ?_
  -- Goal: negPow(m+1)·even + (−(negPow m·odd)) ≈ cosTerm(A+B)(m+1)
  -- Step 2: −(negPow m·odd) ≈ negPow(m+1)·odd  (since negPow(m+1) = −negPow m).
  have hflip : (-(negPow m * oddSub A B m)).eqv (negPow (m + 1) * oddSub A B m) := by
    show (-(negPow m * oddSub A B m)).eqv ((-(negPow m)) * oddSub A B m)
    exact Q'.eqv_symm (Q'.neg_mul_eqv (negPow m) (oddSub A B m))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (negPow (m + 1) * evenSub A B m) _ _ hflip) ?_
  -- Goal: negPow(m+1)·even + negPow(m+1)·odd ≈ cosTerm(A+B)(m+1)
  -- Step 3: factor: ≈ negPow(m+1)·(even+odd)
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_add_eqv (negPow (m + 1)) (evenSub A B m) (oddSub A B m))) ?_
  -- Step 4: even+odd ≈ convAdd A B (2(m+1)) ≈ term(A+B)(2(m+1))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow (m + 1)) _ _
      (Q'.eqv_symm (convAdd_eqv_even_odd A B m))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (negPow (m + 1)) _ _ (convAdd_eqv_term A B (2 * (m + 1)))) ?_
  -- Goal: negPow(m+1)·term(A+B)(2(m+1)) ≈ cosTerm(A+B)(m+1)
  exact Q'.eqv_symm (cosTerm_eqv_negPow_term A B m)

/-! ### 5e. Trig triangle decompositions (cos·cos and sin·sin diagonal sums)

Exactly as `ProductDecompAdd.triAdd` does for the exponential single product, the
cos·cos and sin·sin partial products row-split at the diagonal into a triangle
(whose recurrence peels one `cosConv`/`sinConv` per row) plus a corner.  Here we
land the triangle recurrences `cosTri (n+1) ≃ cosTri n + cosConv n` and
`cosTri n ≃ Σ_{m<n} cosConv m` (and the `sin` analogues).  These are the clean
adaptations of `triAdd_succ`/`triAdd_eqv_convAddSum`; the difference-of-products
diagonal collapse (which needs the degree-shifted telescope of `cosConv_addition`)
and the corner bounds remain — see the footer residual. -/

/-- `cosPartial x n = finSum (cosTerm x) n` (defeq by induction). -/
theorem cosPartial_eq_finSum (x : Q') :
    ∀ n, cosPartial x n = RationalTail.finSum (cosTerm x) n
  | 0 => rfl
  | n + 1 => by
    show cosPartial x n + cosTerm x n = RationalTail.finSum (cosTerm x) n + cosTerm x n
    rw [cosPartial_eq_finSum x n]

/-- `sinPartial x n = finSum (sinTerm x) n` (defeq by induction). -/
theorem sinPartial_eq_finSum (x : Q') :
    ∀ n, sinPartial x n = RationalTail.finSum (sinTerm x) n
  | 0 => rfl
  | n + 1 => by
    show sinPartial x n + sinTerm x n = RationalTail.finSum (sinTerm x) n + sinTerm x n
    rw [sinPartial_eq_finSum x n]

/-- `cosTriTerm A B n i = cosTerm A i · cosPartial B (n−i)`. -/
def cosTriTerm (A B : Q') (n : Nat) : Nat → Q' :=
  fun i => cosTerm A i * cosPartial B (n - i)

/-- `cosTri A B n = Σ_{i<n} cosTerm A i · cosPartial B (n−i)`. -/
def cosTri (A B : Q') (n : Nat) : Q' := RationalTail.finSum (cosTriTerm A B n) n

/-- `sinTriTerm A B n i = sinTerm A i · sinPartial B (n−i)`. -/
def sinTriTerm (A B : Q') (n : Nat) : Nat → Q' :=
  fun i => sinTerm A i * sinPartial B (n - i)

/-- `sinTri A B n = Σ_{i<n} sinTerm A i · sinPartial B (n−i)`. -/
def sinTri (A B : Q') (n : Nat) : Q' := RationalTail.finSum (sinTriTerm A B n) n

/-- Cosine triangle recurrence `cosTri (n+1) ≃ cosTri n + cosConv n`. -/
theorem cosTri_succ (A B : Q') (n : Nat) :
    (cosTri A B (n + 1)).eqv (cosTri A B n + cosConv A B n) := by
  show (RationalTail.finSum (cosTriTerm A B (n + 1)) n + cosTriTerm A B (n + 1) n).eqv
      (cosTri A B n + cosConv A B n)
  -- last term: cosTerm A n · cosPartial B 1 = cosTerm A n · cosTerm B 0
  have hlast : (cosTriTerm A B (n + 1) n).eqv (cosTerm A n * cosTerm B 0) := by
    show (cosTerm A n * cosPartial B ((n + 1) - n)).eqv (cosTerm A n * cosTerm B 0)
    have h1 : (n + 1) - n = 1 := by omega
    rw [h1]
    show (cosTerm A n * ((0 : Q') + cosTerm B 0)).eqv (cosTerm A n * cosTerm B 0)
    exact Q'.mul_eqv_congr_left (cosTerm A n) _ _ (Q'.eqv_of_eq (Q'.zero_add' (cosTerm B 0)))
  -- row split: cosTriTerm (n+1) i ≈ cosTriTerm n i + cosConvTerm n i for i < n
  have hrow : ∀ i, i < n →
      (cosTriTerm A B (n + 1) i).eqv (cosTriTerm A B n i + cosConvTerm A B n i) := by
    intro i hi
    have hsub : (n + 1) - i = (n - i) + 1 := by omega
    show (cosTerm A i * cosPartial B ((n + 1) - i)).eqv
        (cosTerm A i * cosPartial B (n - i) + cosTerm A i * cosTerm B (n - i))
    rw [hsub]
    show (cosTerm A i * (cosPartial B (n - i) + cosTerm B (n - i))).eqv
        (cosTerm A i * cosPartial B (n - i) + cosTerm A i * cosTerm B (n - i))
    exact Q'.mul_add_eqv (cosTerm A i) (cosPartial B (n - i)) (cosTerm B (n - i))
  have hinner : (RationalTail.finSum (cosTriTerm A B (n + 1)) n).eqv
      (cosTri A B n + RationalTail.finSum (cosConvTerm A B n) n) :=
    Q'.eqv_trans _ _ _
      (RationalTail.finSum_eqv_congr_lt (cosTriTerm A B (n + 1))
        (fun i => cosTriTerm A B n i + cosConvTerm A B n i) n hrow)
      (RationalTail.finSum_add (cosTriTerm A B n) (cosConvTerm A B n) n)
  -- cosConv n = finSum (cosConvTerm n) (n+1) = finSum (cosConvTerm n) n + cosConvTerm n n,
  -- and cosConvTerm n n = cosTerm A n · cosTerm B 0.
  have hconv : (cosConv A B n).eqv
      (RationalTail.finSum (cosConvTerm A B n) n + cosTerm A n * cosTerm B 0) := by
    show (RationalTail.finSum (cosConvTerm A B n) n + cosConvTerm A B n n).eqv
        (RationalTail.finSum (cosConvTerm A B n) n + cosTerm A n * cosTerm B 0)
    refine Q'.add_eqv_congr_left _ _ _ ?_
    show (cosTerm A n * cosTerm B (n - n)).eqv (cosTerm A n * cosTerm B 0)
    have hnn : n - n = 0 := by omega
    rw [hnn]
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hinner) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hlast) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (cosTri A B n) (RationalTail.finSum (cosConvTerm A B n) n)
      (cosTerm A n * cosTerm B 0)) ?_
  exact Q'.add_eqv_congr_left (cosTri A B n) _ _ (Q'.eqv_symm hconv)

/-- Sine triangle recurrence `sinTri (n+1) ≃ sinTri n + sinConv n`. -/
theorem sinTri_succ (A B : Q') (n : Nat) :
    (sinTri A B (n + 1)).eqv (sinTri A B n + sinConv A B n) := by
  show (RationalTail.finSum (sinTriTerm A B (n + 1)) n + sinTriTerm A B (n + 1) n).eqv
      (sinTri A B n + sinConv A B n)
  have hlast : (sinTriTerm A B (n + 1) n).eqv (sinTerm A n * sinTerm B 0) := by
    show (sinTerm A n * sinPartial B ((n + 1) - n)).eqv (sinTerm A n * sinTerm B 0)
    have h1 : (n + 1) - n = 1 := by omega
    rw [h1]
    show (sinTerm A n * ((0 : Q') + sinTerm B 0)).eqv (sinTerm A n * sinTerm B 0)
    exact Q'.mul_eqv_congr_left (sinTerm A n) _ _ (Q'.eqv_of_eq (Q'.zero_add' (sinTerm B 0)))
  have hrow : ∀ i, i < n →
      (sinTriTerm A B (n + 1) i).eqv (sinTriTerm A B n i + sinConvTerm A B n i) := by
    intro i hi
    have hsub : (n + 1) - i = (n - i) + 1 := by omega
    show (sinTerm A i * sinPartial B ((n + 1) - i)).eqv
        (sinTerm A i * sinPartial B (n - i) + sinTerm A i * sinTerm B (n - i))
    rw [hsub]
    show (sinTerm A i * (sinPartial B (n - i) + sinTerm B (n - i))).eqv
        (sinTerm A i * sinPartial B (n - i) + sinTerm A i * sinTerm B (n - i))
    exact Q'.mul_add_eqv (sinTerm A i) (sinPartial B (n - i)) (sinTerm B (n - i))
  have hinner : (RationalTail.finSum (sinTriTerm A B (n + 1)) n).eqv
      (sinTri A B n + RationalTail.finSum (sinConvTerm A B n) n) :=
    Q'.eqv_trans _ _ _
      (RationalTail.finSum_eqv_congr_lt (sinTriTerm A B (n + 1))
        (fun i => sinTriTerm A B n i + sinConvTerm A B n i) n hrow)
      (RationalTail.finSum_add (sinTriTerm A B n) (sinConvTerm A B n) n)
  have hconv : (sinConv A B n).eqv
      (RationalTail.finSum (sinConvTerm A B n) n + sinTerm A n * sinTerm B 0) := by
    show (RationalTail.finSum (sinConvTerm A B n) n + sinConvTerm A B n n).eqv
        (RationalTail.finSum (sinConvTerm A B n) n + sinTerm A n * sinTerm B 0)
    refine Q'.add_eqv_congr_left _ _ _ ?_
    show (sinTerm A n * sinTerm B (n - n)).eqv (sinTerm A n * sinTerm B 0)
    have hnn : n - n = 0 := by omega
    rw [hnn]
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hinner) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hlast) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (sinTri A B n) (RationalTail.finSum (sinConvTerm A B n) n)
      (sinTerm A n * sinTerm B 0)) ?_
  exact Q'.add_eqv_congr_left (sinTri A B n) _ _ (Q'.eqv_symm hconv)

/-- `cosTri A B n ≃ Σ_{m<n} cosConv A B m`. -/
theorem cosTri_eqv_convSum (A B : Q') :
    ∀ n, (cosTri A B n).eqv (RationalTail.finSum (cosConv A B) n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
    show (cosTri A B (n + 1)).eqv (RationalTail.finSum (cosConv A B) n + cosConv A B n)
    refine Q'.eqv_trans _ _ _ (cosTri_succ A B n) ?_
    exact Q'.add_eqv_congr_right (cosTri A B n) _ (cosConv A B n) (cosTri_eqv_convSum A B n)

/-- `sinTri A B n ≃ Σ_{m<n} sinConv A B m`. -/
theorem sinTri_eqv_convSum (A B : Q') :
    ∀ n, (sinTri A B n).eqv (RationalTail.finSum (sinConv A B) n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
    show (sinTri A B (n + 1)).eqv (RationalTail.finSum (sinConv A B) n + sinConv A B n)
    refine Q'.eqv_trans _ _ _ (sinTri_succ A B n) ?_
    exact Q'.add_eqv_congr_right (sinTri A B n) _ (sinConv A B n) (sinTri_eqv_convSum A B n)

/-! ### 5f. The diagonal collapse (degree-shifted telescope via (TC))

`Σ_{m<n+1} cosConv m  +  (−ΣQ_{m<n} sinConv m)  ≃  cosPartial (A+B) (n+1)`.  The cos
diagonal sum runs ONE degree past the sin diagonal sum; each paired summand
`cosConv (m+1) − sinConv m` collapses to `cosTerm (A+B) (m+1)` by `cosConv_addition`,
and the unpaired `cosConv 0` collapses by `cosConv_addition_zero`.  This is the
exact `Q'`-level addition law at the *diagonal-sum* level — the trig analogue of
`triAdd_eqv_partialSum`, with the minus and the degree shift made explicit. -/

/-- **Diagonal collapse.**  `(Σ_{m<n+1} cosConv) + (−(Σ_{m<n} sinConv)) ≃
cosPartial (A+B) (n+1)`. -/
theorem cosSum_sub_sinSum_eqv_cosPartial (A B : Q') :
    ∀ n, (RationalTail.finSum (cosConv A B) (n + 1)
        + (-(RationalTail.finSum (sinConv A B) n))).eqv (cosPartial (A + B) (n + 1))
  | 0 => by
    -- (cosConv 0) + (−0) ≃ cosTerm (A+B) 0 = cosPartial (A+B) 1.
    show ((0 : Q') + cosConv A B 0 + (-(0 : Q'))).eqv ((0 : Q') + cosTerm (A + B) 0)
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ 0 (by show (-(0:Q')).eqv 0; decide)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' ((0:Q') + cosConv A B 0))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' (cosConv A B 0))) ?_
    refine Q'.eqv_trans _ _ _ (cosConv_addition_zero A B) ?_
    exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' (cosTerm (A + B) 0)))
  | n + 1 => by
    -- LHS = (Σcos (n+1) + cosConv(n+1)) + (−(Σsin n + sinConv n))
    --     ≃ [Σcos(n+1) + (−Σsin n)] + [cosConv(n+1) + (−sinConv n)]
    --     ≃ cosPartial(A+B)(n+1) + cosTerm(A+B)(n+1) = cosPartial(A+B)(n+2).
    show ((RationalTail.finSum (cosConv A B) (n + 1) + cosConv A B (n + 1))
        + (-(RationalTail.finSum (sinConv A B) n + sinConv A B n))).eqv
        (cosPartial (A + B) (n + 1) + cosTerm (A + B) (n + 1))
    -- expand the negation of the sin sum
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.neg_add_eqv (RationalTail.finSum (sinConv A B) n) (sinConv A B n))) ?_
    -- now: (Σcos(n+1) + cosConv(n+1)) + ((−Σsin n) + (−sinConv n))
    -- rearrange to [Σcos(n+1) + (−Σsin n)] + [cosConv(n+1) + (−sinConv n)]
    refine Q'.eqv_trans _ _ _
      (Q'.add_swap_inner (RationalTail.finSum (cosConv A B) (n + 1)) (cosConv A B (n + 1))
        (-(RationalTail.finSum (sinConv A B) n)) (-(sinConv A B n))) ?_
    -- apply IH and (TC)
    refine Q'.add_eqv_congr' (cosSum_sub_sinSum_eqv_cosPartial A B n) ?_
    exact cosConv_addition A B n

/-! ### 5g. Trig rectangle/corner product decompositions (clean copies)

`cosPartial A n · cosPartial B n ≃ cosTri A B n + cosCorner A B n` (and sin), the
direct trig analogue of `prodAdd_eqv_tri_add_corner`.  Combined with §5e
(`cosTri ≃ Σ cosConv`) and §5f (diagonal collapse), the *only* remaining gap to the
CReal addition law is the vanishing of the corners and the trailing `sinConv`
mismatch term — the analytic (modulus) ingredient, named in the footer. -/

/-- `cosCornerTerm A B n i = cosTerm A i · (cosPartial B n − cosPartial B (n−i))`. -/
def cosCornerTerm (A B : Q') (n : Nat) : Nat → Q' :=
  fun i => cosTerm A i * (cosPartial B n + -(cosPartial B (n - i)))

/-- `cosCorner A B n = Σ_{i<n} cosCornerTerm A B n i`. -/
def cosCorner (A B : Q') (n : Nat) : Q' := RationalTail.finSum (cosCornerTerm A B n) n

/-- `sinCornerTerm A B n i = sinTerm A i · (sinPartial B n − sinPartial B (n−i))`. -/
def sinCornerTerm (A B : Q') (n : Nat) : Nat → Q' :=
  fun i => sinTerm A i * (sinPartial B n + -(sinPartial B (n - i)))

/-- `sinCorner A B n = Σ_{i<n} sinCornerTerm A B n i`. -/
def sinCorner (A B : Q') (n : Nat) : Q' := RationalTail.finSum (sinCornerTerm A B n) n

/-- **Cosine rectangle/corner decomposition.**  `cosPartial A n · cosPartial B n ≃
cosTri A B n + cosCorner A B n`. -/
theorem cosProd_eqv_tri_add_corner (A B : Q') (n : Nat) :
    (cosPartial A n * cosPartial B n).eqv (cosTri A B n + cosCorner A B n) := by
  rw [cosPartial_eq_finSum A]
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_mul_const (cosTerm A) (cosPartial B n) n) ?_
  have hterm : ∀ i, (cosTerm A i * cosPartial B n).eqv
      (cosTriTerm A B n i + cosCornerTerm A B n i) := by
    intro i
    show (cosTerm A i * cosPartial B n).eqv
        (cosTerm A i * cosPartial B (n - i)
          + cosTerm A i * (cosPartial B n + -(cosPartial B (n - i))))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (cosTerm A i) (cosPartial B n)
        (cosPartial B (n - i) + (cosPartial B n + -(cosPartial B (n - i))))
        (Q'.add_sub_cancel_eqv (cosPartial B n) (cosPartial B (n - i)))) ?_
    exact Q'.mul_add_eqv (cosTerm A i) (cosPartial B (n - i))
      (cosPartial B n + -(cosPartial B (n - i)))
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr (fun i => cosTerm A i * cosPartial B n)
      (fun i => cosTriTerm A B n i + cosCornerTerm A B n i) hterm n) ?_
  exact RationalTail.finSum_add (cosTriTerm A B n) (cosCornerTerm A B n) n

/-- **Sine rectangle/corner decomposition.**  `sinPartial A n · sinPartial B n ≃
sinTri A B n + sinCorner A B n`. -/
theorem sinProd_eqv_tri_add_corner (A B : Q') (n : Nat) :
    (sinPartial A n * sinPartial B n).eqv (sinTri A B n + sinCorner A B n) := by
  rw [sinPartial_eq_finSum A]
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_mul_const (sinTerm A) (sinPartial B n) n) ?_
  have hterm : ∀ i, (sinTerm A i * sinPartial B n).eqv
      (sinTriTerm A B n i + sinCornerTerm A B n i) := by
    intro i
    show (sinTerm A i * sinPartial B n).eqv
        (sinTerm A i * sinPartial B (n - i)
          + sinTerm A i * (sinPartial B n + -(sinPartial B (n - i))))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (sinTerm A i) (sinPartial B n)
        (sinPartial B (n - i) + (sinPartial B n + -(sinPartial B (n - i))))
        (Q'.add_sub_cancel_eqv (sinPartial B n) (sinPartial B (n - i)))) ?_
    exact Q'.mul_add_eqv (sinTerm A i) (sinPartial B (n - i))
      (sinPartial B n + -(sinPartial B (n - i)))
  refine Q'.eqv_trans _ _ _
    (RationalTail.finSum_eqv_congr (fun i => sinTerm A i * sinPartial B n)
      (fun i => sinTriTerm A B n i + sinCornerTerm A B n i) hterm n) ?_
  exact RationalTail.finSum_add (sinTriTerm A B n) (sinCornerTerm A B n) n

/-- **Cosine rectangle decomposition, diagonal form.**  `cosPartial A n · cosPartial B n
≃ (Σ_{m<n} cosConv A B m) + cosCorner A B n`. -/
theorem cosProd_eqv_convSum_add_corner (A B : Q') (n : Nat) :
    (cosPartial A n * cosPartial B n).eqv
      (RationalTail.finSum (cosConv A B) n + cosCorner A B n) := by
  refine Q'.eqv_trans _ _ _ (cosProd_eqv_tri_add_corner A B n) ?_
  exact Q'.add_eqv_congr_right (cosTri A B n) _ (cosCorner A B n) (cosTri_eqv_convSum A B n)

/-- **Sine rectangle decomposition, diagonal form.**  `sinPartial A n · sinPartial B n
≃ (Σ_{m<n} sinConv A B m) + sinCorner A B n`. -/
theorem sinProd_eqv_convSum_add_corner (A B : Q') (n : Nat) :
    (sinPartial A n * sinPartial B n).eqv
      (RationalTail.finSum (sinConv A B) n + sinCorner A B n) := by
  refine Q'.eqv_trans _ _ _ (sinProd_eqv_tri_add_corner A B n) ?_
  exact Q'.add_eqv_congr_right (sinTri A B n) _ (sinCorner A B n) (sinTri_eqv_convSum A B n)

/-! ### 5h. The trig rectangle/corner addition identity (step 4, `Q'` level)

Assembling §5f (diagonal collapse) with §5g (rectangle decompositions) gives the
exact `Q'.eqv` identity, for `n = k+1`,

  cosPartial A n · cosPartial B n  −  sinPartial A n · sinPartial B n
      ≃  cosPartial (A+B) n  +  remCorner A B k ,

where `remCorner A B k := (cosCorner A B (k+1) − sinCorner A B (k+1)) − sinConv A B k`
collects the two product corners and the single trailing degree-`k` sin convolution
left over from the degree-shifted telescope.  The CReal addition law (step 5) is
exactly `remCorner → 0` past an explicit modulus (the analytic residual). -/

/-- The combined corner remainder of the trig rectangle decomposition at `n = k+1`. -/
def remCorner (A B : Q') (k : Nat) : Q' :=
  (cosCorner A B (k + 1) + (-(sinCorner A B (k + 1)))) + (-(sinConv A B k))

/-- **The trig rectangle/corner addition identity (`Q'` level).**  For `n = k+1`,
`cosPartial A n · cosPartial B n − sinPartial A n · sinPartial B n
≃ cosPartial (A+B) n + remCorner A B k`. -/
theorem cosSinProd_eqv_cosPartial_add_remCorner (A B : Q') (k : Nat) :
    (cosPartial A (k + 1) * cosPartial B (k + 1)
        + (-(sinPartial A (k + 1) * sinPartial B (k + 1)))).eqv
      (cosPartial (A + B) (k + 1) + remCorner A B k) := by
  -- substitute both rectangle decompositions
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (cosProd_eqv_convSum_add_corner A B (k + 1))
      (Q'.neg_eqv_congr _ _ (sinProd_eqv_convSum_add_corner A B (k + 1)))) ?_
  -- LHS now: (CS + CC) + (−(SS + SC)) with CS=Σcos(k+1), CC=cosCorner, SS=Σsin(k+1),
  -- SC=sinCorner.  Σsin(k+1) = Σsin k + sinConv k (defeq), so peel sinConv k:
  -- −SS ≃ (−Σsin k) + (−sinConv k).  Then a pure 5-term rearrangement lands
  -- [CS + (−Σsin k)] + [(CC + (−SC)) + (−sinConv k)] = [collapse] + remCorner.
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.neg_add_eqv (RationalTail.finSum (sinConv A B) (k + 1)) (sinCorner A B (k + 1)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ (-(sinCorner A B (k + 1)))
        (Q'.neg_add_eqv (RationalTail.finSum (sinConv A B) k) (sinConv A B k)))) ?_
  -- now: (CS + CC) + (((−Σsin k) + (−sinConv k)) + (−SC))
  refine Q'.eqv_trans _ _ _
    (add_rearrange_5 (RationalTail.finSum (cosConv A B) (k + 1)) (cosCorner A B (k + 1))
      (-(RationalTail.finSum (sinConv A B) k)) (-(sinConv A B k)) (-(sinCorner A B (k + 1)))) ?_
  -- goal: [CS + (−Σsin k)] + [(CC + (−SC)) + (−sinConv k)]
  --        ≃ cosPartial(A+B)(k+1) + remCorner A B k
  refine Q'.add_eqv_congr' (cosSum_sub_sinSum_eqv_cosPartial A B k) ?_
  -- (CC + (−SC)) + (−sinConv k) = remCorner A B k  (defeq).
  exact Q'.eqv_refl _

end TrigAdd

end YMGap.Constructive

/-! ## The precise residual (the addition-formula core, honestly named)

What is CLOSED here and discharges `TrigBound`:

  * The `|cA| ≤ 1`/`|sA| ≤ 1` and small-angle budget hypothesis FAMILIES of
    `TrigBound.cos_second_diff_abs_le` are stated over abstract `Q'` data with the
    budgets `Bc`, `Bs` as parameters; `cos_small_angle`/`sin_small_angle` here
    supply the budgets for the actual `cosPartial`/`sinPartial` truncations (the
    `Q'` values a constructive cos/sin delivers), with `Bc = 2·termAbs x 2 = x²`,
    `Bs = 2·termAbs x 3 = x³/3`.  (The block machinery yields these honest
    constants; the sharp `x²/2` would need an alternating-cancellation refinement
    of the magnitude-sum block bound, not landed here.)

Now CLOSED (the addition-formula core, all `Q'.eqv`, no convergence theory):

  * EVEN/ODD REASSEMBLY (`finSum_even_odd_split`): the deinterleave
    `finSum f (2m+1) ≃ Σ_{p≤m} f(2p) + Σ_{p<m} f(2p+1)`, by induction on `m`.

  * THE PER-DEGREE ADDITION IDENTITY `(TC)` (`cosConv_addition`):
        cosConv A B (m+1)  +  (−(sinConv A B m))  ≃  cosTerm (A+B) (m+1) ,
    via the §5a `negPow` sign algebra (`(−1)^{m+1}·(−1)^m = −1` is the MINUS), the
    §4 magnitude bridge, and `ExpAddConv.convAdd_eqv_term`.  The even sub-sum
    reassembles `cosConv` with sign `(−1)^{m+1}`, the odd sub-sum `sinConv` with
    sign `(−1)^m`.  Base case: `cosConv_addition_zero` (`m = 0`).

  * THE DIAGONAL COLLAPSE (`cosSum_sub_sinSum_eqv_cosPartial`):
        (Σ_{m<n+1} cosConv)  +  (−(Σ_{m<n} sinConv))  ≃  cosPartial (A+B) (n+1) ,
    the degree-shifted telescope of `(TC)` (cos diagonal one degree ahead of sin).

  * THE RECTANGLE/CORNER ADDITION IDENTITY at the `Q'` level (step 4,
    `cosSinProd_eqv_cosPartial_add_remCorner`): for `n = k+1`,
        cosPartial A n · cosPartial B n  −  sinPartial A n · sinPartial B n
            ≃  cosPartial (A+B) n  +  remCorner A B k ,
    `remCorner A B k = (cosCorner A B (k+1) − sinCorner A B (k+1)) − sinConv A B k`,
    assembled from the cos/sin rectangle decompositions (`cos/sinProd_eqv_…`) and
    the diagonal collapse.

What REMAINS (the analytic residual — the CReal addition law, steps 5–6):

  ONE named obligation: `remCorner A B k → 0` past an explicit modulus, i.e.
        ∀ ε>0, ∃ N, ∀ k ≥ N, |remCorner A B k| ≤ ε .
  This is the trig analogue of `CornerBoundAdd.cornerAbsAdd_le` (the two product
  corners `cosCorner`/`sinCorner` are dominated by the exponential magnitude
  corner, and the trailing `sinConv A B k` is a degree-`k` convolution coefficient
  which vanishes).  It is NOT a verbatim copy of `CornerBoundAdd` — it needs the
  trig magnitude-corner bound (cos/sin corners ≤ the `blockAbs`-dominated exp
  corner) plus the `sinConv`-tail estimate.  Given that modulus, step 5
  (`cos_add_equiv : CReal.Equiv (cosFull (A+B)) (cosFull A · cosFull B −
  sinFull A · sinFull B)`) copies `ExpAdd.expNeg_add_equiv` — it transfers the
  `Q'`-level identity `cosSinProd_eqv_cosPartial_add_remCorner` to a `CReal.Equiv`
  via `leRat_of_equiv`, using the four-case signed extension
  (`cosFull_even`/`sinFull_odd_of_nonneg`).  Step 6 then discharges the `Q'`-level
  `TrigBound.hadd : cAB ≈ cA·cB + (−(sA·sB))` per approximation index and combines
  with `cos_small_angle`/`sin_small_angle` for the second-difference bound.

# Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.TrigAdd.termAbs_eqv_congr
#print axioms YMGap.Constructive.TrigAdd.cosPartial_eqv_congr
#print axioms YMGap.Constructive.TrigAdd.sinPartial_eqv_congr
#print axioms YMGap.Constructive.TrigAdd.equiv_of_approx_eqv
#print axioms YMGap.Constructive.TrigAdd.cosFull
#print axioms YMGap.Constructive.TrigAdd.sinFull
#print axioms YMGap.Constructive.TrigAdd.cosFull_even
#print axioms YMGap.Constructive.TrigAdd.sinFull_odd_of_nonneg
#print axioms YMGap.Constructive.TrigAdd.blockAbs_two_le
#print axioms YMGap.Constructive.TrigAdd.cos_small_angle
#print axioms YMGap.Constructive.TrigAdd.sin_small_angle
#print axioms YMGap.Constructive.TrigAdd.term_even_eq_abs
#print axioms YMGap.Constructive.TrigAdd.term_odd_eq_neg_abs
#print axioms YMGap.Constructive.TrigAdd.cosConv_addition_zero
#print axioms YMGap.Constructive.TrigAdd.negPow_add
#print axioms YMGap.Constructive.TrigAdd.negPow_self_mul
#print axioms YMGap.Constructive.TrigAdd.negPow_succ_mul
#print axioms YMGap.Constructive.TrigAdd.finSum_even_odd_split
#print axioms YMGap.Constructive.TrigAdd.cosConvTerm_eqv
#print axioms YMGap.Constructive.TrigAdd.sinConvTerm_eqv
#print axioms YMGap.Constructive.TrigAdd.cosConv_eqv_evenSub
#print axioms YMGap.Constructive.TrigAdd.sinConv_eqv_oddSub
#print axioms YMGap.Constructive.TrigAdd.convAdd_eqv_even_odd
#print axioms YMGap.Constructive.TrigAdd.cosConv_addition
#print axioms YMGap.Constructive.TrigAdd.cosTri_succ
#print axioms YMGap.Constructive.TrigAdd.sinTri_succ
#print axioms YMGap.Constructive.TrigAdd.cosTri_eqv_convSum
#print axioms YMGap.Constructive.TrigAdd.sinTri_eqv_convSum
#print axioms YMGap.Constructive.TrigAdd.cosSum_sub_sinSum_eqv_cosPartial
#print axioms YMGap.Constructive.TrigAdd.cosProd_eqv_convSum_add_corner
#print axioms YMGap.Constructive.TrigAdd.sinProd_eqv_convSum_add_corner
#print axioms YMGap.Constructive.TrigAdd.cosSinProd_eqv_cosPartial_add_remCorner
