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

What REMAINS for the `hadd` hypothesis family (the addition formula itself):

  The exact per-degree convolution identity `(TC)`

      cosConv A B m  +  (−(sinConv A B (m−1)))  ≃  cosTerm (A+B) m

  is reduced — via `term_even_eq_abs`/`term_odd_eq_neg_abs` and
  `ExpAddConv.convAdd_eqv_term` (`convAdd A B (2m) ≃ term (A+B) (2m)`) — to ONE
  missing combinatorial lemma:

      EVEN/ODD REASSEMBLY:  finSum (convAddTerm A B (2m)) (2m+1)
          ≃  (Σ even-i terms)  +  (Σ odd-i terms),
      with the even part reindexing to `(−1)^m · cosConv A B m` and the odd part
      to `(−1)^{m−1} · sinConv A B (m−1)` (sign bookkeeping via the bridge).

  The `i²=−1` cross-cancellation of the real addition formula appears here purely
  as the `(−1)^m` vs `(−1)^{m−1}` sign discrepancy between the even and odd
  reindexings, which is exactly the algebraic source of the MINUS sign.  No new
  convergence theory is needed — the reassembly is pure `finSum` reindexing over
  `Q'.eqv`.  Once `(TC)` is in hand, the rectangle/corner decomposition and the
  `CReal.Equiv` addition law copy `ProductDecompAdd.lean` / `CornerBoundAdd.lean`
  / `ExpAdd.lean` verbatim (with cos/sin partials in place of `partialSum`), and
  the signed `cosFull`/`sinFull` four-case extension uses `cosFull_even` /
  `sinFull_odd_of_nonneg`.

  The base case `cosConv_addition_zero` validates `(TC)` at `m = 0`.

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
