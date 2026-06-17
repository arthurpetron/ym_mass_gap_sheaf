/-
Arithmetic and completeness for the canonical-modulus regular constructive
real `RegularCReal`.

# Why this module exists

`RegularCReal` carries its regularity modulus as `∀`-DATA (the canonical
`1/(m+1) + 1/(n+1)` two-sided gap), which makes its Bishop order transitive
and the equivalence relation a genuine setoid.  This module equips it with
the algebra needed downstream for functional linearity and with the
completeness limit:

  * **Addition / negation / subtraction** (`add`, `neg`, `sub`) with the
    canonical regularity PROVED by index doubling, plus the compatibility
    layer (`ofQ'_add`, `add_comm`, `add_assoc`, `add_congr`,
    `add_le_add_left/right/_`, `sub_self_eqv_zero`, `add_czero`,
    `czero_add`).
  * **Rational scaling** (`qmul`) by a `Q'` factor, reindexed by a `Nat`
    bound on `|q|` so the canonical modulus is preserved, with
    `ofQ'_qmul`, `qmul_add`, `qmul_czero`, `qmul_one`, `one_qmul`, and the
    monotonicity `qmul_le` for `0 ≤ q`.
  * **Completeness**: a `ModCauchy` modulus-as-data record, the diagonal
    `completeLimit`, its `ConvergesTo` witness, and bound-passing
    (`ofQ'_le_completeLimit`, the dual, and `isPositive_completeLimit`),
    with a non-vacuity demo.

Because the regularity modulus is fixed (never extracted from an
existential), every construction here is choice-free.

# Constructive content and axiom gate (AGENTS.md Rule 1 / Rule 8)

Every modulus is `Type`-level data; no `Prop`-`∃` carries a recoverable
witness.  Every declaration is gated with `#print axioms` at the bottom;
the permitted output is `propext` / `Quot.sound` only (the latter only via
reused `Nat`/`Int`/`omega` helpers).  No `Classical.*`, no `native_decide`,
no `sorry`.
-/

import YMGap.Constructive.Rationals
import YMGap.Constructive.RationalsMul
import YMGap.Constructive.AbsQ
import YMGap.Constructive.RatNat
import YMGap.Constructive.CRealMul
import YMGap.Constructive.ExpNeg
import YMGap.Constructive.HalfPow
import YMGap.Constructive.RegularCReal

namespace YMGap.Constructive

namespace Q'

/-! ## Q' helpers for the regular-real arithmetic layer

Two families of facts beyond what `RegularCReal.lean` already added:
(i) `invSucc`-collapse identities under index doubling / scaling, the
arithmetic that lets `add`/`qmul` preserve the CANONICAL modulus; and
(ii) a couple of small `eqv`/order glue lemmas. -/

/-- `(invSucc (2k+1) + invSucc (2k+1)) ≃ invSucc k`.  Both sides equal
`1/(k+1)`: the LHS is `2/(2k+2)`.  This is the index-doubling collapse that
makes `add`'s canonical modulus go through (each summand contributes a
`2·invSucc (2·-+1)` error, which collapses to `invSucc -`). -/
theorem invSucc_double_eqv (k : Nat) :
    (Q'.invSucc (2 * k + 1) + Q'.invSucc (2 * k + 1)).eqv (Q'.invSucc k) := by
  -- Cross-product: LHS.num · RHS.den = RHS.num · LHS.den.
  show (Q'.invSucc (2 * k + 1) + Q'.invSucc (2 * k + 1)).num * ((Q'.invSucc k).den : Int)
      = (Q'.invSucc k).num * ((Q'.invSucc (2 * k + 1) + Q'.invSucc (2 * k + 1)).den : Int)
  rw [Q'.add_num_cast, Q'.add_den_cast, Q'.invSucc_num, Q'.invSucc_den, Q'.invSucc_den]
  -- LHS num = 1·(2k+2) + 1·(2k+2) ; den = (2k+2)·(2k+2) ; RHS invSucc k num=1, den=k+1
  show ((1 : Int) * (((2 * k + 1) + 1 : Nat) : Int) + (1 : Int) * (((2 * k + 1) + 1 : Nat) : Int))
        * ((k + 1 : Nat) : Int)
      = (1 : Int) * ((((2 * k + 1) + 1 : Nat) : Int) * (((2 * k + 1) + 1 : Nat) : Int))
  -- Abbreviate t = (k+1 : Int); then (2k+1)+1 = 2·t as Int.
  have hcast : (((2 * k + 1) + 1 : Nat) : Int) = 2 * (((k + 1 : Nat) : Int)) := by
    have : ((2 * k + 1 + 1 : Nat) : Int) = 2 * ((k + 1 : Nat) : Int) := by
      have e1 : ((2 * k + 1 + 1 : Nat) : Int) = 2 * (k : Int) + 2 := by
        rw [Int.natCast_add, Int.natCast_add, Int.natCast_mul]; rfl
      have e2 : 2 * ((k + 1 : Nat) : Int) = 2 * (k : Int) + 2 := by
        rw [Int.natCast_add]; show (2 : Int) * ((k : Int) + ((1 : Nat) : Int)) = _
        rw [Int.mul_add]; rfl
      rw [e1, e2]
    exact this
  rw [hcast, Int.one_mul, Int.one_mul]
  -- Goal: (2t + 2t) * t = (2t) * (2t), with t = (k+1 : Int).
  generalize (((k + 1 : Nat) : Int)) = t
  -- Both sides equal (2*t)*t + (2*t)*t.
  have lhs : (2 * t + 2 * t) * t = (2 * t) * t + (2 * t) * t := Int.add_mul _ _ _
  have rhs : (2 * t) * (2 * t) = (2 * t) * t + (2 * t) * t := by
    have h2 : (2 : Int) * t = t + t := by
      rw [show (2 : Int) = 1 + 1 from by decide, Int.add_mul, Int.one_mul]
    rw [h2, Int.mul_add]
  rw [lhs, rhs]

/-- Negation flips a one-slack bound: `a ≤ b + ε ⟹ -b ≤ -a + ε`.  Re-derived
here (the foundation does not import the `CReal` add layer) from the `Q'`
neg/add `eqv` glue. -/
theorem neg_le_neg_add' {a b ε : Q'} (h : a ≤ b + ε) : -b ≤ -a + ε := by
  have h1 : a + -b ≤ ε := Q'.sub_le_of_le_add h
  have h2 : -b + a ≤ ε := Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_comm_eqv (-b) a)) h1
  have h3 : (-b + a) + -a ≤ ε + -a := Q'.add_le_add_right _ _ (-a) h2
  have e1 : ((-b + a) + -a).eqv (-b) := by
    have a1 := Q'.add_assoc_eqv (-b) a (-a)
    have a2 : (-b + (a + -a)).eqv (-b + 0) :=
      Q'.add_eqv_congr_left (-b) (a + -a) 0 (Q'.add_neg_self_eqv a)
    rw [Q'.add_zero' (-b)] at a2
    exact Q'.eqv_trans _ _ _ a1 a2
  have e2 : (ε + -a).eqv (-a + ε) := Q'.add_comm_eqv ε (-a)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv e1)
    (Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv e2))

/-- A two-summand regrouping: `(a + sa) + (b + sb) ≃ (a + b) + (sa + sb)`.
This is exactly `Q'.add_swap_inner` with the middle pair swapped. -/
theorem add_regroup (a sa b sb : Q') :
    ((a + sa) + (b + sb)).eqv ((a + b) + (sa + sb)) :=
  add_swap_inner a sa b sb

/-- `2·(invSucc (2m+1) + invSucc (2n+1)) ≤ invSucc m + invSucc n`, the canonical
add-modulus collapse, as a `≤` (the doubled error bounded by the canonical
slack). -/
theorem add_slack_collapse (m n : Nat) :
    (Q'.invSucc (2 * m + 1) + Q'.invSucc (2 * n + 1))
      + (Q'.invSucc (2 * m + 1) + Q'.invSucc (2 * n + 1))
      ≤ Q'.invSucc m + Q'.invSucc n := by
  -- regroup to (invSucc(2m+1)+invSucc(2m+1)) + (invSucc(2n+1)+invSucc(2n+1)),
  -- then collapse each half via invSucc_double_eqv.
  have hre := add_swap_inner (Q'.invSucc (2 * m + 1)) (Q'.invSucc (2 * n + 1))
    (Q'.invSucc (2 * m + 1)) (Q'.invSucc (2 * n + 1))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hre) ?_
  -- now bound the two collapsed halves termwise.
  have h1 : (Q'.invSucc (2 * m + 1) + Q'.invSucc (2 * m + 1)) ≤ Q'.invSucc m :=
    Q'.le_of_eqv (invSucc_double_eqv m)
  have h2 : (Q'.invSucc (2 * n + 1) + Q'.invSucc (2 * n + 1)) ≤ Q'.invSucc n :=
    Q'.le_of_eqv (invSucc_double_eqv n)
  exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ h1)
    (Q'.add_le_add_left _ _ _ h2)

end Q'

namespace RegularCReal

/-! ## Priority 1: addition, negation, subtraction -/

/-- The doubled-index helper: regularity of a single regular real at the
add-reindexed points, in the additive shape `add` consumes. -/
private theorem dbl_reg (x : RegularCReal) (m n : Nat) :
    x.approx (2 * m + 1) ≤ x.approx (2 * n + 1)
      + (Q'.invSucc (2 * m + 1) + Q'.invSucc (2 * n + 1)) :=
  (x.regular (2 * m + 1) (2 * n + 1)).1

/-- **Addition**, with the canonical regularity PRESERVED by index doubling:
`(add x y).approx n := x.approx (2n+1) + y.approx (2n+1)`.  Each summand's
error `invSucc (2·+1)` is half the canonical slack, so the doubled total
collapses back to `invSucc m + invSucc n` (`Q'.add_slack_collapse`). -/
def add (x y : RegularCReal) : RegularCReal where
  approx n := x.approx (2 * n + 1) + y.approx (2 * n + 1)
  regular := by
    intro m n
    -- one-directional core, applied in both directions.
    have core : ∀ a b : RegularCReal,
        a.approx (2 * m + 1) + b.approx (2 * m + 1)
          ≤ (a.approx (2 * n + 1) + b.approx (2 * n + 1))
            + (Q'.invSucc m + Q'.invSucc n) := by
      intro a b
      have ha := dbl_reg a m n
      have hb := dbl_reg b m n
      -- sum the two: a_m + b_m ≤ (a_n + sx) + (b_n + sy)
      have hsum : a.approx (2 * m + 1) + b.approx (2 * m + 1)
          ≤ (a.approx (2 * n + 1)
              + (Q'.invSucc (2 * m + 1) + Q'.invSucc (2 * n + 1)))
            + (b.approx (2 * n + 1)
              + (Q'.invSucc (2 * m + 1) + Q'.invSucc (2 * n + 1))) :=
        Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ ha)
          (Q'.add_le_add_left _ _ _ hb)
      -- regroup RHS to (a_n + b_n) + (sx + sy)
      refine Q'.le_trans' _ _ _ hsum ?_
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.add_regroup (a.approx (2 * n + 1))
          (Q'.invSucc (2 * m + 1) + Q'.invSucc (2 * n + 1))
          (b.approx (2 * n + 1))
          (Q'.invSucc (2 * m + 1) + Q'.invSucc (2 * n + 1)))) ?_
      -- now collapse the slack (sx + sy) ≤ invSucc m + invSucc n
      exact Q'.add_le_add_left _ _ _ (Q'.add_slack_collapse m n)
    refine ⟨core x y, ?_⟩
    -- reverse direction: re-run the same chain with roles swapped, then
    -- reorder the swapped slack into `add_slack_collapse m n` shape.
    have ha := (x.regular (2 * n + 1) (2 * m + 1)).1
    have hb := (y.regular (2 * n + 1) (2 * m + 1)).1
    have hsum : x.approx (2 * n + 1) + y.approx (2 * n + 1)
        ≤ (x.approx (2 * m + 1)
            + (Q'.invSucc (2 * n + 1) + Q'.invSucc (2 * m + 1)))
          + (y.approx (2 * m + 1)
            + (Q'.invSucc (2 * n + 1) + Q'.invSucc (2 * m + 1))) :=
      Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ ha)
        (Q'.add_le_add_left _ _ _ hb)
    refine Q'.le_trans' _ _ _ hsum ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.add_regroup (x.approx (2 * m + 1))
        (Q'.invSucc (2 * n + 1) + Q'.invSucc (2 * m + 1))
        (y.approx (2 * m + 1))
        (Q'.invSucc (2 * n + 1) + Q'.invSucc (2 * m + 1)))) ?_
    refine Q'.add_le_add_left _ _ _ ?_
    -- reorder the swapped slack to the `add_slack_collapse m n` input shape.
    refine Q'.le_trans' _ _ _ ?_ (Q'.add_slack_collapse m n)
    -- (invSucc(2n+1)+invSucc(2m+1)) ≃ (invSucc(2m+1)+invSucc(2n+1)), congruent in both halves.
    have hcomm := Q'.add_comm_eqv (Q'.invSucc (2 * n + 1)) (Q'.invSucc (2 * m + 1))
    exact Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ hcomm)
      (Q'.add_eqv_congr_left _ _ _ hcomm))

@[simp] theorem add_approx (x y : RegularCReal) (n : Nat) :
    (add x y).approx n = x.approx (2 * n + 1) + y.approx (2 * n + 1) := rfl

/-- **Negation**: negate the sequence pointwise.  Regularity is inherited
directly (negation reverses each two-sided bound). -/
def neg (x : RegularCReal) : RegularCReal where
  approx n := -(x.approx n)
  regular := by
    intro m n
    obtain ⟨h1, h2⟩ := x.regular m n
    -- x_m ≤ x_n + s  ⟹  -x_n ≤ -x_m + s ; and symmetric.
    exact ⟨Q'.neg_le_neg_add' h2, Q'.neg_le_neg_add' h1⟩

@[simp] theorem neg_approx (x : RegularCReal) (n : Nat) :
    (neg x).approx n = -(x.approx n) := rfl

/-- **Subtraction**: `sub x y := add x (neg y)`. -/
def sub (x y : RegularCReal) : RegularCReal := add x (neg y)

@[simp] theorem sub_approx (x y : RegularCReal) (n : Nat) :
    (sub x y).approx n = x.approx (2 * n + 1) + (-(y.approx (2 * n + 1))) := rfl

/-! ### Equality glue: equivalence from pointwise `Q'.eqv` -/

/-- If every approximation of `x` is `Q'.eqv` to the corresponding one of `y`,
then `Equiv x y`.  The pointwise rational-equality of approximations gives the
two-sided bound with zero residual slack. -/
theorem Equiv_of_approx_eqv {x y : RegularCReal}
    (h : ∀ n : Nat, (x.approx n).eqv (y.approx n)) : Equiv x y := by
  intro n
  have hslack : (0 : Q') ≤ Q'.invSucc n + Q'.invSucc n :=
    Q'.zero_le_add _ _ (Q'.invSucc_nonneg n) (Q'.invSucc_nonneg n)
  refine ⟨?_, ?_⟩
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (h n))
      (Q'.add_le_self_of_nonneg (y.approx n) _ hslack)
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (h n))
      (Q'.add_le_self_of_nonneg (x.approx n) _ hslack)

/-! ### Priority 1 compatibility lemmas -/

/-- `add` commutes with the embedding (up to `Equiv`; in fact the approxes are
`Q'.eqv`): `ofQ' (p + q) ≈ add (ofQ' p) (ofQ' q)`. -/
theorem ofQ'_add (p q : Q') : Equiv (ofQ' (p + q)) (add (ofQ' p) (ofQ' q)) :=
  Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

/-- Addition is commutative up to `Equiv`. -/
theorem add_comm (x y : RegularCReal) : Equiv (add x y) (add y x) :=
  Equiv_of_approx_eqv (fun n => Q'.add_comm_eqv _ _)

/-- `invSucc m ≤ invSucc k` when `k ≤ m` (a larger index gives a smaller
tolerance). -/
private theorem invSucc_antitone {k m : Nat} (h : k ≤ m) :
    Q'.invSucc m ≤ Q'.invSucc k := by
  show (Q'.invSucc m).num * ((Q'.invSucc k).den : Int)
      ≤ (Q'.invSucc k).num * ((Q'.invSucc m).den : Int)
  rw [Q'.invSucc_num, Q'.invSucc_num, Q'.invSucc_den, Q'.invSucc_den]
  show (1 : Int) * ((k + 1 : Nat) : Int) ≤ (1 : Int) * ((m + 1 : Nat) : Int)
  rw [Int.one_mul, Int.one_mul]
  have : (k + 1 : Nat) ≤ (m + 1 : Nat) := by omega
  exact_mod_cast this

/-- `invSucc (2·(2n+1)+1) ≤ invSucc (2n+1)` (index `4n+3 ≥ 2n+1`). -/
private theorem invSucc_quad_le (n : Nat) :
    Q'.invSucc (2 * (2 * n + 1) + 1) ≤ Q'.invSucc (2 * n + 1) :=
  invSucc_antitone (by omega)

/-- The associativity slack collapse: the four reindexed errors at indices
`K = 2(2n+1)+1` and `2n+1` (two from `x`, two from `z`) total at most the
canonical `invSucc n + invSucc n`. -/
private theorem assoc_slack (n : Nat) :
    (Q'.invSucc (2 * (2 * n + 1) + 1) + Q'.invSucc (2 * n + 1))
      + (Q'.invSucc (2 * (2 * n + 1) + 1) + Q'.invSucc (2 * n + 1))
      ≤ Q'.invSucc n + Q'.invSucc n := by
  -- bound each invSucc(4n+3) by invSucc(2n+1), then collapse 2·(2·invSucc(2n+1)).
  have hq := invSucc_quad_le n
  -- termwise: (invSucc(4n+3)+invSucc(2n+1)) ≤ (invSucc(2n+1)+invSucc(2n+1))
  have hhalf : (Q'.invSucc (2 * (2 * n + 1) + 1) + Q'.invSucc (2 * n + 1))
      ≤ (Q'.invSucc (2 * n + 1) + Q'.invSucc (2 * n + 1)) :=
    Q'.add_le_add_right _ _ _ hq
  have hsum : (Q'.invSucc (2 * (2 * n + 1) + 1) + Q'.invSucc (2 * n + 1))
        + (Q'.invSucc (2 * (2 * n + 1) + 1) + Q'.invSucc (2 * n + 1))
      ≤ (Q'.invSucc (2 * n + 1) + Q'.invSucc (2 * n + 1))
        + (Q'.invSucc (2 * n + 1) + Q'.invSucc (2 * n + 1)) :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hhalf)
      (Q'.add_le_add_left _ _ _ hhalf)
  refine Q'.le_trans' _ _ _ hsum ?_
  -- (2·invSucc(2n+1)) + (2·invSucc(2n+1)) ≤ invSucc n + invSucc n
  have hc := Q'.le_of_eqv (Q'.invSucc_double_eqv n)
  exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hc)
    (Q'.add_le_add_left _ _ _ hc)

/-- The abstract associativity chaining step: from `a ≤ b + e1`, `c ≤ d + e2`,
and `e1 + e2 ≤ S`, conclude `(a + y) + c ≤ (b + (y + d)) + S`. -/
private theorem assoc_chain (a b y c d e1 e2 S : Q')
    (hx : a ≤ b + e1) (hz : c ≤ d + e2) (hS : e1 + e2 ≤ S) :
    (a + y) + c ≤ (b + (y + d)) + S := by
  -- (a+y)+c ≤ ((b+e1)+y)+(d+e2)
  have h1 : (a + y) + c ≤ ((b + e1) + y) + (d + e2) :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ (Q'.add_le_add_right _ _ _ hx))
      (Q'.add_le_add_left _ _ _ hz)
  -- ((b+e1)+y)+(d+e2) ≃ (b+(y+d)) + (e1+e2)
  have hre : (((b + e1) + y) + (d + e2)).eqv ((b + (y + d)) + (e1 + e2)) := by
    show (((b + e1) + y) + (d + e2)).num * (((b + (y + d)) + (e1 + e2)).den : Int)
        = ((b + (y + d)) + (e1 + e2)).num * ((((b + e1) + y) + (d + e2)).den : Int)
    simp only [Q'.add_num_cast, Q'.add_den_cast, Int.add_mul, Int.mul_add]
    ac_rfl
  refine Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv hre) ?_)
  exact Q'.add_le_add_left _ _ _ hS

/-- The mirror chaining step (left-associated source): from `a ≤ b + e1`,
`c ≤ d + e2`, `e1 + e2 ≤ S`, conclude `a + (y + c) ≤ (b + (y + d)) + S`. -/
private theorem assoc_chain' (a b y c d e1 e2 S : Q')
    (hx : a ≤ b + e1) (hz : c ≤ d + e2) (hS : e1 + e2 ≤ S) :
    a + (y + c) ≤ (b + (y + d)) + S := by
  have h1 : a + (y + c) ≤ (b + e1) + (y + (d + e2)) :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hx)
      (Q'.add_le_add_left _ _ _ (Q'.add_le_add_left _ _ _ hz))
  have hre : ((b + e1) + (y + (d + e2))).eqv ((b + (y + d)) + (e1 + e2)) := by
    show ((b + e1) + (y + (d + e2))).num * (((b + (y + d)) + (e1 + e2)).den : Int)
        = ((b + (y + d)) + (e1 + e2)).num * (((b + e1) + (y + (d + e2))).den : Int)
    simp only [Q'.add_num_cast, Q'.add_den_cast, Int.add_mul, Int.mul_add]
    ac_rfl
  refine Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv hre) ?_)
  exact Q'.add_le_add_left _ _ _ hS

/-- Addition is associative up to `Equiv`.  Both `(add (add x y) z)` and
`(add x (add y z))` reindex to nested doublings; the index mismatch (`x`, `z`
evaluated at `2(2n+1)+1` on one side, `2n+1` on the other) is absorbed by
regularity, and the four errors collapse to the canonical slack
(`assoc_slack`). -/
theorem add_assoc (x y z : RegularCReal) :
    Equiv (add (add x y) z) (add x (add y z)) := by
  refine (Equiv_iff_le_le _ _).mpr ⟨?_, ?_⟩
  · intro n
    show (x.approx (2 * (2 * n + 1) + 1) + y.approx (2 * (2 * n + 1) + 1))
          + z.approx (2 * n + 1)
        ≤ (x.approx (2 * n + 1)
            + (y.approx (2 * (2 * n + 1) + 1) + z.approx (2 * (2 * n + 1) + 1)))
          + (Q'.invSucc n + Q'.invSucc n)
    have hx := (x.regular (2 * (2 * n + 1) + 1) (2 * n + 1)).1
    have hz := (z.regular (2 * n + 1) (2 * (2 * n + 1) + 1)).1
    -- e1 = invSucc K + invSucc(2n+1), e2 = invSucc(2n+1) + invSucc K ; e1+e2 ≤ 2 invSucc n
    have hS : (Q'.invSucc (2 * (2 * n + 1) + 1) + Q'.invSucc (2 * n + 1))
        + (Q'.invSucc (2 * n + 1) + Q'.invSucc (2 * (2 * n + 1) + 1))
        ≤ Q'.invSucc n + Q'.invSucc n := by
      refine Q'.le_trans' _ _ _ ?_ (assoc_slack n)
      exact Q'.add_le_add_left _ _ _
        (Q'.le_of_eqv (Q'.add_comm_eqv (Q'.invSucc (2 * n + 1))
          (Q'.invSucc (2 * (2 * n + 1) + 1))))
    exact assoc_chain _ _ _ _ _ _ _ _ hx hz hS
  · intro n
    show (x.approx (2 * n + 1)
          + (y.approx (2 * (2 * n + 1) + 1) + z.approx (2 * (2 * n + 1) + 1)))
        ≤ ((x.approx (2 * (2 * n + 1) + 1) + y.approx (2 * (2 * n + 1) + 1))
            + z.approx (2 * n + 1))
          + (Q'.invSucc n + Q'.invSucc n)
    have hx := (x.regular (2 * n + 1) (2 * (2 * n + 1) + 1)).1
    have hz := (z.regular (2 * (2 * n + 1) + 1) (2 * n + 1)).1
    -- shape: x_{2n+1} + (y_K + z_K) ≤ ((x_K + y_K) + z_{2n+1}) + 2 invSucc n
    -- Match assoc_chain with a=x_{2n+1}, b=x_K, y=y_K, c=z_K, d=z_{2n+1}, but the
    -- target groups as (x_K + y_K) + z_{2n+1}; reassociate to x_K + (y_K + z_{2n+1}).
    have hS : (Q'.invSucc (2 * n + 1) + Q'.invSucc (2 * (2 * n + 1) + 1))
        + (Q'.invSucc (2 * (2 * n + 1) + 1) + Q'.invSucc (2 * n + 1))
        ≤ Q'.invSucc n + Q'.invSucc n := by
      refine Q'.le_trans' _ _ _ ?_ (assoc_slack n)
      exact Q'.add_le_add_right _ _ _
        (Q'.le_of_eqv (Q'.add_comm_eqv (Q'.invSucc (2 * n + 1))
          (Q'.invSucc (2 * (2 * n + 1) + 1))))
    -- Use assoc_chain to get x_{2n+1} + (y_K + z_K) ≤ (x_K + (y_K + z_{2n+1})) + 2 invSucc n,
    -- then reassociate the target.
    have hchain := assoc_chain' (x.approx (2 * n + 1)) (x.approx (2 * (2 * n + 1) + 1))
      (y.approx (2 * (2 * n + 1) + 1)) (z.approx (2 * (2 * n + 1) + 1))
      (z.approx (2 * n + 1)) _ _ _ hx hz hS
    -- hchain : x_{2n+1} + (y_K + z_K) ≤ (x_K + (y_K + z_{2n+1})) + (2 invSucc n)
    refine Q'.le_trans' _ _ _ hchain ?_
    -- reassociate x_K + (y_K + z_{2n+1}) → (x_K + y_K) + z_{2n+1}
    refine Q'.add_le_add_right _ _ _ ?_
    exact Q'.ge_of_eqv (Q'.add_assoc_eqv (x.approx (2 * (2 * n + 1) + 1))
      (y.approx (2 * (2 * n + 1) + 1)) (z.approx (2 * n + 1)))

/-- `2·invSucc (2n+1) ≤ invSucc n + invSucc n` (the reindexed slack is within
the canonical slack). -/
private theorem two_invSucc_succ_le (n : Nat) :
    Q'.invSucc (2 * n + 1) + Q'.invSucc (2 * n + 1) ≤ Q'.invSucc n + Q'.invSucc n := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.invSucc_double_eqv n)) ?_
  exact Q'.add_le_self_of_nonneg _ _ (Q'.invSucc_nonneg n)

/-- **`add` respects `Equiv` in both arguments.**  At the reindexed point
`2n+1` each `Equiv` bound is `invSucc n`, and the two halves sum to the
canonical `invSucc n + invSucc n`. -/
theorem add_congr {x x' y y' : RegularCReal}
    (hx : Equiv x x') (hy : Equiv y y') : Equiv (add x y) (add x' y') := by
  -- per-index two-sided; reuse a one-direction core.
  have core : ∀ {a a' b b' : RegularCReal},
      Equiv a a' → Equiv b b' → ∀ n : Nat,
      a.approx (2 * n + 1) + b.approx (2 * n + 1)
        ≤ (a'.approx (2 * n + 1) + b'.approx (2 * n + 1))
          + (Q'.invSucc n + Q'.invSucc n) := by
    intro a a' b b' ha hb n
    -- a_{2n+1} ≤ a'_{2n+1} + 2 invSucc(2n+1) ; similarly b.
    have ha1 := (ha (2 * n + 1)).1
    have hb1 := (hb (2 * n + 1)).1
    have hsum : a.approx (2 * n + 1) + b.approx (2 * n + 1)
        ≤ (a'.approx (2 * n + 1)
            + (Q'.invSucc (2 * n + 1) + Q'.invSucc (2 * n + 1)))
          + (b'.approx (2 * n + 1)
            + (Q'.invSucc (2 * n + 1) + Q'.invSucc (2 * n + 1))) :=
      Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ ha1)
        (Q'.add_le_add_left _ _ _ hb1)
    refine Q'.le_trans' _ _ _ hsum ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.add_regroup (a'.approx (2 * n + 1))
        (Q'.invSucc (2 * n + 1) + Q'.invSucc (2 * n + 1))
        (b'.approx (2 * n + 1))
        (Q'.invSucc (2 * n + 1) + Q'.invSucc (2 * n + 1)))) ?_
    refine Q'.add_le_add_left _ _ _ ?_
    -- (2 invSucc(2n+1)) + (2 invSucc(2n+1)) ≤ invSucc n + invSucc n
    exact Q'.add_slack_collapse n n
  intro n
  exact ⟨core hx hy n, core (Equiv.symm hx) (Equiv.symm hy) n⟩

/-- **Right-monotonicity of `add`.**  `x ≤ x' → add x y ≤ add x' y`. -/
theorem add_le_add_right {x x' : RegularCReal} (y : RegularCReal)
    (h : x ≤ x') : add x y ≤ add x' y := by
  intro n
  show x.approx (2 * n + 1) + y.approx (2 * n + 1)
      ≤ (x'.approx (2 * n + 1) + y.approx (2 * n + 1))
        + (Q'.invSucc n + Q'.invSucc n)
  -- x_{2n+1} ≤ x'_{2n+1} + 2 invSucc(2n+1)
  have hx := h (2 * n + 1)
  have hstep : x.approx (2 * n + 1) + y.approx (2 * n + 1)
      ≤ (x'.approx (2 * n + 1) + (Q'.invSucc (2 * n + 1) + Q'.invSucc (2 * n + 1)))
          + y.approx (2 * n + 1) :=
    Q'.add_le_add_right _ _ _ hx
  refine Q'.le_trans' _ _ _ hstep ?_
  -- regroup (x'_{2n+1} + s) + y_{2n+1} = (x'_{2n+1} + y_{2n+1}) + s
  have hre : ((x'.approx (2 * n + 1) + (Q'.invSucc (2 * n + 1) + Q'.invSucc (2 * n + 1)))
        + y.approx (2 * n + 1)).eqv
      ((x'.approx (2 * n + 1) + y.approx (2 * n + 1))
        + (Q'.invSucc (2 * n + 1) + Q'.invSucc (2 * n + 1))) := by
    show (_ + _ + _ : Q').num * (_ : Int) = (_ : Q').num * (_ : Int)
    simp only [Q'.add_num_cast, Q'.add_den_cast, Int.add_mul, Int.mul_add]
    ac_rfl
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hre) ?_
  exact Q'.add_le_add_left _ _ _ (two_invSucc_succ_le n)

/-- **Left-monotonicity of `add`.**  `y ≤ y' → add x y ≤ add x y'`. -/
theorem add_le_add_left (x : RegularCReal) {y y' : RegularCReal}
    (h : y ≤ y') : add x y ≤ add x y' := by
  -- add x y ≈ add y x ≤ add y' x ≈ add x y'
  refine le_congr_right (add_comm y' x) (le_congr_left (add_comm y x) ?_)
  exact add_le_add_right x h

/-- **Monotonicity of `add` in both arguments.** -/
theorem add_le_add {x x' y y' : RegularCReal}
    (hx : x ≤ x') (hy : y ≤ y') : add x y ≤ add x' y' :=
  le_trans (add_le_add_right y hx) (add_le_add_left x' hy)

/-- `add x czero ≈ x` (right unit). -/
theorem add_czero (x : RegularCReal) : Equiv (add x czero) x := by
  -- (add x czero).approx n = x_{2n+1} + 0 ; reduce to regularity x_{2n+1} ≈ x_n.
  refine (Equiv_iff_le_le _ _).mpr ⟨?_, ?_⟩
  · intro n
    show x.approx (2 * n + 1) + (0 : Q') ≤ x.approx n + (Q'.invSucc n + Q'.invSucc n)
    rw [Q'.add_zero' (x.approx (2 * n + 1))]
    -- x_{2n+1} ≤ x_n + (invSucc(2n+1)+invSucc n) ≤ x_n + (invSucc n + invSucc n)
    refine Q'.le_trans' _ _ _ (x.regular (2 * n + 1) n).1 ?_
    exact Q'.add_le_add_left _ _ _
      (Q'.add_le_add_right _ _ _ (invSucc_antitone (by omega)))
  · intro n
    show x.approx n ≤ (x.approx (2 * n + 1) + (0 : Q')) + (Q'.invSucc n + Q'.invSucc n)
    rw [Q'.add_zero' (x.approx (2 * n + 1))]
    -- x_n ≤ x_{2n+1} + (invSucc n + invSucc(2n+1)) ≤ x_{2n+1} + (invSucc n + invSucc n)
    refine Q'.le_trans' _ _ _ (x.regular n (2 * n + 1)).1 ?_
    exact Q'.add_le_add_left _ _ _
      (Q'.add_le_add_left _ _ _ (invSucc_antitone (by omega)))

/-- `add czero x ≈ x` (left unit). -/
theorem czero_add (x : RegularCReal) : Equiv (add czero x) x :=
  Equiv.trans (add_comm czero x) (add_czero x)

/-- `sub x x ≈ czero`: subtraction of a regular real from itself is zero. -/
theorem sub_self_eqv_zero (x : RegularCReal) : Equiv (sub x x) czero := by
  -- (sub x x).approx n = x_{2n+1} + (-(x_{2n+1})) ≈ 0 = czero.approx n.
  refine Equiv_of_approx_eqv (fun n => ?_)
  show (x.approx (2 * n + 1) + (-(x.approx (2 * n + 1)))).eqv ((0 : Q'))
  exact Q'.add_neg_self_eqv (x.approx (2 * n + 1))

/-! ## Priority 2: scalar multiplication by a rational

`qmul q x` scales the sequence by `q`, reindexing by a `Nat` bound on `|q|`
so the canonical regularity is preserved. -/

/-- `q ≤ p + ε` from `q + (-p) ≤ ε` (the additive form of `sub_le_of_le_add`). -/
private theorem le_add_of_sub_le {p q ε : Q'} (h : q + -p ≤ ε) : q ≤ p + ε := by
  have hstep := Q'.add_le_add_right (q + -p) ε p h
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv ?_))
  · refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv q (-p) p) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left q (-p + p) 0
      (Q'.neg_add_self_eqv p)) ?_
    rw [Q'.add_zero' q]; exact Q'.eqv_refl q
  · exact Q'.add_comm_eqv ε p

/-- The single scaling step: from a two-sided `|a − b| ≤ s` (`s ≥ 0`),
`q·a ≤ q·b + |q|·s` for ANY `q`.  Built from the sign-cased product bound
`mul_le_of_bounds` applied to `u = q`, `v = a + (−b)`. -/
private theorem qmul_reg_step (q a b s : Q') (hs : (0 : Q') ≤ s)
    (h1 : a ≤ b + s) (h2 : b ≤ a + s) :
    q * a ≤ q * b + Q'.abs q * s := by
  -- v = a + (-b) satisfies -s ≤ v ≤ s.
  have hv2 : a + -b ≤ s := Q'.sub_le_of_le_add h1
  have hv1 : -s ≤ a + -b := by
    -- from b ≤ a + s : b + -a ≤ s ⟹ -(a + -b) ≤ s ⟹ -s ≤ a + -b
    have hb : b + -a ≤ s := Q'.sub_le_of_le_add h2
    -- b + -a  ≃  -(a + -b)
    have he : (b + -a).eqv (-(a + -b)) := by
      refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.neg_add_eqv a (-b)))
      refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv b (-a)) ?_
      exact Q'.add_eqv_congr_left (-a) b (-(-b)) (Q'.eqv_symm (Q'.neg_neg_eqv b))
    have hneg : -(a + -b) ≤ s := Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hb
    -- -(a+-b) ≤ s ⟹ -s ≤ a + -b
    have := Q'.neg_le_neg hneg  -- -s ≤ -(-(a+-b))
    exact Q'.le_trans' _ _ _ this (Q'.le_of_eqv (Q'.neg_neg_eqv (a + -b)))
  -- product bound: q·(a + -b) ≤ |q|·s
  have habs1 : -(Q'.abs q) ≤ q :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg (Q'.neg_le_abs q)) (Q'.le_of_eqv (Q'.neg_neg_eqv q))
  have hprod : q * (a + -b) ≤ Q'.abs q * s :=
    Q'.mul_le_of_bounds (Q'.abs_nonneg q) hs habs1 (Q'.le_abs_self q) hv1 hv2
  -- q·(a + -b) ≃ q·a + -(q·b)
  have he2 : (q * (a + -b)).eqv (q * a + -(q * b)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv q a (-b))
      (Q'.add_eqv_congr_left (q * a) (q * -b) (-(q * b)) (Q'.mul_neg_eqv q b))
  have hsub : (q * a + -(q * b)) ≤ Q'.abs q * s :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv he2) hprod
  exact le_add_of_sub_le hsub

/-- A `Nat` bound on `|q|`: `qBound q = |q|.num.toNat + 1`, satisfying
`|q| ≤ ofNat (qBound q)` and `qBound q ≥ 1`. -/
def qBound (q : Q') : Nat := (Q'.abs q).num.toNat + 1

/-- `|q| ≤ ofNat (qBound q)`. -/
theorem abs_le_ofNat_qBound (q : Q') : Q'.abs q ≤ Q'.ofNat (qBound q) := by
  -- |q| ≤ ofNat |q|.num.toNat ≤ ofNat (|q|.num.toNat + 1).
  refine Q'.le_trans' _ _ _ (RatNat.le_ofNat_toNat (Q'.abs q) (Q'.abs_nonneg q)) ?_
  exact CReal.ofNat_le_ofNat (Nat.le_succ _)

/-- The reindexing for `qmul`: `I q n = qBound q · (n+1) − 1`, so
`I q n + 1 = qBound q · (n+1)`. -/
def qIdx (q : Q') (n : Nat) : Nat := qBound q * (n + 1) - 1

theorem qIdx_succ (q : Q') (n : Nat) : qIdx q n + 1 = qBound q * (n + 1) := by
  unfold qIdx
  have h1 : 1 ≤ qBound q * (n + 1) := by
    have : 1 ≤ qBound q := Nat.le_add_left 1 _
    exact Nat.le_trans this (Nat.le_mul_of_pos_right _ (Nat.succ_pos n))
  omega

/-- The key index identity for `qmul` distributivity: the LHS reindexing
(`2·(qIdx q n)+1`) and the RHS reindexing (`qIdx q (2n+1)`) coincide. -/
theorem two_qIdx_succ (q : Q') (n : Nat) :
    2 * qIdx q n + 1 = qIdx q (2 * n + 1) := by
  have h1 := qIdx_succ q n
  have h2 := qIdx_succ q (2 * n + 1)
  -- qBound q * (2*n+1+1) = 2 * (qBound q * (n+1))
  have hprod : qBound q * (2 * n + 1 + 1) = 2 * (qBound q * (n + 1)) := by
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) from by omega, Nat.mul_comm (qBound q) (2 * (n + 1)),
        Nat.mul_assoc, Nat.mul_comm (n + 1) (qBound q)]
  omega

/-- `n ≤ qIdx q n` (since `qBound q ≥ 1`). -/
theorem le_qIdx (q : Q') (n : Nat) : n ≤ qIdx q n := by
  have h := qIdx_succ q n
  have hb : 1 ≤ qBound q := Nat.le_add_left 1 _
  have : (n + 1) ≤ qBound q * (n + 1) := Nat.le_mul_of_pos_left _ hb
  omega

/-- `ofNat (qBound q) · invSucc (qIdx q n) ≃ invSucc n`: scaling the reindexed
tolerance by the `Nat` bound returns the canonical tolerance exactly. -/
theorem ofNat_qBound_mul_invSucc_eqv (q : Q') (n : Nat) :
    (Q'.ofNat (qBound q) * Q'.invSucc (qIdx q n)).eqv (Q'.invSucc n) := by
  show (Q'.ofNat (qBound q) * Q'.invSucc (qIdx q n)).num * ((Q'.invSucc n).den : Int)
      = (Q'.invSucc n).num * ((Q'.ofNat (qBound q) * Q'.invSucc (qIdx q n)).den : Int)
  rw [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.invSucc_num, Q'.invSucc_num,
      Q'.invSucc_den, Q'.invSucc_den, Q'.ofNat_den_cast]
  -- LHS num = qBound·1 ; LHS den part = 1·(qIdx+1) ; RHS = 1·(qBound·(n+1))
  show ((qBound q : Int) * (1 : Int)) * ((n + 1 : Nat) : Int)
      = (1 : Int) * ((1 : Int) * (((qIdx q n) + 1 : Nat) : Int))
  rw [qIdx_succ q n]
  show ((qBound q : Int) * (1 : Int)) * ((n + 1 : Nat) : Int)
      = (1 : Int) * ((1 : Int) * ((qBound q * (n + 1) : Nat) : Int))
  rw [Int.mul_one, Int.one_mul, Int.one_mul, Int.natCast_mul]

end RegularCReal

namespace RegularCReal

/-- **Scalar multiplication by a rational.**  `qmul q x` scales the sequence
by `q`, evaluating `x` at the reindexed point `qIdx q n` (driven by a `Nat`
bound on `|q|`) so the canonical regularity is preserved: the `|q|`-scaled
error `|q|·(invSucc (I m) + invSucc (I n))` is `≤ ofNat (qBound q)·(…)`, which
collapses to `invSucc m + invSucc n`. -/
def qmul (q : Q') (x : RegularCReal) : RegularCReal where
  approx n := q * x.approx (qIdx q n)
  regular := by
    intro m n
    -- the scaling-step slack at the reindexed points.
    have hslack_nn : (0 : Q') ≤ Q'.invSucc (qIdx q m) + Q'.invSucc (qIdx q n) :=
      Q'.zero_le_add _ _ (Q'.invSucc_nonneg _) (Q'.invSucc_nonneg _)
    obtain ⟨hr1, hr2⟩ := x.regular (qIdx q m) (qIdx q n)
    -- |q|·(slack) ≤ ofNat qBound · slack ≤ invSucc m + invSucc n
    have hbound : Q'.abs q
          * (Q'.invSucc (qIdx q m) + Q'.invSucc (qIdx q n))
        ≤ Q'.invSucc m + Q'.invSucc n := by
      -- |q|·s ≤ ofNat qBound · s
      have h1 : Q'.abs q * (Q'.invSucc (qIdx q m) + Q'.invSucc (qIdx q n))
          ≤ Q'.ofNat (qBound q) * (Q'.invSucc (qIdx q m) + Q'.invSucc (qIdx q n)) :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ (abs_le_ofNat_qBound q) hslack_nn
      refine Q'.le_trans' _ _ _ h1 ?_
      -- ofNat qBound · (a + b) ≃ ofNat qBound · a + ofNat qBound · b ; each ≤ invSucc.
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _)) ?_
      have ha := Q'.le_of_eqv (ofNat_qBound_mul_invSucc_eqv q m)
      have hb := Q'.le_of_eqv (ofNat_qBound_mul_invSucc_eqv q n)
      exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ ha)
        (Q'.add_le_add_left _ _ _ hb)
    refine ⟨?_, ?_⟩
    · -- q·x_{Im} ≤ q·x_{In} + |q|·slack ≤ q·x_{In} + (invSucc m + invSucc n)
      refine Q'.le_trans' _ _ _
        (qmul_reg_step q (x.approx (qIdx q m)) (x.approx (qIdx q n)) _ hslack_nn hr1 hr2) ?_
      exact Q'.add_le_add_left _ _ _ hbound
    · refine Q'.le_trans' _ _ _
        (qmul_reg_step q (x.approx (qIdx q n)) (x.approx (qIdx q m)) _ hslack_nn hr2 hr1) ?_
      exact Q'.add_le_add_left _ _ _ hbound

@[simp] theorem qmul_approx (q : Q') (x : RegularCReal) (n : Nat) :
    (qmul q x).approx n = q * x.approx (qIdx q n) := rfl

/-! ### Priority 2 compatibility lemmas -/

/-- `q · r` (rational product) embeds as `qmul q (ofQ' r)` (the approxes are
both `q * r`). -/
theorem ofQ'_qmul (q r : Q') : Equiv (ofQ' (q * r)) (qmul q (ofQ' r)) :=
  Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

/-- `q · 0 ≃ 0` in `Q'`. -/
private theorem q_mul_zero_eqv (q : Q') : (q * (0 : Q')).eqv (0 : Q') := by
  show (q * (0 : Q')).num * ((0 : Q').den : Int) = ((0 : Q').num) * ((q * (0 : Q')).den : Int)
  rw [Q'.mul_num_cast]
  show (q.num * (0 : Int)) * (1 : Int) = (0 : Int) * ((q * (0 : Q')).den : Int)
  rw [Int.mul_zero, Int.zero_mul, Int.zero_mul]

/-- `qmul q czero ≃ czero`. -/
theorem qmul_czero (q : Q') : Equiv (qmul q czero) czero :=
  Equiv_of_approx_eqv (fun _ => q_mul_zero_eqv q)

/-- **Scaling by `1` is the identity up to `Equiv`.**  `qmul 1 x ≈ x`: the
reindexed point is `x.approx (qIdx 1 n)` scaled by `1`, and regularity
identifies it with `x.approx n`. -/
theorem one_qmul (x : RegularCReal) : Equiv (qmul (1 : Q') x) x := by
  refine (Equiv_iff_le_le _ _).mpr ⟨?_, ?_⟩
  · intro n
    show (1 : Q') * x.approx (qIdx (1 : Q') n)
        ≤ x.approx n + (Q'.invSucc n + Q'.invSucc n)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) ?_
    -- x_{qIdx 1 n} ≤ x_n + (invSucc(qIdx 1 n) + invSucc n) ≤ x_n + 2 invSucc n
    refine Q'.le_trans' _ _ _ (x.regular (qIdx (1 : Q') n) n).1 ?_
    refine Q'.add_le_add_left _ _ _ (Q'.add_le_add_right _ _ _ ?_)
    exact invSucc_antitone (le_qIdx (1 : Q') n)
  · intro n
    show x.approx n
        ≤ (1 : Q') * x.approx (qIdx (1 : Q') n) + (Q'.invSucc n + Q'.invSucc n)
    refine Q'.le_trans' _ _ _ (x.regular n (qIdx (1 : Q') n)).1 ?_
    refine Q'.le_trans' _ _ _ ?_
      (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _)))
    refine Q'.add_le_add_left _ _ _ (Q'.add_le_add_left _ _ _ ?_)
    exact invSucc_antitone (le_qIdx (1 : Q') n)

/-- `qmul 1 x ≈ x` (alias matching the `*_one` naming). -/
theorem qmul_one (x : RegularCReal) : Equiv (qmul (1 : Q') x) x := one_qmul x

/-- **`qmul` distributes over `add`.**  `qmul q (add x y) ≈ add (qmul q x) (qmul q y)`.
Both reindexings collapse to the SAME point (`two_qIdx_succ`), so the only
residual is the rational distributivity `q·(a+b) ≃ q·a + q·b`. -/
theorem qmul_add (q : Q') (x y : RegularCReal) :
    Equiv (qmul q (add x y)) (add (qmul q x) (qmul q y)) := by
  refine Equiv_of_approx_eqv (fun n => ?_)
  -- LHS_n = q * (x_{2·qIdx q n+1} + y_{2·qIdx q n+1})
  -- RHS_n = q*x_{qIdx q (2n+1)} + q*y_{qIdx q (2n+1)}
  show (q * (x.approx (2 * qIdx q n + 1) + y.approx (2 * qIdx q n + 1))).eqv
      (q * x.approx (qIdx q (2 * n + 1)) + q * y.approx (qIdx q (2 * n + 1)))
  rw [two_qIdx_succ q n]
  exact Q'.mul_add_eqv q (x.approx (qIdx q (2 * n + 1))) (y.approx (qIdx q (2 * n + 1)))

/-- **Right-monotonicity of `qmul` for `0 ≤ q`.**  `x ≤ x' → qmul q x ≤ qmul q x'`. -/
theorem qmul_le {q : Q'} (hq : (0 : Q') ≤ q) {x x' : RegularCReal}
    (h : x ≤ x') : qmul q x ≤ qmul q x' := by
  intro n
  show q * x.approx (qIdx q n)
      ≤ q * x'.approx (qIdx q n) + (Q'.invSucc n + Q'.invSucc n)
  -- x_I ≤ x'_I + 2 invSucc I ; scale by q ≥ 0.
  have hxI := h (qIdx q n)
  have hstep : q * x.approx (qIdx q n)
      ≤ q * (x'.approx (qIdx q n) + (Q'.invSucc (qIdx q n) + Q'.invSucc (qIdx q n))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hxI hq
  refine Q'.le_trans' _ _ _ hstep ?_
  -- q·(x'_I + 2 invSucc I) ≃ q·x'_I + q·(2 invSucc I) ; bound the slack.
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _)) ?_
  refine Q'.add_le_add_left _ _ _ ?_
  -- q·(invSucc I + invSucc I) ≤ invSucc n + invSucc n
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv q _ _)) ?_
  -- each q·invSucc I ≤ ofNat qBound · invSucc I ≃ invSucc n
  have hone : q * Q'.invSucc (qIdx q n) ≤ Q'.invSucc n := by
    refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv (ofNat_qBound_mul_invSucc_eqv q n))
    -- q ≤ ofNat qBound (for q ≥ 0, |q| = q)
    have hqabs : q ≤ Q'.ofNat (qBound q) :=
      Q'.le_trans' _ _ _ (Q'.le_abs_self q) (abs_le_ofNat_qBound q)
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hqabs (Q'.invSucc_nonneg _)
  exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hone)
    (Q'.add_le_add_left _ _ _ hone)

/-! ## Priority 3: completeness — the modulus-Cauchy diagonal limit

A `RegularCReal` sequence with a `Type`-level outer Cauchy modulus has a
diagonal limit which is itself a `RegularCReal` with the CANONICAL modulus.
The intrinsic regularity field removes the need for an inner modulus (which
the merely-Cauchy `CReal` completeness had to carry). -/

/-- A modulus-Cauchy datum for a `RegularCReal` sequence `s`: an outer
modulus `M` (`Type`-level data) with the two-sided uniform bound and the
antitonicity needed for the diagonal to converge. -/
structure ModCauchy (s : Nat → RegularCReal) where
  /-- Outer Cauchy modulus, `Type`-level data. -/
  M : Q' → Nat
  /-- Two-sided outer bound: for `i, j ≥ M ε`, every approx index is within `ε`. -/
  bound : ∀ ε : Q', (0 : Q') < ε → ∀ i j : Nat, M ε ≤ i → M ε ≤ j →
    ∀ k : Nat, (s i).approx k ≤ (s j).approx k + ε ∧ (s j).approx k ≤ (s i).approx k + ε
  /-- The outer modulus is antitone: a smaller tolerance needs a later stage. -/
  Mmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → M ε ≤ M δ

/-- Running-max of `M (invSucc 1), …, M (invSucc (2k+1))` — monotone, dominating
each `M (invSucc (2j+1))` for `j ≤ k`. -/
def Mhat (s : Nat → RegularCReal) (c : ModCauchy s) : Nat → Nat
  | 0 => c.M (Q'.invSucc (2 * 0 + 1))
  | k + 1 => max (Mhat s c k) (c.M (Q'.invSucc (2 * (k + 1) + 1)))

theorem Mhat_mono_succ (s : Nat → RegularCReal) (c : ModCauchy s) (k : Nat) :
    Mhat s c k ≤ Mhat s c (k + 1) := Nat.le_max_left _ _

theorem Mhat_mono (s : Nat → RegularCReal) (c : ModCauchy s) {a b : Nat} (h : a ≤ b) :
    Mhat s c a ≤ Mhat s c b := by
  induction b with
  | zero => exact Nat.le_of_eq (by cases Nat.le_zero.mp h; rfl)
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · exact Nat.le_trans (ih (Nat.lt_succ_iff.mp hlt)) (Mhat_mono_succ s c b)
    · exact Nat.le_of_eq (by cases Nat.le_antisymm h hge; rfl)

/-- `c.M (invSucc (2k+1)) ≤ Mhat s c k`. -/
theorem M_le_Mhat (s : Nat → RegularCReal) (c : ModCauchy s) (k : Nat) :
    c.M (Q'.invSucc (2 * k + 1)) ≤ Mhat s c k := by
  cases k with
  | zero => exact Nat.le_refl _
  | succ k => exact Nat.le_max_right _ _

/-- The shifted diagonal `D k = (s (Mhat k)).approx (2k+1)`. -/
def diagSeq (s : Nat → RegularCReal) (c : ModCauchy s) (k : Nat) : Q' :=
  (s (Mhat s c k)).approx (2 * k + 1)

/-- The directed canonical regularity of the diagonal: for `a ≤ b`,
`D a ≤ D b + (invSucc a + invSucc b)` two-sided.  Chains the OUTER bound at
scale `invSucc (2a+1)` (terms `Mhat a, Mhat b ≥ M (invSucc (2a+1))`) and the
INTRINSIC regularity of `s (Mhat b)` between approx indices `2a+1, 2b+1`; the
`2·invSucc (2a+1)` collapses to `invSucc a` and `invSucc (2b+1) ≤ invSucc b`. -/
theorem diagSeq_directed (s : Nat → RegularCReal) (c : ModCauchy s)
    {a b : Nat} (hab : a ≤ b) :
    diagSeq s c a ≤ diagSeq s c b + (Q'.invSucc a + Q'.invSucc b) ∧
    diagSeq s c b ≤ diagSeq s c a + (Q'.invSucc a + Q'.invSucc b) := by
  have hpos : (0 : Q') < Q'.invSucc (2 * a + 1) := Q'.invSucc_pos _
  have hMa : c.M (Q'.invSucc (2 * a + 1)) ≤ Mhat s c a := M_le_Mhat s c a
  have hMb : c.M (Q'.invSucc (2 * a + 1)) ≤ Mhat s c b :=
    Nat.le_trans hMa (Mhat_mono s c hab)
  -- OUTER bounds comparing s (Mhat a) and s (Mhat b) at approx index 2a+1.
  obtain ⟨hO1, hO2⟩ := c.bound (Q'.invSucc (2 * a + 1)) hpos
    (Mhat s c a) (Mhat s c b) hMa hMb (2 * a + 1)
  -- INTRINSIC regularity of s (Mhat b) between approx indices 2a+1 and 2b+1.
  obtain ⟨hI1, hI2⟩ := (s (Mhat s c b)).regular (2 * a + 1) (2 * b + 1)
  -- slack collapse: invSucc(2a+1) + (invSucc(2a+1) + invSucc(2b+1)) ≤ invSucc a + invSucc b
  have hcollapse : ∀ w : Q',
      (w + Q'.invSucc (2 * a + 1)) + (Q'.invSucc (2 * a + 1) + Q'.invSucc (2 * b + 1))
        ≤ w + (Q'.invSucc a + Q'.invSucc b) := by
    intro w
    -- regroup (w + s1) + (s1 + s2) ≃ w + ((s1+s1) + s2) ; bound (s1+s1) ≤ invSucc a, s2 ≤ invSucc b.
    have hre : ((w + Q'.invSucc (2 * a + 1))
          + (Q'.invSucc (2 * a + 1) + Q'.invSucc (2 * b + 1))).eqv
        (w + ((Q'.invSucc (2 * a + 1) + Q'.invSucc (2 * a + 1)) + Q'.invSucc (2 * b + 1))) := by
      show ((w + Q'.invSucc (2 * a + 1))
            + (Q'.invSucc (2 * a + 1) + Q'.invSucc (2 * b + 1))).num * (_ : Int)
          = (w + ((Q'.invSucc (2 * a + 1) + Q'.invSucc (2 * a + 1))
              + Q'.invSucc (2 * b + 1))).num * (_ : Int)
      simp only [Q'.add_num_cast, Q'.add_den_cast, Int.add_mul, Int.mul_add]
      ac_rfl
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hre) ?_
    refine Q'.add_le_add_left _ _ _ ?_
    -- (s1+s1) + s2 ≤ invSucc a + invSucc b
    have h1 : Q'.invSucc (2 * a + 1) + Q'.invSucc (2 * a + 1) ≤ Q'.invSucc a :=
      Q'.le_of_eqv (Q'.invSucc_double_eqv a)
    have h2 : Q'.invSucc (2 * b + 1) ≤ Q'.invSucc b := invSucc_antitone (by omega)
    exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ h1)
      (Q'.add_le_add_left _ _ _ h2)
  refine ⟨?_, ?_⟩
  · -- D a = (s Mhat a)_{2a+1} ≤ (s Mhat b)_{2a+1} + s1 ≤ ((s Mhat b)_{2b+1} + (s1+s2)) + s1
    show (s (Mhat s c a)).approx (2 * a + 1)
        ≤ (s (Mhat s c b)).approx (2 * b + 1) + (Q'.invSucc a + Q'.invSucc b)
    have hch : (s (Mhat s c a)).approx (2 * a + 1)
        ≤ ((s (Mhat s c b)).approx (2 * b + 1)
            + (Q'.invSucc (2 * a + 1) + Q'.invSucc (2 * b + 1)))
          + Q'.invSucc (2 * a + 1) :=
      Q'.le_trans' _ _ _ hO1 (Q'.add_le_add_right _ _ _ hI1)
    -- reorder to (D b + s1) + (s1 + s2) and collapse
    refine Q'.le_trans' _ _ _ hch ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (hcollapse ((s (Mhat s c b)).approx (2 * b + 1)))
    -- ((Db + (s1+s2)) + s1) ≃ ((Db + s1) + (s1 + s2))
    show (((s (Mhat s c b)).approx (2 * b + 1)
          + (Q'.invSucc (2 * a + 1) + Q'.invSucc (2 * b + 1))) + Q'.invSucc (2 * a + 1)).num
            * (_ : Int)
        = (((s (Mhat s c b)).approx (2 * b + 1) + Q'.invSucc (2 * a + 1))
            + (Q'.invSucc (2 * a + 1) + Q'.invSucc (2 * b + 1))).num * (_ : Int)
    simp only [Q'.add_num_cast, Q'.add_den_cast, Int.add_mul, Int.mul_add]
    ac_rfl
  · -- D b = (s Mhat b)_{2b+1} ≤ (s Mhat b)_{2a+1} + (s1+s2) ≤ ((s Mhat a)_{2a+1} + s1) + (s1+s2)
    show (s (Mhat s c b)).approx (2 * b + 1)
        ≤ (s (Mhat s c a)).approx (2 * a + 1) + (Q'.invSucc a + Q'.invSucc b)
    have hch : (s (Mhat s c b)).approx (2 * b + 1)
        ≤ ((s (Mhat s c a)).approx (2 * a + 1) + Q'.invSucc (2 * a + 1))
          + (Q'.invSucc (2 * a + 1) + Q'.invSucc (2 * b + 1)) :=
      Q'.le_trans' _ _ _ hI2 (Q'.add_le_add_right _ _ _ hO2)
    exact Q'.le_trans' _ _ _ hch (hcollapse ((s (Mhat s c a)).approx (2 * a + 1)))

/-- **The completeness limit.**  The shifted diagonal of a modulus-Cauchy
`RegularCReal` sequence is itself a `RegularCReal` with the canonical
modulus. -/
def completeLimit (s : Nat → RegularCReal) (c : ModCauchy s) : RegularCReal where
  approx k := diagSeq s c k
  regular := by
    intro m n
    rcases Nat.le_total m n with hmn | hnm
    · obtain ⟨h1, h2⟩ := diagSeq_directed s c hmn
      exact ⟨h1, h2⟩
    · obtain ⟨h1, h2⟩ := diagSeq_directed s c hnm
      -- swap: directed gives bounds with (invSucc n + invSucc m); commute slack.
      refine ⟨?_, ?_⟩
      · refine Q'.le_trans' _ _ _ h2 (Q'.add_le_add_left _ _ _ ?_)
        exact Q'.le_of_eqv (Q'.add_comm_eqv (Q'.invSucc n) (Q'.invSucc m))
      · refine Q'.le_trans' _ _ _ h1 (Q'.add_le_add_left _ _ _ ?_)
        exact Q'.le_of_eqv (Q'.add_comm_eqv (Q'.invSucc n) (Q'.invSucc m))

@[simp] theorem completeLimit_approx (s : Nat → RegularCReal) (c : ModCauchy s) (k : Nat) :
    (completeLimit s c).approx k = (s (Mhat s c k)).approx (2 * k + 1) := rfl

/-- Convergence of a `RegularCReal` sequence to a limit `L`: for every
tolerance `ε > 0`, an eventual term-stage past which every term is two-sided
`ε`-close to `L` at every late approximation index.  (Mirrors the `CReal`
`ConvergesTo` shape, on the regular reals.) -/
def ConvergesTo (s : Nat → RegularCReal) (L : RegularCReal) : Prop :=
  ∀ ε : Q', (0 : Q') < ε → ∃ Nstage : Nat, ∀ N : Nat, Nstage ≤ N →
    ∃ Napx : Nat, ∀ n : Nat, Napx ≤ n →
      (s N).approx n ≤ L.approx n + ε ∧ L.approx n ≤ (s N).approx n + ε

/-- **The diagonal limit is the limit of `s`.**  `ConvergesTo s (completeLimit s c)`.
At scale `ε`: the term-stage is `c.M ε`.  For any `N ≥ c.M ε` and any approx
index `n` so large that `Mhat n ≥ M ε` and the two reindexing tolerances are
absorbed, the OUTER bound compares `s N` and `s (Mhat n)`. -/
theorem convergesTo_completeLimit (s : Nat → RegularCReal) (c : ModCauchy s) :
    ConvergesTo s (completeLimit s c) := by
  intro ε hε
  -- scales: q2 = ½ε (outer), q4 = ½q2 (per-index reindexing slack).
  have hq2 : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  have hq4 : (0 : Q') < HalfPow.half * (HalfPow.half * ε) :=
    ExpNeg.half_mul_pos _ hq2
  refine ⟨c.M (HalfPow.half * ε), fun N hN =>
    ⟨max (HalfPow.half * (HalfPow.half * ε)).den (HalfPow.half * ε).den, fun n hn => ?_⟩⟩
  -- index facts
  have hn4 : (HalfPow.half * (HalfPow.half * ε)).den ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : (HalfPow.half * ε).den ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  -- invSucc n ≤ q4
  have hinvn4 : Q'.invSucc n ≤ HalfPow.half * (HalfPow.half * ε) :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hn4) (HalfPow.invSucc_den_le _ hq4)
  -- invSucc (2n+1) ≤ q2 (since 2n+1 ≥ n ≥ q2.den)
  have hinv2n : Q'.invSucc (2 * n + 1) ≤ HalfPow.half * ε :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le (by omega))
      (HalfPow.invSucc_den_le _ hq2)
  have hinv2npos : (0 : Q') < Q'.invSucc (2 * n + 1) := Q'.invSucc_pos _
  -- M (½ε) ≤ M (invSucc (2n+1)) ≤ Mhat n
  have hMen : c.M (HalfPow.half * ε) ≤ Mhat s c n :=
    Nat.le_trans (c.Mmono (HalfPow.half * ε) (Q'.invSucc (2 * n + 1)) hinv2npos hinv2n)
      (M_le_Mhat s c n)
  -- OUTER bound: s N vs s (Mhat n) at approx index n, scale ½ε.
  obtain ⟨hO1, hO2⟩ := c.bound (HalfPow.half * ε) hq2 N (Mhat s c n) hN hMen n
  -- INTRINSIC regularity of s (Mhat n) between approx indices n and 2n+1.
  obtain ⟨hI1, hI2⟩ := (s (Mhat s c n)).regular n (2 * n + 1)
  -- L.approx n = (s (Mhat n)).approx (2n+1)
  -- collapse: (invSucc n + invSucc (2n+1)) + ½ε ≤ ε  and  ½ε + (invSucc n + invSucc(2n+1)) ≤ ε.
  have htail : Q'.invSucc n + Q'.invSucc (2 * n + 1) ≤ HalfPow.half * ε := by
    -- ≤ invSucc n + invSucc n ≤ q4 + q4 ≃ ½ε
    have hstep : Q'.invSucc n + Q'.invSucc (2 * n + 1) ≤ Q'.invSucc n + Q'.invSucc n :=
      Q'.add_le_add_left _ _ _ (invSucc_antitone (by omega))
    refine Q'.le_trans' _ _ _ hstep ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hinvn4)
        (Q'.add_le_add_left _ _ _ hinvn4)) ?_
    exact Q'.le_of_eqv (ExpNeg.two_halves (HalfPow.half * ε))
  -- two-sided assembly
  refine ⟨?_, ?_⟩
  · -- (s N)_n ≤ L_n + ε
    show (s N).approx n
        ≤ (s (Mhat s c n)).approx (2 * n + 1) + ε
    -- (s N)_n ≤ (s Mhat_n)_n + ½ε ≤ ((s Mhat_n)_{2n+1} + (invSucc n + invSucc(2n+1))) + ½ε
    have hch : (s N).approx n
        ≤ ((s (Mhat s c n)).approx (2 * n + 1)
            + (Q'.invSucc n + Q'.invSucc (2 * n + 1))) + HalfPow.half * ε :=
      Q'.le_trans' _ _ _ hO1 (Q'.add_le_add_right _ _ _ hI1)
    refine Q'.le_trans' _ _ _ hch ?_
    -- ((Db + tail) + ½ε) ≤ Db + ε
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_assoc_eqv _ _ _)) ?_
    refine Q'.add_le_add_left _ _ _ ?_
    -- tail + ½ε ≤ ε
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ htail) ?_
    refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv (ExpNeg.two_halves ε))
    exact Q'.le_refl' _
  · -- L_n ≤ (s N)_n + ε
    show (s (Mhat s c n)).approx (2 * n + 1)
        ≤ (s N).approx n + ε
    -- (s Mhat_n)_{2n+1} ≤ (s Mhat_n)_n + (invSucc n + invSucc(2n+1)) ≤ ((s N)_n + ½ε) + tail
    have hch : (s (Mhat s c n)).approx (2 * n + 1)
        ≤ ((s N).approx n + HalfPow.half * ε)
          + (Q'.invSucc n + Q'.invSucc (2 * n + 1)) :=
      Q'.le_trans' _ _ _ hI2 (Q'.add_le_add_right _ _ _ hO2)
    refine Q'.le_trans' _ _ _ hch ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_assoc_eqv _ _ _)) ?_
    refine Q'.add_le_add_left _ _ _ ?_
    -- ½ε + tail ≤ ε
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ htail) ?_
    refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv (ExpNeg.two_halves ε))
    exact Q'.le_refl' _

/-! ### Priority 3: bound-passing to the diagonal limit -/

/-- **Lower bound passes to the limit.**  If `lb ≤ (s k).approx j` for every
term and index, then `ofQ' lb ≤ completeLimit s c`. -/
theorem ofQ'_le_completeLimit (s : Nat → RegularCReal) (c : ModCauchy s) {lb : Q'}
    (h : ∀ k j : Nat, lb ≤ (s k).approx j) :
    ofQ' lb ≤ completeLimit s c :=
  ofQ'_le_of_approx_ge (fun n => h (Mhat s c n) (2 * n + 1))

/-- **Upper bound passes to the limit.**  If `(s k).approx j ≤ ub` for every
term and index, then `completeLimit s c ≤ ofQ' ub`. -/
theorem completeLimit_le_ofQ' (s : Nat → RegularCReal) (c : ModCauchy s) {ub : Q'}
    (h : ∀ k j : Nat, (s k).approx j ≤ ub) :
    completeLimit s c ≤ ofQ' ub :=
  le_ofQ'_of_approx_le (fun n => h (Mhat s c n) (2 * n + 1))

/-- **Strict positivity passes to the limit.**  If every approximation of every
term is `≥ ε > 0`, then `completeLimit s c` is positive with the same witness. -/
theorem isPositive_completeLimit (s : Nat → RegularCReal) (c : ModCauchy s) {ε : Q'}
    (hε : (0 : Q') < ε) (h : ∀ k j : Nat, ε ≤ (s k).approx j) :
    IsPositive (completeLimit s c) :=
  ⟨ε, hε, ofQ'_le_completeLimit s c h⟩

/-! ### Priority 3: non-vacuity demo

The constant sequence `s k = ofQ' r` is modulus-Cauchy with the trivial outer
modulus, and its diagonal limit is `ofQ' r` at the level of approximations —
exhibiting the completeness machinery end to end. -/

/-- The constant `RegularCReal` sequence at `ofQ' r`. -/
def constSeq (r : Q') : Nat → RegularCReal := fun _ => ofQ' r

/-- The constant sequence is modulus-Cauchy with the trivial (`M ε = 0`)
modulus: all terms are identical, so every pair is within any `ε > 0`. -/
def constSeqModCauchy (r : Q') : ModCauchy (constSeq r) where
  M := fun _ => 0
  bound := by
    intro ε hε i j _ _ k
    -- (constSeq r i).approx k = r = (constSeq r j).approx k ; bound by self + ε.
    refine ⟨?_, ?_⟩ <;>
      exact Q'.add_le_self_of_nonneg r ε (Q'.le_of_lt hε)
  Mmono := by intro _ _ _ _; exact Nat.le_refl 0

/-- The completeness limit of the constant `ofQ' r` sequence. -/
def demoConstLimit (r : Q') : RegularCReal :=
  completeLimit (constSeq r) (constSeqModCauchy r)

/-- The demo limit is `ofQ' r` at the level of approximations (non-vacuity). -/
theorem demoConstLimit_approx (r : Q') (k : Nat) :
    (demoConstLimit r).approx k = r := rfl

/-- The machinery is non-vacuous: the constant sequence converges to its limit. -/
theorem demoConstLimit_converges (r : Q') :
    ConvergesTo (constSeq r) (demoConstLimit r) :=
  convergesTo_completeLimit (constSeq r) (constSeqModCauchy r)

end RegularCReal

end YMGap.Constructive

#print axioms YMGap.Constructive.Q'.invSucc_double_eqv
#print axioms YMGap.Constructive.Q'.add_regroup
#print axioms YMGap.Constructive.Q'.add_slack_collapse
#print axioms YMGap.Constructive.Q'.neg_le_neg_add'
#print axioms YMGap.Constructive.RegularCReal.add
#print axioms YMGap.Constructive.RegularCReal.neg
#print axioms YMGap.Constructive.RegularCReal.sub
#print axioms YMGap.Constructive.RegularCReal.Equiv_of_approx_eqv
#print axioms YMGap.Constructive.RegularCReal.ofQ'_add
#print axioms YMGap.Constructive.RegularCReal.add_comm
#print axioms YMGap.Constructive.RegularCReal.add_assoc
#print axioms YMGap.Constructive.RegularCReal.add_congr
#print axioms YMGap.Constructive.RegularCReal.add_le_add_right
#print axioms YMGap.Constructive.RegularCReal.add_le_add_left
#print axioms YMGap.Constructive.RegularCReal.add_le_add
#print axioms YMGap.Constructive.RegularCReal.add_czero
#print axioms YMGap.Constructive.RegularCReal.czero_add
#print axioms YMGap.Constructive.RegularCReal.sub_self_eqv_zero
#print axioms YMGap.Constructive.RegularCReal.qmul
#print axioms YMGap.Constructive.RegularCReal.qmul_approx
#print axioms YMGap.Constructive.RegularCReal.ofQ'_qmul
#print axioms YMGap.Constructive.RegularCReal.qmul_czero
#print axioms YMGap.Constructive.RegularCReal.one_qmul
#print axioms YMGap.Constructive.RegularCReal.qmul_one
#print axioms YMGap.Constructive.RegularCReal.qmul_add
#print axioms YMGap.Constructive.RegularCReal.qmul_le
#print axioms YMGap.Constructive.RegularCReal.abs_le_ofNat_qBound
#print axioms YMGap.Constructive.RegularCReal.ofNat_qBound_mul_invSucc_eqv
#print axioms YMGap.Constructive.RegularCReal.two_qIdx_succ
#print axioms YMGap.Constructive.RegularCReal.Mhat_mono
#print axioms YMGap.Constructive.RegularCReal.M_le_Mhat
#print axioms YMGap.Constructive.RegularCReal.diagSeq_directed
#print axioms YMGap.Constructive.RegularCReal.completeLimit
#print axioms YMGap.Constructive.RegularCReal.completeLimit_approx
#print axioms YMGap.Constructive.RegularCReal.convergesTo_completeLimit
#print axioms YMGap.Constructive.RegularCReal.ofQ'_le_completeLimit
#print axioms YMGap.Constructive.RegularCReal.completeLimit_le_ofQ'
#print axioms YMGap.Constructive.RegularCReal.isPositive_completeLimit
#print axioms YMGap.Constructive.RegularCReal.demoConstLimit_approx
#print axioms YMGap.Constructive.RegularCReal.demoConstLimit_converges
