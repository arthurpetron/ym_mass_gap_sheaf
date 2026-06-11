/-
# The second-kind Chebyshev bound `|U_{n-1}(x)| ≤ n` over `Q'`
# (discharges `Cheb.OpenProblem.absU_le`)

`ChebyshevBound.lean` closes, at all orders and axiom-clean, the first-kind
bound `|T_n(x)| ≤ 1` on `[−1,1]` (as the square form `Tsq_le_one`) together
with the ladder relations `linRel_all` and the Pythagorean invariant
`pythForm_all`.  It records the *second-kind* bound `|U_{n-1}(x)| ≤ n` as the
open `Prop` `Cheb.OpenProblem.absU_le`.

This module **closes** that bound, as the theorem `absU_le`, by the clean
two-step route:

1. `Tabs_le_one` : the usable two-sided form `−1 ≤ T_n(x) ∧ T_n(x) ≤ 1` on
   `[−1,1]`, derived from `Cheb.Tsq_le_one` (`T_n² ≤ 1`) via the elementary
   `Q'` lemma `abs_le_one_of_sq_le_one` (`a² ≤ 1 → −1 ≤ a ∧ a ≤ 1`), which is
   pure integer cross-product reasoning.

2. `Ushift` : the recurrence `U_{n+2}(x) ≈ U_n(x) + 2·T_{n+2}(x)`.  This is the
   trig identity `cos·(...)`-shadow `U_{n+2} − U_n = 2 T_{n+2}` (each step of
   the Dirichlet-kernel sum adds the two new `±(n+2)` frequencies).  It is the
   *bounded* recurrence: the naive `U_{n+2} = 2x·U_{n+1} − U_n` triangle bound
   fails (`|2x| ≤ 2` gives `≈ 2.414ⁿ`), whereas here the new term `2 T_{n+2}`
   is bounded by `2` since `|T| ≤ 1`.  We derive `Ushift` from the closed
   `linRel_all` ladder relations (it reuses the all-atom core `ladderB_tail`).

3. `absU_le` : two-step induction.  Base `U_0 = 1 ≤ ofNat 1`,
   `U_1 = 2x ∈ [−ofNat 2, ofNat 2]`.  Step: `U_{n+2} ≈ U_n + 2 T_{n+2}`, so
   `|U_{n+2}| ≤ |U_n| + 2·|T_{n+2}| ≤ (n+1) + 2 = (n+2)+1`.

# Axiom gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` enters only through `omega`'s reused `Int` helpers).  No
`Classical.*`, no `sorry`/`sorryAx`, no `native_decide`.
-/

import YMGap.Continuum.ChebyshevBound
import YMGap.Constructive.AbsQ

namespace YMGap.Continuum.ChebU

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.Cheb

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := eqv_trans _ _ _ h1 h2

/-! ## Step 1 — the two-sided `|·| ≤ 1` from a square bound

`a² ≤ 1 → −1 ≤ a ∧ a ≤ 1`.  Over `Q'`, with `a.num = m`, `a.den = d > 0`:
`a*a ≤ 1` unfolds to `m·m ≤ d·d`; `a ≤ 1` to `m ≤ d`; `−1 ≤ a` to `−d ≤ m`.
So everything reduces to the integer fact `m² ≤ d² → m ≤ d ∧ −d ≤ m` for
`d > 0`, which we prove constructively (no `by_contra`/`Classical`) via the
factorization `(d−m)(d+m) = d² − m² ≥ 0` together with `(d−m)+(d+m) = 2d ≥ 0`:
a product and a sum both `≥ 0` force both factors `≥ 0`. -/

/-- One-sided integer kernel: from `0 ≤ a*b` and `0 ≤ a+b`, conclude `0 ≤ a`.
Constructive: if `a < 0` then `0 ≤ a*b` forces `b ≤ 0`, whence `a+b < 0`,
contradicting `0 ≤ a+b`. -/
theorem int_left_nonneg_of_prod_sum (a b : Int)
    (hp : 0 ≤ a * b) (hs : 0 ≤ a + b) : 0 ≤ a := by
  rcases Int.lt_or_le a 0 with ha | ha
  · -- a < 0.  First: b ≤ 0.
    have hb : b ≤ 0 := by
      rcases Int.lt_or_le 0 b with hb | hb
      · -- 0 < b gives a*b < 0, contradicting hp.
        exact absurd hp (Int.not_le.mpr (Int.mul_neg_of_neg_of_pos ha hb))
      · exact hb
    -- a + b ≤ a + 0 = a < 0
    have hab : a + b < 0 := by
      have : a + b ≤ a + 0 := Int.add_le_add_left hb a
      have : a + b ≤ a := by simpa using this
      exact Int.lt_of_le_of_lt this ha
    exact absurd hs (Int.not_le.mpr hab)
  · exact ha

/-- Integer kernel: if a product and the sum of two integers are both `≥ 0`,
both integers are `≥ 0`. -/
theorem int_both_nonneg_of_prod_sum (a b : Int)
    (hp : 0 ≤ a * b) (hs : 0 ≤ a + b) : 0 ≤ a ∧ 0 ≤ b := by
  refine ⟨int_left_nonneg_of_prod_sum a b hp hs, ?_⟩
  refine int_left_nonneg_of_prod_sum b a ?_ ?_
  · rw [Int.mul_comm]; exact hp
  · rw [Int.add_comm]; exact hs

/-- Integer square-root bound: `m² ≤ d²` with `0 ≤ d` gives `m ≤ d` and
`−d ≤ m`.  Via `(d−m)(d+m) = d²−m² ≥ 0` and `(d−m)+(d+m) = 2d ≥ 0`. -/
theorem int_abs_le_of_sq_le (m d : Int) (hd : 0 ≤ d) (h : m * m ≤ d * d) :
    m ≤ d ∧ -d ≤ m := by
  -- product (d + (-m))·(d + m) = d² − m² ≥ 0
  have hfac : (d + (-m)) * (d + m) = d * d + (-(m * m)) := by
    have hc : d * m = m * d := Int.mul_comm d m
    simp only [Int.add_mul, Int.mul_add, Int.neg_mul]
    omega
  have hprod : 0 ≤ (d + (-m)) * (d + m) := by
    rw [hfac]; omega
  -- sum (d + (-m)) + (d + m) = 2d ≥ 0
  have hsum : 0 ≤ (d + (-m)) + (d + m) := by omega
  obtain ⟨h1, h2⟩ := int_both_nonneg_of_prod_sum (d + (-m)) (d + m) hprod hsum
  -- 0 ≤ d − m → m ≤ d ; 0 ≤ d + m → −d ≤ m
  exact ⟨by omega, by omega⟩

/-! ### Lifting to `Q'`

`a*a ≤ 1` over `Q'` is `(a.num)·(a.num) ≤ (a.den)·(a.den)` after the
cross-product unfolding (`(a*a).num = a.num², (a*a).den = a.den², (1).num=1,
(1).den=1`).  `a ≤ 1` is `a.num ≤ a.den`; `−1 ≤ a` is `−a.den ≤ a.num`. -/

/-- Two-sided bound from a square bound over `Q'`:
`a² ≤ 1 → −1 ≤ a ∧ a ≤ 1`. -/
theorem abs_le_one_of_sq_le_one (a : Q') (h : a * a ≤ (1 : Q')) :
    (-(1 : Q')) ≤ a ∧ a ≤ (1 : Q') := by
  -- unfold the square bound to the integer inequality m² ≤ d²
  have hsq : a.num * a.num ≤ (a.den : Int) * (a.den : Int) := by
    have h' : (a * a).num * ((1 : Q').den : Int)
            ≤ (1 : Q').num * ((a * a).den : Int) := h
    -- (a*a).num = a.num*a.num ; (a*a).den = a.den*a.den ; (1).num=1, (1).den=1
    have hnum : (a * a).num = a.num * a.num := rfl
    have hden : ((a * a).den : Int) = (a.den : Int) * (a.den : Int) := by
      show (((a.den * a.den - 1) + 1 : Nat) : Int) = (a.den : Int) * (a.den : Int)
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
        (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (den_pos a) (den_pos a))))]
      exact Int.natCast_mul a.den a.den
    have d1 : ((1 : Q').den : Int) = 1 := rfl
    have n1 : ((1 : Q').num) = 1 := rfl
    rw [hnum, hden, d1, n1] at h'
    simpa using h'
  have hd : (0 : Int) ≤ (a.den : Int) := Int.natCast_nonneg _
  obtain ⟨hle, hge⟩ := int_abs_le_of_sq_le a.num (a.den : Int) hd hsq
  refine ⟨?_, ?_⟩
  · -- −1 ≤ a : (−1).num·a.den ≤ a.num·(−1).den, i.e. −a.den ≤ a.num
    show ((-1 : Q')).num * (a.den : Int) ≤ a.num * ((-1 : Q').den : Int)
    have n1 : ((-1 : Q')).num = -1 := rfl
    have d1 : ((-1 : Q').den : Int) = 1 := rfl
    rw [n1, d1]
    -- goal: (-1)*a.den ≤ a.num*1 ; from hge : -a.den ≤ a.num
    have : (-1 : Int) * (a.den : Int) = -(a.den : Int) := by omega
    rw [this]; simpa using hge
  · -- a ≤ 1 : a.num·1 ≤ 1·a.den, i.e. a.num ≤ a.den
    show a.num * ((1 : Q').den : Int) ≤ (1 : Q').num * (a.den : Int)
    have n1 : ((1 : Q').num) = 1 := rfl
    have d1 : ((1 : Q').den : Int) = 1 := rfl
    rw [n1, d1]
    simpa using hle

/-! ## Step 1 conclusion — the two-sided Chebyshev `T`-bound on `[−1,1]` -/

/-- **Two-sided `|T_n(x)| ≤ 1` on `[−1,1]`**, for every `n ≥ 1`:
`−1 ≤ T_n(x) ∧ T_n(x) ≤ 1`.  From `Cheb.Tsq_le_one` and
`abs_le_one_of_sq_le_one`. -/
theorem Tabs_le_one (n : Nat) (x : Q') (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) :
    (-(1 : Q')) ≤ T (n+1) x ∧ T (n+1) x ≤ (1 : Q') :=
  abs_le_one_of_sq_le_one (T (n+1) x) (Tsq_le_one n x hx1 hxm1)

/-! ## Step 2 — the bounded recurrence `U_{n+2} ≈ U_n + 2·T_{n+2}`

First the "shift" identity `T_{n+2} ≈ x·U_{n+1} − U_n`, derived from the
closed ladder relations `linRel_all` (it reuses the all-atom core
`ladderB_tail`).  Then the `U`-recurrence `U_{n+2} = 2x·U_{n+1} − U_n` is
rewritten as `U_n + 2·T_{n+2}`. -/

/-- **The shift identity** `T_{n+2}(x) ≈ x·U_{n+1}(x) − U_n(x)`.  From the
ladder relations: `T_{n+2} ≈ x·T_{n+1} − c·U_n` (A) and the all-atom core
`ladderB_tail` (`x·(T_{n+1}+x·U_n) − U_n ≈ x·T_{n+1} − c·U_n`), substituting
`U_{n+1} ≈ T_{n+1}+x·U_n` (B). -/
theorem Tshift (n : Nat) (x : Q') :
    T (n+2) x ≈ x * U (n+1) x + (-(U n x)) := by
  obtain ⟨ha, hb⟩ := linRel_all n x
  -- ha : T (n+2) x ≈ x*T(n+1)x + (-(c*U n x))
  -- hb : U (n+1) x ≈ T(n+1)x + x*U n x
  calc T (n+2) x
      ≈ x * T (n+1) x + (-(((1:Q')+(-(x*x))) * U n x)) := ha
    _ ≈ x * (T (n+1) x + x * U n x) + (-(U n x)) :=
        eqv_symm (ladderB_tail x (T (n+1) x) (U n x))
    _ ≈ x * U (n+1) x + (-(U n x)) :=
        add_eqv_congr_right _ _ _ (mul_eqv_congr_left _ _ _ (eqv_symm hb))

/-- `a + (-a) ≈ 0` (companion of `neg_add_self_eqv`). -/
theorem add_neg_self_eqv (a : Q') : a + (-a) ≈ (0 : Q') :=
  eqv_trans _ _ _ (add_comm_eqv a (-a)) (neg_add_self_eqv a)

/-- Pure additive-group regroup `(p + p) + (−w) ≈ w + ((p + (−w)) + (p + (−w)))`.
The two `−w` on the right, together with the leading `w`, leave a single `−w`. -/
theorem regroupU_eqv (p w : Q') :
    (p + p) + (-w) ≈ w + ((p + (-w)) + (p + (-w))) := by
  -- Massage the RHS down to the LHS.
  have hR : w + ((p + (-w)) + (p + (-w))) ≈ (p + p) + (-w) := by
    calc w + ((p + (-w)) + (p + (-w)))
        ≈ w + ((p + p) + ((-w) + (-w))) :=
          add_eqv_congr_left _ _ _ (add_swap_inner p (-w) p (-w))
      _ ≈ (p + p) + (w + ((-w) + (-w))) := by
          -- w + (A + B) ≈ A + (w + B) with A = p+p, B = (-w)+(-w)
          calc w + ((p + p) + ((-w) + (-w)))
              ≈ (w + (p + p)) + ((-w) + (-w)) :=
                eqv_symm (add_assoc_eqv w (p + p) ((-w) + (-w)))
            _ ≈ ((p + p) + w) + ((-w) + (-w)) :=
                add_eqv_congr_right _ _ _ (add_comm_eqv w (p + p))
            _ ≈ (p + p) + (w + ((-w) + (-w))) :=
                add_assoc_eqv (p + p) w ((-w) + (-w))
      _ ≈ (p + p) + ((w + (-w)) + (-w)) :=
          add_eqv_congr_left _ _ _ (eqv_symm (add_assoc_eqv w (-w) (-w)))
      _ ≈ (p + p) + ((0 : Q') + (-w)) :=
          add_eqv_congr_left _ _ _ (add_eqv_congr_right _ _ _ (add_neg_self_eqv w))
      _ ≈ (p + p) + (-w) := by
          rw [zero_add']; exact eqv_refl _
  exact eqv_symm hR

/-- All-atom core for the `U`-recurrence rewrite:
`(2x)·v − w ≈ w + 2·(x·v − w)`. -/
theorem Ushift_tail (x v w : Q') :
    ((2 : Q') * x) * v + (-w) ≈ w + (2 : Q') * (x * v + (-w)) := by
  -- expand (2x)v ≈ xv + xv and 2(xv−w) ≈ (xv−w)+(xv−w), then regroup
  calc ((2 : Q') * x) * v + (-w)
      ≈ (x + x) * v + (-w) :=
        add_eqv_congr_right _ _ _ (mul_eqv_congr_right _ _ _ (two_mul_eqv x))
    _ ≈ (x*v + x*v) + (-w) :=
        add_eqv_congr_right _ _ _ (add_mul_eqv x x v)
    _ ≈ w + (((x*v) + (-w)) + ((x*v) + (-w))) := regroupU_eqv (x*v) w
    _ ≈ w + (2 : Q') * (x * v + (-w)) :=
        add_eqv_congr_left _ _ _ (eqv_symm (two_mul_eqv (x*v + (-w))))

/-- **The bounded recurrence** `U_{n+2}(x) ≈ U_n(x) + 2·T_{n+2}(x)`.  This is
the `+2T` form that the bound needs; the new term `2·T_{n+2}` is bounded by
`2` since `|T| ≤ 1`, in contrast to the failing naive `2x·U_{n+1}` form. -/
theorem Ushift (n : Nat) (x : Q') :
    U (n+2) x ≈ U n x + (2 : Q') * T (n+2) x := by
  rw [U_succ_succ n x]
  calc ((2 : Q') * x) * U (n+1) x + (-(U n x))
      ≈ U n x + (2 : Q') * (x * U (n+1) x + (-(U n x))) :=
        Ushift_tail x (U (n+1) x) (U n x)
    _ ≈ U n x + (2 : Q') * T (n+2) x :=
        add_eqv_congr_left _ _ _ (mul_eqv_congr_left _ _ _ (eqv_symm (Tshift n x)))

/-! ## Step 3 — the two-step induction giving `|U_n(x)| ≤ n+1`

Numeric `Q'` helpers, then `add_le_add` (both arguments), then the bounds
`2·T_{n+2} ∈ [−ofNat 2, ofNat 2]` from the closed `|T| ≤ 1`, then the
two-step induction on `n`. -/

/-- `a ≤ A → b ≤ B → a + b ≤ A + B`. -/
theorem add_le_add (a b A B : Q') (h1 : a ≤ A) (h2 : b ≤ B) : a + b ≤ A + B :=
  le_trans' (a + b) (A + b) (A + B)
    (add_le_add_right a A b h1) (add_le_add_left A b B h2)

/-- `ofNat a + ofNat b ≈ ofNat (a + b)`. -/
theorem ofNat_add_eqv (a b : Nat) :
    Q'.ofNat a + Q'.ofNat b ≈ Q'.ofNat (a + b) := by
  show (Q'.ofNat a + Q'.ofNat b).num * ((Q'.ofNat (a+b)).den : Int)
      = (Q'.ofNat (a+b)).num * ((Q'.ofNat a + Q'.ofNat b).den : Int)
  simp only [add_num, add_den_cast]
  show ((Int.ofNat a) * 1 + (Int.ofNat b) * 1) * 1
      = (Int.ofNat (a+b)) * (1 * 1)
  simp only [Int.ofNat_eq_natCast]
  omega

/-- `(2 : Q') = ofNat 2`, structurally. -/
theorem two_eq_ofNat : (2 : Q') = Q'.ofNat 2 := rfl

/-- `(1 : Q') = ofNat 1`, structurally. -/
theorem one_eq_ofNat : (1 : Q') = Q'.ofNat 1 := rfl

/-- `(1 : Q') + 1 ≈ ofNat 2`. -/
theorem one_add_one_eqv_two : (1 : Q') + 1 ≈ Q'.ofNat 2 := by
  rw [one_eq_ofNat]
  exact ofNat_add_eqv 1 1

/-- `(-(ofNat 2)) ≈ (-1) + (-1)`. -/
theorem neg_two_eqv : (-(Q'.ofNat 2)) ≈ ((-(1:Q')) + (-(1:Q'))) := by
  show (-(Q'.ofNat 2)).num * (((-(1:Q')) + (-(1:Q'))).den : Int)
      = ((-(1:Q')) + (-(1:Q'))).num * ((-(Q'.ofNat 2)).den : Int)
  simp only [add_num, neg_num, add_den_cast, neg_den]
  show (-(Int.ofNat 2)) * (1 * 1)
      = ((-1) * 1 + (-1) * 1) * 1
  decide

/-- Upper bound on `2·T_{n+2}`: `2·T_{n+2}(x) ≤ ofNat 2` on `[−1,1]`.  From
`|T_{n+2}| ≤ 1` (two-sided `Tabs_le_one`) and `2·T ≈ T + T`. -/
theorem two_T_le (n : Nat) (x : Q') (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) :
    (2 : Q') * T (n+2) x ≤ Q'.ofNat 2 := by
  obtain ⟨_, hub⟩ := Tabs_le_one (n+1) x hx1 hxm1   -- T ((n+1)+1) = T (n+2)
  -- 2*T ≈ T + T ≤ 1 + 1 ≈ ofNat 2
  have hstep : (2 : Q') * T (n+2) x ≤ (1 : Q') + 1 :=
    le_trans' _ (T (n+2) x + T (n+2) x) _
      (le_of_eqv (two_mul_eqv (T (n+2) x)))
      (add_le_add _ _ _ _ hub hub)
  exact le_trans' _ ((1:Q') + 1) _ hstep (le_of_eqv one_add_one_eqv_two)

/-- Lower bound on `2·T_{n+2}`: `−ofNat 2 ≤ 2·T_{n+2}(x)` on `[−1,1]`. -/
theorem neg_two_le_T (n : Nat) (x : Q') (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) :
    (-(Q'.ofNat 2)) ≤ (2 : Q') * T (n+2) x := by
  obtain ⟨hlb, _⟩ := Tabs_le_one (n+1) x hx1 hxm1
  -- −ofNat 2 ≈ (−1)+(−1) ≤ T + T ≈ 2*T
  have hstep : ((-(1:Q')) + (-(1:Q'))) ≤ T (n+2) x + T (n+2) x :=
    add_le_add _ _ _ _ hlb hlb
  refine le_trans' _ ((-(1:Q')) + (-(1:Q'))) _ (le_of_eqv neg_two_eqv) ?_
  exact le_trans' _ (T (n+2) x + T (n+2) x) _ hstep
    (le_of_eqv (eqv_symm (two_mul_eqv (T (n+2) x))))

/-! ### The induction predicate and the two-step recursion

We prove `P n : −ofNat(n+1) ≤ U n x ∧ U n x ≤ ofNat(n+1)` by strong/two-step
induction: `P 0`, `P 1`, and `P n → P (n+2)`.  We package the two-step
recursion with an explicit `Nat.rec`-style helper proving `P n ∧ P (n+1)`. -/

/-- The bound predicate at a single index. -/
def UB (n : Nat) (x : Q') : Prop :=
  (-(Q'.ofNat (n+1))) ≤ U n x ∧ U n x ≤ Q'.ofNat (n+1)

/-- Base: `UB 0`.  `U 0 = 1`, `ofNat 1 = 1`. -/
theorem UB_zero (x : Q') : UB 0 x := by
  refine ⟨?_, ?_⟩
  · show (-(Q'.ofNat 1)) ≤ U 0 x
    rw [U_zero]
    -- −ofNat 1 = −1 ≤ 1.  −1 ≤ 1 : (−1).num·1 ≤ 1·1 i.e. −1 ≤ 1.
    show (-(Q'.ofNat 1)).num * ((1:Q').den : Int) ≤ (1:Q').num * ((-(Q'.ofNat 1)).den : Int)
    simp only [neg_num, neg_den]
    show (-(Int.ofNat 1)) * 1 ≤ (1:Int) * 1
    decide
  · show U 0 x ≤ Q'.ofNat 1
    rw [U_zero]
    -- 1 ≤ ofNat 1 : structurally equal, le_refl up to eqv
    show (1:Q') ≤ Q'.ofNat 1
    exact le_of_eqv (by rw [one_eq_ofNat]; exact eqv_refl _)

/-- Base: `UB 1`.  `U 1 = 2x`, and `2x ∈ [−ofNat 2, ofNat 2]` from
`x ∈ [−1,1]` (via `2x ≈ x + x`). -/
theorem UB_one (x : Q') (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) : UB 1 x := by
  refine ⟨?_, ?_⟩
  · show (-(Q'.ofNat 2)) ≤ U 1 x
    rw [U_one]
    -- −ofNat 2 ≈ (−1)+(−1) ≤ x + x ≈ 2x
    refine le_trans' _ ((-(1:Q')) + (-(1:Q'))) _ (le_of_eqv neg_two_eqv) ?_
    exact le_trans' _ (x + x) _ (add_le_add _ _ _ _ hxm1 hxm1)
      (le_of_eqv (eqv_symm (two_mul_eqv x)))
  · show U 1 x ≤ Q'.ofNat 2
    rw [U_one]
    -- 2x ≈ x + x ≤ 1 + 1 ≈ ofNat 2
    refine le_trans' _ (x + x) _ (le_of_eqv (two_mul_eqv x)) ?_
    exact le_trans' _ ((1:Q') + 1) _ (add_le_add _ _ _ _ hx1 hx1)
      (le_of_eqv one_add_one_eqv_two)

/-- Two-step step: `UB n → UB (n+2)`, on `[−1,1]`.  Uses the bounded
recurrence `U_{n+2} ≈ U_n + 2·T_{n+2}` and the `2·T` bounds. -/
theorem UB_step (n : Nat) (x : Q') (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x)
    (ih : UB n x) : UB (n+2) x := by
  obtain ⟨hlb, hub⟩ := ih
  refine ⟨?_, ?_⟩
  · -- lower:  −ofNat(n+3) ≈ −ofNat(n+1) + (−ofNat 2) ≤ U n + 2 T(n+2) ≈ U(n+2)
    show (-(Q'.ofNat (n+2+1))) ≤ U (n+2) x
    have hsum : (-(Q'.ofNat (n+1))) + (-(Q'.ofNat 2)) ≤ U n x + (2 : Q') * T (n+2) x :=
      add_le_add _ _ _ _ hlb (neg_two_le_T n x hx1 hxm1)
    -- −ofNat(n+1) + (−ofNat 2) ≈ −ofNat(n+3)
    have hnum : (-(Q'.ofNat (n+2+1))) ≈ (-(Q'.ofNat (n+1))) + (-(Q'.ofNat 2)) := by
      show (-(Q'.ofNat (n+2+1))).num * (((-(Q'.ofNat (n+1))) + (-(Q'.ofNat 2))).den : Int)
          = ((-(Q'.ofNat (n+1))) + (-(Q'.ofNat 2))).num * ((-(Q'.ofNat (n+2+1))).den : Int)
      simp only [add_num, neg_num, add_den_cast, neg_den]
      show (-(Int.ofNat (n+2+1))) * (1 * 1)
          = ((-(Int.ofNat (n+1))) * 1 + (-(Int.ofNat 2)) * 1) * 1
      simp only [Int.ofNat_eq_natCast]
      push_cast
      omega
    refine le_trans' _ _ _ (le_of_eqv hnum) ?_
    exact le_trans' _ (U n x + (2 : Q') * T (n+2) x) _ hsum
      (le_of_eqv (eqv_symm (Ushift n x)))
  · -- upper:  U(n+2) ≈ U n + 2 T(n+2) ≤ ofNat(n+1) + ofNat 2 ≈ ofNat(n+3)
    show U (n+2) x ≤ Q'.ofNat (n+2+1)
    have hsum : U n x + (2 : Q') * T (n+2) x ≤ Q'.ofNat (n+1) + Q'.ofNat 2 :=
      add_le_add _ _ _ _ hub (two_T_le n x hx1 hxm1)
    refine le_trans' _ (U n x + (2 : Q') * T (n+2) x) _ (le_of_eqv (Ushift n x)) ?_
    refine le_trans' _ (Q'.ofNat (n+1) + Q'.ofNat 2) _ hsum ?_
    -- ofNat(n+1) + ofNat 2 ≈ ofNat(n+3)
    have : Q'.ofNat (n+1) + Q'.ofNat 2 ≈ Q'.ofNat ((n+1)+2) := ofNat_add_eqv (n+1) 2
    refine le_trans' _ _ _ (le_of_eqv this) ?_
    -- (n+1)+2 = n+2+1
    have heq : (n+1)+2 = n+2+1 := by omega
    rw [heq]; exact le_refl' _

/-- Two-step induction packager: `UB n ∧ UB (n+1)` for all `n`. -/
theorem UB_pair (x : Q') (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) :
    ∀ n, UB n x ∧ UB (n+1) x := by
  intro n
  induction n with
  | zero => exact ⟨UB_zero x, UB_one x hx1 hxm1⟩
  | succ k ih =>
      obtain ⟨hk, hk1⟩ := ih
      exact ⟨hk1, UB_step k x hx1 hxm1 hk⟩

/-- **`UB n` at all orders**: `−ofNat(n+1) ≤ U_n(x) ≤ ofNat(n+1)` on
`[−1,1]`, for every `n`. -/
theorem UB_all (n : Nat) (x : Q') (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) :
    UB n x := (UB_pair x hx1 hxm1 n).1

/-! ## Discharging the open problem

`Cheb.OpenProblem.absU_le` is exactly `∀ n x, x ≤ 1 → −1 ≤ x →
(U n x ≤ ofNat (n+1) ∧ −ofNat(n+1) ≤ U n x)`.  `UB_all` gives the two
conjuncts (in the opposite order); we repackage. -/

/-- **The second-kind Chebyshev bound `|U_{n-1}(x)| ≤ n` on `[−1,1]`**, in
the `Q'`/`U`-indexing `−ofNat(n+1) ≤ U_n(x) ≤ ofNat(n+1)`.  This is exactly
`Cheb.OpenProblem.absU_le`, now a proved theorem. -/
theorem absU_le : Cheb.OpenProblem.absU_le := by
  intro n x hx1 hxm1
  obtain ⟨hlb, hub⟩ := UB_all n x hx1 hxm1
  exact ⟨hub, hlb⟩

end YMGap.Continuum.ChebU

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem must report `[propext]` or `[propext, Quot.sound]`
(both MLTT/HoTT-valid; `Quot.sound` enters only via `omega`'s reused `Int`
helpers in the small numeric/cross-product closers) — never `Classical.*`,
`sorryAx`, or `native_decide`. -/

#print axioms YMGap.Continuum.ChebU.int_both_nonneg_of_prod_sum
#print axioms YMGap.Continuum.ChebU.int_abs_le_of_sq_le
#print axioms YMGap.Continuum.ChebU.abs_le_one_of_sq_le_one
#print axioms YMGap.Continuum.ChebU.Tabs_le_one
#print axioms YMGap.Continuum.ChebU.Tshift
#print axioms YMGap.Continuum.ChebU.Ushift_tail
#print axioms YMGap.Continuum.ChebU.Ushift
#print axioms YMGap.Continuum.ChebU.ofNat_add_eqv
#print axioms YMGap.Continuum.ChebU.two_T_le
#print axioms YMGap.Continuum.ChebU.neg_two_le_T
#print axioms YMGap.Continuum.ChebU.UB_zero
#print axioms YMGap.Continuum.ChebU.UB_one
#print axioms YMGap.Continuum.ChebU.UB_step
#print axioms YMGap.Continuum.ChebU.UB_pair
#print axioms YMGap.Continuum.ChebU.UB_all
#print axioms YMGap.Continuum.ChebU.absU_le
