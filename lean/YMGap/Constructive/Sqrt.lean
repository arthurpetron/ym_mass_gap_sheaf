/-
Constructive square root `CReal.sqrt` for positive rationals — the √-bridge
substrate (Milestone F.5 of `docs/uniform-parametric-bound-plan.md`).

# Why this module exists

The mass bound is carried as a `Q'`-rational threshold (`m_0² ≤ ε`); the
dimensional identification `m ≥ √σ̂_∞` was paper-only.  This module builds a
genuine constructive square root so that the mass `m_0 = √σ̂_∞` becomes a real
`CReal` with witnessed positivity and a proved `m_0² ≃ σ̂_∞`.

# Construction (Heron / Newton, division-free in the bound)

For a positive rational `a`, the Heron iteration

    x₀ = a + 1,   x_{n+1} = (x_n + a / x_n) / 2

is built on the rational reciprocal of a *positive* rational (constructible:
`recipPos q = den/num`), so no `Q'` general division is needed.  The
convergence modulus is **explicit and avoids any reference to the (not yet
constructed) limit `√a`**, via the elementary error algebra:

  * `e_n := x_n² − a ≥ 0`              (AM–GM invariant, induction)
  * `x_n ≥ L > 0` with `L² ≤ a`        (uniform rational lower bound)
  * `e_{n+1} ≤ e_n / 4`                (`e_{n+1} = e_n²/(4x_n²) ≤ e_n/4`)
  * `2L·(x_n − x_m) ≤ e_n − e_m ≤ e_n` for `n ≤ m`  ⟹  Cauchy with a
    geometric modulus (no telescoping; uses only `x_k ≥ L`).

`(√a)² ≃ a` follows because `x_n² = a + e_n` and `e_n → 0`; positivity from
`x_n ≥ L`.

The modulus is carried as **`Type`-level data** (`sqrtModulus`, a function
`ε ↦ N`, AGENTS.md Rule 8.3) and applied to fill the legacy `Prop`-level
`cauchy` field.

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` or `[propext, Quot.sound]`
(the `Quot.sound` from `omega`/`Nat`).  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Constructive.Reals
import YMGap.Constructive.CRealMul
import YMGap.Constructive.RationalsMul
import YMGap.Constructive.AbsQ
import YMGap.Constructive.Geometric
import YMGap.Constructive.HalfPow
import YMGap.Constructive.QPoly
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.CRealAdd

namespace YMGap.Constructive

namespace Q'

/-! ## Reciprocal of a positive rational

`recipPos q = q.den / q.num` (valid because `q > 0 ⟹ q.num > 0`).  We only ever
use it on positive rationals, where `q * recipPos q ≃ 1`. -/

/-- `0 < q ⟹ 0 < q.num` (denominator structurally positive). -/
theorem num_pos_of_pos {q : Q'} (hq : (0 : Q') < q) : 0 < q.num := by
  have h : (0 : Int) * (q.den : Int) < q.num * (1 : Int) := hq
  rw [Int.zero_mul, Int.mul_one] at h; exact h

/-- Reciprocal of a positive rational `q = num/den`, namely `den/num`.
The proof obligation `0 < q` is consumed to know `q.num > 0` (so `num.toNat`
is the true numerator). -/
def recipPos (q : Q') (hq : (0 : Q') < q) : Q' :=
  mkPos (q.den : Int) q.num.toNat
    (by have := num_pos_of_pos hq; omega)

theorem recipPos_num (q : Q') (hq : (0 : Q') < q) :
    (recipPos q hq).num = (q.den : Int) := rfl

theorem recipPos_den (q : Q') (hq : (0 : Q') < q) :
    ((recipPos q hq).den : Int) = q.num := by
  have hden : (recipPos q hq).den = q.num.toNat := by
    show (mkPos (q.den : Int) q.num.toNat _).den = q.num.toNat
    exact mkPos_den _ _ _
  rw [hden]
  exact Int.toNat_of_nonneg (Int.le_of_lt (num_pos_of_pos hq))

theorem recipPos_pos (q : Q') (hq : (0 : Q') < q) : (0 : Q') < recipPos q hq := by
  show (0 : Int) * ((recipPos q hq).den : Int) < (recipPos q hq).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one, recipPos_num]
  exact_mod_cast q.den_pos

/-- The defining identity `q · (1/q) ≃ 1` for positive `q`. -/
theorem mul_recipPos_eqv (q : Q') (hq : (0 : Q') < q) :
    (q * recipPos q hq).eqv 1 := by
  show (q * recipPos q hq).num * ((1 : Q').den : Int)
     = (1 : Q').num * ((q * recipPos q hq).den : Int)
  show (q.num * (recipPos q hq).num) * (1 : Int)
     = (1 : Int) * ((q * recipPos q hq).den : Int)
  rw [Int.mul_one, Int.one_mul, mul_den_cast q (recipPos q hq),
      recipPos_num, recipPos_den, Int.mul_comm]

/-- A **total** reciprocal, correct on positive rationals: `q.den / max(1, ⌊num⌋)`.
The `max 1` makes the denominator structurally positive so the Heron sequence is
total (no proof threading through the recursion); on the iteration invariant
`x_n ≥ L > 0` we have `x_n.num ≥ 1`, so `recip` agrees with `recipPos`. -/
def recip (q : Q') : Q' := mkPos (q.den : Int) (max 1 q.num.toNat) (by omega)

theorem recip_num (q : Q') : (recip q).num = (q.den : Int) := rfl

theorem recip_den (q : Q') : (recip q).den = max 1 q.num.toNat := by
  show (mkPos (q.den : Int) (max 1 q.num.toNat) _).den = max 1 q.num.toNat
  exact mkPos_den _ _ _

theorem recip_pos (q : Q') : (0 : Q') < recip q := by
  show (0 : Int) * ((recip q).den : Int) < (recip q).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one, recip_num]
  exact_mod_cast q.den_pos

/-- On a positive rational `recip` agrees with `recipPos`, hence `q · recip q ≃ 1`. -/
theorem mul_recip_eqv (q : Q') (hq : (0 : Q') < q) : (q * recip q).eqv 1 := by
  have hnum : 0 < q.num := num_pos_of_pos hq
  have hmax : max 1 q.num.toNat = q.num.toNat := by omega
  show (q * recip q).num * ((1 : Q').den : Int)
     = (1 : Q').num * ((q * recip q).den : Int)
  show (q.num * (recip q).num) * (1 : Int)
     = (1 : Int) * ((q * recip q).den : Int)
  rw [Int.mul_one, Int.one_mul, mul_den_cast q (recip q), recip_num]
  have hden : ((recip q).den : Int) = q.num := by
    rw [recip_den, hmax]; exact Int.toNat_of_nonneg (Int.le_of_lt hnum)
  rw [hden, Int.mul_comm]

/-! ### Small `Q'` order / algebra facts the Heron analysis needs -/

/-- `0 ≤ a → 0 ≤ b → a ≤ b → c ≤ d → 0 ≤ c → a*c ≤ b*d` (monotone product). -/
theorem mul_le_mul_of_nonneg {a b c d : Q'}
    (hab : a ≤ b) (hcd : c ≤ d) (hb : (0 : Q') ≤ b) (hc : (0 : Q') ≤ c) :
    a * c ≤ b * d :=
  le_trans' (a * c) (b * c) (b * d)
    (mul_le_mul_of_nonneg_right a b c hab hc)
    (mul_le_mul_of_nonneg_left c d b hcd hb)

/-- Product of positives is positive. -/
theorem mul_pos {a b : Q'} (ha : (0 : Q') < a) (hb : (0 : Q') < b) :
    (0 : Q') < a * b := by
  show (0 : Int) * ((a * b).den : Int) < (a * b).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  exact Int.mul_pos (num_pos_of_pos ha) (num_pos_of_pos hb)

/-- Sum of positives is positive. -/
theorem add_pos {a b : Q'} (ha : (0 : Q') < a) (hb : (0 : Q') < b) :
    (0 : Q') < a + b := by
  show (0 : Int) * ((a + b).den : Int) < (a + b).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  show (0 : Int) < a.num * (b.den : Int) + b.num * (a.den : Int)
  have h1 : 0 < a.num * (b.den : Int) :=
    Int.mul_pos (num_pos_of_pos ha) (by exact_mod_cast b.den_pos)
  have h2 : 0 < b.num * (a.den : Int) :=
    Int.mul_pos (num_pos_of_pos hb) (by exact_mod_cast a.den_pos)
  omega

/-- `0 < a → 0 ≤ b → 0 ≤ a + b → ` strict from `add_pos`/`add_le`. -/
theorem pos_add_nonneg {a b : Q'} (ha : (0 : Q') < a) (hb : (0 : Q') ≤ b) :
    (0 : Q') < a + b := by
  show (0 : Int) * ((a + b).den : Int) < (a + b).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  show (0 : Int) < a.num * (b.den : Int) + b.num * (a.den : Int)
  have h1 : 0 < a.num * (b.den : Int) :=
    Int.mul_pos (num_pos_of_pos ha) (by exact_mod_cast b.den_pos)
  have h2 : 0 ≤ b.num * (a.den : Int) :=
    Int.mul_nonneg ((zero_le_iff_num_nonneg b).mp hb) (by exact_mod_cast Nat.zero_le _)
  omega

/-- `a ≤ b → b < c → a < c` on `Q'`. -/
theorem lt_of_le_of_lt {a b c : Q'} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  have e1 : a.num * (b.den : Int) ≤ b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) < c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  -- multiply e1 by c.den, e2 by a.den, chain through b.den>0
  have hbd : (0 : Int) < (b.den : Int) := by exact_mod_cast b.den_pos
  have hcd : (0 : Int) ≤ (c.den : Int) := by exact_mod_cast Nat.zero_le _
  have had : (0 : Int) ≤ (a.den : Int) := by exact_mod_cast Nat.zero_le _
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          ≤ (b.num * (a.den : Int)) * (c.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_right e1 hcd
    -- (a.num*b.den)*c.den ≤ (b.num*a.den)*c.den ; reorder LHS
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at this
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          < (c.num * (a.den : Int)) * (b.den : Int) := by
    have := Int.mul_lt_mul_of_pos_left e2 (by exact_mod_cast a.den_pos : (0:Int) < (a.den:Int))
    -- a.den*(b.num*c.den) < a.den*(c.num*b.den)
    have hl : (a.den : Int) * (b.num * (c.den : Int)) = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_comm b.num (a.den : Int), Int.mul_assoc]
    have hrr : (a.den : Int) * (c.num * (b.den : Int)) = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_comm c.num (a.den : Int), Int.mul_assoc]
    rwa [hl, hrr] at this
  have schain : (a.num * (c.den : Int)) * (b.den : Int)
              < (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_le_of_lt s1 s2
  exact Int.lt_of_mul_lt_mul_right schain (by exact_mod_cast Nat.zero_le _)

/-- Cancel a positive factor in `≤`: `c*a ≤ c*b → 0 < c → a ≤ b`. -/
theorem le_of_mul_le_mul_left {a b c : Q'} (h : c * a ≤ c * b) (hc : (0 : Q') < c) :
    a ≤ b := by
  have hh : (c * a).num * ((c * b).den : Int) ≤ (c * b).num * ((c * a).den : Int) := h
  show a.num * (b.den : Int) ≤ b.num * (a.den : Int)
  have hcn : 0 < c.num := num_pos_of_pos hc
  rw [show (c * a).num = c.num * a.num from rfl,
      show (c * b).num = c.num * b.num from rfl,
      mul_den_cast c b, mul_den_cast c a] at hh
  -- (c.num*a.num)*(c.den*b.den) ≤ (c.num*b.num)*(c.den*a.den)
  have hh2 : (c.num * (c.den : Int)) * (a.num * (b.den : Int))
           ≤ (c.num * (c.den : Int)) * (b.num * (a.den : Int)) := by
    have e1 : (c.num * a.num) * ((c.den : Int) * (b.den : Int))
            = (c.num * (c.den : Int)) * (a.num * (b.den : Int)) := by ac_rfl
    have e2 : (c.num * b.num) * ((c.den : Int) * (a.den : Int))
            = (c.num * (c.den : Int)) * (b.num * (a.den : Int)) := by ac_rfl
    rw [← e1, ← e2]; exact hh
  have hcc : 0 < c.num * (c.den : Int) :=
    Int.mul_pos hcn (by exact_mod_cast c.den_pos)
  exact Int.le_of_mul_le_mul_left hh2 hcc

end Q'

/-! ## The Heron iteration

`step a x = ½·(x + a·(1/x))`, with `x₀ = a + 1`.  All algebra below assumes the
running iterate is positive (the invariant `step_pos`), so `recip` is the true
reciprocal (`mul_recip_eqv`). -/

namespace CReal

open Q' HalfPow

/-- One Heron step for `√a`: `x ↦ ½·(x + a/x)`. -/
def heronStep (a x : Q') : Q' := half * (x + a * recip x)

/-- The Heron iterates `x₀ = a+1`, `x_{n+1} = ½(x_n + a/x_n)`. -/
def heronSeq (a : Q') : Nat → Q'
  | 0 => a + 1
  | n + 1 => heronStep a (heronSeq a n)

@[simp] theorem heronSeq_zero (a : Q') : heronSeq a 0 = a + 1 := rfl
@[simp] theorem heronSeq_succ (a : Q') (n : Nat) :
    heronSeq a (n + 1) = heronStep a (heronSeq a n) := rfl

/-! ### Positivity of a step -/

/-- `0 < a → 0 < x → 0 < heronStep a x`. -/
theorem heronStep_pos {a x : Q'} (ha : (0 : Q') < a) (hx : (0 : Q') < x) :
    (0 : Q') < heronStep a x := by
  have hsum : (0 : Q') < x + a * recip x :=
    Q'.add_pos hx (Q'.mul_pos ha (Q'.recip_pos x))
  exact Q'.mul_pos (by decide) hsum

/-- All Heron iterates of a positive `a` are positive. -/
theorem heronSeq_pos {a : Q'} (ha : (0 : Q') < a) : ∀ n, (0 : Q') < heronSeq a n
  | 0 => by
      show (0 : Q') < a + 1
      exact Q'.add_pos ha (by decide)
  | n + 1 => by
      show (0 : Q') < heronStep a (heronSeq a n)
      exact heronStep_pos ha (heronSeq_pos ha n)

/-! ### The square of a step

We work with `4·s·s` to clear the `½` and reduce everything to a polynomial in
`x` and `r = 1/x` with the side relation `x·r ≃ 1`.  Writing `b := a·r`, the
expansion `(x+b)² = x² + 2·x·b + b²` and `x·b = a·(x·r) ≃ a` give the two facts
the convergence analysis needs. -/

/-- `four · (½·½) ≃ 1`. -/
private theorem four_half_half : ((Q'.ofNat 4) * (half * half)).eqv 1 := by decide

/-- `(½·b)·(½·b) ≃ (½·½)·(b·b)` — pure `half` reassociation. -/
private theorem half_b_sq (b : Q') :
    ((half * b) * (half * b)).eqv ((half * half) * (b * b)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv half b (half * b)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left half (b * (half * b)) (half * (b * b)) ?_)
    (Q'.eqv_symm (Q'.mul_assoc_eqv half half (b * b)))
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv b half b)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (b * half) (half * b) b (Q'.mul_comm_eqv b half)) ?_
  exact Q'.mul_assoc_eqv half b b

/-- `4·s·s ≃ (x + a/x)²` (clears the `½`). -/
theorem four_mul_heronStep_sq (a x : Q') :
    ((Q'.ofNat 4) * (heronStep a x * heronStep a x)).eqv
      ((x + a * recip x) * (x + a * recip x)) := by
  have hss : (heronStep a x * heronStep a x).eqv
      ((half * half) * ((x + a * recip x) * (x + a * recip x))) :=
    half_b_sq (x + a * recip x)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _ hss) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 4) (half * half)
      ((x + a * recip x) * (x + a * recip x)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right ((Q'.ofNat 4) * (half * half)) 1
      ((x + a * recip x) * (x + a * recip x)) four_half_half) ?_
  exact Q'.one_mul_eqv _

/-! ### Polynomial expansion helpers (two free variables) -/

open YMGap.Constructive.QPoly in
/-- `(u+v)·(u+v) ≃ (u·u + u·v) + (u·v + v·v)`. -/
private theorem sq_add (u v : Q') :
    ((u + v) * (u + v)).eqv ((u * u + u * v) + (u * v + v * v)) := by
  -- (u+v)*(u+v) ≃ u*(u+v) + v*(u+v)
  refine Q'.eqv_trans _ _ _ (q_add_mul u v (u + v)) ?_
  -- u*(u+v) ≃ u*u + u*v ; v*(u+v) ≃ v*u + v*v ≃ u*v + v*v
  refine q_add_congr (Q'.mul_add_eqv u u v) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv v u v) ?_
  exact q_add_congr (Q'.mul_comm_eqv v u) (Q'.eqv_refl (v * v))

open YMGap.Constructive.QPoly in
/-- `(u + -v)·(u + -v) ≃ (u·u + -(u·v)) + (-(u·v) + v·v)`. -/
private theorem sq_sub (u v : Q') :
    ((u + -v) * (u + -v)).eqv
      ((u * u + -(u * v)) + (-(u * v) + v * v)) := by
  refine Q'.eqv_trans _ _ _ (sq_add u (-v)) ?_
  refine q_add_congr ?_ ?_
  · exact q_add_congr (Q'.eqv_refl (u * u)) (Q'.mul_neg_eqv u v)
  · refine q_add_congr (Q'.mul_neg_eqv u v) ?_
    -- (-v)*(-v) ≃ v*v
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv v (-v)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv v v)) ?_
    exact Q'.neg_neg_eqv (v * v)

/-- `(ofNat 2)·c ≃ c + c`. -/
private theorem two_mul_eqv (c : Q') :
    ((Q'.ofNat 2) * c).eqv (c + c) := by
  show ((Q'.ofNat 2) * c).num * ((c + c).den : Int)
     = (c + c).num * (((Q'.ofNat 2) * c).den : Int)
  have hn : ((Q'.ofNat 2) * c).num = 2 * c.num := rfl
  have hd : (((Q'.ofNat 2) * c).den : Int) = (c.den : Int) := by
    rw [mul_den_cast]
    show ((Q'.ofNat 2).den : Int) * (c.den : Int) = (c.den : Int)
    rw [show ((Q'.ofNat 2).den : Int) = 1 from rfl, Int.one_mul]
  have hen : (c + c).num = c.num * (c.den : Int) + c.num * (c.den : Int) := rfl
  have hed : ((c + c).den : Int) = (c.den : Int) * (c.den : Int) := add_den_cast c c
  rw [hn, hd, hen, hed]
  generalize c.num = m; generalize (c.den : Int) = E
  show (2 * m) * (E * E) = (m * E + m * E) * E
  rw [show m * E + m * E = 2 * (m * E) by omega, Int.mul_assoc 2 m (E * E),
      Int.mul_assoc 2 (m * E) E, Int.mul_assoc m E E]

/-- `(u+v)·(u+v) ≃ (u·u + v·v) + (u·v + u·v)` — the AM–GM-ready regrouping.
`(uu+uv)+(uv+vv) ≃ (uu+uv)+(vv+uv) ≃ (uu+vv)+(uv+uv)`. -/
private theorem sq_add' (u v : Q') :
    ((u + v) * (u + v)).eqv ((u * u + v * v) + (u * v + u * v)) := by
  refine Q'.eqv_trans _ _ _ (sq_add u v) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (u * u + u * v) (u * v + v * v) (v * v + u * v)
      (Q'.add_comm_eqv (u * v) (v * v))) ?_
  exact Q'.add_swap_inner (u * u) (u * v) (v * v) (u * v)

/-- `(u + -v)·(u + -v) ≃ (u·u + v·v) + -(u·v + u·v)`. -/
private theorem sq_sub' (u v : Q') :
    ((u + -v) * (u + -v)).eqv ((u * u + v * v) + -(u * v + u * v)) := by
  refine Q'.eqv_trans _ _ _ (sq_sub u v) ?_
  -- (uu + -(uv)) + (-(uv) + vv) ≃ (uu + vv) + (-(uv) + -(uv)) ≃ (uu+vv) + -(uv+uv)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (u * u + -(u * v)) (-(u * v) + v * v) (v * v + -(u * v))
      (Q'.add_comm_eqv (-(u * v)) (v * v))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_swap_inner (u * u) (-(u * v)) (v * v) (-(u * v))) ?_
  exact Q'.add_eqv_congr_left (u * u + v * v) (-(u * v) + -(u * v)) (-(u * v + u * v))
    (Q'.eqv_symm (Q'.neg_add_eqv (u * v) (u * v)))

/-- `4·c ≃ (c+c)+(c+c)`. -/
private theorem four_mul_eqv (c : Q') :
    ((Q'.ofNat 4) * c).eqv ((c + c) + (c + c)) := by
  show ((Q'.ofNat 4) * c).num * (((c + c) + (c + c)).den : Int)
     = ((c + c) + (c + c)).num * (((Q'.ofNat 4) * c).den : Int)
  have hPnum : ((Q'.ofNat 4) * c).num = 4 * c.num := rfl
  have hPden : (((Q'.ofNat 4) * c).den : Int) = (c.den : Int) := by
    rw [mul_den_cast]
    show ((Q'.ofNat 4).den : Int) * (c.den : Int) = (c.den : Int)
    rw [show ((Q'.ofNat 4).den : Int) = 1 from rfl, Int.one_mul]
  have hccden : (((c + c)).den : Int) = (c.den : Int) * (c.den : Int) := add_den_cast c c
  have hQnum : ((c + c) + (c + c)).num
      = (c.num * (c.den : Int) + c.num * (c.den : Int)) * ((c.den : Int) * (c.den : Int))
        + (c.num * (c.den : Int) + c.num * (c.den : Int)) * ((c.den : Int) * (c.den : Int)) := by
    show (c + c).num * (((c + c)).den : Int) + (c + c).num * (((c + c)).den : Int)
       = (c.num * (c.den : Int) + c.num * (c.den : Int)) * ((c.den : Int) * (c.den : Int))
         + (c.num * (c.den : Int) + c.num * (c.den : Int)) * ((c.den : Int) * (c.den : Int))
    rw [show (c + c).num = c.num * (c.den : Int) + c.num * (c.den : Int) from rfl, hccden]
  have hQden : (((c + c) + (c + c)).den : Int)
      = ((c.den : Int) * (c.den : Int)) * ((c.den : Int) * (c.den : Int)) := by
    rw [add_den_cast (c + c) (c + c), hccden]
  rw [hPnum, hPden, hQnum, hQden]
  generalize c.num = n
  generalize (c.den : Int) = D
  -- (4n)·(D²·D²) = ((nD+nD)·D² + (nD+nD)·D²)·D ; both = 4·n·D⁴
  show (4 * n) * ((D * D) * (D * D))
     = ((n * D + n * D) * (D * D) + (n * D + n * D) * (D * D)) * D
  have e4 : (4 : Int) * n = n + n + (n + n) := by omega
  rw [e4]
  simp only [Int.add_mul, Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

/-! ### The cross term `x·(a/x) ≃ a` and the AM–GM invariant -/

/-- For `0 < x`, `x·(a·(1/x)) ≃ a`. -/
theorem x_mul_b_eqv (a x : Q') (hx : (0 : Q') < x) :
    (x * (a * recip x)).eqv a := by
  -- x*(a*r) ≃ (x*a)*r ≃ (a*x)*r ≃ a*(x*r) ≃ a*1 ≃ a
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv x a (recip x))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (x * a) (a * x) (recip x) (Q'.mul_comm_eqv x a)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a x (recip x)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a (x * recip x) 1 (Q'.mul_recip_eqv x hx)) ?_
  exact Q'.mul_one_eqv a

/-- `(x·b + x·b) ≃ a + a` when `x·b ≃ a`. -/
private theorem two_xb_eqv (a x : Q') (hx : (0 : Q') < x) :
    ((x * (a * recip x) + x * (a * recip x))).eqv (a + a) :=
  QPoly.q_add_congr (x_mul_b_eqv a x hx) (x_mul_b_eqv a x hx)

/-- **AM–GM invariant (scaled by 4):** `0 < a → 0 < x →
`(a+a)+(a+a) ≤ (x + a/x)·(x + a/x)`. -/
theorem four_a_le_sq (a x : Q') (hx : (0 : Q') < x) :
    ((a + a) + (a + a)) ≤ (x + a * recip x) * (x + a * recip x) := by
  -- abbreviations
  have hxb : (x * (a * recip x)).eqv a := x_mul_b_eqv a x hx
  -- (x-b)² ≥ 0  ⟹  (x·b + x·b) ≤ x·x + b·b
  have hsos : (0 : Q') ≤ (x + -(a * recip x)) * (x + -(a * recip x)) :=
    SumOfSquares.q_mul_self_nonneg _
  have hsub := sq_sub' x (a * recip x)
  -- 0 ≤ (x·x + b·b) + -(x·b + x·b)
  have h0 : (0 : Q') ≤ (x * x + (a * recip x) * (a * recip x))
      + -(x * (a * recip x) + x * (a * recip x)) :=
    Q'.le_trans' _ _ _ hsos (Q'.le_of_eqv hsub)
  -- ⟹ (x·b + x·b) ≤ x·x + b·b
  have hcross_le : (x * (a * recip x) + x * (a * recip x))
      ≤ (x * x + (a * recip x) * (a * recip x)) := by
    have := Q'.add_le_add_right _ _ (x * (a * recip x) + x * (a * recip x)) h0
    -- 0 + S ≤ (T + -S) + S ≃ T
    rw [Q'.zero_add'] at this
    refine Q'.le_trans' _ _ _ this (Q'.le_of_eqv ?_)
    -- (T + -S) + S ≃ T
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (x * x + (a * recip x) * (a * recip x))
      (-(x * (a * recip x) + x * (a * recip x)))
      (x * (a * recip x) + x * (a * recip x))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ 0
      (Q'.neg_add_self_eqv (x * (a * recip x) + x * (a * recip x)))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' _)
  -- (x+b)² ≃ (x·x + b·b) + (x·b + x·b) ≥ (x·b+x·b)+(x·b+x·b) ≃ (a+a)+(a+a)
  have hexp := sq_add' x (a * recip x)
  have hge : ((x * (a * recip x) + x * (a * recip x))
              + (x * (a * recip x) + x * (a * recip x)))
      ≤ (x + a * recip x) * (x + a * recip x) := by
    refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hexp)
    exact Q'.add_le_add_right _ _ _ hcross_le
  refine Q'.le_trans' _ _ _ ?_ hge
  -- (a+a)+(a+a) ≤ (x·b+x·b)+(x·b+x·b) via congruence (actually ≃)
  exact Q'.le_of_eqv (QPoly.q_add_congr (Q'.eqv_symm (two_xb_eqv a x hx))
    (Q'.eqv_symm (two_xb_eqv a x hx)))

/-! ### Monotonicity of a step (given the invariant `a ≤ x²`) -/

/-- `½·(x + x) ≃ x`. -/
private theorem half_double (x : Q') : (half * (x + x)).eqv x := by
  -- half*(x+x) ≃ half*((ofNat 2)*x) ≃ (half*ofNat2)*x ≃ 1*x ≃ x
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left half (x + x) ((Q'.ofNat 2) * x)
      (Q'.eqv_symm (by
        -- (ofNat 2)*x ≃ x + x
        show ((Q'.ofNat 2) * x).eqv (x + x)
        refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_refl (x + x))
        -- (ofNat2)*x ≃ x + x : prove via num/den
        show ((Q'.ofNat 2) * x).num * ((x + x).den : Int)
           = (x + x).num * (((Q'.ofNat 2) * x).den : Int)
        have hn : ((Q'.ofNat 2) * x).num = 2 * x.num := rfl
        have hd : (((Q'.ofNat 2) * x).den : Int) = (x.den : Int) := by
          rw [mul_den_cast]; show ((Q'.ofNat 2).den : Int) * (x.den : Int) = (x.den : Int)
          rw [show ((Q'.ofNat 2).den : Int) = 1 from rfl, Int.one_mul]
        have hxn : (x + x).num = x.num * (x.den : Int) + x.num * (x.den : Int) := rfl
        have hxd : ((x + x).den : Int) = (x.den : Int) * (x.den : Int) := add_den_cast x x
        rw [hn, hd, hxn, hxd]
        generalize x.num = m; generalize (x.den : Int) = E
        show (2 * m) * (E * E) = (m * E + m * E) * E
        rw [show m * E + m * E = 2 * (m * E) by omega, Int.mul_assoc 2 m (E * E),
            Int.mul_assoc 2 (m * E) E, Int.mul_assoc m E E]))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv half (Q'.ofNat 2) x)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (half * Q'.ofNat 2) 1 x (by decide)) ?_
  exact Q'.one_mul_eqv x

/-- `b ≤ x` from the invariant `a ≤ x²` (here `b = a/x`). -/
theorem b_le_x (a x : Q') (hx : (0 : Q') < x) (hinv : a ≤ x * x) :
    a * recip x ≤ x := by
  have hr : (0 : Q') ≤ recip x := Q'.le_of_lt (Q'.recip_pos x)
  -- a*r ≤ (x*x)*r ≃ x*(x*r) ≃ x
  have h1 : a * recip x ≤ (x * x) * recip x :=
    Q'.mul_le_mul_of_nonneg_right a (x * x) (recip x) hinv hr
  refine Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv x x (recip x)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left x (x * recip x) 1
    (Q'.mul_recip_eqv x hx)) ?_
  exact Q'.mul_one_eqv x

/-- **Monotonicity:** `0 < x → a ≤ x² → heronStep a x ≤ x`. -/
theorem heronStep_le (a x : Q') (hx : (0 : Q') < x) (hinv : a ≤ x * x) :
    heronStep a x ≤ x := by
  show half * (x + a * recip x) ≤ x
  -- half*(x+b) ≤ half*(x+x) ≃ x
  have hxb : x + a * recip x ≤ x + x :=
    Q'.add_le_add_left x (a * recip x) x (b_le_x a x hx hinv)
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left (x + a * recip x) (x + x) half hxb (by decide)) ?_
  exact Q'.le_of_eqv (half_double x)

/-! ### The post-step invariant `a ≤ s²` (holds for any positive `x`) -/

/-- `0 < x → a ≤ (heronStep a x)²`.  AM–GM: a Heron step never undershoots. -/
theorem a_le_heronStep_sq (a x : Q') (hx : (0 : Q') < x) :
    a ≤ heronStep a x * heronStep a x := by
  -- four*a ≤ four*(s*s), cancel four
  have hfa : (Q'.ofNat 4) * a ≤ (Q'.ofNat 4) * (heronStep a x * heronStep a x) := by
    -- four*a ≃ (a+a)+(a+a) ≤ (x+b)² ≃ four*(s*s)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (four_mul_eqv a)) ?_
    refine Q'.le_trans' _ _ _ (four_a_le_sq a x hx) ?_
    exact Q'.ge_of_eqv (four_mul_heronStep_sq a x)
  exact Q'.le_of_mul_le_mul_left hfa (by decide)

/-! ### `b² ≤ a` (the geometric-decay ingredient), then `4·e_{n+1} ≤ e_n`

`e x := x·x − a`.  With `b = a/x`, `4·(s² − a) = (x − b)²` and
`(x − b)² ≤ x² − a` reduces to `b² ≤ a`, itself reducing (×x²>0) to
`a·a ≤ a·x²` i.e. the invariant `a ≤ x²`. -/

/-- `b² ≤ a` from the invariant `a ≤ x²` (`b = a/x`). -/
theorem b_sq_le_a (a x : Q') (hx : (0 : Q') < x) (ha : (0 : Q') ≤ a)
    (hinv : a ≤ x * x) :
    (a * recip x) * (a * recip x) ≤ a := by
  -- cancel x*x > 0 : (b*b)*(x*x) ≃ a*a ≤ a*(x*x) ≃ a*(x*x)
  have hxx : (0 : Q') < x * x := Q'.mul_pos hx hx
  apply Q'.le_of_mul_le_mul_left (c := x * x) _ hxx
  -- (x*x)*(b*b) ≤ (x*x)*a
  have hxb : (x * (a * recip x)).eqv a := x_mul_b_eqv a x hx
  -- (x*x)*(b*b) ≃ (x*b)*(x*b) ≃ a*a
  have hL : ((x * x) * ((a * recip x) * (a * recip x))).eqv
      ((x * (a * recip x)) * (x * (a * recip x))) := by
    -- (x*x)*(b*b) ≃ (x*b)*(x*b) : interchange middle
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv x x ((a*recip x)*(a*recip x))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left x _ (((a*recip x)) * (x * (a*recip x))) ?_) ?_
    · -- x*(b*b) ≃ b*(x*b)
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv x (a*recip x) (a*recip x))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (x*(a*recip x)) ((a*recip x)*x) (a*recip x)
          (Q'.mul_comm_eqv x (a*recip x))) ?_
      exact Q'.mul_assoc_eqv (a*recip x) x (a*recip x)
    · exact Q'.eqv_symm (Q'.mul_assoc_eqv x (a*recip x) (x*(a*recip x)))
  have hLa : ((x * x) * ((a * recip x) * (a * recip x))).eqv (a * a) :=
    Q'.eqv_trans _ _ _ hL
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (x*(a*recip x)) a (x*(a*recip x)) hxb)
        (Q'.mul_eqv_congr_left a (x*(a*recip x)) a hxb))
  -- a*a ≤ (x*x)*a , and (x*x)*(b*b) ≃ a*a ; goal (x*x)*(b*b) ≤ (x*x)*a
  have haa : a * a ≤ (x * x) * a :=
    Q'.mul_le_mul_of_nonneg_right a (x * x) a hinv ha
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLa) ?_
  exact haa

/-! ### Sequence-level invariants -/

/-- Every iterate (from index 0) satisfies the AM–GM invariant `a ≤ x_n²`.
For `n = 0`, `(a+1)² = a² + 2a + 1 ≥ a`. -/
theorem heronSeq_sq_ge (a : Q') (ha : (0 : Q') < a) :
    ∀ n, a ≤ heronSeq a n * heronSeq a n
  | 0 => by
      have ha' : (0 : Q') ≤ a := Q'.le_of_lt ha
      show a ≤ (a + 1) * (a + 1)
      -- (a+1)² = a*a + a + a + 1 ≥ a
      refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv (sq_add a 1))
      -- a ≤ (a*a + a*1) + (a*1 + 1*1)
      have e1 : (a * (1 : Q')).eqv a := Q'.mul_one_eqv a
      -- a ≤ 0 + (a + (0+0))  ... simpler: a ≤ (a*a + a) + (a + 1)
      have hle : a ≤ (a * a + a) + (a + (1 : Q')) := by
        refine Q'.le_trans' _ _ _ ?_
          (Q'.add_le_self_of_nonneg (a * a + a) (a + 1) ?_)
        · -- a ≤ a*a + a
          refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_zero_add_eqv a))) ?_
          exact Q'.add_le_add_right 0 (a * a) a (SumOfSquares.q_mul_self_nonneg a)
        · exact Q'.le_trans' _ _ _ ha' (Q'.add_le_self_of_nonneg a 1 (by decide))
      refine Q'.le_trans' _ _ _ hle (Q'.le_of_eqv (QPoly.q_add_congr ?_ ?_))
      · exact Q'.add_eqv_congr_left (a * a) a (a * 1) (Q'.eqv_symm e1)
      · exact QPoly.q_add_congr (Q'.eqv_symm e1) (Q'.eqv_symm (Q'.mul_one_eqv 1))
  | n + 1 => by
      show a ≤ heronStep a (heronSeq a n) * heronStep a (heronSeq a n)
      exact a_le_heronStep_sq a (heronSeq a n) (heronSeq_pos ha n)

/-- Monotone decreasing: `x_{n+1} ≤ x_n`. -/
theorem heronSeq_antitone_step (a : Q') (ha : (0 : Q') < a) (n : Nat) :
    heronSeq a (n + 1) ≤ heronSeq a n := by
  show heronStep a (heronSeq a n) ≤ heronSeq a n
  exact heronStep_le a (heronSeq a n) (heronSeq_pos ha n) (heronSeq_sq_ge a ha n)

/-- `x_{n+d} ≤ x_n` for every `d` (decreasing). -/
theorem heronSeq_antitone_add (a : Q') (ha : (0 : Q') < a) (n : Nat) :
    ∀ d, heronSeq a (n + d) ≤ heronSeq a n
  | 0 => Q'.le_refl' _
  | d + 1 => by
      refine Q'.le_trans' _ _ _ ?_ (heronSeq_antitone_add a ha n d)
      rw [show n + (d + 1) = (n + d) + 1 from by omega]
      exact heronSeq_antitone_step a ha (n + d)

/-- Monotone decreasing globally: `n ≤ m → x_m ≤ x_n`. -/
theorem heronSeq_antitone (a : Q') (ha : (0 : Q') < a) {n m : Nat} (h : n ≤ m) :
    heronSeq a m ≤ heronSeq a n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact heronSeq_antitone_add a ha n d

/-! ### Uniform rational lower bound `L ≤ x_n` -/

/-- Square-root monotonicity on the positive cone: `0 < u → 0 ≤ v → v² ≤ u² → v ≤ u`.
(Contrapositive of `u < v ⟹ u² < v²`.) -/
theorem le_of_sq_le_sq {u v : Q'} (hu : (0 : Q') < u) (hv : (0 : Q') ≤ v)
    (h : v * v ≤ u * u) : v ≤ u := by
  show v.num * (u.den : Int) ≤ u.num * (v.den : Int)
  refine Int.not_lt.mp (fun hlt0 => ?_)
  have hlt : u < v := hlt0
  -- u < v, both ≥0 ⟹ u*u < v*v, contradiction
  have huv : u * u < v * v := by
    have h1 : u * u ≤ v * u := Q'.mul_le_mul_of_nonneg_right u v u (Q'.le_of_lt hlt)
      (Q'.le_of_lt hu)
    -- v*u < v*v since u<v and v>0
    have hvpos : (0 : Q') < v := by
      have hun : 0 < u.num := num_pos_of_pos hu
      have huvn : u.num * (v.den : Int) < v.num * (u.den : Int) := hlt
      have h1 : 0 < u.num * (v.den : Int) :=
        Int.mul_pos hun (by exact_mod_cast v.den_pos)
      have h2 : 0 < v.num * (u.den : Int) := Int.lt_trans h1 huvn
      show (0 : Int) * (v.den : Int) < v.num * (1 : Int)
      rw [Int.zero_mul, Int.mul_one]
      rcases Int.lt_or_le 0 v.num with h | h
      · exact h
      · exfalso
        have : v.num * (u.den : Int) ≤ 0 :=
          Int.mul_nonpos_of_nonpos_of_nonneg h (by exact_mod_cast Nat.zero_le _)
        omega
    have h2 : v * u < v * v := by
      show (v * u).num * ((v * v).den : Int) < (v * v).num * ((v * u).den : Int)
      rw [show (v * u).num = v.num * u.num from rfl,
          show (v * v).num = v.num * v.num from rfl,
          mul_den_cast v v, mul_den_cast v u]
      have hvn : 0 < v.num := num_pos_of_pos hvpos
      have huvn : u.num * (v.den : Int) < v.num * (u.den : Int) := hlt
      -- (v.num*u.num)*(v.den*v.den) < (v.num*v.num)*(v.den*u.den)
      have e1 : (v.num * u.num) * ((v.den : Int) * (v.den : Int))
              = (v.num * (v.den : Int)) * (u.num * (v.den : Int)) := by
        rw [Int.mul_assoc, Int.mul_assoc]; congr 1
        rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm u.num (v.den : Int)]
      have e2 : (v.num * v.num) * ((v.den : Int) * (u.den : Int))
              = (v.num * (v.den : Int)) * (v.num * (u.den : Int)) := by
        rw [Int.mul_assoc, Int.mul_assoc]; congr 1
        rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm v.num (v.den : Int)]
      rw [e1, e2]
      exact Int.mul_lt_mul_of_pos_left huvn
        (Int.mul_pos hvn (by exact_mod_cast v.den_pos))
    exact Q'.lt_of_le_of_lt h1 h2
  exact absurd h (Int.not_le.mpr huv)

/-- `L ≤ x_n` for any positive `L` with `L² ≤ a` (so `L² ≤ a ≤ x_n²`). -/
theorem heronSeq_lb (a L : Q') (ha : (0 : Q') < a) (hLpos : (0 : Q') < L)
    (hLa : L * L ≤ a) (n : Nat) : L ≤ heronSeq a n :=
  le_of_sq_le_sq (heronSeq_pos ha n) (Q'.le_of_lt hLpos)
    (Q'.le_trans' _ _ _ hLa (heronSeq_sq_ge a ha n))

/-! ### Geometric error decay

`errAt a n := x_n·x_n + -a ≥ 0`.  We prove `4·errAt(n+1) ≤ errAt n`, hence
`errAt(n+1) ≤ ½·errAt n` and `errAt n ≤ errAt 0 · ½ⁿ`. -/

/-- The (nonnegative) error `x_n² − a`. -/
def errAt (a : Q') (n : Nat) : Q' := heronSeq a n * heronSeq a n + -a

/-- `0 ≤ errAt a n`. -/
theorem errAt_nonneg (a : Q') (ha : (0 : Q') < a) (n : Nat) : (0 : Q') ≤ errAt a n := by
  show (0 : Q') ≤ heronSeq a n * heronSeq a n + -a
  have hge := heronSeq_sq_ge a ha n   -- a ≤ x_n²
  -- 0 ≤ x_n² + -a
  have := Q'.add_le_add_right a (heronSeq a n * heronSeq a n) (-a) hge
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.add_neg_self_eqv a))) this

/-- `4·s² ≤ x² + (a+a+a)` (the geometric-step kernel, additive form). -/
theorem four_sq_le (a x : Q') (hx : (0 : Q') < x) (ha : (0 : Q') ≤ a)
    (hinv : a ≤ x * x) :
    (Q'.ofNat 4) * (heronStep a x * heronStep a x)
      ≤ x * x + ((a + a) + a) := by
  -- 4s² ≃ (x+b)² ≃ (x²+b²)+(a+a) ≤ (x²+a)+(a+a) ≃ x²+((a+a)+a)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (four_mul_heronStep_sq a x)) ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (sq_add' x (a * recip x))) ?_
  -- (x²+b²)+(x·b+x·b) ≃ (x²+b²)+(a+a)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (Q'.add_eqv_congr_left (x * x + (a * recip x) * (a * recip x)) _ (a + a)
      (two_xb_eqv a x hx))) ?_
  -- (x²+b²)+(a+a) ≤ (x²+a)+(a+a)
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_right (x * x + (a * recip x) * (a * recip x)) (x * x + a) (a + a)
      (Q'.add_le_add_left (x * x) ((a * recip x) * (a * recip x)) a
        (b_sq_le_a a x hx ha hinv))) ?_
  -- (x²+a)+(a+a) ≃ x²+((a+a)+a) ≃ x²+(a+(a+a)) ... just reassociate
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (x * x) a (a + a)) ?_
  exact Q'.add_eqv_congr_left (x * x) (a + (a + a)) ((a + a) + a)
    (Q'.eqv_symm (Q'.add_assoc_eqv a a a))

/-- `(ofNat 4)·c ≃ ((c+c)+(c+c))` is `four_mul_eqv`; here `(ofNat 4)·(-a) ≃ -((a+a)+(a+a))`. -/
private theorem four_mul_neg (a : Q') :
    ((Q'.ofNat 4) * (-a)).eqv (-((a + a) + (a + a))) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (Q'.ofNat 4) a)
    (Q'.neg_eqv_congr _ _ (four_mul_eqv a))

/-- **Geometric kernel:** `4·errAt(n+1) ≤ errAt n`. -/
theorem four_errAt_succ_le (a : Q') (ha : (0 : Q') < a) (n : Nat) :
    (Q'.ofNat 4) * errAt a (n + 1) ≤ errAt a n := by
  have ha' : (0 : Q') ≤ a := Q'.le_of_lt ha
  have hx : (0 : Q') < heronSeq a n := heronSeq_pos ha n
  have hinv : a ≤ heronSeq a n * heronSeq a n := heronSeq_sq_ge a ha n
  -- errAt (n+1) = s*s + -a where s = heronStep a x_n
  show (Q'.ofNat 4) * (heronStep a (heronSeq a n) * heronStep a (heronSeq a n) + -a)
      ≤ heronSeq a n * heronSeq a n + -a
  -- 4*(s² + -a) ≃ 4*s² + 4*(-a)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv (Q'.ofNat 4)
    (heronStep a (heronSeq a n) * heronStep a (heronSeq a n)) (-a))) ?_
  -- 4*s² + 4*(-a) ≤ (x²+(a+a+a)) + 4*(-a)
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ ((Q'.ofNat 4) * (-a))
      (four_sq_le a (heronSeq a n) hx ha' hinv)) ?_
  -- (x²+(a+a+a)) + 4*(-a) ≃ (x²+(a+a+a)) + -((a+a)+(a+a)) ≃ x² + -a
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (heronSeq a n * heronSeq a n + ((a + a) + a))
      ((Q'.ofNat 4) * (-a)) (-((a + a) + (a + a))) (four_mul_neg a)) ?_
  -- (x² + 3a) + -(4a) ≃ x² + -a   [3a + -(4a) ≃ -a]
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (heronSeq a n * heronSeq a n) ((a + a) + a) (-((a + a) + (a + a)))) ?_
  refine Q'.add_eqv_congr_left (heronSeq a n * heronSeq a n) _ (-a) ?_
  -- ((a+a)+a) + -((a+a)+(a+a)) ≃ -a , writing T := (a+a)+a:
  -- (a+a)+(a+a) ≃ T + a, so -(...) ≃ -(T+a) ≃ -T + -a, then T + (-T + -a) ≃ -a.
  have hTa : ((a + a) + (a + a)).eqv (((a + a) + a) + a) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (a + a) a a)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left ((a + a) + a) (-((a + a) + (a + a))) (-(((a + a) + a) + a))
      (Q'.neg_eqv_congr _ _ hTa)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left ((a + a) + a) (-(((a + a) + a) + a)) (-((a + a) + a) + -a)
      (Q'.neg_add_eqv ((a + a) + a) a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv ((a + a) + a) (-((a + a) + a)) (-a))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ 0 (-a) (Q'.add_neg_self_eqv ((a + a) + a))) ?_
  exact QPoly.q_zero_add_eqv (-a)

/-- `errAt(n+1) ≤ ½·errAt n`. -/
theorem errAt_succ_le_half (a : Q') (ha : (0 : Q') < a) (n : Nat) :
    errAt a (n + 1) ≤ half * errAt a n := by
  have hnn : (0 : Q') ≤ errAt a (n + 1) := errAt_nonneg a ha (n + 1)
  -- errAt(n+1) ≤ errAt(n+1) + errAt(n+1) ≃ half*(4*errAt(n+1)) ≤ half*errAt n
  have hdbl : errAt a (n + 1) ≤ errAt a (n + 1) + errAt a (n + 1) :=
    Q'.add_le_self_of_nonneg (errAt a (n + 1)) (errAt a (n + 1)) hnn
  refine Q'.le_trans' _ _ _ hdbl ?_
  -- errAt(n+1)+errAt(n+1) ≃ half*(4*errAt(n+1))
  have heq : (errAt a (n + 1) + errAt a (n + 1)).eqv
      (half * ((Q'.ofNat 4) * errAt a (n + 1))) := by
    -- half*(4*e) ≃ (half*4)*e ≃ 2*e ≃ e+e
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv half (Q'.ofNat 4) (errAt a (n+1)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (half * Q'.ofNat 4) (Q'.ofNat 2) (errAt a (n+1)) (by decide)) ?_
    -- 2*e ≃ e+e (direct num proof)
    exact two_mul_eqv (errAt a (n + 1))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ half (four_errAt_succ_le a ha n) (by decide)

/-- `errAt n ≤ errAt 0 · ½ⁿ`. -/
theorem errAt_le_geom (a : Q') (ha : (0 : Q') < a) :
    ∀ n, errAt a n ≤ errAt a 0 * half ^ n
  | 0 => by
      show errAt a 0 ≤ errAt a 0 * half ^ 0
      rw [Q'.pow_zero]
      exact Q'.ge_of_eqv (Q'.mul_one_eqv (errAt a 0))
  | n + 1 => by
      -- errAt(n+1) ≤ half*errAt n ≤ half*(errAt0*half^n) ≃ errAt0*half^(n+1)
      refine Q'.le_trans' _ _ _ (errAt_succ_le_half a ha n) ?_
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ half (errAt_le_geom a ha n) (by decide)) ?_
      -- half*(errAt0*half^n) ≃ errAt0*(half*half^n) = errAt0*half^(n+1)
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv half (errAt a 0) (half ^ n))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (half * errAt a 0) (errAt a 0 * half) (half ^ n)
          (Q'.mul_comm_eqv half (errAt a 0))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (errAt a 0) half (half ^ n)) ?_
      exact Q'.eqv_refl _

/-! ### The Cauchy gap bound -/

/-- Difference of squares: `(u + -v)·(u + v) ≃ u·u + -(v·v)`. -/
private theorem diff_sq (u v : Q') :
    ((u + -v) * (u + v)).eqv (u * u + -(v * v)) := by
  -- (u + -v)*(u+v) ≃ u*(u+v) + (-v)*(u+v) ≃ (uu+uv) + (-(vu) + -(vv))
  refine Q'.eqv_trans _ _ _ (QPoly.q_add_mul u (-v) (u + v)) ?_
  refine Q'.eqv_trans _ _ _
    (QPoly.q_add_congr (Q'.mul_add_eqv u u v) (Q'.mul_add_eqv (-v) u v)) ?_
  -- (uu + uv) + ((-v)*u + (-v)*v) ; (-v)*u ≃ -(vu) ≃ -(uv); (-v)*v ≃ -(vv)
  refine Q'.eqv_trans _ _ _
    (QPoly.q_add_congr (Q'.eqv_refl (u * u + u * v))
      (QPoly.q_add_congr
        (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv v u)
          (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv v u)))
        (Q'.neg_mul_eqv v v))) ?_
  -- (uu + uv) + (-(uv) + -(vv)) ≃ (uu + uv) + (-(vv) + -(uv)) ≃ (uu + -(vv)) + (uv + -(uv))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (u * u + u * v) (-(u * v) + -(v * v)) (-(v * v) + -(u * v))
      (Q'.add_comm_eqv (-(u * v)) (-(v * v)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_swap_inner (u * u) (u * v) (-(v * v)) (-(u * v))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (u * u + -(v * v)) (u * v + -(u * v)) 0
      (Q'.add_neg_self_eqv (u * v))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' (u * u + -(v * v)))

/-- `errAt n + -(errAt m) ≃ x_n² + -(x_m²)`. -/
private theorem errAt_diff (a : Q') (n m : Nat) :
    (errAt a n + -(errAt a m)).eqv
      (heronSeq a n * heronSeq a n + -(heronSeq a m * heronSeq a m)) := by
  show ((heronSeq a n * heronSeq a n + -a) + -(heronSeq a m * heronSeq a m + -a)).eqv
       (heronSeq a n * heronSeq a n + -(heronSeq a m * heronSeq a m))
  -- -(P + -a) ≃ -P + a
  refine QPoly.q_eqv_of_sub_zero ?_
  -- reduce ((Xn + -a) + -(Xm + -a)) + -(Xn + -Xm) ≃ 0 via num
  show ((((heronSeq a n * heronSeq a n + -a) + -(heronSeq a m * heronSeq a m + -a))
        + -(heronSeq a n * heronSeq a n + -(heronSeq a m * heronSeq a m)))).eqv 0
  -- Let P := Xn, Q := Xm.  ((P + -a) + -(Q + -a)) + -(P + -Q) ≃ 0.
  generalize heronSeq a n * heronSeq a n = P
  generalize heronSeq a m * heronSeq a m = R
  -- (P + -a) + -(R + -a) ≃ P + -R  : show difference ≃ 0
  -- -(R + -a) ≃ -R + a ; (P + -a) + (-R + a) ≃ (P + -R) + (-a + a) ≃ (P + -R) + 0 ≃ P + -R
  have e1 : ((P + -a) + -(R + -a)).eqv (P + -R) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (P + -a) (-(R + -a)) (-R + -(-a)) (Q'.neg_add_eqv R (-a))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (P + -a) (-R + -(-a)) (-R + a)
        (Q'.add_eqv_congr_left (-R) (-(-a)) a (Q'.neg_neg_eqv a))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_swap_inner P (-a) (-R) a) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (P + -R) (-a + a) 0 (Q'.neg_add_self_eqv a)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' (P + -R))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((P + -a) + -(R + -a)) (P + -R) (-(P + -R)) e1) ?_
  exact Q'.add_neg_self_eqv (P + -R)

/-- `b ≤ a → 0 ≤ a + -b`. -/
private theorem nonneg_sub_of_le {a b : Q'} (h : b ≤ a) : (0 : Q') ≤ a + -b := by
  have := Q'.add_le_add_right b a (-b) h
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv b)) this

/-- **Gap bound:** for `n ≤ m`, `(x_n − x_m)·(L+L) ≤ errAt n`. -/
theorem gap_bound (a L : Q') (ha : (0 : Q') < a) (hLpos : (0 : Q') < L)
    (hLa : L * L ≤ a) {n m : Nat} (hnm : n ≤ m) :
    (heronSeq a n + -heronSeq a m) * (L + L) ≤ errAt a n := by
  -- 0 ≤ x_n - x_m (antitone)
  have hdnn : (0 : Q') ≤ heronSeq a n + -heronSeq a m :=
    nonneg_sub_of_le (heronSeq_antitone a ha hnm)
  -- L+L ≤ x_n + x_m
  have hLLsum : L + L ≤ heronSeq a n + heronSeq a m :=
    Q'.add_le_add (heronSeq_lb a L ha hLpos hLa n) (heronSeq_lb a L ha hLpos hLa m)
  -- (x_n - x_m)*(L+L) ≤ (x_n - x_m)*(x_n+x_m) = x_n² - x_m² = errAt n - errAt m ≤ errAt n
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left (L + L) (heronSeq a n + heronSeq a m)
      (heronSeq a n + -heronSeq a m) hLLsum hdnn) ?_
  -- (x_n - x_m)*(x_n+x_m) ≃ x_n² + -(x_m²) ≃ errAt n + -(errAt m) ≤ errAt n
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (diff_sq (heronSeq a n) (heronSeq a m))) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (errAt_diff a n m))) ?_
  -- errAt n + -(errAt m) ≤ errAt n  (since errAt m ≥ 0 ⟹ -errAt m ≤ 0)
  have hngm : -errAt a m ≤ (0 : Q') := by
    have h := Q'.neg_le_neg (errAt_nonneg a ha m)   -- -(errAt m) ≤ -0
    refine Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by decide : ((-(0:Q'))).eqv 0))
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_left (errAt a n) (-errAt a m) 0 hngm) (Q'.le_of_eqv ?_)
  exact Q'.eqv_of_eq (Q'.add_zero' (errAt a n))

/-- `errAt (n+d) ≤ errAt n`. -/
theorem errAt_antitone_add (a : Q') (ha : (0 : Q') < a) (n : Nat) :
    ∀ d, errAt a (n + d) ≤ errAt a n
  | 0 => Q'.le_refl' _
  | d + 1 => by
      refine Q'.le_trans' _ _ _ ?_ (errAt_antitone_add a ha n d)
      rw [show n + (d + 1) = (n + d) + 1 from by omega]
      refine Q'.le_trans' _ _ _ (errAt_succ_le_half a ha (n + d)) ?_
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right half 1 (errAt a (n + d)) (by decide)
          (errAt_nonneg a ha (n + d))) ?_
      exact Q'.le_of_eqv (Q'.one_mul_eqv (errAt a (n + d)))

/-- `errAt` is decreasing: `n ≤ m → errAt m ≤ errAt n`. -/
theorem errAt_antitone (a : Q') (ha : (0 : Q') < a) {n m : Nat} (h : n ≤ m) :
    errAt a m ≤ errAt a n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact errAt_antitone_add a ha n d

/-- From `(c)·(L+L) ≤ (L+L)·ε`, get `c ≤ ε` (cancel positive `L+L`). -/
private theorem cancel_LL {c L ε : Q'} (hLpos : (0 : Q') < L)
    (h : c * (L + L) ≤ (L + L) * ε) : c ≤ ε := by
  have hLL : (0 : Q') < L + L := Q'.add_pos hLpos hLpos
  refine Q'.le_of_mul_le_mul_left (c := L + L) ?_ hLL
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv (L + L) c)) h

/-- From `x_q − x_p ≤ ε`, get `x_q ≤ x_p + ε`. -/
private theorem le_add_of_sub_le {p q ε : Q'} (h : q + -p ≤ ε) : q ≤ p + ε := by
  have := Q'.add_le_add_right (q + -p) ε p h
  -- (q + -p) + p ≃ q ; ε + p ≃ p + ε
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) (Q'.le_trans' _ _ _ this (Q'.le_of_eqv ?_))
  · -- ((q + -p) + p) ≃ q
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv q (-p) p) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left q (-p + p) 0
      (Q'.neg_add_self_eqv p)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' q)
  · exact Q'.add_comm_eqv ε p

/-! ### The constructive square root as a `CReal`

`sqrtFrom a L _ _ _` is `√a` for a positive rational `a` with a positive
rational lower-bound witness `L` (`0 < L`, `L² ≤ a`).  Its approximations are
the Heron iterates; the Cauchy modulus is **Type-level data** (`sqrtModulus`),
a function `ε ↦ N` built from `exists_mul_le` and `pow_half_le`. -/

/-- A **Type-level** division-free modulus `δ > 0` with `B·δ ≤ ε`, returned as
`Σ` data (AGENTS.md Rule 8.3 — the `Prop`-level `CReal.exists_mul_le` would
hide the witness behind `Classical.choose`).  `δ = ε.num / (ε.den·(⌊B⌋+1))`. -/
def mulModulus (B ε : Q') (hB : (0 : Q') ≤ B) (hε : (0 : Q') < ε) :
    Σ' δ : Q', (0 : Q') < δ ∧ B * δ ≤ ε := by
  have hεn : 0 < ε.num := Q'.num_pos_of_pos hε
  have hden : 0 < ε.den * (B.num.toNat + 1) := Nat.mul_pos ε.den_pos (Nat.succ_pos _)
  refine ⟨Q'.mkPos ε.num (ε.den * (B.num.toNat + 1)) hden, ?_, ?_⟩
  · -- positive
    show (0 : Int) * _ < (Q'.mkPos ε.num (ε.den * (B.num.toNat + 1)) hden).num * (1 : Int)
    rw [Int.zero_mul, Int.mul_one, Q'.mkPos_num]; exact hεn
  · -- B·δ ≤ ε  : same computation as `exists_mul_le`
    have hBM : B ≤ Q'.ofNat (B.num.toNat + 1) :=
      Q'.le_trans' B (Q'.ofNat B.num.toNat) (Q'.ofNat (B.num.toNat + 1))
        (RatNat.le_ofNat_toNat B hB) (ofNat_le_ofNat (by omega))
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right B (Q'.ofNat (B.num.toNat + 1)) _ hBM
        (Q'.le_of_lt (by
          show (0 : Int) * _ < (Q'.mkPos ε.num (ε.den * (B.num.toNat + 1)) hden).num * (1 : Int)
          rw [Int.zero_mul, Int.mul_one, Q'.mkPos_num]; exact hεn)))
      (Q'.le_of_eqv (CReal.ofNatMul_mkPos_eqv (B.num.toNat + 1) ε hden))

/-- The Cauchy modulus, as Type-level data (AGENTS.md Rule 8.3): given a
tolerance `ε > 0`, return a stage `N` past which the Heron iterates agree to
within `ε`.  `N` is the denominator of the `δ` solving `errAt 0 · δ ≤ (L+L)·ε`. -/
def sqrtModulus (a L : Q') (ha : (0 : Q') < a) (hLpos : (0 : Q') < L)
    (ε : Q') (hε : (0 : Q') < ε) : Nat :=
  (mulModulus (errAt a 0) ((L + L) * ε) (errAt_nonneg a ha 0)
    (Q'.mul_pos (Q'.add_pos hLpos hLpos) hε)).1.den

/-- The modulus works: `errAt (sqrtModulus …) ≤ (L+L)·ε`. -/
theorem errAt_modulus_le (a L : Q') (ha : (0 : Q') < a) (hLpos : (0 : Q') < L)
    (ε : Q') (hε : (0 : Q') < ε) :
    errAt a (sqrtModulus a L ha hLpos ε hε) ≤ (L + L) * ε := by
  -- the δ data
  let md := mulModulus (errAt a 0) ((L + L) * ε) (errAt_nonneg a ha 0)
      (Q'.mul_pos (Q'.add_pos hLpos hLpos) hε)
  have hδpos : (0 : Q') < md.1 := md.2.1
  have hδle : errAt a 0 * md.1 ≤ (L + L) * ε := md.2.2
  show errAt a md.1.den ≤ (L + L) * ε
  -- errAt δ.den ≤ errAt0*half^(δ.den) ≤ errAt0*δ ≤ (L+L)*ε
  refine Q'.le_trans' _ _ _ (errAt_le_geom a ha md.1.den) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left (half ^ md.1.den) md.1 (errAt a 0)
      (HalfPow.pow_half_le md.1 hδpos) (errAt_nonneg a ha 0)) ?_
  exact hδle

/-- **Cauchy direction:** for `N ≤ q ≤ p` (with `N = sqrtModulus`), `x_q ≤ x_p + ε`. -/
theorem sqrt_cauchy_dir (a L : Q') (ha : (0 : Q') < a) (hLpos : (0 : Q') < L)
    (hLa : L * L ≤ a) (ε : Q') (hε : (0 : Q') < ε)
    {p q : Nat} (hNq : sqrtModulus a L ha hLpos ε hε ≤ q) (hqp : q ≤ p) :
    heronSeq a q ≤ heronSeq a p + ε := by
  -- (x_q - x_p)*(L+L) ≤ errAt q ≤ errAt N ≤ (L+L)*ε
  have hgap : (heronSeq a q + -heronSeq a p) * (L + L) ≤ errAt a q :=
    gap_bound a L ha hLpos hLa hqp
  have herr : errAt a q ≤ (L + L) * ε :=
    Q'.le_trans' _ _ _ (errAt_antitone a ha hNq) (errAt_modulus_le a L ha hLpos ε hε)
  have hmul : (heronSeq a q + -heronSeq a p) * (L + L) ≤ (L + L) * ε :=
    Q'.le_trans' _ _ _ hgap herr
  -- cancel (L+L) : x_q - x_p ≤ ε ; then x_q ≤ x_p + ε
  exact le_add_of_sub_le (cancel_LL hLpos hmul)

/-- **The constructive square root** `√a` as a `CReal`, for a positive rational
`a` with a positive rational lower-bound witness `L` (`0 < L`, `L² ≤ a`).
Approximations are the Heron iterates; the Cauchy modulus is `sqrtModulus`. -/
def sqrtFrom (a L : Q') (ha : (0 : Q') < a) (hLpos : (0 : Q') < L)
    (hLa : L * L ≤ a) : CReal where
  approx n := heronSeq a n
  cauchy := by
    intro ε hε
    refine ⟨sqrtModulus a L ha hLpos ε hε, fun p q hp hq => ?_⟩
    -- both directions, by casing on the order of p, q
    rcases Nat.le_total q p with hqp | hpq
    · -- q ≤ p : x_p ≤ x_q (antitone) ≤ x_q + ε ; x_q ≤ x_p + ε by cauchy_dir
      refine ⟨?_, sqrt_cauchy_dir a L ha hLpos hLa ε hε hq hqp⟩
      exact Q'.le_trans' _ _ _ (heronSeq_antitone a ha hqp)
        (Q'.add_le_self_of_nonneg (heronSeq a q) ε (Q'.le_of_lt hε))
    · -- p ≤ q : symmetric
      refine ⟨sqrt_cauchy_dir a L ha hLpos hLa ε hε hp hpq, ?_⟩
      exact Q'.le_trans' _ _ _ (heronSeq_antitone a ha hpq)
        (Q'.add_le_self_of_nonneg (heronSeq a p) ε (Q'.le_of_lt hε))

@[simp] theorem sqrtFrom_approx (a L : Q') (ha : (0 : Q') < a) (hLpos : (0 : Q') < L)
    (hLa : L * L ≤ a) (n : Nat) :
    (sqrtFrom a L ha hLpos hLa).approx n = heronSeq a n := rfl

/-! ### Positivity of `√a` -/

/-- `√a` is strictly positive (witnessed by the rational lower bound `L`). -/
theorem sqrtFrom_isPositive (a L : Q') (ha : (0 : Q') < a) (hLpos : (0 : Q') < L)
    (hLa : L * L ≤ a) : CReal.IsPositive (sqrtFrom a L ha hLpos hLa) :=
  CReal.isPositive_of_approx_ge hLpos (fun n => heronSeq_lb a L ha hLpos hLa n)

/-! ### The defining identity `(√a)² ≃ a` -/

/-- The error is eventually small: `∀ ε>0, ∃N, ∀ n≥N, errAt n ≤ ε`. -/
theorem errAt_eventually_small (a : Q') (ha : (0 : Q') < a) (ε : Q') (hε : (0 : Q') < ε) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → errAt a n ≤ ε := by
  let md := mulModulus (errAt a 0) ε (errAt_nonneg a ha 0) hε
  refine ⟨md.1.den, fun n hn => ?_⟩
  have hδpos : (0 : Q') < md.1 := md.2.1
  have hδle : errAt a 0 * md.1 ≤ ε := md.2.2
  -- errAt n ≤ errAt(md.den) ≤ errAt0*half^(md.den) ≤ errAt0*δ ≤ ε
  refine Q'.le_trans' _ _ _ (errAt_antitone a ha hn) ?_
  refine Q'.le_trans' _ _ _ (errAt_le_geom a ha md.1.den) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left (half ^ md.1.den) md.1 (errAt a 0)
      (HalfPow.pow_half_le md.1 hδpos) (errAt_nonneg a ha 0)) ?_
  exact hδle

/-- **`(√a)² ≃ a`.**  The product of `√a` with itself is `CReal.Equiv` to the
constant `ofQ' a`: `x_n·x_n = a + errAt n` with `errAt n → 0`. -/
theorem sqrtFrom_sq_equiv (a L : Q') (ha : (0 : Q') < a) (hLpos : (0 : Q') < L)
    (hLa : L * L ≤ a) :
    CReal.Equiv (CReal.mul (sqrtFrom a L ha hLpos hLa) (sqrtFrom a L ha hLpos hLa))
      (CReal.ofQ' a) := by
  intro ε hε
  obtain ⟨N, hN⟩ := errAt_eventually_small a ha ε hε
  refine ⟨N, fun n hn => ?_⟩
  -- A_n = x_n*x_n , B_n = a ; A_n = a + errAt n
  have hge : a ≤ heronSeq a n * heronSeq a n := heronSeq_sq_ge a ha n
  have herr : errAt a n ≤ ε := hN n hn
  -- A_n = x_n² ≃ a + errAt n
  have hAeq : (heronSeq a n * heronSeq a n).eqv (a + errAt a n) := by
    show (heronSeq a n * heronSeq a n).eqv (a + (heronSeq a n * heronSeq a n + -a))
    -- a + (P + -a) ≃ P
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a (heronSeq a n * heronSeq a n + -a)
        (-a + heronSeq a n * heronSeq a n) (Q'.add_comm_eqv (heronSeq a n * heronSeq a n) (-a))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv a (-a) (heronSeq a n * heronSeq a n))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (a + -a) 0 (heronSeq a n * heronSeq a n)
        (Q'.add_neg_self_eqv a)) ?_
    exact QPoly.q_zero_add_eqv (heronSeq a n * heronSeq a n)
  refine ⟨?_, ?_⟩
  · -- A_n ≤ a + ε  : A_n ≃ a + errAt n ≤ a + ε
    show heronSeq a n * heronSeq a n ≤ a + ε
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hAeq) ?_
    exact Q'.add_le_add_left a (errAt a n) ε herr
  · -- a ≤ A_n + ε  : a ≤ A_n ≤ A_n + ε
    show a ≤ heronSeq a n * heronSeq a n + ε
    exact Q'.le_trans' _ _ _ hge
      (Q'.add_le_self_of_nonneg (heronSeq a n * heronSeq a n) ε (Q'.le_of_lt hε))

/-! ### Monotonicity: `√` order-reflects squaring

`√a ≤ c` whenever `a ≤ c²` (`0 < c`): the iterates are eventually `≤ c`.  In
particular `a ≤ b ⟹ √a ≤ √b` once `(√b)² ≃ b ≥ a` (consume this with the
square identity).  We state the rational-bound form `leRat (√a) c`. -/

/-- **`√a ≤ c` when `a ≤ c²`** (the order-reflection of squaring), as the sound
rational upper bound `CReal.leRat (√a) c`.  Hence `√` is monotone: `a ≤ b` gives
`√a ≤ √b` by taking `c`-approximations of `√b`. -/
theorem sqrtFrom_leRat_of_sq (a L : Q') (ha : (0 : Q') < a) (hLpos : (0 : Q') < L)
    (hLa : L * L ≤ a) (c : Q') (hc : (0 : Q') < c) (hac : a ≤ c * c) :
    CReal.leRat (sqrtFrom a L ha hLpos hLa) c := by
  intro ε hε
  -- choose N with errAt N ≤ c·ε + c·ε (drop the ε² term)
  obtain ⟨N, hN⟩ := errAt_eventually_small a ha (c * ε + c * ε)
    (Q'.add_pos (Q'.mul_pos hc hε) (Q'.mul_pos hc hε))
  refine ⟨N, fun n hn => ?_⟩
  show heronSeq a n ≤ c + ε
  -- x_n ≤ c+ε ⟸ x_n² ≤ (c+ε)² ; x_n² = a + errAt n ≤ c² + (cε+cε) ≤ (c+ε)²
  refine le_of_sq_le_sq (Q'.add_pos hc hε) (Q'.le_of_lt (heronSeq_pos ha n)) ?_
  -- x_n² ≤ (c+ε)²
  have hxsq : (heronSeq a n * heronSeq a n).eqv (a + errAt a n) := by
    show (heronSeq a n * heronSeq a n).eqv (a + (heronSeq a n * heronSeq a n + -a))
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a (heronSeq a n * heronSeq a n + -a)
        (-a + heronSeq a n * heronSeq a n)
        (Q'.add_comm_eqv (heronSeq a n * heronSeq a n) (-a))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv a (-a) (heronSeq a n * heronSeq a n))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (a + -a) 0 (heronSeq a n * heronSeq a n)
        (Q'.add_neg_self_eqv a)) ?_
    exact QPoly.q_zero_add_eqv (heronSeq a n * heronSeq a n)
  -- a + errAt n ≤ c² + (cε+cε)
  have hub : a + errAt a n ≤ c * c + (c * ε + c * ε) :=
    Q'.add_le_add hac (hN n hn)
  -- (c+ε)² ≃ (c² + ε²) + (cε+cε) ≥ c² + (cε+cε)
  have hexp : ((c + ε) * (c + ε)).eqv ((c * c + ε * ε) + (c * ε + c * ε)) :=
    sq_add' c ε
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hxsq) ?_
  refine Q'.le_trans' _ _ _ hub ?_
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hexp)
  -- c² + (cε+cε) ≤ (c²+ε²) + (cε+cε)
  exact Q'.add_le_add_right (c * c) (c * c + ε * ε) (c * ε + c * ε)
    (Q'.add_le_self_of_nonneg (c * c) (ε * ε) (SumOfSquares.q_mul_self_nonneg ε))

end CReal

end YMGap.Constructive

#print axioms YMGap.Constructive.Q'.recipPos_den
#print axioms YMGap.Constructive.Q'.mul_recipPos_eqv
#print axioms YMGap.Constructive.Q'.mul_recip_eqv
#print axioms YMGap.Constructive.Q'.le_of_mul_le_mul_left
#print axioms YMGap.Constructive.CReal.heronStep_pos
#print axioms YMGap.Constructive.CReal.four_mul_heronStep_sq
#print axioms YMGap.Constructive.CReal.a_le_heronStep_sq
#print axioms YMGap.Constructive.CReal.heronSeq_sq_ge
#print axioms YMGap.Constructive.CReal.heronSeq_lb
#print axioms YMGap.Constructive.CReal.four_errAt_succ_le
#print axioms YMGap.Constructive.CReal.errAt_le_geom
#print axioms YMGap.Constructive.CReal.gap_bound
#print axioms YMGap.Constructive.CReal.mulModulus
#print axioms YMGap.Constructive.CReal.sqrtModulus
#print axioms YMGap.Constructive.CReal.errAt_modulus_le
#print axioms YMGap.Constructive.CReal.sqrtFrom
#print axioms YMGap.Constructive.CReal.sqrtFrom_isPositive
#print axioms YMGap.Constructive.CReal.sqrtFrom_sq_equiv
#print axioms YMGap.Constructive.CReal.sqrtFrom_leRat_of_sq
