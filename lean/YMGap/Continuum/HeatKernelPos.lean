/-
Pointwise positivity of the SU(2) heat kernel — the algebraic core, formalized
constructively over `Q'` / `CReal`.

# What this module proves and why it is the "Piece A" deliverable

The SU(2) heat kernel on a conjugacy class `θ ∈ (0,π)` is

    K_t(θ) = Σ_{s≥0} (s+1) · a^{s(s+2)} · χ_s(θ),   χ_s(θ) = sin((s+1)θ)/sin θ,

with `a ∈ (0,1)` the heat-kernel parameter.  The PSD program needs the
pointwise bound `K_t(θ) ≥ 0`.  The analytic reduction (verified numerically to
40 digits in `docs/heat-kernel-pos-notes.md`) is:

  * `K_t(θ)·sin θ = a^{-1}·D(θ)`, `D(θ) = Σ_{n≥1} n a^{n²} sin(nθ) = −½ ϑ₃'(θ)`,
    where `ϑ₃(θ) = 1 + 2 Σ_{n≥1} a^{n²} cos(nθ)`;
  * hence on `(0,π)` (where `sin θ > 0`), `K_t ≥ 0 ⟺ ϑ₃' ≤ 0 ⟺ ϑ₃ ↓ on [0,π]`;
  * **Jacobi triple product:**
      `ϑ₃(θ) = ∏_{n≥1} (1−a^{2n})·(1 + 2 a^{2n-1} cos θ + a^{4n-2})`,
    every factor `> 0`;
  * **Monotonicity:**
      `ϑ₃'(θ)/ϑ₃(θ) = Σ_{n≥1} (−2 a^{2n-1} sin θ) / (1 + 2 a^{2n-1} cos θ + a^{4n-2})`,
    and on `(0,π)` every term is `≤ 0` (numerator `≤ 0`, denominator `> 0`),
    so `ϑ₃'/ϑ₃ ≤ 0` and, since `ϑ₃ > 0`, `ϑ₃' ≤ 0`.

The genuinely-constructive, genuinely-closeable heart of this argument is the
**termwise algebra**, and that is what this module proves *as exact `Q'`
inequalities*, with the per-factor amplitude `c = a^{2n-1} ∈ (0,1)`,
`x = cos θ ∈ [−1,1]`, `s = sin θ ≥ 0` carried as rational parameters:

  1. `factorLB_le_factor` — the **square-completion**
        `(1−c)² ≤ 1 + 2 c x + c²`   for `−1 ≤ x`, `0 ≤ c`,
     via the exact identity `1 + 2cx + c² − (1−c)² = 2c(x+1)`
     (`factor_sub_factorLB_eqv`).
  2. `factorLB_pos` / `factor_pos` — each Jacobi factor is `> 0`
     (`0 < 1−c ⇒ 0 < (1−c)² ≤ factor`).
  3. `logderiv_term_numer_nonpos` — the log-derivative term numerator
        `−2 c s ≤ 0`   for `0 ≤ c`, `0 ≤ s`,
     so every term of `ϑ₃'/ϑ₃` is `≤ 0` on `(0,π)`.
  4. `thetaTrunc_pos` — the **finite-truncation** theta
        `ϑ₃^{(M)} = ∏_{n<M} factor cₙ`
     is `> 0` (finite product of positive factors), with each `cₙ ∈ (0,1)`.

# The precise remaining gap (honest, per AGENTS.md Rule 6)

This module does **not** close the full infinite-product monotonicity
`ϑ₃' ≤ 0` as a single `CReal` statement.  What is proved is the complete
*termwise* algebra (factor positivity + term sign) and the finite-truncation
positivity.  The two steps deliberately left as the stated gap are:

  (G1) Convergence of the infinite product `ϑ₃` and the series `D` as `CReal`
       with explicit modulus.  The decay `a^{n²}` is super-geometric, so the
       modulus exists (engine: `Continuum/KPLimit.lean`'s
       `crealOfGeoIncrement`); wiring the `a^{2n-1}`-amplitude product through
       it is mechanical but lengthy and is not done here.
  (G2) Passing the termwise sign `ϑ₃'/ϑ₃ ≤ 0` from the partial sums to the
       limit `ϑ₃' ≤ 0` (a monotone-limit / `geRat`-style step).

These are named, not faked.  Everything below is fully proved and axiom-gated.

# Axiom-gate (AGENTS.md Rule 1)

Every theorem reports `[propext]` (or empty).  No `Classical.*`, no
`Quot.sound`, no `sorryAx`, no `sorry`.
-/

import YMGap.Constructive.Rationals
import YMGap.Constructive.RationalsMul
import YMGap.Constructive.Geometric
import YMGap.Constructive.CRealMul
import YMGap.Constructive.CRealMulMono
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.QPoly
import YMGap.Constructive.Soundness
import YMGap.Constructive.AbsQ

namespace YMGap.Continuum.HKPos

open YMGap.Constructive
open YMGap.Constructive.QPoly (q_add_congr q_interchange q_zero_add_eqv q_add_zero_eqv)

/-! ## A strict-positivity multiplication lemma for `Q'`

`Rationals.lean` provides `Q'.mul_nonneg` (non-strict).  The Jacobi factor
positivity needs the strict version `0 < a → 0 < b → 0 < a·b`, which is not in
the base API; we prove it here from the numerator characterisation
(`pos_of_num_pos` / `num_pos_of_pos`). -/

/-- `≤`-then-`<` transitivity on `Q'`, via the cross-product representation.
Mirrors `Q'.le_trans'` but with a strict second step. -/
theorem q_lt_of_le_of_lt {p q r : Q'} (h_pq : p ≤ q) (h_qr : q < r) : p < r := by
  show p.num * (r.den : Int) < r.num * (p.den : Int)
  have h1 : p.num * (q.den : Int) ≤ q.num * (p.den : Int) := h_pq
  have h2 : q.num * (r.den : Int) < r.num * (q.den : Int) := h_qr
  have h_p_pos : (0 : Int) < (p.den : Int) := by exact_mod_cast Q'.den_pos p
  have h_r_nn : (0 : Int) ≤ (r.den : Int) := Int.natCast_nonneg _
  have h_q_pos : (0 : Int) < (q.den : Int) := by exact_mod_cast Q'.den_pos q
  have step1 : p.num * (q.den : Int) * (r.den : Int)
             ≤ q.num * (p.den : Int) * (r.den : Int) :=
    Int.mul_le_mul_of_nonneg_right h1 h_r_nn
  have step2 : q.num * (r.den : Int) * (p.den : Int)
             < r.num * (q.den : Int) * (p.den : Int) :=
    Int.mul_lt_mul_of_pos_right h2 h_p_pos
  have e3 : p.num * (q.den : Int) * (r.den : Int)
          = p.num * (r.den : Int) * (q.den : Int) := by
    rw [Int.mul_assoc, Int.mul_comm (q.den : Int) (r.den : Int), ← Int.mul_assoc]
  have e1 : q.num * (p.den : Int) * (r.den : Int)
          = q.num * (r.den : Int) * (p.den : Int) := by
    rw [Int.mul_assoc, Int.mul_comm (p.den : Int) (r.den : Int), ← Int.mul_assoc]
  have e2 : r.num * (q.den : Int) * (p.den : Int)
          = r.num * (p.den : Int) * (q.den : Int) := by
    rw [Int.mul_assoc, Int.mul_comm (q.den : Int) (p.den : Int), ← Int.mul_assoc]
  have chain : p.num * (r.den : Int) * (q.den : Int)
             < r.num * (p.den : Int) * (q.den : Int) := by
    rw [← e3, ← e2]
    exact Int.lt_of_le_of_lt step1 (by rw [e1]; exact step2)
  exact Int.lt_of_mul_lt_mul_right chain (Int.le_of_lt h_q_pos)

/-- Strict product positivity on `Q'`: `0 < a → 0 < b → 0 < a·b`. -/
theorem q_mul_pos {a b : Q'} (ha : (0 : Q') < a) (hb : (0 : Q') < b) :
    (0 : Q') < a * b := by
  have hna : 0 < a.num := CReal.num_pos_of_pos ha
  have hnb : 0 < b.num := CReal.num_pos_of_pos hb
  have : 0 < (a * b).num := by
    show 0 < a.num * b.num
    exact Int.mul_pos hna hnb
  exact CReal.pos_of_num_pos this

/-! ## The Jacobi triple-product factor and its square-completion

For the `n`-th Jacobi factor we abstract the amplitude `c = a^{2n-1}` and the
angle data `x = cos θ`.  The factor is

    factor c x = 1 + (2c·x + c·c)        (= 1 + 2 a^{2n-1} cos θ + a^{4n-2}),

and its square-completion lower bound is

    factorLB c = (1 + (−c))·(1 + (−c))   (= (1 − a^{2n-1})²).

The headline algebraic identity is `factor − factorLB = 2c·x + 2c = 2c(x+1)`,
which is `≥ 0` whenever `−1 ≤ x` and `0 ≤ c`. -/

/-- `2·c` as a `Q'` (the doubled amplitude). -/
def two (c : Q') : Q' := c + c

/-- The `n`-th Jacobi factor `1 + 2c·x + c²` with `c = a^{2n-1}`, `x = cos θ`. -/
def factor (c x : Q') : Q' := 1 + (two c * x + c * c)

/-- The square-completion lower bound `(1 − c)²` for the `n`-th factor. -/
def factorLB (c : Q') : Q' := (1 + (-c)) * (1 + (-c))

/-! ### The square-completion identity

`factor c x + −(factorLB c) ≃ two c * x + two c`.  Proved by the `Q'` ring
`eqv`-lemmas (this is a fixed two-variable polynomial identity; we chain the
distributive/commutative lemmas rather than invoke a decision procedure, since
the variables `c, x` are abstract). -/
theorem factor_sub_factorLB_eqv (c x : Q') :
    (factor c x + -(factorLB c)).eqv (two c * x + two c) := by
  -- factorLB c = (1 + -c)*(1 + -c) ≃ 1 + (-(two c) + c*c)
  have hLB : (factorLB c).eqv (1 + (-(two c) + c * c)) := by
    -- (1 + -c)*(1 + -c) = 1*(1+-c) + (-c)*(1+-c)
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 (-c) (1 + (-c))) ?_
    -- = (1*1 + 1*(-c)) + ((-c)*1 + (-c)*(-c))
    have e1 : ((1 : Q') * (1 + (-c))).eqv (1 + (-c)) := Q'.one_mul_eqv (1 + (-c))
    have e2 : ((-c) * (1 + (-c))).eqv ((-c) * 1 + (-c) * (-c)) :=
      Q'.mul_add_eqv (-c) 1 (-c)
    refine Q'.eqv_trans _ _ _ (q_add_congr e1 e2) ?_
    -- (1 + -c) + ((-c)*1 + (-c)*(-c))
    -- (-c)*1 ≃ -c ; (-c)*(-c) ≃ c*c
    have e3 : ((-c) * 1).eqv (-c) := Q'.mul_one_eqv (-c)
    have e4 : ((-c) * (-c)).eqv (c * c) := by
      refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv c (-c)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv c c)) ?_
      exact Q'.neg_neg_eqv (c * c)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (1 + (-c)) _ ((-c) + c * c) (q_add_congr e3 e4)) ?_
    -- now: (1 + -c) + (-c + c*c)  ≃  1 + (-(two c) + c*c)
    -- two c = c + c, so -(two c) = -c + -c
    have hneg2 : (-(two c)).eqv ((-c) + (-c)) := by
      show (-(c + c)).eqv ((-c) + (-c))
      exact Q'.neg_add_eqv c c
    -- regroup (1 + -c) + (-c + c*c) = 1 + ((-c + -c) + c*c) = 1 + (-(two c) + c*c)
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv 1 (-c) ((-c) + c * c)) ?_
    refine Q'.add_eqv_congr_left 1 _ (-(two c) + c * c) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (-c) (-c) (c * c))) ?_
    exact Q'.add_eqv_congr_right ((-c) + (-c)) (-(two c)) (c * c) (Q'.eqv_symm hneg2)
  -- factor c x = 1 + (two c * x + c*c)
  -- factor + -(factorLB) ≃ (1 + (two c*x + c*c)) + -(1 + (-(two c) + c*c))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (factor c x) (-(factorLB c)) (-(1 + (-(two c) + c * c)))
      (Q'.neg_eqv_congr _ _ hLB)) ?_
  -- now a concrete polynomial identity in (two c * x), c*c, two c — chain to goal
  show ((1 + (two c * x + c * c)) + -(1 + (-(two c) + c * c))).eqv (two c * x + two c)
  -- -(1 + (-(two c) + c*c)) ≃ (-1) + ((two c) + -(c*c))
  have hN : (-(1 + (-(two c) + c * c))).eqv ((-1) + (two c + -(c * c))) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv 1 (-(two c) + c * c)) ?_
    refine Q'.add_eqv_congr_left (-1) _ (two c + -(c * c)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (-(two c)) (c * c)) ?_
    exact Q'.add_eqv_congr_right (-(-(two c))) (two c) (-(c * c)) (Q'.neg_neg_eqv (two c))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ ((-1) + (two c + -(c * c))) hN) ?_
  -- (1 + (two c*x + c*c)) + ((-1) + (two c + -(c*c)))  ≃  two c * x + two c
  -- Group: = (1 + (-1)) + ((two c*x + c*c) + (two c + -(c*c)))  [interchange]
  refine Q'.eqv_trans _ _ _
    (q_interchange 1 (two c * x + c * c) (-1) (two c + -(c * c))) ?_
  -- (1 + -1) ≃ 0
  have h11 : ((1 : Q') + (-1)).eqv 0 := Q'.add_neg_self_eqv 1
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ 0 _ h11) ?_
  -- 0 + ((two c*x + c*c) + (two c + -(c*c)))  ≃  two c * x + two c
  refine Q'.eqv_trans _ _ _ (q_zero_add_eqv _) ?_
  -- (two c*x + c*c) + (two c + -(c*c)) ≃ two c*x + two c
  -- interchange to (two c*x + two c) + (c*c + -(c*c))
  refine Q'.eqv_trans _ _ _
    (q_interchange (two c * x) (c * c) (two c) (-(c * c))) ?_
  have hcc : (c * c + -(c * c)).eqv 0 := Q'.add_neg_self_eqv (c * c)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ 0 hcc) ?_
  exact q_add_zero_eqv (two c * x + two c)

/-! ### The square-completion inequality and factor positivity -/

/-- `0 ≤ two c` whenever `0 ≤ c`. -/
theorem two_nonneg {c : Q'} (hc : (0 : Q') ≤ c) : (0 : Q') ≤ two c :=
  Q'.zero_le_add c c hc hc

/-- The Jacobi-factor right-hand side `two c * x + two c` is `≥ 0` for
`−1 ≤ x` and `0 ≤ c` — i.e. `2c(x+1) ≥ 0`. -/
theorem two_c_x_plus_two_c_nonneg {c x : Q'}
    (hc : (0 : Q') ≤ c) (hx : (-1 : Q') ≤ x) :
    (0 : Q') ≤ two c * x + two c := by
  have h2c : (0 : Q') ≤ two c := two_nonneg hc
  -- two c * (-1) ≤ two c * x
  have hmul : two c * (-1) ≤ two c * x :=
    Q'.mul_le_mul_of_nonneg_left (-1) x (two c) hx h2c
  -- two c * (-1) ≃ -(two c)
  have he : (two c * (-1)).eqv (-(two c)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (two c) 1) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv (two c))
  have hge : -(two c) ≤ two c * x :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hmul
  -- add two c to both sides: 0 = -(two c) + two c ≤ two c * x + two c
  have hadd : -(two c) + two c ≤ two c * x + two c :=
    Q'.add_le_add_right _ _ (two c) hge
  have hz : ((-(two c)) + two c).eqv 0 := Q'.neg_add_self_eqv (two c)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hz) hadd

/-- **Square-completion inequality:** `(1−c)² ≤ 1 + 2c·x + c²` for `−1 ≤ x`,
`0 ≤ c`.  This is the load-bearing per-factor lower bound: the Jacobi factor
dominates `(1−c)²`. -/
theorem factorLB_le_factor {c x : Q'}
    (hc : (0 : Q') ≤ c) (hx : (-1 : Q') ≤ x) :
    factorLB c ≤ factor c x := by
  apply Q'.le_of_sub_nonneg
  -- 0 ≤ factor c x + -(factorLB c), via the identity = two c * x + two c ≥ 0
  exact Q'.le_trans' _ _ _ (two_c_x_plus_two_c_nonneg hc hx)
    (Q'.ge_of_eqv (factor_sub_factorLB_eqv c x))

/-- `0 < 1 + (−c)` (i.e. `0 < 1 − c`) for `c < 1`.  Reduces to the numerator
inequality `c.num < c.den`, which `c < 1` already supplies. -/
theorem one_sub_pos {c : Q'} (hc1 : c < (1 : Q')) : (0 : Q') < 1 + (-c) := by
  -- c < 1 unfolds to c.num * 1 < 1 * c.den, i.e. c.num < c.den.
  have hlt : c.num * (1 : Int) < (1 : Int) * (c.den : Int) := hc1
  have hnum : c.num < (c.den : Int) := by
    rw [Int.mul_one, Int.one_mul] at hlt; exact hlt
  -- (1 + -c).num = 1 * c.den + (-c.num) * 1 = c.den - c.num > 0.
  apply CReal.pos_of_num_pos
  show 0 < (1 + (-c)).num
  show 0 < (1 : Int) * (c.den : Int) + (-c.num) * (1 : Int)
  rw [Int.one_mul, Int.mul_one]
  -- 0 < c.den + (-c.num), from c.num < c.den.
  have hsub : (0 : Int) < (c.den : Int) - c.num := Int.sub_pos.mpr hnum
  rwa [Int.sub_eq_add_neg] at hsub

/-- `0 < factorLB c` (i.e. `0 < (1−c)²`) for `c < 1` (so `0 < 1−c`). -/
theorem factorLB_pos {c : Q'} (hc1 : c < (1 : Q')) : (0 : Q') < factorLB c :=
  q_mul_pos (one_sub_pos hc1) (one_sub_pos hc1)

/-- **Jacobi-factor positivity:** `0 < 1 + 2c·x + c²` for `0 ≤ c`, `c < 1`,
`−1 ≤ x`.  Combines `factorLB_pos` (the lower bound is positive) with
`factorLB_le_factor` (the factor dominates it). -/
theorem factor_pos {c x : Q'}
    (hc0 : (0 : Q') ≤ c) (hc1 : c < (1 : Q')) (hx : (-1 : Q') ≤ x) :
    (0 : Q') < factor c x :=
  Q'.pos_of_lt_of_le (factorLB_pos hc1) (factorLB_le_factor hc0 hx)

/-! ## The log-derivative term sign

The monotonicity argument writes
  `ϑ₃'(θ)/ϑ₃(θ) = Σ_{n≥1} (−2 a^{2n-1} sin θ) / factorₙ`,
and concludes each term is `≤ 0` from: numerator `−2 c s ≤ 0` and denominator
`factorₙ > 0` (the previous section).  This is the numerator-sign half. -/

/-- **Log-derivative term numerator is nonpositive:** `−2c·s ≤ 0` for
`0 ≤ c`, `0 ≤ s` (here `c = a^{2n-1} ≥ 0`, `s = sin θ ≥ 0` on `(0,π)`).
Equivalently `0 ≤ 2c·s`.  Each term of `ϑ₃'/ϑ₃` is therefore
`(≤0 numerator)/(>0 denominator) ≤ 0`. -/
theorem logderiv_term_numer_nonpos {c s : Q'}
    (hc : (0 : Q') ≤ c) (hs : (0 : Q') ≤ s) :
    -(two c * s) ≤ (0 : Q') := by
  have hpos : (0 : Q') ≤ two c * s := Q'.mul_nonneg (two c) s (two_nonneg hc) hs
  -- 0 ≤ A ⟹ -A ≤ 0
  have h := Q'.neg_le_neg hpos
  rwa [show (-(0 : Q')) = 0 from rfl] at h

/-! ## Finite-truncation theta and its positivity

The truncated theta `ϑ₃^{(M)}(x) = ∏_{n<M} factor (cs n) x` is a finite product
of Jacobi factors.  When every amplitude `cs n ∈ [0,1)` and `−1 ≤ x` (so each
factor is `> 0` by `factor_pos`), the truncated product is `> 0`.  This is the
finite-stage positivity statement; the infinite-product positivity is the
convergence gap (G1) named in the module header. -/

/-- The truncated Jacobi theta as a finite product of factors:
`thetaTrunc cs x M = ∏_{n<M} factor (cs n) x` (empty product `= 1`). -/
def thetaTrunc (cs : Nat → Q') (x : Q') : Nat → Q'
  | 0 => 1
  | (M + 1) => thetaTrunc cs x M * factor (cs M) x

@[simp] theorem thetaTrunc_zero (cs : Nat → Q') (x : Q') :
    thetaTrunc cs x 0 = 1 := rfl

@[simp] theorem thetaTrunc_succ (cs : Nat → Q') (x : Q') (M : Nat) :
    thetaTrunc cs x (M + 1) = thetaTrunc cs x M * factor (cs M) x := rfl

/-- **Finite-truncation theta positivity:** `0 < ϑ₃^{(M)}(x)` whenever every
amplitude `cs n ∈ [0,1)` and `−1 ≤ x`.  Finite product of positive factors,
by induction on `M` with `q_mul_pos`. -/
theorem thetaTrunc_pos {cs : Nat → Q'} {x : Q'}
    (hc0 : ∀ n, (0 : Q') ≤ cs n) (hc1 : ∀ n, cs n < (1 : Q'))
    (hx : (-1 : Q') ≤ x) :
    ∀ M, (0 : Q') < thetaTrunc cs x M
  | 0 => by
      show (0 : Q') < (1 : Q')
      exact CReal.pos_of_num_pos (by decide)
  | (M + 1) => by
      rw [thetaTrunc_succ]
      exact q_mul_pos (thetaTrunc_pos hc0 hc1 hx M)
        (factor_pos (hc0 M) (hc1 M) hx)

/-! ## Concrete geometric amplitudes `cs n = a^{2n+1}`, `a ∈ (0,1)`

To exhibit the `cs n ∈ [0,1)` hypotheses of `thetaTrunc_pos` for the actual
heat-kernel amplitudes, we bound powers of `a ∈ (0,1)`.  The Jacobi amplitude
sequence is `a^{2n-1}` (`n ≥ 1`), i.e. `a^{2k+1}` for `k = n−1 ≥ 0`, with
exponent `≥ 1`, so each `cs k ≤ a < 1`. -/

/-- `a^k ≤ 1` for `0 ≤ a ≤ 1`.  Induction on `k`. -/
theorem pow_le_one {a : Q'} (h0 : (0 : Q') ≤ a) (h1 : a ≤ (1 : Q')) (k : Nat) :
    a ^ k ≤ (1 : Q') := by
  induction k with
  | zero =>
      show (1 : Q') ≤ (1 : Q')
      exact Q'.le_refl' 1
  | succ k ih =>
      show a * a ^ k ≤ (1 : Q')
      -- a * a^k ≤ a * 1 = a ≤ 1
      have hstep : a * a ^ k ≤ a * 1 :=
        Q'.mul_le_mul_of_nonneg_left (a ^ k) 1 a ih h0
      have he : (a * 1).eqv a := Q'.mul_one_eqv a
      exact Q'.le_trans' _ _ _ hstep (Q'.le_trans' _ _ _ (Q'.le_of_eqv he) h1)

/-- `a^{k+1} ≤ a` for `0 ≤ a ≤ 1` (powers with exponent `≥ 1` do not exceed
`a`).  Hence `a^{k+1} < 1` whenever `a < 1`. -/
theorem pow_succ_le_self {a : Q'} (h0 : (0 : Q') ≤ a) (h1 : a ≤ (1 : Q')) (k : Nat) :
    a ^ (k + 1) ≤ a := by
  show a * a ^ k ≤ a
  have hstep : a * a ^ k ≤ a * 1 :=
    Q'.mul_le_mul_of_nonneg_left (a ^ k) 1 a (pow_le_one h0 h1 k) h0
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.mul_one_eqv a))

/-- `0 < a^k` for `0 < a`.  Induction on `k`. -/
theorem pow_pos {a : Q'} (h0 : (0 : Q') < a) (k : Nat) : (0 : Q') < a ^ k := by
  induction k with
  | zero =>
      show (0 : Q') < (1 : Q')
      exact CReal.pos_of_num_pos (by decide)
  | succ m ih =>
      show (0 : Q') < a * a ^ m
      exact q_mul_pos h0 ih

/-- `0 < a^{k+1} < 1` for `0 < a < 1`: the heat-kernel amplitudes
`cs k = a^{2k+1}` lie strictly in `(0,1)`. -/
theorem pow_succ_pos_lt_one {a : Q'} (h0 : (0 : Q') < a) (h1 : a < (1 : Q')) (k : Nat) :
    (0 : Q') < a ^ (k + 1) ∧ a ^ (k + 1) < (1 : Q') :=
  ⟨pow_pos h0 (k + 1),
   q_lt_of_le_of_lt (pow_succ_le_self (Q'.le_of_lt h0) (Q'.le_of_lt h1) k) h1⟩

/-- The heat-kernel Jacobi amplitude sequence `geoAmp a k = a^{2k+1}`
(`= a^{2n−1}` for `n = k+1`).  Always has exponent `≥ 1`. -/
def geoAmp (a : Q') (k : Nat) : Q' := a ^ (2 * k + 1)

/-- **Capstone: positivity of the truncated Jacobi theta at the actual
heat-kernel amplitudes.**  For any `a ∈ (0,1)`, any `x = cos θ ∈ [−1,1]`, and
any truncation depth `M`, the truncated product
`ϑ₃^{(M)}(x) = ∏_{k<M} (1 + 2 a^{2k+1} x + a^{2(2k+1)})` is strictly positive.

This is `thetaTrunc_pos` with the `cs k ∈ [0,1)` hypotheses discharged via
`pow_succ_pos_lt_one` (`2k+1 = (2k)+1`, exponent `≥ 1`). -/
theorem thetaTrunc_geo_pos {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (M : Nat) :
    (0 : Q') < thetaTrunc (geoAmp a) x M := by
  refine thetaTrunc_pos (fun k => ?_) (fun k => ?_) hx M
  · -- 0 ≤ geoAmp a k
    show (0 : Q') ≤ a ^ (2 * k + 1)
    exact Q'.le_of_lt ((pow_succ_pos_lt_one ha0 ha1 (2 * k)).1)
  · -- geoAmp a k < 1
    show a ^ (2 * k + 1) < (1 : Q')
    exact (pow_succ_pos_lt_one ha0 ha1 (2 * k)).2

end YMGap.Continuum.HKPos

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` or empty. -/

#print axioms YMGap.Continuum.HKPos.q_lt_of_le_of_lt
#print axioms YMGap.Continuum.HKPos.q_mul_pos
#print axioms YMGap.Continuum.HKPos.factor_sub_factorLB_eqv
#print axioms YMGap.Continuum.HKPos.two_nonneg
#print axioms YMGap.Continuum.HKPos.two_c_x_plus_two_c_nonneg
#print axioms YMGap.Continuum.HKPos.factorLB_le_factor
#print axioms YMGap.Continuum.HKPos.one_sub_pos
#print axioms YMGap.Continuum.HKPos.factorLB_pos
#print axioms YMGap.Continuum.HKPos.factor_pos
#print axioms YMGap.Continuum.HKPos.logderiv_term_numer_nonpos
#print axioms YMGap.Continuum.HKPos.thetaTrunc_pos
#print axioms YMGap.Continuum.HKPos.pow_le_one
#print axioms YMGap.Continuum.HKPos.pow_succ_le_self
#print axioms YMGap.Continuum.HKPos.pow_pos
#print axioms YMGap.Continuum.HKPos.pow_succ_pos_lt_one
#print axioms YMGap.Continuum.HKPos.thetaTrunc_geo_pos
