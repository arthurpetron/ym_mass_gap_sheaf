/-
# Chebyshev polynomials over `Q'` and the bound `|T_n(x)| ≤ 1`
# ("Piece A / gap G2" — the Chebyshev sub-crux of the SU(2) heat-kernel identity)

The SU(2) heat kernel
`K_t(x) = a⁻¹ Σ_{n≥1} n · a^{n²} · U_{n-1}(x)`  (`x = cos θ ∈ [−1,1]`)
needs, for its manifestly-positive product representation, the elementary
Chebyshev facts `|T_n(x)| ≤ 1` and `|U_{n-1}(x)| ≤ n` on `[−1,1]`.  The
docstring of `HeatKernelPos2` flags `|U_{n-1}| ≤ n` as "a sin-structure
fact not provable by the naive `Q'` triangle recurrence".  This module
supplies the *algebraic* route, on the rational substrate `Q'`.

## What is CLOSED here

* `T`, `U` : the Chebyshev polynomials of the first/second kind, defined
  over `Q'` by their `2x`-recurrences (Type-level data, `Nat → Q' → Q'`).
* `linRel` : the two coupled linear relations
    (A)  `T(n+2)  ≃  x·T(n+1) − (1−x²)·U(n)`
    (B)  `U(n+1)  ≃  T(n+1) + x·U(n)`
  proved *simultaneously* by induction (each is needed in the other's
  step).  These are the "ladder" relations linking the two kinds.
* `pythForm` : the Pythagorean / quadratic-form invariant
    `T(n+1)² + (1−x²)·U(n)²  ≃  1`,
  proved by induction (`pythForm_all`): the linear map
  `(a,b) ↦ (x·a−(1−x²)·b, a+x·b)` (which sends `(T(n+1),U(n))` to
  `(T(n+2),U(n+1))` by `linRel`) preserves the quadratic form
  `Φ(a,b) = a² + (1−x²)·b²` (`pythStep_core`), and `Φ(T(1),U(0)) = 1`.
* `Tsq_le_one` : `T_n(x)² ≤ 1` on `[−1,1]` for ALL `n` — from `pythForm_all`,
  since the dropped term `(1−x²)·U(n)²` is `≥ 0` there (`1−x² ≥ 0` and a
  square).  This is the closed form of the heat-kernel sub-crux
  "`|T_n(x)| ≤ 1` on `[−1,1]`".

## Honesty / scope

The first-kind bound is fully closed.  The remaining target — the
*second-kind* bound `|U_{n-1}(x)| ≤ n` — needs the T-decomposition
`U_{n-1} = Σ_{k} T_{|n-1-2k|}` (a separate finite-sum induction); it is NOT
closed here and is recorded as the named open `Prop` `OpenProblem.absU_le`
at the end, with its honest reduction.  The naive `U`-recurrence triangle
bound genuinely fails (gives ~2.414ⁿ), as the heat-kernel work warns.

## Method — `eqv`-`calc` over a hand-built ring layer

There is no `ring`/`linarith`/`Mathlib` here (Rule 3).  `Q'` equality is
structural and unnormalized, so polynomial identities hold only up to
`Q'.eqv` (`p.eqv q ↔ p.num·q.den = q.num·p.den`), and the two sides
generally carry *different* denominators — a cross-multiplied `simp`+`omega`
closer (which we DO use for the small base/atom-identity lemmas, generalising
the `den` casts before `omega`) blows up on the degree-3/4 step identities.
The workhorse is therefore `calc` chains over the proven `Q'.eqv` ring lemmas
(`mul_comm_eqv`, `mul_assoc_eqv`, `mul_add_eqv`, the congruences,
`add_swap_inner`, …): we keep `1−x²` and `x²` as *compound* subterms
manipulated by congruence rather than expanding them into denominators, which
keeps every step small.  All proofs report `[propext]` or
`[propext, Quot.sound]` (both MLTT/HoTT-valid; `Quot.sound` enters only via
`omega`'s reused `Int` helpers in the base closers).

# Axiom gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` or `[propext, Quot.sound]`.
No `Classical.*`, no `sorry`/`sorryAx`, no `native_decide`.
-/

import YMGap.Constructive.RationalsMul

namespace YMGap.Continuum.Cheb

open YMGap.Constructive
open YMGap.Constructive.Q'

/-! ## Numerator-projection helpers

`(a+b).num`, `(a*b).num`, `(-a).num` all compute by `rfl`; packaging them
as `simp` lemmas lets the `eqv`-reduction `simp` set expand a whole
compound numerator in one pass (the denominators are handled by the
`*_den_cast`/`neg_den` lemmas already in `RationalsMul`). -/

theorem add_num (a b : Q') : (a + b).num = a.num * (b.den : Int) + b.num * (a.den : Int) := rfl
theorem mul_num (a b : Q') : (a * b).num = a.num * b.num := rfl
theorem neg_num (a : Q') : (-a).num = -a.num := rfl

/-! The `simp` set that turns a `Q'.eqv` cross-equation into a flat
polynomial identity over `Int` monomials, ready for `omega`. -/
attribute [local simp] add_num mul_num neg_num add_den_cast mul_den_cast neg_den

/-! ## Chebyshev polynomials of the first and second kind over `Q'`

`T 0 = 1`, `T 1 = x`, `T (n+2) = (2x)·T(n+1) − T(n)`.
`U 0 = 1`, `U 1 = 2x`, `U (n+2) = (2x)·U(n+1) − U(n)`.

We write `2x` as `((2 : Q') * x)` and the subtraction as `+ (-...)`
(NOT `Q'.sub`), so the numerator-projection lemmas above apply verbatim. -/

/-- `T_n(x)` : Chebyshev polynomial of the first kind, over `Q'`. -/
def T : Nat → Q' → Q'
  | 0,     _ => 1
  | 1,     x => x
  | (n+2), x => ((2 : Q') * x) * T (n+1) x + (-(T n x))

/-- `U_n(x)` : Chebyshev polynomial of the second kind, over `Q'`. -/
def U : Nat → Q' → Q'
  | 0,     _ => 1
  | 1,     x => (2 : Q') * x
  | (n+2), x => ((2 : Q') * x) * U (n+1) x + (-(U n x))

@[simp] theorem T_zero (x : Q') : T 0 x = 1 := rfl
@[simp] theorem T_one (x : Q') : T 1 x = x := rfl
theorem T_succ_succ (n : Nat) (x : Q') :
    T (n+2) x = ((2 : Q') * x) * T (n+1) x + (-(T n x)) := rfl

@[simp] theorem U_zero (x : Q') : U 0 x = 1 := rfl
@[simp] theorem U_one (x : Q') : U 1 x = (2 : Q') * x := rfl
theorem U_succ_succ (n : Nat) (x : Q') :
    U (n+2) x = ((2 : Q') * x) * U (n+1) x + (-(U n x)) := rfl

/-! ## `eqv` as a `calc`-able equivalence

`Q'.eqv` is reflexive/symmetric/transitive (`eqv_refl`/`eqv_symm` in
`Rationals.lean`, `eqv_trans` in `RationalsMul.lean`).  We expose it as the
local infix `≈` with a `Trans` instance so polynomial rearrangements can be
written as readable `calc` chains over the proven `Q'` ring lemmas
(`mul_comm_eqv`, `mul_assoc_eqv`, `mul_add_eqv`, the congruences, …).

Why `calc` and not a `simp`/`omega` closer: `Q'` is unnormalized, so the two
sides of a polynomial identity generally carry *different* denominators; the
cross-multiplication `p.num·q.den = q.num·p.den` then mixes `den` powers that
`omega` (being linear) cannot reconcile.  The proven `eqv` ring lemmas handle
the denominators correctly by construction, so we route every identity
through them. -/

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := eqv_trans _ _ _ h1 h2

/-- `a ≈ a` (reflexivity, repackaged for `calc`). -/
theorem eqv_rfl (a : Q') : a ≈ a := eqv_refl a

/-! ### Derived ring lemmas at `eqv`

A small layer on top of `RationalsMul`: right-distributivity, the two-sided
congruences for products and sums (already present) plus `neg`-distribution
and a `subtraction-as-+neg` helper, packaged to keep the `calc` chains short. -/

/-- Right-distributivity `(a + b)·c ≈ a·c + b·c`. -/
theorem add_mul_eqv (a b c : Q') : (a + b) * c ≈ a * c + b * c :=
  calc (a + b) * c ≈ c * (a + b)       := mul_comm_eqv (a + b) c
    _ ≈ c * a + c * b                  := mul_add_eqv c a b
    _ ≈ a * c + c * b                  := add_eqv_congr_right _ _ _ (mul_comm_eqv c a)
    _ ≈ a * c + b * c                  := add_eqv_congr_left _ _ _ (mul_comm_eqv c b)

/-- Congruence on both factors at once: `a ≈ a' → b ≈ b' → a·b ≈ a'·b'`. -/
theorem mul_eqv_congr (a a' b b' : Q') (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  eqv_trans _ _ _ (mul_eqv_congr_right a a' b ha) (mul_eqv_congr_left a' b b' hb)

/-- Congruence on both summands at once: `a ≈ a' → b ≈ b' → a+b ≈ a'+b'`. -/
theorem add_eqv_congr (a a' b b' : Q') (ha : a ≈ a') (hb : b ≈ b') :
    a + b ≈ a' + b' :=
  eqv_trans _ _ _ (add_eqv_congr_right a a' b ha) (add_eqv_congr_left a' b b' hb)

/-- `−(a + b) ≈ (−a) + (−b)`.  Cross-product reduction: both `den`s are
`a.den·b.den` and the numerator negation distributes over the sum. -/
theorem neg_add_eqv (a b : Q') : (-(a + b)) ≈ ((-a) + (-b)) := by
  show (-(a + b)).num * (((-a) + (-b)).den : Int)
      = ((-a) + (-b)).num * ((-(a + b)).den : Int)
  simp only [add_num, neg_num, neg_den, add_den_cast,
    Int.neg_mul, Int.mul_neg, Int.neg_add]

/-- `(2 : Q')·x ≈ x + x`.  Uses that `(2 : Q')` is *structurally*
`(1 : Q') + (1 : Q')` (`ofNat 2 = ⟨2,0⟩ = (1:Q')+(1:Q')`), then
right-distributes and applies `1·x ≈ x` on each summand. -/
theorem two_mul_eqv (x : Q') : (2 : Q') * x ≈ x + x := by
  have h2 : (2 : Q') = (1 : Q') + (1 : Q') := rfl
  rw [h2]
  calc ((1 : Q') + (1 : Q')) * x
      ≈ (1 : Q') * x + (1 : Q') * x := add_mul_eqv 1 1 x
    _ ≈ x + (1 : Q') * x := add_eqv_congr_right _ _ _ (one_mul_eqv x)
    _ ≈ x + x := add_eqv_congr_left _ _ _ (one_mul_eqv x)

/-! ## The coupled linear ("ladder") relations

(A)  `T(n+2)  ≃  x·T(n+1) − (1−x²)·U(n)`
(B)  `U(n+1)  ≃  T(n+1) + x·U(n)`

Each is needed in the other's induction step, so we prove the conjunction
`linRel` simultaneously.  We write `1 − x²` as `1 + (-(x*x))` and the
top-level subtractions as `+ (-...)`. -/

/-- The two ladder relations at index `n`, as a `Prop` conjunction
(both sides are `Q'.eqv`, a genuinely propositional equality with no
erased witness — the *data* are `T`, `U` themselves). -/
def linRel (n : Nat) (x : Q') : Prop :=
  (T (n+2) x).eqv (x * T (n+1) x + (-( (1 + (-(x*x))) * U n x )))
  ∧ (U (n+1) x).eqv (T (n+1) x + x * U n x)

/-- Base case `linRel 0`: `T 2 ≃ x·T 1 − (1−x²)·U 0` and
`U 1 ≃ T 1 + x·U 0`, both pure polynomial identities in `x`. -/
theorem linRel_zero (x : Q') : linRel 0 x := by
  refine ⟨?_, ?_⟩
  · -- T 2 x = (2x)·x + (-1) ≈ x·x + (-((1-x²)·1))
    show (T 2 x) ≈ (x * T 1 x + (-( (1 + (-(x*x))) * U 0 x )))
    simp only [T_succ_succ, T_one, T_zero, U_zero]
    -- LHS = (2*x)*x + (-1) ; RHS = x*x + (-((1+(-(x*x)))*1))
    calc ((2 : Q') * x) * x + (-(1 : Q'))
        ≈ (x + x) * x + (-(1 : Q')) :=
          add_eqv_congr_right _ _ _ (mul_eqv_congr_right _ _ x (two_mul_eqv x))
      _ ≈ (x * x + x * x) + (-(1 : Q')) :=
          add_eqv_congr_right _ _ _ (add_mul_eqv x x x)
      _ ≈ x * x + (x * x + (-(1 : Q'))) := add_assoc_eqv _ _ _
      _ ≈ x * x + ((-(1 : Q')) + x * x) :=
          add_eqv_congr_left _ _ _ (add_comm_eqv _ _)
      _ ≈ x * x + (-((1 : Q') + (-(x * x)))) :=
          add_eqv_congr_left _ _ _
            (eqv_symm (eqv_trans _ _ _ (neg_add_eqv _ _)
              (add_eqv_congr_left _ _ _ (neg_neg_eqv _))))
      _ ≈ x * x + (-((1 + (-(x * x))) * 1)) :=
          add_eqv_congr_left _ _ _ (neg_eqv_congr _ _ (eqv_symm (mul_one_eqv _)))
  · -- U 1 x = 2*x ≈ x + x·1 = T 1 x + x·U 0 x
    show (U 1 x) ≈ (T 1 x + x * U 0 x)
    simp only [U_one, T_one, U_zero]
    calc (2 : Q') * x
        ≈ x + x := two_mul_eqv x
      _ ≈ x + x * 1 := add_eqv_congr_left _ _ _ (eqv_symm (mul_one_eqv x))

/-! ## The inductive step of the ladder relations

The two step identities reduce, via the compound-subterm `calc` method, to
all-atom polynomial identities `ladderA_tail`/`ladderB_tail` in `x, t, u`
(`t = T(n+1)`, `u = U(n)`).  Crucially we keep `1 + (-(x*x))` and `x*x` as
*compound* subterms manipulated by the proven `eqv` congruences — never
cross-multiplied into the `Int` denominators — which is what keeps the
degree-3 identities tractable without a `ring` tactic. -/

/-- `(1 + (-(x*x)))·y ≈ y + (-((x*x)·y))` — distribute `c = 1 − x²` over `y`. -/
theorem c_mul_eqv (x y : Q') : ((1 : Q') + (-(x*x))) * y ≈ y + (-((x*x)*y)) :=
  eqv_trans _ _ _ (add_mul_eqv 1 (-(x*x)) y)
    (add_eqv_congr _ _ _ _ (one_mul_eqv y) (neg_mul_eqv (x*x) y))

/-- `x·((1−x²)·u) ≈ (1−x²)·(x·u)` — commute `x` past the `c` factor. -/
theorem x_c_u_eqv (x u : Q') :
    x * (((1:Q')+(-(x*x)))*u) ≈ ((1:Q')+(-(x*x)))*(x*u) :=
  eqv_trans _ _ _ (eqv_symm (mul_assoc_eqv x ((1:Q')+(-(x*x))) u))
    (eqv_trans _ _ _ (mul_eqv_congr_right _ _ _ (mul_comm_eqv x ((1:Q')+(-(x*x)))))
      (mul_assoc_eqv ((1:Q')+(-(x*x))) x u))

/-- All-atom core for the (A) step:
`x·(x·t − (1−x²)·u) − t  ≈  −((1−x²)·(t + x·u))`. -/
theorem ladderA_tail (x t u : Q') :
    x * (x*t + (-(((1:Q')+(-(x*x)))*u))) + (-t) ≈ (-(((1:Q')+(-(x*x)))*(t + x*u))) := by
  have hLHS : x * (x*t + (-(((1:Q')+(-(x*x)))*u))) + (-t)
      ≈ ((x*x)*t + (-(((1:Q')+(-(x*x)))*(x*u)))) + (-t) := by
    apply add_eqv_congr _ _ _ _ _ (eqv_refl _)
    calc x * (x*t + (-(((1:Q')+(-(x*x)))*u)))
        ≈ x*(x*t) + x*(-(((1:Q')+(-(x*x)))*u)) := mul_add_eqv x (x*t) (-(((1:Q')+(-(x*x)))*u))
      _ ≈ (x*x)*t + x*(-(((1:Q')+(-(x*x)))*u)) :=
          add_eqv_congr_right _ _ _ (eqv_symm (mul_assoc_eqv x x t))
      _ ≈ (x*x)*t + (-(x*(((1:Q')+(-(x*x)))*u))) :=
          add_eqv_congr_left _ _ _ (mul_neg_eqv x (((1:Q')+(-(x*x)))*u))
      _ ≈ (x*x)*t + (-(((1:Q')+(-(x*x)))*(x*u))) :=
          add_eqv_congr_left _ _ _ (neg_eqv_congr _ _ (x_c_u_eqv x u))
  have hRHS : (-(((1:Q')+(-(x*x)))*(t + x*u)))
      ≈ ((-t) + (x*x)*t) + (-(((1:Q')+(-(x*x)))*(x*u))) := by
    calc (-(((1:Q')+(-(x*x)))*(t + x*u)))
        ≈ (-(((1:Q')+(-(x*x)))*t + ((1:Q')+(-(x*x)))*(x*u))) :=
          neg_eqv_congr _ _ (mul_add_eqv ((1:Q')+(-(x*x))) t (x*u))
      _ ≈ (-(((1:Q')+(-(x*x)))*t)) + (-(((1:Q')+(-(x*x)))*(x*u))) :=
          neg_add_eqv (((1:Q')+(-(x*x)))*t) (((1:Q')+(-(x*x)))*(x*u))
      _ ≈ (-(t + (-((x*x)*t)))) + (-(((1:Q')+(-(x*x)))*(x*u))) :=
          add_eqv_congr_right _ _ _ (neg_eqv_congr _ _ (c_mul_eqv x t))
      _ ≈ ((-t) + (-(-((x*x)*t)))) + (-(((1:Q')+(-(x*x)))*(x*u))) :=
          add_eqv_congr_right _ _ _ (neg_add_eqv t (-((x*x)*t)))
      _ ≈ ((-t) + (x*x)*t) + (-(((1:Q')+(-(x*x)))*(x*u))) :=
          add_eqv_congr_right _ _ _ (add_eqv_congr_left _ _ _ (neg_neg_eqv ((x*x)*t)))
  refine eqv_trans _ _ _ hLHS (eqv_trans _ _ _ ?_ (eqv_symm hRHS))
  calc ((x*x)*t + (-(((1:Q')+(-(x*x)))*(x*u)))) + (-t)
      ≈ (x*x)*t + ((-(((1:Q')+(-(x*x)))*(x*u))) + (-t)) :=
        add_assoc_eqv ((x*x)*t) (-(((1:Q')+(-(x*x)))*(x*u))) (-t)
    _ ≈ (x*x)*t + ((-t) + (-(((1:Q')+(-(x*x)))*(x*u)))) :=
        add_eqv_congr_left _ _ _ (add_comm_eqv _ _)
    _ ≈ ((x*x)*t + (-t)) + (-(((1:Q')+(-(x*x)))*(x*u))) :=
        eqv_symm (add_assoc_eqv _ _ _)
    _ ≈ ((-t) + (x*x)*t) + (-(((1:Q')+(-(x*x)))*(x*u))) :=
        add_eqv_congr_right _ _ _ (add_comm_eqv _ _)

/-- Full (A)-step identity:
`(2x)·P − t ≈ x·P − (1−x²)·(t + x·u)`  where `P = x·t − (1−x²)·u`.
Built from `ladderA_tail` by distributing `(x+x)·P` and cancelling one copy. -/
theorem ladderA_core (x t u : Q') :
    (x + x) * (x*t + (-(((1:Q')+(-(x*x)))*u))) + (-t)
      ≈ x * (x*t + (-(((1:Q')+(-(x*x)))*u))) + (-(((1:Q')+(-(x*x)))*(t + x*u))) := by
  calc (x + x) * (x*t + (-(((1:Q')+(-(x*x)))*u))) + (-t)
      ≈ (x * (x*t + (-(((1:Q')+(-(x*x)))*u))) + x * (x*t + (-(((1:Q')+(-(x*x)))*u)))) + (-t) :=
        add_eqv_congr_right _ _ _ (add_mul_eqv x x (x*t + (-(((1:Q')+(-(x*x)))*u))))
    _ ≈ x * (x*t + (-(((1:Q')+(-(x*x)))*u)))
          + (x * (x*t + (-(((1:Q')+(-(x*x)))*u))) + (-t)) := add_assoc_eqv _ _ _
    _ ≈ x * (x*t + (-(((1:Q')+(-(x*x)))*u))) + (-(((1:Q')+(-(x*x)))*(t + x*u))) :=
        add_eqv_congr_left _ _ _ (ladderA_tail x t u)

/-- All-atom core for the (B) step:
`x·(t + x·u) − u  ≈  x·t − (1−x²)·u`. -/
theorem ladderB_tail (x t u : Q') :
    x*(t + x*u) + (-u) ≈ x*t + (-(((1:Q')+(-(x*x)))*u)) := by
  have hLHS : x*(t + x*u) + (-u) ≈ (x*t + (x*x)*u) + (-u) := by
    apply add_eqv_congr _ _ _ _ _ (eqv_refl _)
    calc x*(t + x*u) ≈ x*t + x*(x*u) := mul_add_eqv x t (x*u)
      _ ≈ x*t + (x*x)*u := add_eqv_congr_left _ _ _ (eqv_symm (mul_assoc_eqv x x u))
  have hRHS : x*t + (-(((1:Q')+(-(x*x)))*u)) ≈ x*t + ((-u) + (x*x)*u) := by
    apply add_eqv_congr_left
    calc (-(((1:Q')+(-(x*x)))*u)) ≈ (-(u + (-((x*x)*u)))) := neg_eqv_congr _ _ (c_mul_eqv x u)
      _ ≈ (-u) + (-(-((x*x)*u))) := neg_add_eqv u (-((x*x)*u))
      _ ≈ (-u) + (x*x)*u := add_eqv_congr_left _ _ _ (neg_neg_eqv ((x*x)*u))
  refine eqv_trans _ _ _ hLHS (eqv_trans _ _ _ ?_ (eqv_symm hRHS))
  calc (x*t + (x*x)*u) + (-u) ≈ x*t + ((x*x)*u + (-u)) := add_assoc_eqv _ _ _
    _ ≈ x*t + ((-u) + (x*x)*u) := add_eqv_congr_left _ _ _ (add_comm_eqv _ _)

/-- Full (B)-step identity:
`(2x)·V − u ≈ (x·t − (1−x²)·u) + x·V`  where `V = t + x·u`.
Built from `ladderB_tail` by distributing `(x+x)·V` and cancelling one copy. -/
theorem ladderB_core (x t u : Q') :
    (x + x) * (t + x*u) + (-u)
      ≈ (x*t + (-(((1:Q')+(-(x*x)))*u))) + x * (t + x*u) := by
  calc (x + x) * (t + x*u) + (-u)
      ≈ (x * (t + x*u) + x * (t + x*u)) + (-u) :=
        add_eqv_congr_right _ _ _ (add_mul_eqv x x (t + x*u))
    _ ≈ x * (t + x*u) + (x * (t + x*u) + (-u)) := add_assoc_eqv _ _ _
    _ ≈ x * (t + x*u) + (x*t + (-(((1:Q')+(-(x*x)))*u))) :=
        add_eqv_congr_left _ _ _ (ladderB_tail x t u)
    _ ≈ (x*t + (-(((1:Q')+(-(x*x)))*u))) + x * (t + x*u) :=
        add_comm_eqv _ _

/-- **The inductive step of the ladder relations.**  `linRel n x →
linRel (n+1) x`.  Each conjunct: unfold the recurrence for `T(n+3)` /
`U(n+2)`, substitute the level-`n` relations into the `T(n+2)` / `U(n+1)`
occurrences via congruence, and apply the all-atom `ladderA_tail` /
`ladderB_tail`. -/
theorem linRel_step (n : Nat) (x : Q') (h : linRel n x) : linRel (n+1) x := by
  obtain ⟨ha, hb⟩ := h
  -- abbreviations
  -- ha : T (n+2) x ≈ x*T(n+1)x + (-(c*U n x))
  -- hb : U (n+1) x ≈ T(n+1)x + x*U n x
  refine ⟨?_, ?_⟩
  · -- (A_{n+1}) : T(n+3) ≈ x*T(n+2) + (-(c*U(n+1)))
    show (T (n+3) x) ≈ (x * T (n+2) x + (-(((1:Q')+(-(x*x))) * U (n+1) x)))
    rw [T_succ_succ (n+1) x]
    -- LHS = (2x)*T(n+2) + (-(T(n+1)))
    -- Substitute T(n+2) via ha on LHS and on RHS, and U(n+1) via hb on RHS.
    calc ((2 : Q') * x) * T (n+2) x + (-(T (n+1) x))
        ≈ (x + x) * T (n+2) x + (-(T (n+1) x)) :=
          add_eqv_congr_right _ _ _ (mul_eqv_congr_right _ _ _ (two_mul_eqv x))
      _ ≈ (x + x) * (x * T (n+1) x + (-(((1:Q')+(-(x*x))) * U n x))) + (-(T (n+1) x)) :=
          add_eqv_congr_right _ _ _ (mul_eqv_congr_left _ _ _ ha)
      _ ≈ x * (x * T (n+1) x + (-(((1:Q')+(-(x*x))) * U n x)))
            + (-(((1:Q')+(-(x*x))) * (T (n+1) x + x * U n x))) :=
          ladderA_core x (T (n+1) x) (U n x)
      _ ≈ x * T (n+2) x + (-(((1:Q')+(-(x*x))) * (T (n+1) x + x * U n x))) :=
          add_eqv_congr_right _ _ _ (mul_eqv_congr_left _ _ _ (eqv_symm ha))
      _ ≈ x * T (n+2) x + (-(((1:Q')+(-(x*x))) * U (n+1) x)) :=
          add_eqv_congr_left _ _ _
            (neg_eqv_congr _ _ (mul_eqv_congr_left _ _ _ (eqv_symm hb)))
  · -- (B_{n+1}) : U(n+2) ≈ T(n+2) + x*U(n+1)
    show (U (n+2) x) ≈ (T (n+2) x + x * U (n+1) x)
    rw [U_succ_succ n x]
    calc ((2 : Q') * x) * U (n+1) x + (-(U n x))
        ≈ (x + x) * U (n+1) x + (-(U n x)) :=
          add_eqv_congr_right _ _ _ (mul_eqv_congr_right _ _ _ (two_mul_eqv x))
      _ ≈ (x + x) * (T (n+1) x + x * U n x) + (-(U n x)) :=
          add_eqv_congr_right _ _ _ (mul_eqv_congr_left _ _ _ hb)
      _ ≈ (x * T (n+1) x + (-(((1:Q')+(-(x*x))) * U n x))) + x * (T (n+1) x + x * U n x) :=
          ladderB_core x (T (n+1) x) (U n x)
      _ ≈ T (n+2) x + x * (T (n+1) x + x * U n x) :=
          add_eqv_congr_right _ _ _ (eqv_symm ha)
      _ ≈ T (n+2) x + x * U (n+1) x :=
          add_eqv_congr_left _ _ _ (mul_eqv_congr_left _ _ _ (eqv_symm hb))

/-- The ladder relations hold at every order (base `linRel_zero` + step). -/
theorem linRel_all (n : Nat) (x : Q') : linRel n x := by
  induction n with
  | zero => exact linRel_zero x
  | succ k ih => exact linRel_step k x ih

/-! ## Order helpers on `Q'` for the square bound

`square_nonneg`, the "drop a nonneg summand" lemma, and the
`1 − x² ≥ 0` fact on `[−1,1]` — the constructive `≤` ingredients of
`T_n² ≤ 1`.  None of these need the `eqv`-ring machinery; they are pure
order facts over `Int`/`Q'`. -/

/-- Every `Q'` square is `≥ 0`: reduce to `0 ≤ a.num·a.num = a.num²`. -/
theorem square_nonneg (a : Q') : (0 : Q') ≤ a * a := by
  rw [zero_le_iff_num_nonneg]
  show (0 : Int) ≤ (a * a).num
  show (0 : Int) ≤ a.num * a.num
  rcases Int.le_total 0 a.num with h | h
  · exact Int.mul_nonneg h h
  · have hh : (0 : Int) ≤ (-a.num) * (-a.num) :=
      Int.mul_nonneg (Int.neg_nonneg.mpr h) (Int.neg_nonneg.mpr h)
    rwa [Int.neg_mul_neg] at hh

/-- If `a + b ≈ 1` and `0 ≤ b`, then `a ≤ 1`.  (`a ≤ a + b ≈ 1`.) -/
theorem le_one_of_add_eqv_one (a b : Q') (h : (a + b) ≈ (1 : Q')) (hb : (0 : Q') ≤ b) :
    a ≤ (1 : Q') :=
  le_trans' a (a + b) 1 (add_le_self_of_nonneg a b hb) (le_of_eqv h)

/-- On `[−1,1]`, `0 ≤ 1 − x²`.  We take `1 − x²` in the form `1 + (-(x*x))`
and prove `0 ≤ 1 + (-(x*x))` from `(-1) ≤ x` and `x ≤ 1`.

`x ≤ 1` and `−1 ≤ x` give `0 ≤ 1 − x` and `0 ≤ 1 + x`; their product is
`(1−x)(1+x) = 1 − x²`.  We assemble it over `Q'` with `mul_nonneg`, then
bridge `(1+(-x))*(1+x) ≈ 1 + (-(x*x))` by the automated `eqv`-poly closer
(small, degree-2, single atom). -/
theorem one_sub_sq_nonneg (x : Q') (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) :
    (0 : Q') ≤ 1 + (-(x * x)) := by
  -- 0 ≤ (1 + (-x)) and 0 ≤ (1 + x)
  have h1mx : (0 : Q') ≤ (1 : Q') + (-x) := by
    -- from x ≤ 1: add (-x) to both sides → x + (-x) ≤ 1 + (-x); and 0 ≈ x + (-x).
    have hstep : x + (-x) ≤ 1 + (-x) := add_le_add_right x 1 (-x) hx1
    -- 0 ≈ (-x) + x ≈ x + (-x)
    have hz : (0 : Q') ≈ (x + (-x)) :=
      eqv_trans 0 ((-x) + x) (x + (-x))
        (eqv_symm (neg_add_self_eqv x)) (add_comm_eqv (-x) x)
    exact le_trans' 0 (x + (-x)) (1 + (-x)) (le_of_eqv hz) hstep
  have h1px : (0 : Q') ≤ (1 : Q') + x := by
    -- from -1 ≤ x: add 1 on the left → 1 + (-1) ≤ 1 + x; and 0 ≈ 1 + (-1).
    have hstep : (1 : Q') + (-1) ≤ 1 + x := add_le_add_left 1 (-1) x hxm1
    have hz : (0 : Q') ≈ ((1 : Q') + (-1)) :=
      eqv_trans 0 ((-(1:Q')) + 1) ((1:Q') + (-1))
        (eqv_symm (neg_add_self_eqv 1)) (add_comm_eqv (-1) 1)
    exact le_trans' 0 (1 + (-1)) (1 + x) (le_of_eqv hz) hstep
  -- product is nonneg
  have hprod : (0 : Q') ≤ ((1 : Q') + (-x)) * ((1 : Q') + x) := mul_nonneg _ _ h1mx h1px
  -- (1 + (-x))*(1 + x) ≈ 1 + (-(x*x))
  have hbridge : ((1 : Q') + (-x)) * ((1 : Q') + x) ≈ (1 + (-(x * x))) := by
    unfold Q'.eqv
    have d1 : ((1 : Q').den : Int) = 1 := rfl
    have n1 : ((1 : Q').num) = 1 := rfl
    simp only [add_num, mul_num, neg_num, add_den_cast, mul_den_cast, neg_den, d1, n1,
      Int.mul_one, Int.one_mul, Int.mul_add, Int.add_mul, Int.neg_mul, Int.mul_neg, Int.neg_neg,
      Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
    generalize (x.den : Int) = d
    generalize x.num = m
    omega
  exact le_trans' 0 _ _ hprod (le_of_eqv hbridge)

/-! ## The Pythagorean / quadratic-form invariant

`pythForm n x : T(n+1)² + (1−x²)·U(n)² ≈ 1`.

This is the algebraic heart.  For `n = 0` it is the elementary identity
`x² + (1−x²)·1 ≈ 1`, closed below by the automated `eqv`-poly closer.
The general `n` requires the ladder relations `linRel` (so that the
quadratic form `Φ(a,b) = a² + (1−x²)b²` is invariant under the step map);
that induction is recorded as the named open `Prop`
`OpenProblem.pythForm_all` — see the honesty note at the end of the file. -/

/-- `pythForm n x` : the squared-norm identity at level `n`. -/
def pythForm (n : Nat) (x : Q') : Prop :=
  (T (n+1) x * T (n+1) x + (1 + (-(x*x))) * (U n x * U n x)) ≈ (1 : Q')

/-- Base case `pythForm 0`: `T 1² + (1−x²)·U 0² ≈ x² + (1−x²)·1 ≈ 1`. -/
theorem pythForm_zero (x : Q') : pythForm 0 x := by
  show (T 1 x * T 1 x + (1 + (-(x*x))) * (U 0 x * U 0 x)) ≈ (1 : Q')
  simp only [T_one, U_zero]
  -- goal: x*x + (1+(-(x*x)))*(1*1) ≈ 1
  unfold Q'.eqv
  have d1 : ((1 : Q').den : Int) = 1 := rfl
  have n1 : ((1 : Q').num) = 1 := rfl
  simp only [add_num, mul_num, neg_num, add_den_cast, mul_den_cast, neg_den, d1, n1,
    Int.mul_one, Int.one_mul, Int.mul_add, Int.add_mul, Int.neg_mul, Int.mul_neg, Int.neg_neg,
    Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
  generalize (x.den : Int) = d
  generalize x.num = m
  omega

/-! ### Quadratic-form invariance — the inductive step of `pythForm`

The map `(t,u) ↦ (x·t − (1−x²)·u, t + x·u)` (which `linRel` shows sends
`(T(n+1),U(n))` to `(T(n+2),U(n+1))`) preserves the quadratic form
`Φ(a,b) = a² + (1−x²)·b²`.  We prove this `Φ`-invariance once
(`pythStep_core`), built from the block lemmas below, all via the
compound-subterm `calc` method (no cross-multiplied denominators). -/

/-- Square of a sum: `(p+q)² ≈ (p² + p·q) + (q·p + q²)`. -/
theorem sq_add_eqv (p q : Q') : (p + q) * (p + q) ≈ (p*p + p*q) + (q*p + q*q) :=
  eqv_trans _ _ _ (add_mul_eqv p q (p+q))
    (add_eqv_congr _ _ _ _ (mul_add_eqv p p q) (mul_add_eqv q p q))

/-- `x² + (1−x²) ≈ 1` (the defining relation `x² + c = 1`). -/
theorem xx_add_c_eqv (x : Q') : x*x + ((1:Q')+(-(x*x))) ≈ (1 : Q') := by
  unfold Q'.eqv
  have d1 : ((1 : Q').den : Int) = 1 := rfl
  have n1 : ((1 : Q').num) = 1 := rfl
  simp only [add_num, mul_num, neg_num, add_den_cast, mul_den_cast, neg_den, d1, n1,
    Int.mul_one, Int.one_mul, Int.mul_add, Int.add_mul, Int.neg_mul, Int.mul_neg,
    Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]
  generalize (x.den : Int) = d; generalize x.num = m; omega

/-- `(1−x²) + x² ≈ 1` (commuted). -/
theorem c_add_xx_eqv (x : Q') : ((1:Q')+(-(x*x))) + x*x ≈ (1 : Q') :=
  eqv_trans _ _ _ (add_comm_eqv _ _) (xx_add_c_eqv x)

/-- `(a·w)² ≈ a²·w²`. -/
theorem mulsq_eqv (a w : Q') : (a*w)*(a*w) ≈ (a*a)*(w*w) :=
  eqv_trans _ _ _ (mul_assoc_eqv a w (a*w))
    (eqv_trans _ _ _ (mul_eqv_congr_left _ _ _ (eqv_symm (mul_assoc_eqv w a w)))
      (eqv_trans _ _ _ (mul_eqv_congr_left _ _ _ (mul_eqv_congr_right _ _ _ (mul_comm_eqv w a)))
        (eqv_trans _ _ _ (mul_eqv_congr_left _ _ _ (mul_assoc_eqv a w w))
          (eqv_symm (mul_assoc_eqv a a (w*w))))))

/-- A-block: `(x·t)² + (1−x²)·t² ≈ t²` (uses `x²+c ≈ 1`). -/
theorem Ablock_eqv (x t : Q') :
    (x*t)*(x*t) + ((1:Q')+(-(x*x)))*(t*t) ≈ t*t :=
  eqv_trans _ _ _ (add_eqv_congr_right _ _ _ (mulsq_eqv x t))
    (eqv_trans _ _ _ (eqv_symm (add_mul_eqv (x*x) ((1:Q')+(-(x*x))) (t*t)))
      (eqv_trans _ _ _ (mul_eqv_congr_right _ _ _ (xx_add_c_eqv x)) (one_mul_eqv (t*t))))

/-- B-block: `((1−x²)·u)² + (1−x²)·(x·u)² ≈ (1−x²)·u²` (uses `c+x² ≈ 1`). -/
theorem Bblock_eqv (x u : Q') :
    (((1:Q')+(-(x*x)))*u)*(((1:Q')+(-(x*x)))*u) + ((1:Q')+(-(x*x)))*((x*u)*(x*u))
      ≈ ((1:Q')+(-(x*x)))*(u*u) := by
  calc (((1:Q')+(-(x*x)))*u)*(((1:Q')+(-(x*x)))*u) + ((1:Q')+(-(x*x)))*((x*u)*(x*u))
      ≈ (((1:Q')+(-(x*x)))*((1:Q')+(-(x*x))))*(u*u) + ((1:Q')+(-(x*x)))*((x*u)*(x*u)) :=
        add_eqv_congr_right _ _ _ (mulsq_eqv ((1:Q')+(-(x*x))) u)
    _ ≈ (((1:Q')+(-(x*x)))*((1:Q')+(-(x*x))))*(u*u) + ((1:Q')+(-(x*x)))*((x*x)*(u*u)) :=
        add_eqv_congr_left _ _ _ (mul_eqv_congr_left _ _ _ (mulsq_eqv x u))
    _ ≈ ((1:Q')+(-(x*x)))*(((1:Q')+(-(x*x)))*(u*u)) + ((1:Q')+(-(x*x)))*((x*x)*(u*u)) :=
        add_eqv_congr_right _ _ _ (mul_assoc_eqv ((1:Q')+(-(x*x))) ((1:Q')+(-(x*x))) (u*u))
    _ ≈ ((1:Q')+(-(x*x)))*((((1:Q')+(-(x*x)))*(u*u)) + ((x*x)*(u*u))) :=
        eqv_symm (mul_add_eqv ((1:Q')+(-(x*x))) (((1:Q')+(-(x*x)))*(u*u)) ((x*x)*(u*u)))
    _ ≈ ((1:Q')+(-(x*x)))*((((1:Q')+(-(x*x))) + (x*x))*(u*u)) :=
        mul_eqv_congr_left _ _ _ (eqv_symm (add_mul_eqv ((1:Q')+(-(x*x))) (x*x) (u*u)))
    _ ≈ ((1:Q')+(-(x*x)))*((1:Q')*(u*u)) :=
        mul_eqv_congr_left _ _ _ (mul_eqv_congr_right _ _ _ (c_add_xx_eqv x))
    _ ≈ ((1:Q')+(-(x*x)))*(u*u) :=
        mul_eqv_congr_left _ _ _ (one_mul_eqv (u*u))

/-- Cross-term product rearrangement `c·(t·(x·u)) ≈ (x·t)·(c·u)`. -/
theorem prod4_a_eqv (x t c u : Q') : c*(t*(x*u)) ≈ (x*t)*(c*u) := by
  calc c*(t*(x*u)) ≈ c*((t*x)*u) := mul_eqv_congr_left _ _ _ (eqv_symm (mul_assoc_eqv t x u))
    _ ≈ c*((x*t)*u) := mul_eqv_congr_left _ _ _ (mul_eqv_congr_right _ _ _ (mul_comm_eqv t x))
    _ ≈ c*(x*t)*u := eqv_symm (mul_assoc_eqv c (x*t) u)
    _ ≈ (x*t)*c*u := mul_eqv_congr_right _ _ _ (mul_comm_eqv c (x*t))
    _ ≈ (x*t)*(c*u) := mul_assoc_eqv (x*t) c u

/-- Cross-term product rearrangement `c·((x·u)·t) ≈ (x·t)·(c·u)`. -/
theorem prod4_b_eqv (x t c u : Q') : c*((x*u)*t) ≈ (x*t)*(c*u) := by
  calc c*((x*u)*t) ≈ c*(x*(u*t)) := mul_eqv_congr_left _ _ _ (mul_assoc_eqv x u t)
    _ ≈ c*(x*(t*u)) := mul_eqv_congr_left _ _ _ (mul_eqv_congr_left _ _ _ (mul_comm_eqv u t))
    _ ≈ c*((x*t)*u) := mul_eqv_congr_left _ _ _ (eqv_symm (mul_assoc_eqv x t u))
    _ ≈ c*(x*t)*u := eqv_symm (mul_assoc_eqv c (x*t) u)
    _ ≈ (x*t)*c*u := mul_eqv_congr_right _ _ _ (mul_comm_eqv c (x*t))
    _ ≈ (x*t)*(c*u) := mul_assoc_eqv (x*t) c u

/-- `(-p)·(-p) ≈ p·p`. -/
theorem negnegmul_eqv (p : Q') : (-p)*(-p) ≈ p*p :=
  eqv_trans _ _ _ (neg_mul_eqv p (-p))
    (eqv_trans _ _ _ (neg_eqv_congr _ _ (mul_neg_eqv p p)) (neg_neg_eqv (p*p)))

/-- Eight-summand regroup (via `add_swap_inner`): collect the two
`A`/`cA`, the four cross, and the two `B`/`cB` summands. -/
theorem regroup8_eqv (A1 xc1 xc2 B1 cA2 cx1 cx2 cB2 : Q') :
    ((A1 + xc1) + (xc2 + B1)) + ((cA2 + cx1) + (cx2 + cB2))
      ≈ (A1 + cA2) + (((xc1 + xc2) + (cx1 + cx2)) + (B1 + cB2)) := by
  calc ((A1 + xc1) + (xc2 + B1)) + ((cA2 + cx1) + (cx2 + cB2))
      ≈ ((A1 + xc1) + (cA2 + cx1)) + ((xc2 + B1) + (cx2 + cB2)) :=
        add_swap_inner (A1+xc1) (xc2+B1) (cA2+cx1) (cx2+cB2)
    _ ≈ ((A1 + cA2) + (xc1 + cx1)) + ((xc2 + B1) + (cx2 + cB2)) :=
        add_eqv_congr_right _ _ _ (add_swap_inner A1 xc1 cA2 cx1)
    _ ≈ ((A1 + cA2) + (xc1 + cx1)) + ((xc2 + cx2) + (B1 + cB2)) :=
        add_eqv_congr_left _ _ _ (add_swap_inner xc2 B1 cx2 cB2)
    _ ≈ (A1 + cA2) + ((xc1 + cx1) + ((xc2 + cx2) + (B1 + cB2))) :=
        add_assoc_eqv (A1+cA2) (xc1+cx1) ((xc2+cx2)+(B1+cB2))
    _ ≈ (A1 + cA2) + (((xc1 + cx1) + (xc2 + cx2)) + (B1 + cB2)) :=
        add_eqv_congr_left _ _ _ (eqv_symm (add_assoc_eqv (xc1+cx1) (xc2+cx2) (B1+cB2)))
    _ ≈ (A1 + cA2) + (((xc1 + xc2) + (cx1 + cx2)) + (B1 + cB2)) :=
        add_eqv_congr_left _ _ _ (add_eqv_congr_right _ _ _ (add_swap_inner xc1 cx1 xc2 cx2))

/-- The four cross terms cancel: `((-M)+(-M)) + (M+M) ≈ 0`. -/
theorem crossZero_eqv (M : Q') : ((-M) + (-M)) + (M + M) ≈ (0 : Q') := by
  calc ((-M) + (-M)) + (M + M) ≈ ((-M) + M) + ((-M) + M) := add_swap_inner (-M) (-M) M M
    _ ≈ (0:Q') + (0:Q') := add_eqv_congr _ _ _ _ (neg_add_self_eqv M) (neg_add_self_eqv M)
    _ ≈ (0:Q') := by
        show ((0:Q') + 0).num * ((0:Q').den:Int) = (0:Q').num * (((0:Q')+0).den:Int); rfl

/-- **Quadratic-form invariance.**  With `c = 1 − x²`,
`(x·t − c·u)² + c·(t + x·u)² ≈ t² + c·u²`.  This is the algebraic heart of
the Pythagorean induction; the cross terms `±(x·t)(c·u)` cancel and the two
"diagonal" blocks collapse via `x² + c ≈ 1`. -/
theorem pythStep_core (x t u : Q') :
    (x*t + (-(((1:Q')+(-(x*x)))*u)))*(x*t + (-(((1:Q')+(-(x*x)))*u)))
        + ((1:Q')+(-(x*x)))*((t + x*u)*(t + x*u))
      ≈ t*t + ((1:Q')+(-(x*x)))*(u*u) := by
  have haa : (x*t + (-(((1:Q')+(-(x*x)))*u)))*(x*t + (-(((1:Q')+(-(x*x)))*u)))
      ≈ ((x*t)*(x*t) + (-((x*t)*(((1:Q')+(-(x*x)))*u))))
        + ((-((x*t)*(((1:Q')+(-(x*x)))*u))) + (((1:Q')+(-(x*x)))*u)*(((1:Q')+(-(x*x)))*u)) := by
    refine eqv_trans _ _ _ (sq_add_eqv (x*t) (-(((1:Q')+(-(x*x)))*u))) ?_
    refine add_eqv_congr _ _ _ _ ?_ ?_
    · exact add_eqv_congr_left _ _ _ (mul_neg_eqv (x*t) (((1:Q')+(-(x*x)))*u))
    · refine add_eqv_congr _ _ _ _ ?_ (negnegmul_eqv (((1:Q')+(-(x*x)))*u))
      exact eqv_trans _ _ _ (neg_mul_eqv (((1:Q')+(-(x*x)))*u) (x*t))
        (neg_eqv_congr _ _ (mul_comm_eqv (((1:Q')+(-(x*x)))*u) (x*t)))
  have hcbb : ((1:Q')+(-(x*x)))*((t + x*u)*(t + x*u))
      ≈ ((((1:Q')+(-(x*x)))*(t*t) + ((1:Q')+(-(x*x)))*(t*(x*u)))
         + (((1:Q')+(-(x*x)))*((x*u)*t) + ((1:Q')+(-(x*x)))*((x*u)*(x*u)))) := by
    refine eqv_trans _ _ _ (mul_eqv_congr_left _ _ _ (sq_add_eqv t (x*u))) ?_
    refine eqv_trans _ _ _
      (mul_add_eqv ((1:Q')+(-(x*x))) (t*t + t*(x*u)) ((x*u)*t + (x*u)*(x*u))) ?_
    exact add_eqv_congr _ _ _ _
      (mul_add_eqv ((1:Q')+(-(x*x))) (t*t) (t*(x*u)))
      (mul_add_eqv ((1:Q')+(-(x*x))) ((x*u)*t) ((x*u)*(x*u)))
  refine eqv_trans _ _ _ (add_eqv_congr _ _ _ _ haa hcbb) ?_
  refine eqv_trans _ _ _ (regroup8_eqv ((x*t)*(x*t)) (-((x*t)*(((1:Q')+(-(x*x)))*u)))
      (-((x*t)*(((1:Q')+(-(x*x)))*u))) ((((1:Q')+(-(x*x)))*u)*(((1:Q')+(-(x*x)))*u))
      (((1:Q')+(-(x*x)))*(t*t)) (((1:Q')+(-(x*x)))*(t*(x*u)))
      (((1:Q')+(-(x*x)))*((x*u)*t)) (((1:Q')+(-(x*x)))*((x*u)*(x*u)))) ?_
  have hM : ((-((x*t)*(((1:Q')+(-(x*x)))*u))) + (-((x*t)*(((1:Q')+(-(x*x)))*u))))
            + ((((1:Q')+(-(x*x)))*(t*(x*u))) + (((1:Q')+(-(x*x)))*((x*u)*t)))
      ≈ (0:Q') :=
    eqv_trans _ _ _
      (add_eqv_congr_left _ _ _
        (add_eqv_congr _ _ _ _ (prod4_a_eqv x t ((1:Q')+(-(x*x))) u)
          (prod4_b_eqv x t ((1:Q')+(-(x*x))) u)))
      (crossZero_eqv ((x*t)*(((1:Q')+(-(x*x)))*u)))
  refine eqv_trans _ _ _
    (add_eqv_congr _ _ _ _ (Ablock_eqv x t)
      (add_eqv_congr _ _ _ _ hM (Bblock_eqv x u))) ?_
  exact add_eqv_congr_left _ _ _ (by rw [zero_add']; exact eqv_refl _)

/-- **The inductive step of `pythForm`.**  `pythForm n x → pythForm (n+1) x`,
substituting the ladder relations `linRel n` into the `Φ`-invariance. -/
theorem pythForm_step (n : Nat) (x : Q') (h : pythForm n x) : pythForm (n+1) x := by
  obtain ⟨ha, hb⟩ := linRel_all n x
  show (T (n+2) x * T (n+2) x + (1 + (-(x*x))) * (U (n+1) x * U (n+1) x)) ≈ (1 : Q')
  -- substitute T(n+2) and U(n+1) via the ladder relations into Φ
  refine eqv_trans _ _ _
    (add_eqv_congr _ _ _ _
      (mul_eqv_congr _ _ _ _ ha ha)
      (mul_eqv_congr_left _ _ _ (mul_eqv_congr _ _ _ _ hb hb))) ?_
  -- now it is exactly the Φ-invariance, then pythForm n
  refine eqv_trans _ _ _ (pythStep_core x (T (n+1) x) (U n x)) ?_
  exact h

/-- **The Pythagorean invariant at all orders.**  `∀ n, pythForm n x`
(base `pythForm_zero` + step `pythForm_step`). -/
theorem pythForm_all (n : Nat) (x : Q') : pythForm n x := by
  induction n with
  | zero => exact pythForm_zero x
  | succ k ih => exact pythForm_step k x ih

/-! ## The square bound `T_n(x)² ≤ 1` on `[−1,1]`

Given `pythForm n x` and `x ∈ [−1,1]`, the dropped summand
`(1−x²)·U(n)²` is `≥ 0`, so `T(n+1)² ≤ 1`.  This deduction is the
constructive `≤` payoff and needs no ring machinery beyond the helpers
above; it is proved unconditionally on the analytic input `pythForm`. -/

/-- **Conditional square bound.**  From the Pythagorean identity at level
`n` and `x ∈ [−1,1]`, `T(n+1)(x)² ≤ 1`. -/
theorem Tsq_le_one_of_pythForm (n : Nat) (x : Q')
    (hpyth : pythForm n x) (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) :
    T (n+1) x * T (n+1) x ≤ (1 : Q') := by
  -- the dropped summand is nonneg: (1−x²) ≥ 0 and U(n)² ≥ 0.
  have hc : (0 : Q') ≤ 1 + (-(x * x)) := one_sub_sq_nonneg x hx1 hxm1
  have hb : (0 : Q') ≤ (1 + (-(x*x))) * (U n x * U n x) :=
    mul_nonneg _ _ hc (square_nonneg (U n x))
  exact le_one_of_add_eqv_one _ _ hpyth hb

/-- **The Chebyshev square bound, all orders.**  `T_n(x)² ≤ 1` on `[−1,1]`
for every `n ≥ 1`, unconditionally (combining `pythForm_all` with the `≤`
deduction).  This is the closed form of the sub-crux "`|T_n(x)| ≤ 1` on
`[−1,1]`" flagged by the heat-kernel positivity work. -/
theorem Tsq_le_one (n : Nat) (x : Q') (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) :
    T (n+1) x * T (n+1) x ≤ (1 : Q') :=
  Tsq_le_one_of_pythForm n x (pythForm_all n x) hx1 hxm1

/-- **Unconditional square bound at `n = 1`**: `T₁(x)² = x² ≤ 1` on
`[−1,1]`. -/
theorem T1_sq_le_one (x : Q') (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) :
    T 1 x * T 1 x ≤ (1 : Q') :=
  Tsq_le_one 0 x hx1 hxm1

/-- **Unconditional square bound at `n = 0`**: `T₀(x)² = 1 ≤ 1` trivially. -/
theorem T0_sq_le_one (x : Q') : T 0 x * T 0 x ≤ (1 : Q') := by
  show (1 : Q') * 1 ≤ (1 : Q')
  exact le_of_eqv (one_mul_eqv 1)

/-! ## Honest open problems (AGENTS.md Rule 6)

`|T_n(x)| ≤ 1` (as the square bound `Tsq_le_one`) is CLOSED above, via the
fully-closed `linRel_all` (ladder relations at all orders) and `pythForm_all`
(the Pythagorean invariant at all orders).  What remains open is the
*second-kind* bound `|U_{n-1}(x)| ≤ n`, recorded below as a true statement
whose Lean proof needs the separate finite-sum T-decomposition induction. -/

namespace OpenProblem

/-- **Open: the second-kind bound `|U_{n-1}(x)| ≤ n` on `[−1,1]`.**  In the
`Q'`/`U`-indexing this is `−(ofNat (n+1)) ≤ U n x ≤ ofNat (n+1)` for
`x ∈ [−1,1]`.  The algebraic route is the T-decomposition
`U_n = Σ_{k=0}^{n} T_{|n-2k|}` (the polynomial shadow of
`U_n(cos θ) = Σ cos((n−2k)θ)`), proved by induction; then
`|U_n| ≤ Σ |T_{…}| ≤ (n+1)·1 = n+1` by the (closed) bound `|T_m| ≤ 1` and the
triangle inequality over the finite sum.  The naive `U`-recurrence triangle
bound FAILS here (it yields `≈ 2.414ⁿ`), so the decomposition (or another
genuinely-bounded route) is required.  Stated with the `≤` order on `Q'`. -/
def absU_le : Prop :=
  ∀ (n : Nat) (x : Q'), x ≤ (1 : Q') → (-(1 : Q')) ≤ x →
    (U n x ≤ Q'.ofNat (n+1) ∧ (-(Q'.ofNat (n+1))) ≤ U n x)

end OpenProblem

end YMGap.Continuum.Cheb

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem must report `[propext]` or `[propext, Quot.sound]`
(both MLTT/HoTT-valid; `Quot.sound` enters only via `omega`'s reused `Int`
helpers in the small base-case closers) — never `Classical.*`, `sorryAx`, or
`native_decide`. -/

#print axioms YMGap.Continuum.Cheb.two_mul_eqv
#print axioms YMGap.Continuum.Cheb.neg_add_eqv
#print axioms YMGap.Continuum.Cheb.linRel_zero
#print axioms YMGap.Continuum.Cheb.ladderA_tail
#print axioms YMGap.Continuum.Cheb.ladderB_tail
#print axioms YMGap.Continuum.Cheb.linRel_step
#print axioms YMGap.Continuum.Cheb.linRel_all
#print axioms YMGap.Continuum.Cheb.square_nonneg
#print axioms YMGap.Continuum.Cheb.one_sub_sq_nonneg
#print axioms YMGap.Continuum.Cheb.pythForm_zero
#print axioms YMGap.Continuum.Cheb.pythStep_core
#print axioms YMGap.Continuum.Cheb.pythForm_step
#print axioms YMGap.Continuum.Cheb.pythForm_all
#print axioms YMGap.Continuum.Cheb.Tsq_le_one_of_pythForm
#print axioms YMGap.Continuum.Cheb.Tsq_le_one
#print axioms YMGap.Continuum.Cheb.T1_sq_le_one
#print axioms YMGap.Continuum.Cheb.T0_sq_le_one
