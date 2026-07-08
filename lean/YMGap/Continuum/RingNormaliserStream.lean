/-
**Streaming / grid decision procedure for HIGH-DEGREE multivariate polynomial
identities over `Q'` (Lean-core; no Mathlib, no `native_decide`).**

`RingNormaliser.lean` decides a polynomial identity `∀ρ, eval e₁ ρ ≃ eval e₂ ρ`
by canonicalising both sides (`normalize`) and a kernel `decide` on the
resulting `NormalPoly` list equality.  That canonical form is materialised by
`rawMul`, which DISTRIBUTES: a product of `k` binomials expands to `2^k`
intermediate monomials before `canon` combines them.  The kernel `decide` then
has to build *and* compare those large lists, which blows up — empirically the
Chu–Vandermonde convolution demos in `RingNormaliser` stop at degree 4.

This module adds a **sound decision procedure that never materialises the
expanded polynomial.**  The idea is deterministic Schwartz–Zippel:

  * A polynomial of degree `≤ d` in one variable that vanishes at `d+1`
    DISTINCT points is identically zero (`roots_zero`, the load-bearing theorem,
    proved from a division-free factor theorem `eval_deflate` iterated over the
    root list — a genuine induction, never assumed).
  * Hence a `k`-variable polynomial of degree `≤ d` in each variable that
    vanishes on the integer grid `{0,…,d}^k` is identically zero.  For `k=2`
    (`poly_identity_of_grid2`) this is two applications of `roots_zero`.
  * The grid is a FINITE set of point-evaluations.  Each point-evaluation is a
    cheap Horner-style number crunch on `RingNormaliser.eval` at an integer
    environment — NO symbolic expansion.  The whole grid check is one decidable
    `Bool` (`gridCheck2B`, decided by the kernel), so the degree ceiling is set
    by `(d+1)²` cheap evaluations, not by an exponential monomial blow-up.

The bridge from `RingNormaliser.eval` (the homomorphic multivariate evaluator)
to "is a univariate polynomial of bounded degree in variable `v`" is
`coeffAt` / `eval_coeffAt` (a reflection into `QPoly.Poly`, structurally like
`RingNormaliser.eval_rawNormalize` but one variable at a time) together with the
structural degree bound `degBound` / `length_coeffAt_le`.  `coeffAt` appears
ONLY inside proofs — it is never kernel-computed on the demonstrated identity,
so it does not reintroduce the blow-up.

# Demonstration (the capacity gain)

`vandermonde_deg6` proves the degree-**6** Chu–Vandermonde falling-factorial
convolution `Σ_k C(6,k)(m)_k(n)_{6-k} = (m+n)_6`, two degrees past
`RingNormaliser.vandermonde_deg4` — the current normaliser's feasible ceiling —
via the grid procedure (a `(6+1)² = 49`-point kernel `decide`, no expansion).

# Constructive contract (AGENTS.md Rules 1/6/8)

Mathlib-free; `Q'` / `Nat` / `Int` core only.  No `Real`, `Classical.*`,
`native_decide`, `ring`/`nlinarith`.  `decide` is a genuine kernel decision on a
SMALL finite grid of integer evaluations.  No `sorry`/`admit`/new `axiom`.  The
soundness theorems (`eval_deflate`, `roots_zero`, `poly_identity_of_grid2`) are
genuinely proved by induction.  `#print axioms` gated (`propext`/`Quot.sound`).
-/
import YMGap.Constructive.QPoly
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.RingNormaliserStream

open YMGap.Constructive
open YMGap.Constructive.QPoly

/-! ## 0. `Q'` facts: no zero divisors + subtraction sign lemmas. -/

/-- `(a * b).eqv 0` forces `a.num * b.num = 0` (numerators; `Q'` is a domain). -/
theorem mul_num_zero {a b : Q'} (h : (a * b).eqv 0) : a.num * b.num = 0 := by
  have h' : (a * b).num * ((0 : Q').den : Int) = (0 : Q').num * ((a * b).den : Int) := h
  -- (a*b).num = a.num*b.num ; (0).den = 1 ; (0).num = 0
  have : a.num * b.num * (1 : Int) = 0 * ((a * b).den : Int) := h'
  simpa using this

/-- `a.eqv 0 ↔ a.num = 0`. -/
theorem eqv_zero_iff_num {a : Q'} : a.eqv 0 ↔ a.num = 0 := by
  constructor
  · intro h
    have h' : a.num * (1 : Int) = (0 : Int) * (a.den : Int) := h
    simpa using h'
  · intro h
    show a.num * (1 : Int) = (0 : Int) * (a.den : Int)
    simp [h]

/-- **No zero divisors** (contrapositive form): if `a` is not `≃ 0` and
`(a * b).eqv 0`, then `b.eqv 0`. -/
theorem eqv_zero_of_mul_left {a b : Q'} (ha : ¬ a.eqv 0) (h : (a * b).eqv 0) :
    b.eqv 0 := by
  have hnum : a.num * b.num = 0 := mul_num_zero h
  have hanum : a.num ≠ 0 := fun hc => ha (eqv_zero_iff_num.2 hc)
  rcases Int.mul_eq_zero.1 hnum with h0 | h0
  · exact absurd h0 hanum
  · exact eqv_zero_iff_num.2 h0

/-- `(y + -x).eqv 0 ↔ x.eqv y` (difference vanishes iff points coincide). -/
theorem sub_eqv_zero_iff {x y : Q'} : (y + -x).eqv 0 ↔ x.eqv y := by
  have hnum : (y + -x).num = y.num * (x.den : Int) - x.num * (y.den : Int) := by
    show y.num * ((-x).den : Int) + (-x).num * (y.den : Int)
        = y.num * (x.den : Int) - x.num * (y.den : Int)
    have h1 : ((-x).den : Int) = (x.den : Int) := by rw [Q'.neg_den]
    have h2 : (-x).num = -x.num := rfl
    rw [h1, h2, Int.neg_mul, Int.sub_eq_add_neg]
  rw [eqv_zero_iff_num, hnum]
  constructor
  · intro h
    -- y.num*x.den - x.num*y.den = 0  ⊢  x.num*y.den = y.num*x.den
    show x.num * (y.den : Int) = y.num * (x.den : Int)
    omega
  · intro h
    -- x.eqv y : x.num*y.den = y.num*x.den  ⊢  y.num*x.den - x.num*y.den = 0
    have hxy : x.num * (y.den : Int) = y.num * (x.den : Int) := h
    omega

/-- From distinct points, the difference is a nonzero scalar. -/
theorem sub_ne_zero_of_ne {x y : Q'} (h : ¬ x.eqv y) : ¬ (y + -x).eqv 0 :=
  fun hc => h (sub_eqv_zero_iff.1 hc)

/-! ## 1. Division-free factor theorem (`deflate`) — `p(x) − p(r) = (x−r)·q(x)`.

`deflate r p` is the quotient `q`; it is built WITHOUT dividing by `r` (so it is
total, even at `r = 0`), using `x^k − r^k = (x−r)(x^{k−1}+…+r^{k−1})`.  Its length
is one less than `p`'s, which drives the root-count induction. -/

/-- The deflation quotient of `p` at `r` (division-free synthetic division). -/
def deflate (r : Q') : Poly → Poly
  | []            => []
  | [_]           => []
  | (_ :: c₁ :: cs) => (eval (c₁ :: cs) r) :: deflate r (c₁ :: cs)

/-- `deflate` strictly shortens (its length is `≤ p.length − 1`). -/
theorem length_deflate_le (r : Q') : ∀ (p : Poly), (deflate r p).length ≤ p.length - 1
  | []            => Nat.le_refl 0
  | [_]           => Nat.le_refl 0
  | (_ :: c₁ :: cs) => by
      have ih := length_deflate_le r (c₁ :: cs)
      show ((eval (c₁ :: cs) r) :: deflate r (c₁ :: cs)).length ≤ (c₁ :: cs).length
      simp only [List.length_cons] at *
      omega

/-- The opaque-atom algebra core of `eval_deflate`'s recursive step: given the
inductive hypothesis `E ≃ Er + (x−r)·Q`, the Horner recurrence holds. -/
theorem deflate_algebra (c x r E Er Q : Q')
    (ih : E.eqv (Er + (x + -r) * Q)) :
    (c + x * E).eqv ((c + r * Er) + (x + -r) * (Er + x * Q)) := by
  -- common target T := (c + x*Er) + (x-r)*(x*Q)
  have hLHS : (c + x * E).eqv ((c + x * Er) + (x + -r) * (x * Q)) := by
    have s1 : (x * E).eqv (x * (Er + (x + -r) * Q)) := Q'.mul_eqv_congr_left x _ _ ih
    have s2 : (x * (Er + (x + -r) * Q)).eqv (x * Er + x * ((x + -r) * Q)) :=
      Q'.mul_add_eqv x Er ((x + -r) * Q)
    have s3 : (x * ((x + -r) * Q)).eqv ((x + -r) * (x * Q)) := by
      refine Q'.eqv_trans _ ((x * (x + -r)) * Q) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv x (x + -r) Q)) ?_
      refine Q'.eqv_trans _ (((x + -r) * x) * Q) _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv x (x + -r))) ?_
      exact Q'.mul_assoc_eqv (x + -r) x Q
    have sxE : (x * E).eqv (x * Er + (x + -r) * (x * Q)) :=
      Q'.eqv_trans _ (x * Er + x * ((x + -r) * Q)) _
        (Q'.eqv_trans _ (x * (Er + (x + -r) * Q)) _ s1 s2)
        (Q'.add_eqv_congr_left _ _ _ s3)
    refine Q'.eqv_trans _ (c + (x * Er + (x + -r) * (x * Q))) _
      (Q'.add_eqv_congr_left _ _ _ sxE) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv c (x * Er) ((x + -r) * (x * Q)))
  have hRHS : ((c + r * Er) + (x + -r) * (Er + x * Q)).eqv
                ((c + x * Er) + (x + -r) * (x * Q)) := by
    have e1 : ((x + -r) * (Er + x * Q)).eqv
                ((x * Er + (-r) * Er) + (x + -r) * (x * Q)) := by
      refine Q'.eqv_trans _ ((x + -r) * Er + (x + -r) * (x * Q)) _
        (Q'.mul_add_eqv (x + -r) Er (x * Q)) ?_
      exact Q'.add_eqv_congr_right _ _ _ (q_add_mul x (-r) Er)
    refine Q'.eqv_trans _
      ((c + r * Er) + ((x * Er + (-r) * Er) + (x + -r) * (x * Q))) _
      (Q'.add_eqv_congr_left _ _ _ e1) ?_
    refine Q'.eqv_trans _ (c + (r * Er + ((x * Er + (-r) * Er) + (x + -r) * (x * Q)))) _
      (Q'.add_assoc_eqv c (r * Er) ((x * Er + (-r) * Er) + (x + -r) * (x * Q))) ?_
    have hin : (r * Er + ((x * Er + (-r) * Er) + (x + -r) * (x * Q))).eqv
                 (x * Er + (x + -r) * (x * Q)) := by
      refine Q'.eqv_trans _ (r * Er + (x * Er + ((-r) * Er + (x + -r) * (x * Q)))) _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.add_assoc_eqv (x * Er) ((-r) * Er) ((x + -r) * (x * Q)))) ?_
      refine Q'.eqv_trans _ ((r * Er + x * Er) + ((-r) * Er + (x + -r) * (x * Q))) _
        (Q'.eqv_symm (Q'.add_assoc_eqv (r * Er) (x * Er) ((-r) * Er + (x + -r) * (x * Q)))) ?_
      refine Q'.eqv_trans _ ((x * Er + r * Er) + ((-r) * Er + (x + -r) * (x * Q))) _
        (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv (r * Er) (x * Er))) ?_
      refine Q'.eqv_trans _ (x * Er + (r * Er + ((-r) * Er + (x + -r) * (x * Q)))) _
        (Q'.add_assoc_eqv (x * Er) (r * Er) ((-r) * Er + (x + -r) * (x * Q))) ?_
      refine Q'.add_eqv_congr_left _ _ _ ?_
      refine Q'.eqv_trans _ ((r * Er + (-r) * Er) + (x + -r) * (x * Q)) _
        (Q'.eqv_symm (Q'.add_assoc_eqv (r * Er) ((-r) * Er) ((x + -r) * (x * Q)))) ?_
      refine Q'.eqv_trans _ ((0 : Q') + (x + -r) * (x * Q)) _ ?_ (q_zero_add_eqv _)
      refine Q'.add_eqv_congr_right _ _ _ ?_
      refine Q'.eqv_trans _ (r * Er + -(r * Er)) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.neg_mul_eqv r Er)) ?_
      exact Q'.eqv_trans _ (-(r * Er) + r * Er) _
        (Q'.add_comm_eqv (r * Er) (-(r * Er))) (Q'.neg_add_self_eqv (r * Er))
    refine Q'.eqv_trans _ (c + (x * Er + (x + -r) * (x * Q))) _
      (Q'.add_eqv_congr_left _ _ _ hin) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv c (x * Er) ((x + -r) * (x * Q)))
  exact Q'.eqv_trans _ ((c + x * Er) + (x + -r) * (x * Q)) _ hLHS (Q'.eqv_symm hRHS)

/-- **The factor identity** (division-free): for all `x`,
`eval p x ≃ eval p r + (x + -r) · eval (deflate r p) x`. -/
theorem eval_deflate (r : Q') : ∀ (p : Poly) (x : Q'),
    (eval p x).eqv (eval p r + (x + -r) * eval (deflate r p) x)
  | [], x => by
      -- 0 ≃ 0 + (x-r)*0
      show (0 : Q').eqv (0 + (x + -r) * eval ([] : Poly) x)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ ((x + -r) * (0 : Q')) _ (q_zero_add_eqv _) (q_mul_zero _)
  | [c], x => by
      -- eval [c] x = c + x*0 ; RHS = (c + r*0) + (x-r)*0
      show (c + x * eval ([] : Poly) x).eqv
            ((c + r * eval ([] : Poly) x) + (x + -r) * eval (deflate r [c]) x)
      have hL : (c + x * eval ([] : Poly) x).eqv c :=
        Q'.eqv_trans _ (c + (0 : Q')) _
          (Q'.add_eqv_congr_left _ _ _ (q_mul_zero x)) (q_add_zero_eqv c)
      have hR : ((c + r * eval ([] : Poly) x) + (x + -r) * eval (deflate r [c]) x).eqv c := by
        -- deflate r [c] = [] ; eval [] x = 0
        refine Q'.eqv_trans _ ((c + r * eval ([] : Poly) x) + (0 : Q')) _
          (Q'.add_eqv_congr_left _ _ _ (q_mul_zero (x + -r))) ?_
        refine Q'.eqv_trans _ (c + r * eval ([] : Poly) x) _ (q_add_zero_eqv _) ?_
        exact Q'.eqv_trans _ (c + (0 : Q')) _
          (Q'.add_eqv_congr_left _ _ _ (q_mul_zero r)) (q_add_zero_eqv c)
      exact Q'.eqv_trans _ c _ hL (Q'.eqv_symm hR)
  | (c :: c₁ :: cs), x => by
      have ih := eval_deflate r (c₁ :: cs) x
      -- Goal is defeq to the `deflate_algebra` conclusion with
      --   E := eval (c₁::cs) x, Er := eval (c₁::cs) r, Q := eval (deflate r (c₁::cs)) x.
      show (c + x * eval (c₁ :: cs) x).eqv
            ((c + r * eval (c₁ :: cs) r)
              + (x + -r) * (eval (c₁ :: cs) r + x * eval (deflate r (c₁ :: cs)) x))
      exact deflate_algebra c x r (eval (c₁ :: cs) x) (eval (c₁ :: cs) r)
        (eval (deflate r (c₁ :: cs)) x) ih

/-! ## 2. The root-count theorem — deterministic Schwartz–Zippel, one variable.

A polynomial with `n` distinct roots and length `≤ n` is identically zero.
Proved by induction on the root list: strip one root via `deflate`, use the
no-zero-divisor law to transfer the remaining roots to the quotient, recurse. -/

/-- Pairwise-distinct (`¬ eqv`) list of `Q'` points. -/
inductive QDistinct : List Q' → Prop
  | nil : QDistinct []
  | cons : ∀ {x : Q'} {xs : List Q'},
      (∀ y ∈ xs, ¬ x.eqv y) → QDistinct xs → QDistinct (x :: xs)

/-- **THE ROOT-COUNT THEOREM.**  If `xs` is a list of pairwise-distinct points
and `p` has length `≤ xs.length` and vanishes at every point of `xs`, then `p`
vanishes everywhere.  (Deterministic Schwartz–Zippel in one variable; genuinely
proved, never assumed.) -/
theorem roots_zero : ∀ (xs : List Q'), QDistinct xs → ∀ (p : Poly),
    p.length ≤ xs.length → (∀ y ∈ xs, (eval p y).eqv 0) → ∀ z, (eval p z).eqv 0
  | [], _, p, hlen, _, z => by
      cases p with
      | nil => exact Q'.eqv_refl 0
      | cons a as => simp at hlen
  | (x₀ :: rest), hdist, p, hlen, hroots, z => by
      cases hdist with
      | cons hne hdrest =>
        have hpx0 : (eval p x₀).eqv 0 := hroots x₀ (List.mem_cons_self ..)
        have hlenq : (deflate x₀ p).length ≤ rest.length := by
          have h1 := length_deflate_le x₀ p
          have h2 : p.length ≤ rest.length + 1 := by
            simpa [List.length_cons] using hlen
          omega
        have hrootsq : ∀ y ∈ rest, (eval (deflate x₀ p) y).eqv 0 := by
          intro y hy
          have hpy : (eval p y).eqv 0 := hroots y (List.mem_cons_of_mem _ hy)
          have hdef := eval_deflate x₀ p y
          -- eval p x₀ ≃ 0 ⇒ (eval p x₀ + B) ≃ B  where B = (y-x₀)*eval q y
          have hAB : (eval p x₀ + (y + -x₀) * eval (deflate x₀ p) y).eqv
                       ((y + -x₀) * eval (deflate x₀ p) y) :=
            Q'.eqv_trans _ ((0 : Q') + (y + -x₀) * eval (deflate x₀ p) y) _
              (Q'.add_eqv_congr_right _ _ _ hpx0)
              (q_zero_add_eqv _)
          have hB0 : ((y + -x₀) * eval (deflate x₀ p) y).eqv 0 :=
            Q'.eqv_trans _ (eval p y) _
              (Q'.eqv_symm (Q'.eqv_trans _ _ _ hdef hAB)) hpy
          exact eqv_zero_of_mul_left (sub_ne_zero_of_ne (hne y hy)) hB0
        have ih := roots_zero rest hdrest (deflate x₀ p) hlenq hrootsq z
        -- eval p z ≃ eval p x₀ + (z-x₀)*eval q z ≃ 0 + 0 ≃ 0
        have hqz0 : ((z + -x₀) * eval (deflate x₀ p) z).eqv 0 :=
          Q'.eqv_trans _ ((z + -x₀) * (0 : Q')) _
            (Q'.mul_eqv_congr_left _ _ _ ih) (q_mul_zero _)
        exact Q'.eqv_trans _ (eval p x₀ + (z + -x₀) * eval (deflate x₀ p) z) _
          (eval_deflate x₀ p z)
          (Q'.eqv_trans _ ((0 : Q') + (0 : Q')) _
            (q_add_congr hpx0 hqz0) (q_zero_add_eqv 0))

/-! ## 3. From `RingNormaliser.eval` to a univariate `QPoly` in one variable.

`coeffAt v e ρ` is the coefficient list of `e` viewed as a polynomial in variable
`v`, with all OTHER variables set to their `ρ`-values.  It is a homomorphism into
`QPoly.Poly`, so `eval_coeffAt` (proved by structural induction) says
`RingNormaliser.eval (ρ with v↦x) e ≃ QPoly.eval (coeffAt v e ρ) x`.  `coeffAt`
is used ONLY inside proofs — never kernel-computed on a demonstrated identity, so
it does not reintroduce the canonical-form blow-up. -/

/-- `p` raised to a `Nat` power in the univariate ring. -/
def ppow (p : Poly) : Nat → Poly
  | 0     => [1]
  | n + 1 => pmul (ppow p n) p

/-- Two singleton/linear evaluation helpers. -/
theorem eval_single (c x : Q') : (eval [c] x).eqv c :=
  Q'.eqv_trans _ (c + (0 : Q')) _
    (Q'.add_eqv_congr_left _ _ _ (q_mul_zero x)) (q_add_zero_eqv c)

theorem eval_lin (x : Q') : (eval [(0 : Q'), (1 : Q')] x).eqv x := by
  refine Q'.eqv_trans _ ((0 : Q') + x * (1 : Q')) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left x _ _ (eval_single 1 x))) ?_
  exact Q'.eqv_trans _ ((0 : Q') + x) _
    (Q'.add_eqv_congr_left _ _ _ (Q'.mul_one_eqv x)) (q_zero_add_eqv x)

/-- `ppow` is an `eval`-homomorphism into `qpow`. -/
theorem eval_ppow (p : Poly) : ∀ (n : Nat) (x : Q'),
    (eval (ppow p n) x).eqv (RingNormaliser.qpow (eval p x) n)
  | 0, x => by
      -- eval [1] x ≃ 1 = qpow _ 0
      show (eval [(1 : Q')] x).eqv 1
      exact eval_single 1 x
  | n + 1, x => by
      show (eval (pmul (ppow p n) p) x).eqv (RingNormaliser.qpow (eval p x) n * eval p x)
      refine Q'.eqv_trans _ (eval (ppow p n) x * eval p x) _
        (eval_pmul (ppow p n) p x) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (eval_ppow p n x)

/-- The coefficient list of `e` in variable `v` (others taken from `ρ`). -/
def coeffAt (v : Nat) : RingNormaliser.PolyExpr → (Nat → Q') → Poly
  | .const c, _ => [Q'.ofInt c]
  | .var i,   ρ => if i = v then [0, 1] else [ρ i]
  | .add a b, ρ => padd (coeffAt v a ρ) (coeffAt v b ρ)
  | .mul a b, ρ => pmul (coeffAt v a ρ) (coeffAt v b ρ)
  | .neg a,   ρ => pneg (coeffAt v a ρ)
  | .pow a n, ρ => ppow (coeffAt v a ρ) n

/-- **The reflection soundness:** `RingNormaliser.eval` with `v ↦ x` equals the
Horner evaluation of `coeffAt v e ρ` at `x`.  Structural induction; `QPoly` homs. -/
theorem eval_coeffAt (v : Nat) : ∀ (e : RingNormaliser.PolyExpr) (ρ : Nat → Q') (x : Q'),
    (RingNormaliser.eval (fun i => if i = v then x else ρ i) e).eqv
      (eval (coeffAt v e ρ) x)
  | .const c, ρ, x => by
      show (Q'.ofInt c).eqv (eval [Q'.ofInt c] x)
      exact Q'.eqv_symm (eval_single (Q'.ofInt c) x)
  | .var i, ρ, x => by
      show (if i = v then x else ρ i).eqv
            (eval (if i = v then [(0 : Q'), 1] else [ρ i]) x)
      by_cases h : i = v
      · rw [if_pos h, if_pos h]; exact Q'.eqv_symm (eval_lin x)
      · rw [if_neg h, if_neg h]; exact Q'.eqv_symm (eval_single (ρ i) x)
  | .add a b, ρ, x => by
      have iha := eval_coeffAt v a ρ x
      have ihb := eval_coeffAt v b ρ x
      show (RingNormaliser.eval (fun i => if i = v then x else ρ i) a
            + RingNormaliser.eval (fun i => if i = v then x else ρ i) b).eqv
            (eval (padd (coeffAt v a ρ) (coeffAt v b ρ)) x)
      refine Q'.eqv_trans _ (eval (coeffAt v a ρ) x + eval (coeffAt v b ρ) x) _
        (q_add_congr iha ihb) ?_
      exact Q'.eqv_symm (eval_padd (coeffAt v a ρ) (coeffAt v b ρ) x)
  | .mul a b, ρ, x => by
      have iha := eval_coeffAt v a ρ x
      have ihb := eval_coeffAt v b ρ x
      show (RingNormaliser.eval (fun i => if i = v then x else ρ i) a
            * RingNormaliser.eval (fun i => if i = v then x else ρ i) b).eqv
            (eval (pmul (coeffAt v a ρ) (coeffAt v b ρ)) x)
      refine Q'.eqv_trans _ (eval (coeffAt v a ρ) x * eval (coeffAt v b ρ) x) _
        (Q'.eqv_trans _
          (eval (coeffAt v a ρ) x
            * RingNormaliser.eval (fun i => if i = v then x else ρ i) b) _
          (Q'.mul_eqv_congr_right _ _ _ iha)
          (Q'.mul_eqv_congr_left _ _ _ ihb)) ?_
      exact Q'.eqv_symm (eval_pmul (coeffAt v a ρ) (coeffAt v b ρ) x)
  | .neg a, ρ, x => by
      have iha := eval_coeffAt v a ρ x
      show (-(RingNormaliser.eval (fun i => if i = v then x else ρ i) a)).eqv
            (eval (pneg (coeffAt v a ρ)) x)
      refine Q'.eqv_trans _ (-(eval (coeffAt v a ρ) x)) _
        (Q'.neg_eqv_congr _ _ iha) ?_
      exact Q'.eqv_symm (eval_pneg (coeffAt v a ρ) x)
  | .pow a n, ρ, x => by
      have iha := eval_coeffAt v a ρ x
      show (RingNormaliser.qpow (RingNormaliser.eval (fun i => if i = v then x else ρ i) a) n).eqv
            (eval (ppow (coeffAt v a ρ) n) x)
      refine Q'.eqv_trans _ (RingNormaliser.qpow (eval (coeffAt v a ρ) x) n) _
        (RingNormaliser.qpow_eqv_congr iha n) ?_
      exact Q'.eqv_symm (eval_ppow (coeffAt v a ρ) n x)

/-! ### Structural degree bound + length control of `coeffAt`. -/

/-- A structural (blow-up-free) upper bound on the per-variable degree. -/
def degBound : RingNormaliser.PolyExpr → Nat
  | .const _ => 0
  | .var _   => 1
  | .add a b => max (degBound a) (degBound b)
  | .mul a b => degBound a + degBound b
  | .neg a   => degBound a
  | .pow a n => n * degBound a + n

theorem length_pscale (k : Q') : ∀ (p : Poly), (pscale k p).length = p.length
  | []      => rfl
  | _ :: cs => by simp [pscale, length_pscale k cs]

theorem length_pneg (p : Poly) : (pneg p).length = p.length := length_pscale _ p

theorem length_padd : ∀ (p q : Poly), (padd p q).length = max p.length q.length
  | [], q => by simp [padd]
  | (_ :: _), [] => by simp [padd]
  | (a :: p), (b :: q) => by
      show (padd (a :: p) (b :: q)).length = max (a :: p).length (b :: q).length
      simp only [padd, List.length_cons]
      rw [length_padd p q]; omega

theorem length_pmul_le : ∀ (p q : Poly), (pmul p q).length ≤ p.length + q.length - 1
  | [], q => by simp [pmul]
  | (a :: p), q => by
      have ih := length_pmul_le p q
      have hpadd : (pmul (a :: p) q).length = max q.length ((pmul p q).length + 1) := by
        show (padd (pscale a q) (0 :: pmul p q)).length = max q.length ((pmul p q).length + 1)
        rw [length_padd, length_pscale]; rfl
      rw [hpadd]
      simp only [List.length_cons]
      exact Nat.max_le.mpr ⟨by omega, by omega⟩

theorem length_ppow_le (p : Poly) : ∀ (n : Nat), (ppow p n).length ≤ n * p.length + 1
  | 0 => by simp [ppow]
  | n + 1 => by
      show (pmul (ppow p n) p).length ≤ (n + 1) * p.length + 1
      have h1 := length_pmul_le (ppow p n) p
      have ih := length_ppow_le p n
      have hexp : (n + 1) * p.length = n * p.length + p.length := Nat.succ_mul n p.length
      omega

/-- `coeffAt` has length `≤ degBound e + 1` (the per-variable degree bound). -/
theorem length_coeffAt_le (v : Nat) : ∀ (e : RingNormaliser.PolyExpr) (ρ : Nat → Q'),
    (coeffAt v e ρ).length ≤ degBound e + 1
  | .const c, ρ => by simp [coeffAt, degBound]
  | .var i, ρ => by
      show (if i = v then ([0, 1] : Poly) else [ρ i]).length
            ≤ degBound (RingNormaliser.PolyExpr.var i) + 1
      by_cases h : i = v
      · rw [if_pos h]; simp [degBound]
      · rw [if_neg h]; simp [degBound]
  | .add a b, ρ => by
      have ha := length_coeffAt_le v a ρ
      have hb := length_coeffAt_le v b ρ
      show (padd (coeffAt v a ρ) (coeffAt v b ρ)).length ≤ max (degBound a) (degBound b) + 1
      rw [length_padd]; omega
  | .mul a b, ρ => by
      have ha := length_coeffAt_le v a ρ
      have hb := length_coeffAt_le v b ρ
      have hm := length_pmul_le (coeffAt v a ρ) (coeffAt v b ρ)
      show (pmul (coeffAt v a ρ) (coeffAt v b ρ)).length ≤ (degBound a + degBound b) + 1
      omega
  | .neg a, ρ => by
      have ha := length_coeffAt_le v a ρ
      show (pneg (coeffAt v a ρ)).length ≤ degBound a + 1
      rw [length_pneg]; exact ha
  | .pow a n, ρ => by
      have ha := length_coeffAt_le v a ρ
      have hp := length_ppow_le (coeffAt v a ρ) n
      show (ppow (coeffAt v a ρ) n).length ≤ (n * degBound a + n) + 1
      have hmul : n * (coeffAt v a ρ).length ≤ n * degBound a + n := by
        have h := Nat.mul_le_mul_left n ha
        rw [Nat.mul_add, Nat.mul_one] at h
        exact h
      omega

/-! ### The integer grid `{ofNat 0, …, ofNat (n-1)}` and its distinctness. -/

/-- `(ofNat a).eqv (ofNat b) ↔ a = b`. -/
theorem ofNat_eqv_iff (a b : Nat) : (Q'.ofNat a).eqv (Q'.ofNat b) ↔ a = b := by
  constructor
  · intro h
    have h' : (Int.ofNat a) * (1 : Int) = (Int.ofNat b) * (1 : Int) := h
    have h'' : (Int.ofNat a) = (Int.ofNat b) := by
      rw [Int.mul_one, Int.mul_one] at h'; exact h'
    exact Int.ofNat.inj h''
  · intro h; subst h; exact Q'.eqv_refl _

/-- The grid `[ofNat (n-1), …, ofNat 0]` of `n` distinct integer points. -/
def gridList : Nat → List Q'
  | 0     => []
  | n + 1 => Q'.ofNat n :: gridList n

theorem length_gridList : ∀ (n : Nat), (gridList n).length = n
  | 0     => rfl
  | n + 1 => by simp [gridList, length_gridList n]

theorem mem_gridList : ∀ (n : Nat) (y : Q'), y ∈ gridList n → ∃ k, k < n ∧ y = Q'.ofNat k
  | 0, y, h => by simp [gridList] at h
  | n + 1, y, h => by
      simp only [gridList, List.mem_cons] at h
      rcases h with h | h
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · rcases mem_gridList n y h with ⟨k, hk, hy⟩
        exact ⟨k, Nat.lt_succ_of_lt hk, hy⟩

theorem qdistinct_gridList : ∀ (n : Nat), QDistinct (gridList n)
  | 0     => QDistinct.nil
  | n + 1 => by
      refine QDistinct.cons ?_ (qdistinct_gridList n)
      intro y hy
      rcases mem_gridList n y hy with ⟨k, hk, hy'⟩
      subst hy'
      intro hc
      have := (ofNat_eqv_iff n k).mp hc
      omega

/-! ### The two-variable environment + grid identity theorem. -/

/-- Explicit two-variable environment (`x₀ = m`, `x₁ = n`, others `0`). -/
def env2 (m n : Q') : Nat → Q' := fun i => if i = 0 then m else if i = 1 then n else 0

theorem update0_env2 (m a : Q') :
    (fun i => if i = 0 then m else env2 (0 : Q') a i) = env2 m a := by
  funext i; by_cases h : i = 0 <;> simp [env2, h]

theorem update1_env2 (m n : Q') :
    (fun i => if i = 1 then n else env2 m (0 : Q') i) = env2 m n := by
  funext i
  by_cases h0 : i = 0
  · subst h0; simp [env2]
  · by_cases h1 : i = 1
    · subst h1; simp [env2]
    · simp [env2, h0, h1]

/-- **THE TWO-VARIABLE GRID IDENTITY THEOREM** (deterministic Schwartz–Zippel).
If `F` has per-variable degree `≤ d` and vanishes on the whole integer grid
`{0,…,d}²`, then `F` vanishes everywhere.  Two applications of `roots_zero`. -/
theorem poly_identity_of_grid2 (F : RingNormaliser.PolyExpr) (d : Nat)
    (hdeg : degBound F ≤ d)
    (hgrid : ∀ i j, i ≤ d → j ≤ d →
      (RingNormaliser.eval (env2 (Q'.ofNat i) (Q'.ofNat j)) F).eqv 0) :
    ∀ m n, (RingNormaliser.eval (env2 m n) F).eqv 0 := by
  have stepA : ∀ j, j ≤ d → ∀ m, (RingNormaliser.eval (env2 m (Q'.ofNat j)) F).eqv 0 := by
    intro j hj
    have hPeval : ∀ x, (RingNormaliser.eval (env2 x (Q'.ofNat j)) F).eqv
                        (eval (coeffAt 0 F (env2 (0 : Q') (Q'.ofNat j))) x) := by
      intro x
      have h := eval_coeffAt 0 F (env2 (0 : Q') (Q'.ofNat j)) x
      rw [update0_env2] at h; exact h
    have hlen : (coeffAt 0 F (env2 (0 : Q') (Q'.ofNat j))).length ≤ (gridList (d + 1)).length := by
      have := length_coeffAt_le 0 F (env2 (0 : Q') (Q'.ofNat j))
      rw [length_gridList]; omega
    have hroots : ∀ y ∈ gridList (d + 1),
        (eval (coeffAt 0 F (env2 (0 : Q') (Q'.ofNat j))) y).eqv 0 := by
      intro y hy
      rcases mem_gridList (d + 1) y hy with ⟨i, hi, hy'⟩
      subst hy'
      exact Q'.eqv_trans _ (RingNormaliser.eval (env2 (Q'.ofNat i) (Q'.ofNat j)) F) _
        (Q'.eqv_symm (hPeval (Q'.ofNat i))) (hgrid i j (Nat.lt_succ_iff.mp hi) hj)
    have hzero := roots_zero (gridList (d + 1)) (qdistinct_gridList (d + 1))
      (coeffAt 0 F (env2 (0 : Q') (Q'.ofNat j))) hlen hroots
    intro m
    exact Q'.eqv_trans _ (eval (coeffAt 0 F (env2 (0 : Q') (Q'.ofNat j))) m) _
      (hPeval m) (hzero m)
  intro m n
  have hGeval : ∀ x, (RingNormaliser.eval (env2 m x) F).eqv
                      (eval (coeffAt 1 F (env2 m (0 : Q'))) x) := by
    intro x
    have h := eval_coeffAt 1 F (env2 m (0 : Q')) x
    rw [update1_env2] at h; exact h
  have hlen : (coeffAt 1 F (env2 m (0 : Q'))).length ≤ (gridList (d + 1)).length := by
    have := length_coeffAt_le 1 F (env2 m (0 : Q'))
    rw [length_gridList]; omega
  have hroots : ∀ y ∈ gridList (d + 1),
      (eval (coeffAt 1 F (env2 m (0 : Q'))) y).eqv 0 := by
    intro y hy
    rcases mem_gridList (d + 1) y hy with ⟨j, hj, hy'⟩
    subst hy'
    exact Q'.eqv_trans _ (RingNormaliser.eval (env2 m (Q'.ofNat j)) F) _
      (Q'.eqv_symm (hGeval (Q'.ofNat j))) (stepA j (Nat.lt_succ_iff.mp hj) m)
  have hzero := roots_zero (gridList (d + 1)) (qdistinct_gridList (d + 1))
    (coeffAt 1 F (env2 m (0 : Q'))) hlen hroots
  exact Q'.eqv_trans _ (eval (coeffAt 1 F (env2 m (0 : Q'))) n) _ (hGeval n) (hzero n)

/-! ### The decidable grid check (the cheap, blow-up-free kernel computation). -/

/-- The finite grid check: `F ≃ 0` at every integer point of `{0,…,d}²`.
Each entry is a Horner-style number crunch on `RingNormaliser.eval` — NO
symbolic expansion.  Decidable. -/
def gridCheck2B (F : RingNormaliser.PolyExpr) (d : Nat) : Bool :=
  (List.range (d + 1)).all (fun i =>
    (List.range (d + 1)).all (fun j =>
      decide ((RingNormaliser.eval (env2 (Q'.ofNat i) (Q'.ofNat j)) F).eqv 0)))

theorem grid_of_check (F : RingNormaliser.PolyExpr) (d : Nat)
    (h : gridCheck2B F d = true) :
    ∀ i j, i ≤ d → j ≤ d → (RingNormaliser.eval (env2 (Q'.ofNat i) (Q'.ofNat j)) F).eqv 0 := by
  intro i j hi hj
  have hi' : i ∈ List.range (d + 1) := List.mem_range.mpr (Nat.lt_succ_of_le hi)
  have hj' : j ∈ List.range (d + 1) := List.mem_range.mpr (Nat.lt_succ_of_le hj)
  have h1 := (List.all_eq_true.mp h) i hi'
  have h2 := (List.all_eq_true.mp h1) j hj'
  exact of_decide_eq_true h2

/-! ## 4. Demonstration — a DEGREE-6 Chu–Vandermonde identity (past the deg-4 ceiling).

The `p = 6` Chu–Vandermonde falling-factorial convolution
`Σ_{k=0}^{6} C(6,k)·(m)_k·(n)_{6−k} = (m+n)_6`  (`C(6,·) = 1,6,15,20,15,6,1`),
two degrees past `RingNormaliser.vandermonde_deg4` — the current
`normalize`+`decide` ceiling — verified by the grid procedure (a `7² = 49`-point
kernel `decide`, no monomial expansion). -/

/-- `((m+n))_k = ∏_{t=0}^{k-1} (x₀ + x₁ − t)` as a `PolyExpr`. -/
def sumVarFalling : Nat → RingNormaliser.PolyExpr
  | 0     => .const 1
  | k + 1 => .mul (sumVarFalling k)
      (.add (.add (.var 0) (.var 1)) (.const (-(k : Int))))

/-- LHS of the degree-6 convolution: `Σ_{k=0}^{6} C(6,k) (m)_k (n)_{6-k}`. -/
def vdm6LHS : RingNormaliser.PolyExpr :=
  .add (.add (.add (.add (.add (.add
    (RingNormaliser.fallingExpr 1 6)
    (.mul (.const 6)  (.mul (RingNormaliser.fallingExpr 0 1) (RingNormaliser.fallingExpr 1 5))))
    (.mul (.const 15) (.mul (RingNormaliser.fallingExpr 0 2) (RingNormaliser.fallingExpr 1 4))))
    (.mul (.const 20) (.mul (RingNormaliser.fallingExpr 0 3) (RingNormaliser.fallingExpr 1 3))))
    (.mul (.const 15) (.mul (RingNormaliser.fallingExpr 0 4) (RingNormaliser.fallingExpr 1 2))))
    (.mul (.const 6)  (.mul (RingNormaliser.fallingExpr 0 5) (RingNormaliser.fallingExpr 1 1))))
    (RingNormaliser.fallingExpr 0 6)

/-- RHS of the degree-6 convolution: `(m+n)_6`. -/
def vdm6RHS : RingNormaliser.PolyExpr := sumVarFalling 6

/-- **The degree-6 Chu–Vandermonde convolution identity** (∀ `m,n : Q'`), proved
by the grid / deterministic Schwartz–Zippel procedure — a `49`-point kernel
`decide`, with NO canonical-form expansion.  This is two degrees past the
`RingNormaliser.vandermonde_deg4` ceiling of the `normalize`+`decide` route. -/
theorem vandermonde_deg6 (m n : Q') :
    (RingNormaliser.eval (env2 m n) vdm6LHS).eqv
      (RingNormaliser.eval (env2 m n) vdm6RHS) := by
  have hF : (RingNormaliser.eval (env2 m n) (.add vdm6LHS (.neg vdm6RHS))).eqv 0 :=
    poly_identity_of_grid2 (.add vdm6LHS (.neg vdm6RHS)) 6 (by decide)
      (grid_of_check _ 6 (by decide)) m n
  exact q_eqv_of_sub_zero hF

end YMGap.Continuum.RingNormaliserStream

/-! Axiom gate (AGENTS.md Rule 1). -/
#print axioms YMGap.Continuum.RingNormaliserStream.eval_deflate
#print axioms YMGap.Continuum.RingNormaliserStream.eqv_zero_of_mul_left
#print axioms YMGap.Continuum.RingNormaliserStream.sub_ne_zero_of_ne
#print axioms YMGap.Continuum.RingNormaliserStream.roots_zero
#print axioms YMGap.Continuum.RingNormaliserStream.eval_coeffAt
#print axioms YMGap.Continuum.RingNormaliserStream.length_coeffAt_le
#print axioms YMGap.Continuum.RingNormaliserStream.poly_identity_of_grid2
#print axioms YMGap.Continuum.RingNormaliserStream.grid_of_check
#print axioms YMGap.Continuum.RingNormaliserStream.vandermonde_deg6
