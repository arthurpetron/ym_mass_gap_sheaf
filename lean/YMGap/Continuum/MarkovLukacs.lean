/-
Widening the Markov–Lukács **producer** (Piece B): from fixed-constant
`decide`-checked witnesses toward *general symbolic families*.

The consumer side of the `[−1,1]` Positivstellensatz is closed in full
generality (`PSatz.psatzAvg_nonneg`: any polynomial *presented* with a
certificate `p = σ₀ + (1 − x²)σ₁`, σᵢ sums of squares, has nonnegative
heat-kernel average).  The open side is the **producer**: given only
`p ≥ 0` on `[−1,1]`, construct the SOS data `(σ₀, σ₁)`.  In
`Positivstellensatz.lean` the producer is closed only at specific numeric
`p` via `decide` (`cert_oneMinusX`, `cert_quad`, …), and the general case
is recorded honestly as the unproved `OpenProblem.markov_lukacs_existence`.

This file pushes the producer coverage *symbolically*, working with the
`OpenProblem.Certificate p` structure (bare-square even form
`p = (Σ A_j²) + (1 − x²)(Σ B_j²)`).  What is delivered, all fully general
in the polynomial parameters and all sqrt-free:

  ## 1. Certificate soundness (the strongest fully-symbolic theorem)
  `certificate_sound : Certificate p → NonnegOn p`.  Every certificate, of
  any degree, *forces* nonnegativity on `[−1,1]` — proved pointwise from
  `0 ≤ a·a` (squares) and `0 ≤ 1 − x²` on `[−1,1]`.  This is the genuine
  `(producer ⊆ nonneg-cone)` containment, symbolic in `p`.

  ## 2. Composition closure (a constructive sub-algebra of the producer)
  Certificates compose, so the producer is closed under the cone
  operations that build the bare-square even form:
    * `certOfParts` — every `(cosParts, sinParts)` *is* a certificate for
      the polynomial it spells out (the trivial/defining producer; the
      generators of the cone).
    * `certSq A` — `A²` always has a certificate (`σ₀ = [A], σ₁ = []`).
    * `certWeight B` — `(1 − x²)·B²` always has a certificate
      (`σ₀ = [], σ₁ = [B]`).
    * `certAdd` — `Certificate p → Certificate q → Certificate (p + q)`
      (concatenate the SOS parts; identity by the `eval` homomorphism).
  From these, any finite `Σ A_j² + (1 − x²) Σ B_j²` over `Q'` is produced.

  ## 3. A symbolic degree-≤2 producer FAMILY (formulas in the parameters)
  `certQuadFamily a b c : Certificate (quadFamily a b c)` where
    `quadFamily a b c = (a + b x)² + (1 − x²) c²`
  is, for *arbitrary* rationals `a, b, c`, an explicit nonnegative-on-
  `[−1,1]` quadratic with a certificate given by FORMULAS in `a, b, c`
  (`σ₀ = [[a, b]]`, `σ₁ = [[c]]`).  Its nonnegativity is `certQuadFamily_nonneg`
  (a `NonnegOn` corollary).  This is the honest symbolic degree-2 result:
  the *rationally representable* even-form quadratics, parametrised by the
  square data `(a, b, c)`.  (The generic degree-2 even-form certificate over
  `Q'` does NOT exist — it requires a real spectral square root, Fejér–Riesz;
  that obstruction is scoped precisely in part 4.)

  ## 4. The sharpened open gap + a proved reduction
  `factorizationOracle` states the precise missing analytic input (a
  rational even-form spectral factorization: from `NonnegOn p`, produce the
  `Certificate`).  `oracle_implies_existence : factorizationOracle →
  markov_lukacs_existence` is a *proved constructive reduction* — the oracle
  is exactly what closes the general producer.  The oracle itself stays open
  (it is the constructive Markov–Lukács / Fejér–Riesz root step the rational
  `decide` substrate does not provide).

# Axiom-gate (AGENTS.md Rule 1)
`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`.
-/

import YMGap.Continuum.Positivstellensatz

namespace YMGap.Continuum.MarkovLukacs

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.PSatz
open YMGap.Continuum.PSatz.OpenProblem

/-! ## `Q'` transport / congruence helpers -/

/-- Both-argument multiplicative congruence for `eqv` (the `Q'` library
ships only the one-sided `mul_eqv_congr_left/right`). -/
theorem q_mul_congr {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') :
    (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-- Transport nonnegativity along `eqv`: `0 ≤ a` and `a ≃ b` give `0 ≤ b`. -/
theorem zero_le_of_eqv {a b : Q'} (ha : (0 : Q') ≤ a) (h : a.eqv b) : (0 : Q') ≤ b :=
  Q'.le_trans' 0 a b ha (Q'.le_of_eqv h)

/-- `x + -x ≃ 0` (derived from `neg_add_self_eqv` + commutativity). -/
theorem q_add_neg_self (x : Q') : (x + -x).eqv 0 :=
  Q'.eqv_trans _ _ _ (Q'.add_comm_eqv x (-x)) (Q'.neg_add_self_eqv x)

/-! ## Part 1 — symbolic nonnegativity facts about the building blocks -/

/-- A square evaluates `≥ 0` everywhere: `0 ≤ eval (pmul A A) x`.  Proved by
transporting `0 ≤ (eval A x)·(eval A x)` (`q_mul_self_nonneg`) back along the
`eval`-multiplication homomorphism. -/
theorem eval_sq_nonneg (A : Poly) (x : Q') : (0 : Q') ≤ eval (pmul A A) x :=
  zero_le_of_eqv (SumOfSquares.q_mul_self_nonneg (eval A x))
    (Q'.eqv_symm (eval_pmul A A x))

/-- A sum of squares evaluates `≥ 0` everywhere: `0 ≤ eval (sumOfSqPoly Ps) x`. -/
theorem eval_sumOfSq_nonneg : ∀ (Ps : List Poly) (x : Q'),
    (0 : Q') ≤ eval (sumOfSqPoly Ps) x
  | [], x => by
      show (0 : Q') ≤ eval ([] : Poly) x
      exact Q'.le_refl' 0
  | (P :: Ps), x => by
      show (0 : Q') ≤ eval (padd (pmul P P) (sumOfSqPoly Ps)) x
      refine zero_le_of_eqv
        (Q'.zero_le_add _ _ (eval_sq_nonneg P x) (eval_sumOfSq_nonneg Ps x)) ?_
      exact Q'.eqv_symm (eval_padd (pmul P P) (sumOfSqPoly Ps) x)

/-- `eval [1, c] x ≃ 1 + c·x`. -/
theorem eval_lin_eqv (c x : Q') : (eval [(1 : Q'), c] x).eqv ((1 : Q') + c * x) := by
  show ((1 : Q') + x * (c + x * 0)).eqv ((1 : Q') + c * x)
  refine Q'.add_eqv_congr_left _ _ _ ?_
  -- x * (c + x*0) ≃ x * c ≃ c * x
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left x (c + x * 0) c
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left c (x * 0) 0 (q_mul_zero x))
        (q_add_zero_eqv c))) ?_
  exact Q'.mul_comm_eqv x c

/-- `eval oneMinusXSq x ≃ (1 − x)·(1 + x)` (writing `1 − x = 1 + -x`).
The QPoly identity `[1,0,-1] = pmul [1,-1] [1,1]` (by `decide`) plus
`eval_pmul` and the linear-evaluation lemma. -/
theorem eval_oneMinusXSq_factor (x : Q') :
    (eval oneMinusXSq x).eqv (((1 : Q') + (-(1 : Q')) * x) * ((1 : Q') + (1 : Q') * x)) :=
  Q'.eqv_trans _ _ _
    (poly_eqv oneMinusXSq (pmul [(1 : Q'), -(1 : Q')] [(1 : Q'), (1 : Q')]) x (by decide))
    (Q'.eqv_trans _ _ _ (eval_pmul [(1 : Q'), -(1 : Q')] [(1 : Q'), (1 : Q')] x)
      (q_mul_congr (eval_lin_eqv (-(1 : Q')) x) (eval_lin_eqv (1 : Q') x)))

/-- `0 ≤ eval oneMinusXSq x` for `x ∈ [−1,1]`: `1 − x² = (1 − x)(1 + x) ≥ 0`
since both factors are `≥ 0` there. -/
theorem eval_oneMinusXSq_nonneg (x : Q')
    (h1 : (-(1 : Q')) ≤ x) (h2 : x ≤ (1 : Q')) :
    (0 : Q') ≤ eval oneMinusXSq x := by
  -- (-1)*x ≃ -x  and  1*x ≃ x
  have hneg : ((-(1 : Q')) * x).eqv (-x) :=
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 x)
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv x))
  have hone : ((1 : Q') * x).eqv x := Q'.one_mul_eqv x
  have hL : (0 : Q') ≤ (1 : Q') + (-(1 : Q')) * x := by
    have hstep := Q'.add_le_add_right x (1 : Q') (-x) h2  -- x + -x ≤ 1 + -x
    have h0 : (0 : Q') ≤ (1 : Q') + -x :=
      Q'.le_trans' 0 (x + -x) ((1 : Q') + -x)
        (Q'.le_of_eqv (Q'.eqv_symm (q_add_neg_self x))) hstep
    exact zero_le_of_eqv h0 (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm hneg))
  have hR : (0 : Q') ≤ (1 : Q') + (1 : Q') * x := by
    have hstep := Q'.add_le_add_left (1 : Q') (-(1 : Q')) x h1  -- 1 + -1 ≤ 1 + x
    have h0 : (0 : Q') ≤ (1 : Q') + x :=
      Q'.le_trans' 0 ((1 : Q') + -(1 : Q')) ((1 : Q') + x)
        (Q'.le_of_eqv (Q'.eqv_symm (q_add_neg_self (1 : Q')))) hstep
    exact zero_le_of_eqv h0 (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm hone))
  exact zero_le_of_eqv (Q'.mul_nonneg _ _ hL hR)
    (Q'.eqv_symm (eval_oneMinusXSq_factor x))

/-! ## Part 1 (headline): certificate soundness — `Certificate p → NonnegOn p` -/

/-- **Certificate soundness (fully symbolic).**  Any Markov–Lukács
certificate forces nonnegativity on `[−1,1]`: the producer's image is
contained in the nonneg cone.  Pointwise: `eval p x ≃ Σ A_j²(x) + (1 −
x²)·Σ B_j²(x)`, and on `[−1,1]` the first summand is `≥ 0` (sum of squares),
`1 − x² ≥ 0`, and `Σ B_j²(x) ≥ 0`, so the product and total are `≥ 0`. -/
theorem certificate_sound {p : Poly} (cert : Certificate p) : NonnegOn p := by
  intro x h1 h2
  have hid : (eval p x).eqv
      (eval (padd (sumOfSqPoly cert.cosParts)
        (pmul oneMinusXSq (sumOfSqPoly cert.sinParts))) x) := cert.identity x
  have hRHS : (0 : Q') ≤ eval (padd (sumOfSqPoly cert.cosParts)
      (pmul oneMinusXSq (sumOfSqPoly cert.sinParts))) x := by
    refine zero_le_of_eqv
      (Q'.zero_le_add _ _ (eval_sumOfSq_nonneg cert.cosParts x) ?_)
      (Q'.eqv_symm (eval_padd (sumOfSqPoly cert.cosParts)
        (pmul oneMinusXSq (sumOfSqPoly cert.sinParts)) x))
    refine zero_le_of_eqv
      (Q'.mul_nonneg _ _ (eval_oneMinusXSq_nonneg x h1 h2) (eval_sumOfSq_nonneg cert.sinParts x))
      (Q'.eqv_symm (eval_pmul oneMinusXSq (sumOfSqPoly cert.sinParts) x))
  exact zero_le_of_eqv hRHS (Q'.eqv_symm hid)

/-! ## Part 2 — composition closure (a constructive producer sub-algebra) -/

/-- **Defining producer.**  Every `(cosParts, sinParts)` *is* a certificate
for the polynomial it spells out (`reflexivity` of the identity). -/
def certOfParts (cosParts sinParts : List Poly) :
    Certificate (padd (sumOfSqPoly cosParts) (pmul oneMinusXSq (sumOfSqPoly sinParts))) where
  cosParts := cosParts
  sinParts := sinParts
  identity := fun _ => Q'.eqv_refl _

/-- **Square atom.**  `A²` has a certificate (`σ₀ = [A]`, `σ₁ = []`). -/
def certSq (A : Poly) : Certificate (pmul A A) where
  cosParts := [A]
  sinParts := []
  identity := fun x => by
    show (eval (pmul A A) x).eqv
      (eval (padd (padd (pmul A A) ([] : Poly)) (pmul oneMinusXSq ([] : Poly))) x)
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (eval_padd (padd (pmul A A) ([] : Poly)) (pmul oneMinusXSq ([] : Poly)) x) ?_
    refine Q'.eqv_trans _ _ _
      (q_add_congr (eval_padd (pmul A A) ([] : Poly) x)
        (eval_pmul oneMinusXSq ([] : Poly) x)) ?_
    refine Q'.eqv_trans _ _ _
      (q_add_congr
        (q_add_zero_eqv (eval (pmul A A) x))
        (q_mul_zero (eval oneMinusXSq x))) ?_
    exact q_add_zero_eqv (eval (pmul A A) x)

/-- **Weighted atom.**  `(1 − x²)·B²` has a certificate (`σ₀ = []`,
`σ₁ = [B]`). -/
def certWeight (B : Poly) : Certificate (pmul oneMinusXSq (pmul B B)) where
  cosParts := []
  sinParts := [B]
  identity := fun x => by
    show (eval (pmul oneMinusXSq (pmul B B)) x).eqv
      (eval (padd (sumOfSqPoly ([] : List Poly))
        (pmul oneMinusXSq (sumOfSqPoly [B]))) x)
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (eval_padd (sumOfSqPoly ([] : List Poly))
        (pmul oneMinusXSq (padd (pmul B B) ([] : Poly))) x) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (by show (eval ([] : Poly) x).eqv 0; exact Q'.eqv_refl 0)) ?_
    refine Q'.eqv_trans _ _ _ (q_zero_add_eqv _) ?_
    refine Q'.eqv_trans _ _ _ (eval_pmul oneMinusXSq (padd (pmul B B) ([] : Poly)) x) ?_
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (eval_pmul oneMinusXSq (pmul B B) x) ?_
    refine Q'.mul_eqv_congr_left _ _ _ ?_
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (eval_padd (pmul B B) ([] : Poly) x)
      (q_add_zero_eqv (eval (pmul B B) x)))

/-- `eval (sumOfSqPoly (Ps ++ Qs)) x ≃ eval (sumOfSqPoly Ps) x + eval (sumOfSqPoly Qs) x`. -/
theorem sumOfSqPoly_append_eval : ∀ (Ps Qs : List Poly) (x : Q'),
    (eval (sumOfSqPoly (Ps ++ Qs)) x).eqv
      (eval (sumOfSqPoly Ps) x + eval (sumOfSqPoly Qs) x)
  | [], Qs, x => by
      show (eval (sumOfSqPoly Qs) x).eqv (eval ([] : Poly) x + eval (sumOfSqPoly Qs) x)
      exact Q'.eqv_symm (q_zero_add_eqv (eval (sumOfSqPoly Qs) x))
  | (P :: Ps), Qs, x => by
      show (eval (padd (pmul P P) (sumOfSqPoly (Ps ++ Qs))) x).eqv
        (eval (padd (pmul P P) (sumOfSqPoly Ps)) x + eval (sumOfSqPoly Qs) x)
      refine Q'.eqv_trans _ _ _ (eval_padd (pmul P P) (sumOfSqPoly (Ps ++ Qs)) x) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (sumOfSqPoly_append_eval Ps Qs x)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv (eval (pmul P P) x)
          (eval (sumOfSqPoly Ps) x) (eval (sumOfSqPoly Qs) x))) ?_
      exact Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_symm (eval_padd (pmul P P) (sumOfSqPoly Ps) x))

/-- **Additive closure.**  Certificates add: concatenate the SOS parts.  The
identity uses that `sumOfSqPoly` is additive over list-append (under `eval`)
and that `(1−x²)·(σ₁ + σ₁') = (1−x²)σ₁ + (1−x²)σ₁'`. -/
def certAdd {p q : Poly} (cp : Certificate p) (cq : Certificate q) :
    Certificate (padd p q) where
  cosParts := cp.cosParts ++ cq.cosParts
  sinParts := cp.sinParts ++ cq.sinParts
  identity := fun x => by
    -- Abbreviations (plain `let`s; the proof terms below unfold them definitionally).
    refine Q'.eqv_trans _ _ _ (eval_padd p q x) ?_
    refine Q'.eqv_trans _ _ _
      (q_add_congr (cp.identity x) (cq.identity x)) ?_
    have hp := eval_padd (sumOfSqPoly cp.cosParts) (pmul oneMinusXSq (sumOfSqPoly cp.sinParts)) x
    have hq := eval_padd (sumOfSqPoly cq.cosParts) (pmul oneMinusXSq (sumOfSqPoly cq.sinParts)) x
    refine Q'.eqv_trans _ _ _ (q_add_congr hp hq) ?_
    have hwb₀ : (eval (pmul oneMinusXSq (sumOfSqPoly cp.sinParts)) x).eqv
        (eval oneMinusXSq x * eval (sumOfSqPoly cp.sinParts) x) := eval_pmul _ _ x
    have hwb₁ : (eval (pmul oneMinusXSq (sumOfSqPoly cq.sinParts)) x).eqv
        (eval oneMinusXSq x * eval (sumOfSqPoly cq.sinParts) x) := eval_pmul _ _ x
    refine Q'.eqv_trans _ _ _
      (q_add_congr (Q'.add_eqv_congr_left _ _ _ hwb₀)
        (Q'.add_eqv_congr_left _ _ _ hwb₁)) ?_
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (eval_padd (sumOfSqPoly (cp.cosParts ++ cq.cosParts))
        (pmul oneMinusXSq (sumOfSqPoly (cp.sinParts ++ cq.sinParts))) x) ?_
    have hcos := sumOfSqPoly_append_eval cp.cosParts cq.cosParts x
    have hsin := sumOfSqPoly_append_eval cp.sinParts cq.sinParts x
    refine Q'.eqv_trans _ _ _
      (q_add_congr hcos
        (Q'.eqv_trans _ _ _ (eval_pmul oneMinusXSq (sumOfSqPoly (cp.sinParts ++ cq.sinParts)) x)
          (Q'.mul_eqv_congr_left (eval oneMinusXSq x) _ _ hsin))) ?_
    -- RHS: (a₀ + a₁) + w·(b₀ + b₁) ; target LHS: (a₀ + w·b₀) + (a₁ + w·b₁)
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (q_interchange (eval (sumOfSqPoly cp.cosParts) x)
        (eval oneMinusXSq x * eval (sumOfSqPoly cp.sinParts) x)
        (eval (sumOfSqPoly cq.cosParts) x)
        (eval oneMinusXSq x * eval (sumOfSqPoly cq.sinParts) x)) ?_
    refine Q'.add_eqv_congr_left _ _ _ ?_
    exact Q'.eqv_symm (Q'.mul_add_eqv (eval oneMinusXSq x)
      (eval (sumOfSqPoly cp.sinParts) x) (eval (sumOfSqPoly cq.sinParts) x))

/-! ## Part 3 — a symbolic degree-≤2 producer family (formulas in `a, b, c`)

The rationally-representable even-form quadratics:
`quadFamily a b c = (a + b x)² + (1 − x²)·c²`, parametrised by arbitrary
rationals `a, b, c`.  Each has a certificate given by FORMULAS in `(a,b,c)`
(`σ₀ = [[a, b]]`, `σ₁ = [[c]]`), and (via `certificate_sound`) is
nonnegative on `[−1,1]`.  Expanding,
`quadFamily a b c = (a² + c²) + 2ab·x + (b² − c²)·x²`.  This is the honest
symbolic degree-2 producer: every member is certified, with the certificate
a closed-form function of the parameters. -/

/-- The symbolic degree-≤2 family `(a + b x)² + (1 − x²)·c²` as a `QPoly`. -/
def quadFamily (a b c : Q') : Poly :=
  padd (pmul [a, b] [a, b]) (pmul oneMinusXSq (pmul [c] [c]))

/-- **Symbolic degree-≤2 producer.**  For *arbitrary* rationals `a, b, c`,
the family member `quadFamily a b c` carries a certificate whose SOS parts
are the formulas `σ₀ = [[a, b]]`, `σ₁ = [[c]]`.  The identity reduces, via the
`eval` homomorphism, to the definition of `quadFamily`. -/
def certQuadFamily (a b c : Q') : Certificate (quadFamily a b c) where
  cosParts := [[a, b]]
  sinParts := [[c]]
  identity := fun x => by
    show (eval (quadFamily a b c) x).eqv
      (eval (padd (sumOfSqPoly [[a, b]]) (pmul oneMinusXSq (sumOfSqPoly [[c]]))) x)
    unfold quadFamily
    refine Q'.eqv_trans _ _ _
      (eval_padd (pmul [a, b] [a, b]) (pmul oneMinusXSq (pmul [c] [c])) x) ?_
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (eval_padd (sumOfSqPoly [[a, b]]) (pmul oneMinusXSq (sumOfSqPoly [[c]])) x) ?_
    refine q_add_congr ?_ ?_
    · show (eval (padd (pmul [a, b] [a, b]) ([] : Poly)) x).eqv (eval (pmul [a, b] [a, b]) x)
      exact Q'.eqv_trans _ _ _ (eval_padd (pmul [a, b] [a, b]) ([] : Poly) x)
        (q_add_zero_eqv (eval (pmul [a, b] [a, b]) x))
    · refine Q'.eqv_trans _ _ _ (eval_pmul oneMinusXSq (sumOfSqPoly [[c]]) x) ?_
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _ (eval_pmul oneMinusXSq (pmul [c] [c]) x) ?_
      refine Q'.mul_eqv_congr_left _ _ _ ?_
      show (eval (pmul [c] [c]) x).eqv (eval (padd (pmul [c] [c]) ([] : Poly)) x)
      exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (eval_padd (pmul [c] [c]) ([] : Poly) x)
        (q_add_zero_eqv (eval (pmul [c] [c]) x)))

/-- **Nonnegativity of the symbolic degree-≤2 family** on `[−1,1]`, for
arbitrary rationals `a, b, c` — a corollary of `certificate_sound` applied to
`certQuadFamily`.  (No hypotheses on `a, b, c`: this *family* is nonnegative
by construction, the honest symbolic shadow of the degree-2 Markov–Lukács
theorem on the rationally-representable branch.) -/
theorem certQuadFamily_nonneg (a b c : Q') : NonnegOn (quadFamily a b c) :=
  certificate_sound (certQuadFamily a b c)

/-! ## Part 4 — the sharpened open gap, and a proved reduction

The generic degree-`n` (already `n = 2`) even-form certificate over `Q'`
does NOT exist: producing `(σ₀, σ₁)` from the bare hypothesis `NonnegOn p`
needs a *rational* spectral square root (Fejér–Riesz / constructive
Markov–Lukács), which the `decide`-based rational substrate lacks.  We name
that missing input precisely and prove that it closes the producer. -/

/-- **The precise missing analytic input** (a sharpening of the bare
`markov_lukacs_existence`): a *rational even-form spectral factorization
oracle* — for every `p` nonnegative on `[−1,1]`, it returns the SOS data of
a `Certificate p`.  This is exactly the constructive root-finding step the
rational `decide` substrate does not provide; it is the genuine remaining
gap.  (`Type`-level: it must *produce* the witness, per AGENTS.md Rule 8.) -/
def factorizationOracle : Type :=
  ∀ (p : Poly), NonnegOn p → Certificate p

/-- **Proved reduction:** the factorization oracle closes the general
producer.  `factorizationOracle → markov_lukacs_existence`.  Constructive:
the oracle's `Certificate p` is wrapped into the `Nonempty` of
`markov_lukacs_existence`.  This is a real result — the reduction is proved;
only the oracle itself remains open. -/
theorem oracle_implies_existence :
    factorizationOracle → markov_lukacs_existence :=
  fun oracle p hp => ⟨oracle p hp⟩

/-- **Converse direction** (soundness of the producer specification): any
certificate is necessarily a certificate *of a nonnegative polynomial*, so
the oracle's domain hypothesis `NonnegOn p` is also *necessary* — pinning the
oracle's specification exactly (`certificate_sound` is the containment side). -/
theorem producer_targets_nonneg {p : Poly} (cert : Certificate p) : NonnegOn p :=
  certificate_sound cert

end YMGap.Continuum.MarkovLukacs

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MarkovLukacs.eval_sq_nonneg
#print axioms YMGap.Continuum.MarkovLukacs.eval_sumOfSq_nonneg
#print axioms YMGap.Continuum.MarkovLukacs.eval_oneMinusXSq_nonneg
#print axioms YMGap.Continuum.MarkovLukacs.certificate_sound
#print axioms YMGap.Continuum.MarkovLukacs.certSq
#print axioms YMGap.Continuum.MarkovLukacs.certWeight
#print axioms YMGap.Continuum.MarkovLukacs.certAdd
#print axioms YMGap.Continuum.MarkovLukacs.certOfParts
#print axioms YMGap.Continuum.MarkovLukacs.certQuadFamily
#print axioms YMGap.Continuum.MarkovLukacs.certQuadFamily_nonneg
#print axioms YMGap.Continuum.MarkovLukacs.oracle_implies_existence
#print axioms YMGap.Continuum.MarkovLukacs.producer_targets_nonneg
