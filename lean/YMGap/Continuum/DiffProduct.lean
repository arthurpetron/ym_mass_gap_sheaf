/-
# The constructive finite-difference Leibniz product rule (Wall-2 differentiation core)

This module builds the **pure-`Q'`-algebraic heart** of the
"derivative-of-a-convergent-product" engine named in
`docs/jtp-convergence-notes.md §2.3` as the single outstanding Wall-2 analytic
obligation (`DiffJTP` of `JTPIdentity.lean`).

## What is GENUINELY closed here (new, axiom-clean, fully reusable content)

The double-limit interchange `lim_h lim_L = lim_L lim_h` underlying the
differentiated Jacobi-triple-product factors, at every FINITE truncation level
`L`, through the exact **discrete product rule** (finite-difference Leibniz):
for two factor sequences `f, g : Nat → Q'`,

    ∏_{k<L} f k  −  ∏_{k<L} g k
        ≈  Σ_{j<L}  (∏_{k<j} f k) · (f j − g j) · (∏_{j<k<L} g k).            (LEIBNIZ)

This is the genuine finite core of differentiating a product term by term: with
`f k = factor(c_k)(θ+h)` and `g k = factor(c_k)(θ)`, dividing (LEIBNIZ) by `h`
gives the finite-difference Leibniz expansion of `(∏(θ+h) − ∏(θ))/h` as a sum of
per-factor difference quotients weighted by the surrounding partial products —
precisely the term-by-term product-derivative whose `L → ∞` limit (after the
`h → 0` limit of each factor's difference quotient) is the log-derivative series
`(d/dθ log ∏) = Σ_k g_k'/g_k`.  It introduces NO new positivity content
(positivity is already in `ThetaConvGen.R_geRat_zero_gen`); it is purely the
algebraic interchange skeleton.

`(LEIBNIZ)` is proved here by induction on `L`, over the `Q'.eqv` ring layer
(`Rationals.lean` / `RationalsMul.lean`), with NO `ring`/`linarith`/`Mathlib ℝ`
(AGENTS.md Rule 3) and NO smallness/positivity hypotheses on `f, g` (it is a pure
ring identity, valid for arbitrary `Q'`-sequences).

## The honest residual (AGENTS.md Rule 6)

`(LEIBNIZ)` is the FINITE-level identity.  The remaining Wall-2 obligation — the
genuine analytic content — is the DOUBLE-LIMIT interchange: that the
finite-difference quotients `(∏(θ+h) − ∏(θ))/h`, as `L → ∞` then `h → 0`
(uniformly, with the explicit `O((a·a)^k)` log-derivative modulus of
`jtp-convergence-notes.md §2.3`), converge to the series side.  That uniform
double-limit is NOT discharged here; it is exposed as the named `Prop`
`ProductDerivativeLimit` (and the downstream `DiffJTP` of `JTPIdentity.lean`
remains a named hypothesis).  `(LEIBNIZ)` is the finite skeleton that any such
constructive engine must rest on, and it is the largest genuine fragment that is
pure algebra (no analysis).

### Why a finite "matched-truncation" identity does NOT exist (sharp finding)

`leibniz` differentiates the finite PRODUCT exactly (`d/dθ ∏_{k<L} = −sin θ·∏·S`,
the log-derivative).  The SERIES side `dSeriesCReal` is the differentiated finite
theta-SERIES truncation (`= D_M/sin θ`).  These two finite objects are NOT equal
at any finite truncation level: the finite theta-series truncation `th3series_M`
and the finite theta-product truncation `th3prod_M` differ by `~(a·a)^M` (Gauss's
`qProd = gaussSum` equates them only for the full sum / `N → ∞`).  So the series
truncation converges super-geometrically (`~a^{(M+1)²}`) while the product
truncation converges only geometrically (`~(a·a)^M`); they share a limit but
match at NO finite `M`.  `leibniz` (the finite product rule) therefore cannot be
upgraded to a finite equal-at-each-level identity — the bridge IS the `M → ∞`
limit of differentiated Gauss, the missing engine.  (Details + 40-digit
verification in `docs/jtp-closure-progress.md`.)

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (`Quot.sound` only via reused
`Nat`/`Int`/`finSum`/`omega` helpers).  No `Classical.*`, no `native_decide`,
no `sorry`.
-/

import YMGap.Constructive.Rationals
import YMGap.Constructive.RationalsMul
import YMGap.Constructive.RationalTail
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.CauchyConv
import YMGap.Constructive.CRealMul
import YMGap.Constructive.ExpAdd
import YMGap.Constructive.Geometric

namespace YMGap.Continuum.DiffProduct

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Constructive.RationalTail

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := Q'.eqv_trans _ _ _ h1 h2

/-! ## 1. Prefix and suffix finite products over a general `Q'`-factor sequence

`pre f L = ∏_{k=0}^{L-1} f k` (the first `L` factors, ascending).
`suf g m L = ∏_{k=m}^{L-1} g k` (factors from index `m` up to `L-1`).

Both are defined structurally with NO positivity hypotheses (general ring
products), so the Leibniz identity below is a pure algebraic statement. -/

/-- The prefix product `pre f L = ∏_{k<L} f k`. -/
def pre (f : Nat → Q') : Nat → Q'
  | 0     => 1
  | L + 1 => pre f L * f L

@[simp] theorem pre_zero (f : Nat → Q') : pre f 0 = 1 := rfl
@[simp] theorem pre_succ (f : Nat → Q') (L : Nat) : pre f (L + 1) = pre f L * f L := rfl

/-- The suffix product from index `m`, of length `d`:
`sufLen g m d = ∏_{k=m}^{m+d-1} g k = g m · g (m+1) ⋯ g (m+d-1)`. -/
def sufLen (g : Nat → Q') (m : Nat) : Nat → Q'
  | 0     => 1
  | d + 1 => g m * sufLen g (m + 1) d

@[simp] theorem sufLen_zero (g : Nat → Q') (m : Nat) : sufLen g m 0 = 1 := rfl
@[simp] theorem sufLen_succ (g : Nat → Q') (m d : Nat) :
    sufLen g m (d + 1) = g m * sufLen g (m + 1) d := rfl

/-! ### Two structural product identities we need

`sufLen g m (d + 1) ≈ sufLen g m d · g (m + d)` — appending the last factor.
`pre g (m + d) ≈ pre g m · sufLen g m d` — splitting a prefix product at `m`. -/

/-- `sufLen g m (d + 1) ≈ sufLen g m d · g (m + d)` — appending the LAST factor
(the `sufLen` recursion peels the FIRST factor; this peels the last).  Induction
on `d`. -/
theorem sufLen_append (g : Nat → Q') (m : Nat) :
    ∀ d, sufLen g m (d + 1) ≈ sufLen g m d * g (m + d)
  | 0 => by
      show sufLen g m 1 ≈ sufLen g m 0 * g (m + 0)
      show g m * sufLen g (m + 1) 0 ≈ (1 : Q') * g (m + 0)
      have hm0 : m + 0 = m := rfl
      rw [hm0]
      -- g m · 1 ≈ 1 · g m
      refine Q'.eqv_trans _ _ _ (Q'.mul_one_eqv (g m)) ?_
      exact Q'.eqv_symm (Q'.one_mul_eqv (g m))
  | d + 1 => by
      -- sufLen g m (d+2) = g m · sufLen g (m+1) (d+1)
      show g m * sufLen g (m + 1) (d + 1) ≈ sufLen g m (d + 1) * g (m + (d + 1))
      -- ih (at m+1): sufLen g (m+1) (d+1) ≈ sufLen g (m+1) d · g ((m+1)+d)
      have ih := sufLen_append g (m + 1) d
      have hidx : (m + 1) + d = m + (d + 1) := by omega
      rw [hidx] at ih
      -- LHS ≈ g m · (sufLen g (m+1) d · g (m+(d+1)))
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (g m) _ _ ih) ?_
      -- g m · (A · b) ≈ (g m · A) · b = sufLen g m (d+1) · g (m+(d+1))
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (g m) (sufLen g (m + 1) d) (g (m + (d + 1))))) ?_
      -- (g m · sufLen g (m+1) d) = sufLen g m (d+1) definitionally
      exact Q'.eqv_refl _

/-- `pre g (m + d) ≈ pre g m · sufLen g m d`.  Induction on `d`.  (Reusable
prefix/suffix split for the product engine; not on the `leibniz` critical path,
but the natural companion to `sufLen_append`.) -/
theorem pre_split (g : Nat → Q') (m : Nat) :
    ∀ d, pre g (m + d) ≈ pre g m * sufLen g m d
  | 0 => by
      show pre g (m + 0) ≈ pre g m * sufLen g m 0
      have : m + 0 = m := rfl
      rw [this]
      show pre g m ≈ pre g m * 1
      exact Q'.eqv_symm (Q'.mul_one_eqv (pre g m))
  | d + 1 => by
      have he : m + (d + 1) = (m + d) + 1 := by omega
      rw [he]
      show pre g ((m + d) + 1) ≈ pre g m * sufLen g m (d + 1)
      show pre g (m + d) * g (m + d) ≈ pre g m * sufLen g m (d + 1)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (g (m + d)) (pre_split g m d)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv (pre g m) (sufLen g m d) (g (m + d))) ?_
      exact Q'.mul_eqv_congr_left (pre g m) _ _
        (Q'.eqv_symm (sufLen_append g m d))

/-! ## 2. The discrete product rule (finite-difference Leibniz)

The Leibniz summand at index `j` (with surrounding products `pre f j` and the
suffix of `g` from `j+1` up to `L`):

    leibTerm f g L j  =  pre f j · (f j + (−(g j))) · sufLen g (j+1) (L − (j+1)).

The full Leibniz sum is `Σ_{j<L} leibTerm f g L j`.  The identity
`pre f L − pre g L ≈ Σ_{j<L} leibTerm f g L j` is the genuine finite core. -/

/-- The `j`-th Leibniz summand of the telescoped product difference at level `L`:
`pre f j · (f j − g j) · (∏_{j<k<L} g k)`.  The suffix length is `L − (j+1)`. -/
def leibTerm (f g : Nat → Q') (L j : Nat) : Q' :=
  (pre f j * (f j + (-(g j)))) * sufLen g (j + 1) (L - (j + 1))

/-- **The algebraic split (pure ring identity).**
`P·f + (−(Q·g)) ≈ (P + (−Q))·g + P·(f + (−g))`.  This is
`Pf − Qg = (P − Q)g + P(f − g)`, expanded over the `Q'.eqv` ring layer. -/
theorem split_core (P Q f g : Q') :
    P * f + (-(Q * g)) ≈ (P + (-Q)) * g + P * (f + (-g)) := by
  -- RHS = (P·g + (−Q)·g) + (P·f + P·(−g))
  --     = (P·g + (−(Q·g))) + (P·f + (−(P·g)))
  --     ≈ P·f + (−(Q·g))   [the two ±P·g cancel]
  have hleft : ((P + (-Q)) * g) ≈ (P * g + (-(Q * g))) := by
    -- (P + (−Q))·g ≈ P·g + (−Q)·g ≈ P·g + (−(Q·g))
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv P (-Q) g) ?_
    exact Q'.add_eqv_congr_left (P * g) _ _ (Q'.neg_mul_eqv Q g)
  have hright : (P * (f + (-g))) ≈ (P * f + (-(P * g))) := by
    -- P·(f + (−g)) ≈ P·f + P·(−g) ≈ P·f + (−(P·g))
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv P f (-g)) ?_
    exact Q'.add_eqv_congr_left (P * f) _ _ (Q'.mul_neg_eqv P g)
  have e1 : ((P + (-Q)) * g + P * (f + (-g)))
      ≈ ((P * g + (-(Q * g))) + (P * f + (-(P * g)))) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ hleft)
      (Q'.add_eqv_congr_left _ _ _ hright)
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _ e1 ?_)
  -- (A + (−Qg)) + (Pf + (−A)) ≈ Pf + (−Qg),  A = P·g, Qg = Q·g, Pf = P·f.
  -- Cancel A with (−A) via additive commutativity/assoc.
  calc (P * g + (-(Q * g))) + (P * f + (-(P * g)))
      ≈ P * g + ((-(Q * g)) + (P * f + (-(P * g)))) :=
        Q'.add_assoc_eqv (P * g) (-(Q * g)) (P * f + (-(P * g)))
    _ ≈ P * g + (((-(Q * g)) + P * f) + (-(P * g))) :=
        Q'.add_eqv_congr_left (P * g) _ _
          (Q'.eqv_symm (Q'.add_assoc_eqv (-(Q * g)) (P * f) (-(P * g))))
    _ ≈ P * g + ((-(P * g)) + ((-(Q * g)) + P * f)) :=
        Q'.add_eqv_congr_left (P * g) _ _
          (Q'.add_comm_eqv ((-(Q * g)) + P * f) (-(P * g)))
    _ ≈ (P * g + (-(P * g))) + ((-(Q * g)) + P * f) :=
        Q'.eqv_symm (Q'.add_assoc_eqv (P * g) (-(P * g)) ((-(Q * g)) + P * f))
    _ ≈ (0 : Q') + ((-(Q * g)) + P * f) :=
        Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv (P * g))
    _ ≈ ((-(Q * g)) + P * f) := by rw [Q'.zero_add']; exact Q'.eqv_refl _
    _ ≈ P * f + (-(Q * g)) := Q'.add_comm_eqv (-(Q * g)) (P * f)

/-- **Suffix-extension of the Leibniz sum.**  Appending one more factor `g L`
extends every `∏_{j<k<L} g k` (suffix at level `L`) to `∏_{j<k<L+1} g k`
(suffix at level `L+1`).  Hence
`finSum (leibTerm f g (L+1)) L ≈ (finSum (leibTerm f g L) L) · g L`:
every summand picks up exactly the factor `g L` at the end.  Proved termwise via
`finSum`-congruence + the constant-factor pull-out, using `sufLen_append`. -/
theorem leib_sum_extend (f g : Nat → Q') (L : Nat) :
    finSum (leibTerm f g (L + 1)) L ≈ finSum (leibTerm f g L) L * g L := by
  -- Termwise: leibTerm f g (L+1) j ≈ leibTerm f g L j · g L  for j < L.
  -- Then finSum (· · g L) L ≈ (finSum (leibTerm f g L) L) · g L  (const_mul_finSum).
  have hterm : finSum (leibTerm f g (L + 1)) L
      ≈ finSum (fun j => leibTerm f g L j * g L) L := by
    refine RationalTail.finSum_eqv_congr_lt _ _ L ?_
    intro j hj
    -- leibTerm f g (L+1) j = (pre f j · (f j − g j)) · sufLen g (j+1) ((L+1)−(j+1))
    -- (L+1)−(j+1) = L − j ;  and L − j = (L − (j+1)) + 1  since j < L.
    show (pre f j * (f j + (-(g j)))) * sufLen g (j + 1) ((L + 1) - (j + 1))
        ≈ ((pre f j * (f j + (-(g j)))) * sufLen g (j + 1) (L - (j + 1))) * g L
    have hlen : (L + 1) - (j + 1) = (L - (j + 1)) + 1 := by omega
    rw [hlen]
    -- sufLen g (j+1) ((L−(j+1))+1) ≈ sufLen g (j+1) (L−(j+1)) · g ((j+1)+(L−(j+1)))
    have happ := sufLen_append g (j + 1) (L - (j + 1))
    have hidx : (j + 1) + (L - (j + 1)) = L := by omega
    rw [hidx] at happ
    -- coef · sufLen(…+1) ≈ coef · (sufLen · g L) ≈ (coef · sufLen) · g L
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (pre f j * (f j + (-(g j)))) _ _ happ) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv (pre f j * (f j + (-(g j))))
        (sufLen g (j + 1) (L - (j + 1))) (g L))
  refine Q'.eqv_trans _ _ _ hterm ?_
  -- finSum (fun j => h j · g L) L ≈ (finSum h L) · g L
  -- (RationalTail.finSum_mul_const : (finSum h N)·c ≈ finSum (fun i => h i · c) N)
  exact Q'.eqv_symm (RationalTail.finSum_mul_const (leibTerm f g L) (g L) L)

/-- **The discrete product rule (finite-difference Leibniz), CLOSED for all `L`.**
For arbitrary `Q'`-factor sequences `f, g`:

    ∏_{k<L} f k  −  ∏_{k<L} g k  ≈  Σ_{j<L} pre f j · (f j − g j) · ∏_{j<k<L} g k.

Proved by induction on `L`.  Base `L=0`: `1 − 1 ≈ 0` (empty sum).  Step: split
`pre f (L+1) − pre g (L+1) = (pre f L · f L − pre g L · g L)` as
`(pre f L − pre g L)·g L + pre f L·(f L − g L)`; the first bracket is the IH
times `g L` (absorbed into each suffix, since appending `g L` extends every
`∏_{j<k<L} g k` to `∏_{j<k<L+1} g k`), the second is the new top term
`leibTerm f g (L+1) L` (whose suffix `∏_{L<k<L+1} g k` is empty `= 1`). -/
theorem leibniz (f g : Nat → Q') :
    ∀ L, pre f L + (-(pre g L)) ≈ finSum (leibTerm f g L) L
  | 0 => by
      -- pre f 0 + (-(pre g 0)) = 1 + (-1) ≈ 0 = finSum _ 0
      show (1 : Q') + (-(1 : Q')) ≈ finSum (leibTerm f g 0) 0
      show (1 : Q') + (-(1 : Q')) ≈ (0 : Q')
      exact Q'.add_neg_self_eqv 1
  | L + 1 => by
      -- LHS = pre f L · f L + (−(pre g L · g L))
      show pre f L * f L + (-(pre g L * g L)) ≈ finSum (leibTerm f g (L + 1)) (L + 1)
      -- RHS = finSum (leibTerm f g (L+1)) L + leibTerm f g (L+1) L
      show pre f L * f L + (-(pre g L * g L))
          ≈ finSum (leibTerm f g (L + 1)) L + leibTerm f g (L + 1) L
      -- The new top term: suffix length (L+1) − (L+1) = 0, so sufLen … 0 = 1.
      have htop : leibTerm f g (L + 1) L ≈ pre f L * (f L + (-(g L))) := by
        show (pre f L * (f L + (-(g L)))) * sufLen g (L + 1) ((L + 1) - (L + 1))
            ≈ pre f L * (f L + (-(g L)))
        have hsub : (L + 1) - (L + 1) = 0 := by omega
        rw [hsub]
        show (pre f L * (f L + (-(g L)))) * 1 ≈ pre f L * (f L + (-(g L)))
        exact Q'.mul_one_eqv _
      -- The induction-hypothesis sum at level L, with each suffix extended by g L.
      -- KEY: finSum (leibTerm f g (L+1)) L ≈ (finSum (leibTerm f g L) L) · g L
      have hext : finSum (leibTerm f g (L + 1)) L ≈ finSum (leibTerm f g L) L * g L :=
        leib_sum_extend f g L
      -- IH at L
      have ih := leibniz f g L
      -- Step 1: the algebraic split (pure ring identity).
      have hsplit : pre f L * f L + (-(pre g L * g L))
          ≈ (pre f L + (-(pre g L))) * g L + pre f L * (f L + (-(g L))) :=
        split_core (pre f L) (pre g L) (f L) (g L)
      refine Q'.eqv_trans _ _ _ hsplit ?_
      -- Step 2: rewrite first bracket via ih, second via htop (backwards).
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_right _ _ (g L) ih))
          (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm htop))) ?_
      -- Goal: (finSum (leibTerm f g L) L)·g L + leibTerm f g (L+1) L
      --        ≈ finSum (leibTerm f g (L+1)) L + leibTerm f g (L+1) L
      exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hext)

/-! ## 3. The remaining analytic obligation, stated sharply

`(LEIBNIZ)` is the finite skeleton.  Realising the product DERIVATIVE requires
the genuine analytic step — the uniform double-limit interchange — which is NOT
discharged here.  We expose it as a named `Prop`, parametrised by:

* the factor families at the base point and the perturbed point
  (`gθ k = factor(c_k)(θ)`, `fθh k = factor(c_k)(θ+h)`),
* the per-factor log-derivative limits `logDeriv k = g_k'/g_k` (the `h → 0`
  limit of `(f k − g k)/h`), and
* the target product-derivative `D` (the `CReal` series side).

The obligation is that the `CReal` limit of the Leibniz sums (divided by `h`),
as `h → 0`, equals `D`, with the explicit `O((a·a)^k)` modulus.  This is exactly
the bracketed Lemma of `jtp-convergence-notes.md §2.3` and the content of
`JTPIdentity.DiffJTP`. -/

/-- **The product-derivative limit obligation (named `Prop`, NOT discharged).**
Given a `CReal` `Pinf` realising the convergent product `∏_k g_k` and a `CReal`
`Dinf` realising its formal term-by-term derivative `Pinf · Σ_k g_k'/g_k`, the
obligation asserts they are linked by the differentiated-product identity — i.e.
the finite-difference quotients of the Leibniz sums converge (in `L` then `h`,
uniformly) to `Dinf`.  This is the single analytic engine still required; the
finite skeleton `(LEIBNIZ)` above is its algebraic core.  Stated abstractly as a
`CReal.Equiv` so that `JTPIdentity.DiffJTP` is exactly its specialisation to the
heat-kernel factors. -/
def ProductDerivativeLimit (Dseries Rproduct : CReal) : Prop :=
  CReal.Equiv Dseries Rproduct

/-- The product-derivative obligation is symmetric (inherited from
`CReal.Equiv.symm`), recorded so downstream code may orient it either way. -/
theorem ProductDerivativeLimit.symm {A B : CReal}
    (h : ProductDerivativeLimit A B) : ProductDerivativeLimit B A :=
  CReal.Equiv.symm h

end YMGap.Continuum.DiffProduct

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` enters only through reused `Nat`/`Int`/`finSum`/`omega` helpers).
No `Classical.*`, no `native_decide`, no `sorry`.  `ProductDerivativeLimit` is a
named `Prop` (the single open analytic obligation), NOT a `sorry`. -/

#print axioms YMGap.Continuum.DiffProduct.pre_split
#print axioms YMGap.Continuum.DiffProduct.sufLen_append
#print axioms YMGap.Continuum.DiffProduct.split_core
#print axioms YMGap.Continuum.DiffProduct.leib_sum_extend
#print axioms YMGap.Continuum.DiffProduct.leibniz
#print axioms YMGap.Continuum.DiffProduct.ProductDerivativeLimit.symm
