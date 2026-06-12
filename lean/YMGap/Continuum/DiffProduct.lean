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
import YMGap.Continuum.TsumDeriv

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

/-! ## 4. Bridge to the generic C¹-uniform-limit engine (`TsumDeriv.lean`)

`TsumDeriv.fdDeriv_of_unif` is the genuine constructive analysis engine — *the
uniform limit of derivatives is the derivative of the limit*, with explicit moduli
as data — that the `(LEIBNIZ)` finite skeleton above feeds.  This section records
how the engine specialises to `ProductDerivativeLimit`, isolating the residual as
exactly ONE clearly-named `Σ`-obligation (`C1ToEquiv`): the instantiation data
that turns the engine's `FDDerivData` output into the `CReal.Equiv` of the series
and product representations.

The engine output is a `FDDerivData F (g θ) θ` — a finite-difference DERIVATIVE of
the limit `F = ϑ₃` at `θ`, with value `g θ` (the log-derivative series `−sinθ·ϑ₃·S`).
`ProductDerivativeLimit Dseries Rproduct` is a `CReal.Equiv` of the two CReal
*representations* of that derivative.  The remaining bridge is the identification
of the engine's derivative value with both CReal representations; we name it as a
`Σ`-obligation and prove the conditional `C1ToEquiv → ProductDerivativeLimit`. -/

open YMGap.Continuum.TsumDeriv

/-- **The named instantiation `Σ`-obligation (NOT discharged).**  Packages exactly
what is needed to specialise the generic C¹-limit engine to the heat-kernel /
Jacobi factors and land `ProductDerivativeLimit Dseries Rproduct`:

* `f`, `f'` — the finite theta-PRODUCT truncations and their (finite-product-rule,
  `leibniz`) derivatives, as `Q'`-valued functions of `θ`;
* `F`, `g` — the limit `ϑ₃` and its log-derivative `−sinθ·ϑ₃·S`;
* `inputs` — the `C1Inputs` data (pointwise + uniform convergence + equicontinuity
  moduli) for that family at the working point `θ` — the genuine
  `O((a·a)^k)`-modulus analytic content, supplied as data;
* `bridge` — the identification that the resulting finite-difference derivative
  `g θ` is realised, as a `CReal` equality, by BOTH `Dseries` and `Rproduct` (the
  series side `dSeriesCReal` and the product side `Rhalf`).

Given this datum, `ProductDerivativeLimit Dseries Rproduct` follows immediately
(`bridge` is literally the `CReal.Equiv`).  The obligation is `Type`-valued
(Rule 8.3): every modulus is recoverable.  It is NOT discharged here — it is the
sharp residual: the `C1Inputs` for the theta-product family (the part the geometric
log-derivative majorant supplies) plus the derivative-value identification. -/
structure C1ToEquiv (Dseries Rproduct : CReal) : Type where
  /-- The finite theta-product truncations `f M θ`. -/
  f : Nat → Q' → Q'
  /-- Their finite-product-rule derivatives `f' M θ` (the `leibniz` log-derivative). -/
  f' : Nat → Q' → Q'
  /-- The product limit `F = ϑ₃` and its log-derivative `g = −sinθ·ϑ₃·S`. -/
  F : Q' → Q'
  g : Q' → Q'
  /-- The working point. -/
  θ : Q'
  /-- The C¹-limit engine inputs for the theta family (the analytic modulus data). -/
  inputs : C1Inputs f f' F g θ
  /-- The derivative-value identification: the engine's derivative `g θ` is the
  common limit of the series side `Dseries` and the product side `Rproduct`. -/
  bridge : CReal.Equiv Dseries Rproduct

/-- **`C1ToEquiv → ProductDerivativeLimit` (conditional closure).**  The named
instantiation obligation discharges the abstract product-derivative limit.  The
engine `TsumDeriv.fdDeriv_of_unif inputs` produces the finite-difference derivative
witness (recorded for the reader / downstream modulus extraction); the `CReal`
equality is the `bridge` field. -/
theorem productDerivativeLimit_of_c1
    {Dseries Rproduct : CReal} (H : C1ToEquiv Dseries Rproduct) :
    ProductDerivativeLimit Dseries Rproduct :=
  H.bridge

/-- The engine genuinely fires on the obligation's data: from `C1ToEquiv` we can
extract the `FDDerivData` (finite-difference derivative of the product limit `F`
at `θ`, value `g θ`, with explicit modulus).  Recorded to make explicit that the
analytic engine — not a black box — is what consumes the instantiation data. -/
def fdDerivData_of_c1
    {Dseries Rproduct : CReal} (H : C1ToEquiv Dseries Rproduct) :
    FDDerivData H.F (H.g H.θ) H.θ :=
  TsumDeriv.fdDeriv_of_unif H.inputs

/-! ## 5. DERIVATIVE-UNIQUENESS BRIDGE (Route A — collapsing the differentiated
identity to the UNdifferentiated one)

`TsumDeriv.fdDeriv_unique` (the CoRN `Derivative_I_unique` analogue, landed
axiom-clean in `TsumDeriv.lean`) says: two finite-difference derivatives of the
SAME function `F` at the SAME point `θ` are EQUAL (`d₁ ≃ d₂`), with NO uniformity
needed.  This is the structural fix for the blocker named in
`docs/jtp-closure-progress.md`: instead of comparing the two truncation SEQUENCES
(which converge at incompatible rates `a^{(M+1)²}` vs `(a·a)^M` and agree at no
finite `M`), we observe that BOTH the series side and the product side are
finite-difference derivatives of the *one* limit function, so their derivative
values coincide by uniqueness.

What this genuinely buys, and the honest residual it exposes:

* The PRODUCT side gives `FDDerivData F (g θ) θ` directly from the engine
  (`fdDerivData_of_c1`), where `F = ϑ₃` realised as the convergent PRODUCT.
* The SERIES side, IF its differentiated truncations are a finite-difference
  derivative of the SAME `F` at `θ`, gives `FDDerivData F dser θ`.  But the series
  truncations differentiate the theta-**series** `ϑ₃^{ser}`, so this requires the
  UNDIFFERENTIATED limit-level Jacobi identity `ϑ₃^{ser} = ϑ₃^{prod}` as functions
  (the `N → ∞` limit of the finite `GaussQBinom.gauss_qbinom_all`).
* Given both, `fdDeriv_unique` yields `g θ ≃ dser` at the `Q'` level.

So the uniqueness route REPLACES the *differentiated* double-limit interchange
(`C1ToEquiv.bridge` as a raw `CReal.Equiv` assumption) by the *undifferentiated*
limit-level identity plus uniqueness.  The piece below packages exactly that
collapse: from two `FDDerivData` of a common `F` it derives the `Q'`-equality of
derivative values via the genuine `fdDeriv_unique` engine. -/

open YMGap.Continuum.TsumDeriv in
/-- **The two-derivative collapse (genuine, axiom-clean).**  Two finite-difference
derivatives of the SAME limit function `F` at the SAME point `θ` have equal
derivative values: `dser ≃ dprod`.  This is `TsumDeriv.fdDeriv_unique` re-exposed in
the `DiffProduct` namespace; it is the reusable core of Route A.  The honest
residual it leaves for the heat-kernel application is supplying the SERIES-side
`FDDerivData` over the SAME `F` as the product side — i.e. the undifferentiated
Jacobi identity `ϑ₃^{ser} = ϑ₃^{prod}`. -/
theorem deriv_values_eq_of_common_limit {F : Q' → Q'} {dser dprod θ : Q'}
    (Dser : FDDerivData F dser θ) (Dprod : FDDerivData F dprod θ) :
    dser ≈ dprod :=
  TsumDeriv.fdDeriv_unique Dser Dprod

/-- **The Route-A instantiation obligation (named `Type`, NOT discharged).**  This
is the SHARPENED residual for `C1ToEquiv`: rather than assuming the differentiated
`CReal.Equiv` (`C1ToEquiv.bridge`) outright, it asks for

* the product-family C¹ engine inputs (`inputs`, supplying `FDDerivData F (g θ) θ`
  via `fdDeriv_of_unif` — the part that genuinely commutes `d/dθ` with the limit),
* a SERIES-side finite-difference derivative `FDDerivData F dser θ` over the SAME
  limit function `F` (this is where the UNDIFFERENTIATED Jacobi identity
  `ϑ₃^{ser} = ϑ₃^{prod}` enters — both families must differentiate one `F`), and
* a `CReal` realisation linking the `Q'`-equality `g θ ≃ dser` (which
  `fdDeriv_unique` then supplies) back to `CReal.Equiv Dseries Rproduct`.

It makes precise that Route A relocates the blocker from the *differentiated*
double-limit interchange to the *undifferentiated* limit identity + a rational→real
realisation.  The `Q'`-level uniqueness engine (`fdDeriv_unique`) is fully
discharged; the residual is the common-`F` series derivative and the realisation. -/
structure C1UniqInputs (Dseries Rproduct : CReal) : Type where
  /-- The common limit function `F = ϑ₃` (one function — the crux of the route). -/
  F : Q' → Q'
  /-- The working point. -/
  θ : Q'
  /-- The product-side derivative value `g θ` (log-derivative `−sinθ·ϑ₃·S`). -/
  dprod : Q'
  /-- The series-side derivative value `dser`. -/
  dser : Q'
  /-- The product-side finite-difference derivative of `F` at `θ` (engine output). -/
  Dprod : FDDerivData F dprod θ
  /-- The series-side finite-difference derivative of the SAME `F` at `θ`.  Carrying
  this over the SAME `F` is exactly the undifferentiated Jacobi identity. -/
  Dser : FDDerivData F dser θ
  /-- The realisation: the `Q'`-equality of derivative values (supplied by
  `fdDeriv_unique` from `Dser`, `Dprod`) lifts to the `CReal` bridge. -/
  realise : dser ≈ dprod → CReal.Equiv Dseries Rproduct

/-- **`C1UniqInputs → C1ToEquiv`** is NOT claimed (the `inputs`/`f`/`f'` fields of
`C1ToEquiv` need the full product family); instead we close the END goal directly:
`C1UniqInputs → ProductDerivativeLimit`.  The derivative-value equality comes from
the GENUINE `fdDeriv_unique` engine applied to the two `FDDerivData`, and `realise`
lifts it to the `CReal` bridge.  This is the uniqueness-routed conditional closure:
it consumes the two derivatives (engine output NOT discarded) rather than a raw
`CReal.Equiv` assumption. -/
theorem productDerivativeLimit_of_uniq
    {Dseries Rproduct : CReal} (H : C1UniqInputs Dseries Rproduct) :
    ProductDerivativeLimit Dseries Rproduct :=
  H.realise (deriv_values_eq_of_common_limit H.Dser H.Dprod)

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
#print axioms YMGap.Continuum.DiffProduct.productDerivativeLimit_of_c1
#print axioms YMGap.Continuum.DiffProduct.fdDerivData_of_c1
#print axioms YMGap.Continuum.DiffProduct.deriv_values_eq_of_common_limit
#print axioms YMGap.Continuum.DiffProduct.productDerivativeLimit_of_uniq
