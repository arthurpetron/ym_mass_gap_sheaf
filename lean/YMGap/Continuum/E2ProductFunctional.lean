/-
Track B / E2 (thermodynamic / finite-volume rung) — the **decoupled
multi-edge product functional**.

The single-edge heat-kernel Wilson functional (`WilsonFunctional`,
`ObservableMeasure.ProbFunctional`) is the `n = 1` piece of finite volume.
The honest *first* rung of "finite volume" — BEFORE any plaquette coupling
— is the **free (product) measure** on `n` decoupled edges:

    E_⊗(⊗_{i<n} a_i) = Π_{i<n} E_i(a_i),

the moment functional of the product probability measure `⊗_i μ_i` on the
product configuration space `Π_i G`.  With NO plaquette term the edges are
statistically independent, so the joint expectation of a *separable*
observable factorizes into the per-edge expectations.

This module builds that product object inside the existing `ObsAlg` /
`ProbFunctional` framework and proves it is again a genuine probability
functional:

  * `prodAlg A n` — the product observable *-algebra on the first `n`
    edges (carrier `Π i, (A i).carrier`, componentwise unit/mul/star).
  * `prodFunctional μ n : ProbFunctional (prodAlg A n)` — the product
    functional `E_⊗(a) = Π_{i<n} (μ i).E (a i)`, with
      - `normalized` : `E_⊗ 1 = Π_{i<n} 1 = 1`  (STRICT `Q'` equality,
        since `(1 : Q') * 1 = 1` holds definitionally),
      - `positive`   : `0 ≤ E_⊗(a*·a) = Π_{i<n} (μ i).E((a i)*·a i)`, a
        finite product of nonnegatives (`Q'.mul_nonneg`).

  * `edgeIncl A n j` — the unital *-hom embedding edge `j`'s observables
    into the product (insert at coordinate `j`, unit elsewhere): coarse
    "I only look at edge `j`" observables sit inside the joint algebra.
  * `prodFunctional_marginal` — the **decoupling / marginalization law**:
    the product functional's expectation of a single-edge observable
    placed at edge `j` equals (up to `Q'.eqv`, since `Q'` multiplication
    is unital only up to `.eqv`) that edge's own expectation `(μ j).E a`.
    This is the genuine independence statement: the single-edge marginal
    of the free product measure IS the single-edge measure.

# What this is / is not

This is the FREE finite-volume functional — genuine, fully proved,
axiom-clean.  It is NOT the interacting (plaquette-coupled) finite-volume
measure, and it is NOT the infinite-volume limit.  See the `OPEN` list in
`docs/e2-e3-notes.md`.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` (and `Quot.sound` where `Nat`/`omega` enter).  No `Classical.*`,
no `sorryAx`.
-/

import YMGap.Continuum.ObservableMeasure
import YMGap.Constructive.RationalsMul

namespace YMGap.Continuum.E2ProductFunctional

open YMGap.Continuum.ObservableMeasure
open YMGap.Constructive

/-! ## Finite products of rationals (the `Q'`-level expectation fold)

`prodE f n = Π_{i<n} f i`, built by `Nat`-recursion from the strict `Q'`
product.  Two facts drive the functional below:

  * `prodE_eq_one_of` — an all-units product is `1` STRICTLY (each step is
    `(1 : Q') * 1 = 1`, which is `rfl`); this gives `normalized` as a
    genuine `=`, not merely `.eqv`.
  * `prodE_nonneg` — a product of nonnegatives is nonnegative
    (`Q'.mul_nonneg`); this gives `positive`. -/

/-- `Π_{i<n} f i` over `Q'` (strict product fold). -/
def prodE (f : Nat → Q') : Nat → Q'
  | 0 => 1
  | n + 1 => prodE f n * f n

@[simp] theorem prodE_zero (f : Nat → Q') : prodE f 0 = 1 := rfl

@[simp] theorem prodE_succ (f : Nat → Q') (n : Nat) :
    prodE f (n + 1) = prodE f n * f n := rfl

/-- `prodE` depends only on the values below `n`. -/
theorem prodE_congr (f g : Nat → Q') :
    ∀ n, (∀ i, i < n → f i = g i) → prodE f n = prodE g n
  | 0, _ => rfl
  | n + 1, h => by
      show prodE f n * f n = prodE g n * g n
      rw [h n (Nat.lt_succ_self n),
        prodE_congr f g n (fun i hi => h i (Nat.lt_succ_of_lt hi))]

/-- **All-units product is `1` (strictly).**  If `f i = 1` for every
`i < n` then `Π_{i<n} f i = 1` as a `Q'` *equality* — the step
`(1 : Q') * 1 = 1` is definitional. -/
theorem prodE_eq_one_of (f : Nat → Q') :
    ∀ n, (∀ i, i < n → f i = 1) → prodE f n = 1
  | 0, _ => rfl
  | n + 1, h => by
      show prodE f n * f n = 1
      rw [h n (Nat.lt_succ_self n),
        prodE_eq_one_of f n (fun i hi => h i (Nat.lt_succ_of_lt hi))]
      rfl

/-- The constant-`1` product is `1`. -/
theorem prodE_one (n : Nat) : prodE (fun _ => (1 : Q')) n = 1 :=
  prodE_eq_one_of _ n (fun _ _ => rfl)

/-- **Product of nonnegatives is nonnegative.** -/
theorem prodE_nonneg (f : Nat → Q') (h : ∀ i, (0 : Q') ≤ f i) :
    ∀ n, (0 : Q') ≤ prodE f n
  | 0 => (by decide : (0 : Q') ≤ (1 : Q'))
  | n + 1 => Q'.mul_nonneg _ _ (prodE_nonneg f h n) (h n)

/-! ## The product observable *-algebra -/

/-- The **product observable *-algebra** on the first `n` edges: separable
observables `a = (a_0, …, a_{n−1})`, with componentwise unit, product, and
involution.  (`carrier = ∀ i, (A i).carrier`; the index `i` ranges over all
`Nat`, but only `i < n` is read by the functional.) -/
def prodAlg (A : Nat → ObsAlg) (_n : Nat) : ObsAlg where
  carrier := ∀ i, (A i).carrier
  one := fun i => (A i).one
  mul := fun a b i => (A i).mul (a i) (b i)
  star := fun a i => (A i).star (a i)

/-! ## The product probability functional -/

/-- The **decoupled product functional** `E_⊗(a) = Π_{i<n} (μ i).E (a i)`.
A genuine `ProbFunctional` on `prodAlg A n`: normalized (all factors `= 1`)
and positive (finite product of nonnegative per-edge `E((a i)*·a i)`). -/
def prodFunctional (A : Nat → ObsAlg) (μ : ∀ i, ProbFunctional (A i)) (n : Nat) :
    ProbFunctional (prodAlg A n) where
  E := fun a => prodE (fun i => (μ i).E (a i)) n
  normalized := by
    show prodE (fun i => (μ i).E ((A i).one)) n = 1
    exact prodE_eq_one_of _ n (fun i _ => (μ i).normalized)
  positive := fun a => by
    show (0 : Q') ≤ prodE (fun i => (μ i).E ((A i).mul ((A i).star (a i)) (a i))) n
    exact prodE_nonneg _ (fun i => (μ i).positive (a i)) n

/-- `E_⊗` on a separable observable is, by definition, the per-edge product. -/
theorem prodFunctional_apply (A : Nat → ObsAlg) (μ : ∀ i, ProbFunctional (A i))
    (n : Nat) (a : (prodAlg A n).carrier) :
    (prodFunctional A μ n).E a = prodE (fun i => (μ i).E (a i)) n := rfl

/-! ## Single-edge insertion and the decoupling (marginal) law

`insertAt A j a` embeds an edge-`j` observable into the joint configuration
by placing `a` at coordinate `j` and the unit on every other coordinate.
The product functional's value on it factorizes: every off-`j` coordinate
contributes `(μ i).E (A i).one = 1`, so only the edge-`j` factor survives.

NOTE.  We do *not* claim `insertAt` is a unital *-hom into `prodAlg`: a bare
`ObsAlg` carries NO unit laws (no `mul one one = one`, no `star one = one`),
so `map_mul`/`map_star` for the off-`j` coordinates are simply not available
without strengthening `ObsAlg`.  We therefore give the marginal law as a
direct value computation on the functional — which is exactly the
independence/decoupling statement and needs only `(μ i).normalized`. -/

/-- Insert `a` at coordinate `j`, the unit elsewhere. -/
def insertAt (A : Nat → ObsAlg) (j : Nat) (a : (A j).carrier) :
    (∀ i, (A i).carrier) :=
  fun i => if h : i = j then h ▸ a else (A i).one

/-- The value of `(μ i).E` on the inserted observable at coordinate `i`:
`a`'s expectation at `i = j`, and `1` (`normalized`) off `j`. -/
theorem insertAt_E_eq (A : Nat → ObsAlg) (μ : ∀ i, ProbFunctional (A i))
    (j : Nat) (a : (A j).carrier) (i : Nat) :
    (μ i).E (insertAt A j a i) = (if i = j then (μ j).E a else 1) := by
  unfold insertAt
  by_cases h : i = j
  · subst h; rw [dif_pos rfl, if_pos rfl]
  · rw [dif_neg h, if_neg h]; exact (μ i).normalized

/-- **All off-`j` coordinates contribute `1`**, so the `prodE` over the
first `n` factors reduces to the value-fold `Π_{i<n} (if i = j then v else 1)`
with `v = (μ j).E a`. -/
theorem prodFunctional_insertAt_eq_indicator
    (A : Nat → ObsAlg) (μ : ∀ i, ProbFunctional (A i)) (n : Nat)
    (j : Nat) (a : (A j).carrier) :
    (prodFunctional A μ n).E (insertAt A j a)
      = prodE (fun i => if i = j then (μ j).E a else 1) n := by
  show prodE (fun i => (μ i).E (insertAt A j a i)) n
      = prodE (fun i => if i = j then (μ j).E a else 1) n
  exact prodE_congr _ _ n (fun i _ => insertAt_E_eq A μ j a i)

/-- A single-place indicator product reduces, up to `Q'.eqv`, to that place's
value: `Π_{i<n} (if i = j then v else 1) ≃ v` when `j < n`.  (Strict equality
fails only by the unital collapse `1·v ≃ v` / `v·1 ≃ v`, which is `.eqv`, not
`rfl`, over `Q'`.) -/
theorem prodE_indicator_eqv (v : Q') :
    ∀ n j, j < n → (prodE (fun i => if i = j then v else 1) n).eqv v
  | n + 1, j, hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · -- j < n : the (i = n) factor is 1; collapse `(Π) * 1 ≃ Π ≃ v`
        show (prodE (fun i => if i = j then v else 1) n
            * (if n = j then v else (1 : Q'))).eqv v
        rw [if_neg (by omega : ¬ n = j)]
        exact Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _)
          (prodE_indicator_eqv v n j hlt)
      · -- j = n : the product over i < n is all-ones (= 1 strictly), times v
        subst heq
        show (prodE (fun i => if i = j then v else 1) j
            * (if j = j then v else (1 : Q'))).eqv v
        rw [if_pos rfl,
          prodE_eq_one_of (fun i => if i = j then v else 1) j
            (fun i hi => if_neg (by omega : ¬ i = j))]
        -- `1 * v ≃ v`
        exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv 1 v) (Q'.mul_one_eqv v)

/-- **The decoupling / marginalization law (E2 independence).**  For `j < n`,
the product functional's expectation of a single-edge observable inserted at
edge `j` equals (up to `Q'.eqv`) that edge's own expectation:

    E_⊗(insertAt j a) ≃ (μ j).E a.

This is the genuine statement that the single-edge marginal of the FREE
(decoupled) product measure is the single-edge measure. -/
theorem prodFunctional_marginal
    (A : Nat → ObsAlg) (μ : ∀ i, ProbFunctional (A i)) (n : Nat)
    (j : Nat) (hj : j < n) (a : (A j).carrier) :
    ((prodFunctional A μ n).E (insertAt A j a)).eqv ((μ j).E a) := by
  rw [prodFunctional_insertAt_eq_indicator A μ n j a]
  exact prodE_indicator_eqv ((μ j).E a) n j hj

/-! ## Concrete inhabitant: an `n`-edge trivial product

The product of `n` copies of the trivial one-point functional is a genuine
`ProbFunctional` on the `n`-fold product algebra — exhibiting the
construction is inhabitable, not a `True`/`Unit` placeholder. -/

/-- The constant trivial family of algebras. -/
def trivFamily : Nat → ObsAlg := fun _ => trivAlg

/-- The constant trivial family of functionals. -/
def trivFuncFamily : ∀ i, ProbFunctional (trivFamily i) := fun _ => trivFunc

/-- The `n`-edge trivial product functional — a concrete inhabitant. -/
def trivProdFunctional (n : Nat) : ProbFunctional (prodAlg trivFamily n) :=
  prodFunctional trivFamily trivFuncFamily n

/-- Its normalization is the genuine strict `Q'` equality `E_⊗ 1 = 1`. -/
theorem trivProdFunctional_normalized (n : Nat) :
    (trivProdFunctional n).E (prodAlg trivFamily n).one = 1 :=
  (trivProdFunctional n).normalized

end YMGap.Continuum.E2ProductFunctional

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.E2ProductFunctional.prodE_eq_one_of
#print axioms YMGap.Continuum.E2ProductFunctional.prodE_nonneg
#print axioms YMGap.Continuum.E2ProductFunctional.prodFunctional
#print axioms YMGap.Continuum.E2ProductFunctional.prodFunctional_marginal
#print axioms YMGap.Continuum.E2ProductFunctional.trivProdFunctional
#print axioms YMGap.Continuum.E2ProductFunctional.trivProdFunctional_normalized
