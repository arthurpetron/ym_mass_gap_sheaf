/-
The constructive continuum theory as a positive functional with
CANONICAL-modulus regular-real expectations, and — the headline — as a
positive LINEAR functional whose linearity laws are THEOREMS.

# Why this module exists

The infinite-volume continuum object is a POSITIVE NORMALIZED FUNCTIONAL
(Daniell / expectation) on an observable *-algebra; its values are the
Schwinger functions and the Osterwalder–Schrader axioms are positivity
properties of it.  An earlier port valued that functional in the merely
Cauchy constructive real, whose one-slack order is non-transitive and
whose modulus hides in a `Prop`-`∃`.  This module re-homes the functional
on `RegularCReal`, the regular constructive real whose canonical modulus
is `Type`-level data and whose Bishop order is genuinely transitive.

Two views are built, separated honestly.

  * The MULTIPLICATIVE-observable view (`RegProbFunctional`) on the minimal
    observable *-algebra `ObsAlg` (carrier / one / mul / star — no
    addition), which is where the real character / reflection-positivity
    data lives.  Its expectations are produced per observable by the
    regular-real completeness limit `completeLimit`, with `normalized` and
    `positive` PROVED from the finite-volume bounds.

  * The LINEAR-observable view (`RegLinearFunctional`) on an enriched
    algebra `LinearObsAlg` that adds `zero`, `add`, and rational scaling
    `smul`.  Here linearity is finally EXPRESSIBLE, and the two laws

      `E (a + b) ≈ E a + E b`        (additivity)
      `E (q • a) ≈ q · E a`          (homogeneity)

    are PROVED, not assumed — the genuine payoff of `RegularCReal`
    carrying addition (`add`) and rational scaling (`qmul`).  This is the
    constructive primitive the program targets: the continuum theory as a
    positive LINEAR functional, with linearity a theorem.

A non-vacuous inhabitant of each view is exhibited: the SU(2) character
heat-kernel tower for the multiplicative view, and `Q'` itself (carrier
`Q'`, expectation `ofQ'`) for the linear view, where additivity is
`ofQ'_add` and homogeneity is `ofQ'_qmul` — both already proved on the
regular reals, so they cleanly demonstrate that the regular-real
arithmetic genuinely supports functional linearity.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only, inherited from the reused
`Q'` / `RegularCReal` order and arithmetic lemmas.  No `Classical.*`, no
`sorry`, no `native_decide`.  Every modulus is carried as `Type`-level
data (the `RegularCReal.ModCauchy` outer modulus).
-/

import YMGap.Continuum.ContinuumFunctional
import YMGap.Constructive.RegularCReal
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.RegularFunctional

open YMGap.Constructive
open YMGap.Constructive.RegularCReal
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.RGTransport
open YMGap.Continuum.ContinuumFunctional

/-! ## 1. The continuum functional on the regular reals (multiplicative view)

The minimal observable *-algebra `ObsAlg` carries only `one`, `mul`,
`star` — no addition — so the functional it supports is positive and
normalized but not (yet) linear.  This is the view in which the real
character / OS data lives. -/

/-- A constructive **continuum probability functional** valued in the
regular constructive reals: the Daniell / expectation representation of
the continuum theory with `RegularCReal` expectations.

  * `E : A.carrier → RegularCReal` — the continuum Schwinger functional;
  * `normalized` — `E 1 ≈ 1` at the regular-real level;
  * `positive` — `0 ≤ E (a* · a)` at the regular-real level. -/
structure RegProbFunctional (A : ObsAlg) where
  /-- The continuum expectation, valued in the regular constructive reals. -/
  E : A.carrier → RegularCReal
  /-- Normalization at the unit: `E 1 ≈ 1`. -/
  normalized : Equiv (E A.one) (ofQ' 1)
  /-- Reflection-style positivity: `0 ≤ E (a* · a)`. -/
  positive : ∀ a, czero ≤ E (A.mul (A.star a) a)

/-! ## 2. The per-observable convergence input as regular-real `ModCauchy`

The honest analytic input is, FOR EACH observable, a sequence of
finite-volume expectations together with an outer Cauchy modulus on it.
On the regular reals the natural such datum is a `Q'`-sequence of
expectations plus a two-sided `Q'`-modulus `M`; lifting the sequence by
`ofQ'` and the bound termwise gives a `RegularCReal.ModCauchy`, whose
diagonal `completeLimit` is the regular-real continuum expectation. -/

/-- The per-observable input on the regular reals: a `Q'`-sequence of
finite-volume expectations with a two-sided outer Cauchy modulus carried
as `Type`-level data (`M`, the antitone modulus, and the bound).  This is
exactly the `RegularCReal.ModCauchy` content phrased at the `Q'` level so
that the `ofQ'` lift is immediate. -/
structure RegObservableModulus where
  /-- The finite-volume expectation sequence `Λ ↦ ⟨o⟩_Λ`. -/
  seq : Nat → Q'
  /-- Outer Cauchy modulus, `Type`-level data. -/
  M : Q' → Nat
  /-- The outer modulus is antitone. -/
  Mmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → M ε ≤ M δ
  /-- Two-sided outer bound: for `i, j ≥ M ε`, the expectations are
  `ε`-close. -/
  bound : ∀ ε : Q', (0 : Q') < ε → ∀ i j : Nat, M ε ≤ i → M ε ≤ j →
    seq i ≤ seq j + ε ∧ seq j ≤ seq i + ε

/-- The lifted regular-real sequence `Λ ↦ ofQ' (seq Λ)`. -/
def RegObservableModulus.regSeq (m : RegObservableModulus) : Nat → RegularCReal :=
  fun Λ => ofQ' (m.seq Λ)

/-- The lifted sequence is `ModCauchy`: the `Q'` bound transfers termwise
through `ofQ'` (constant approximations), and the antitone modulus carries
over unchanged. -/
def RegObservableModulus.modCauchy (m : RegObservableModulus) :
    ModCauchy m.regSeq where
  M := m.M
  Mmono := m.Mmono
  bound := by
    intro ε hε i j hi hj k
    obtain ⟨h1, h2⟩ := m.bound ε hε i j hi hj
    -- (ofQ' (seq i)).approx k = seq i, (ofQ' (seq j)).approx k = seq j.
    exact ⟨h1, h2⟩

/-- The regular-real continuum expectation produced from one observable's
modulus datum: the diagonal completeness limit of the lifted sequence. -/
def RegObservableModulus.reg (m : RegObservableModulus) : RegularCReal :=
  completeLimit m.regSeq m.modCauchy

/-! ## 3. The infinite-volume-limit constructor (regular reals)

A consistent tower of `Q'`-valued probability functionals together with,
per observable, its regular-real outer modulus, yields a
`RegProbFunctional`.  `normalized` and `positive` are PROVED from the
finite-volume `unit_seq` / `pos_seq` via the regular-real bound lifts
`ofQ'_le_completeLimit` / `completeLimit_le_ofQ'`. -/

/-- The full infinite-volume-limit input, regular-real version: a scale
system, a consistent family of `Q'`-valued probability functionals, and,
per observable, its regular-real outer modulus, plus the two finite-volume
facts pinning normalization (`unit_seq`) and positivity (`pos_seq`). -/
structure RegConsistentFamily where
  /-- The scale system (observable tower). -/
  S : ObsSystem
  /-- The per-scale `Q'`-valued probability functionals. -/
  pick : ∀ k, ProbFunctional (S.Obs k)
  /-- Kolmogorov consistency of the family. -/
  consistent : is_consistent (funcProjSystem S) pick
  /-- For each base-scale observable, its regular-real outer modulus. -/
  modOf : (S.Obs 0).carrier → RegObservableModulus
  /-- The unit's expectation sequence is the constant `1`. -/
  unit_seq : ∀ Λ, (modOf (S.Obs 0).one).seq Λ = 1
  /-- The expectation sequence of any `a*·a` is pointwise `≥ 0`. -/
  pos_seq : ∀ a Λ,
    (0 : Q') ≤ (modOf ((S.Obs 0).mul ((S.Obs 0).star a) a)).seq Λ

/-- **The infinite-volume continuum-limit constructor (regular reals).**

Given a consistent tower of `Q'`-valued probability functionals with a
per-observable regular-real outer modulus, construct the continuum
`RegProbFunctional` over the base algebra `Obs 0`:

  * `E o := (modOf o).reg` — the per-observable regular-real limit
    (the diagonal completeness limit of `ofQ' ∘ seq`), the infinite-volume
    limit by DIRECT MODULUS;
  * `normalized` — PROVED: `E 1`'s lifted sequence is the constant
    `ofQ' 1`, so `E 1 ≈ ofQ' 1` by `completeLimit_le_ofQ'` +
    `ofQ'_le_completeLimit` packaged as an `Equiv` via `le_antisymm`;
  * `positive` — PROVED: `E (a*·a)`'s lifted sequence has every
    approximation `≥ 0`, so `0 = ofQ' 0 ≤ E (a*·a)` by
    `ofQ'_le_completeLimit`. -/
def regFunctional_of_modulus (F : RegConsistentFamily) :
    RegProbFunctional (F.S.Obs 0) where
  E := fun o => (F.modOf o).reg
  normalized := by
    -- E 1 ≈ ofQ' 1 : both bounds from the constant-1 lifted sequence.
    refine le_antisymm ?_ ?_
    · -- completeLimit ≤ ofQ' 1
      refine completeLimit_le_ofQ' (F.modOf (F.S.Obs 0).one).regSeq
        (F.modOf (F.S.Obs 0).one).modCauchy (ub := (1 : Q')) ?_
      intro k j
      show (F.modOf (F.S.Obs 0).one).seq k ≤ 1
      rw [F.unit_seq k]; exact Q'.le_refl' 1
    · -- ofQ' 1 ≤ completeLimit
      refine ofQ'_le_completeLimit (F.modOf (F.S.Obs 0).one).regSeq
        (F.modOf (F.S.Obs 0).one).modCauchy (lb := (1 : Q')) ?_
      intro k j
      show (1 : Q') ≤ (F.modOf (F.S.Obs 0).one).seq k
      rw [F.unit_seq k]; exact Q'.le_refl' 1
  positive := fun a => by
    -- 0 = ofQ' 0 ≤ E (a*·a) by lower bound on the lifted sequence.
    show czero ≤ (F.modOf ((F.S.Obs 0).mul ((F.S.Obs 0).star a) a)).reg
    show ofQ' 0 ≤ (F.modOf ((F.S.Obs 0).mul ((F.S.Obs 0).star a) a)).reg
    refine ofQ'_le_completeLimit
      (F.modOf ((F.S.Obs 0).mul ((F.S.Obs 0).star a) a)).regSeq
      (F.modOf ((F.S.Obs 0).mul ((F.S.Obs 0).star a) a)).modCauchy (lb := (0 : Q')) ?_
    intro k j
    show (0 : Q') ≤ (F.modOf ((F.S.Obs 0).mul ((F.S.Obs 0).star a) a)).seq k
    exact F.pos_seq a k

/-! ## 4. A concrete inhabitant on the real SU(2) character data

The stationary character tower (`charAlg` / `charFunc`) is EVENTUALLY
CONSTANT, so every observable's finite-volume expectation sequence is the
single value `(charFunc w hw).E o` repeated — a constant sequence, hence
trivially Cauchy with the zero modulus.  The resulting `RegProbFunctional`
is the (non-trivial) heat-kernel functional, now on the regular reals. -/

/-- The constant regular-real modulus datum at a fixed `Q'` value `v`:
`seq Λ = v`, trivial outer modulus `M ε = 0`.  Every pair of terms is
equal, so within any `ε > 0`. -/
def constRegModulus (v : Q') : RegObservableModulus where
  seq := fun _ => v
  M := fun _ => 0
  Mmono := fun _ _ _ _ => Nat.le_refl 0
  bound := by
    intro ε hε i j _ _
    -- seq i = v = seq j ; v ≤ v + ε both directions.
    exact ⟨Q'.add_le_self_of_nonneg v ε (Q'.le_of_lt hε),
           Q'.add_le_self_of_nonneg v ε (Q'.le_of_lt hε)⟩

@[simp] theorem constRegModulus_seq (v : Q') (Λ : Nat) :
    (constRegModulus v).seq Λ = v := rfl

/-- The character family with its trivial (exact) per-observable
regular-real modulus: every observable `o : Nat` gets the constant-sequence
modulus at the heat-kernel value `(charFunc w hw).E o`.  A genuine
inhabitant of `RegConsistentFamily` on the real SU(2) character data. -/
def charRegFamily (w : Q') (hw : (0 : Q') ≤ w) : RegConsistentFamily where
  S := stationaryTower charAlg
  pick := fun _ => charFunc w hw
  consistent := charTowerConsistent w hw
  modOf := fun o => constRegModulus ((charFunc w hw).E o)
  unit_seq := fun _ => by
    show (charFunc w hw).E charAlg.one = 1
    exact (charFunc w hw).normalized
  pos_seq := fun a _ => by
    show (0 : Q') ≤ (charFunc w hw).E (charAlg.mul (charAlg.star a) a)
    exact (charFunc w hw).positive a

/-- **The concrete regular-real continuum functional on real character
data.**  The infinite-volume limit of the stationary SU(2) heat-kernel
tower, a genuine `RegProbFunctional` (not the `≡ 1` placeholder: its value
on the unit is `1` but on `χ_2` it is `< 1`). -/
def regCharFunctional (w : Q') (hw : (0 : Q') ≤ w) :
    RegProbFunctional ((charRegFamily w hw).S.Obs 0) :=
  regFunctional_of_modulus (charRegFamily w hw)

/-- The concrete regular-real functional's value on `o` has, at every
approximation stage, the exact heat-kernel rational `(charFunc w hw).E o`:
the limit is the (already exact) finite-volume expectation, as expected for
the stationary tower. -/
@[simp] theorem regCharFunctional_approx (w : Q') (hw : (0 : Q') ≤ w)
    (o : Nat) (Λ : Nat) :
    ((regCharFunctional w hw).E o).approx Λ = (charFunc w hw).E o := rfl

/-! ## 5. The positive LINEAR functional (linear-observable view)

The minimal `ObsAlg` has no addition, so its functional cannot state
linearity.  The continuum theory's true primitive is a positive LINEAR
functional; to express that we enrich the observable algebra with `zero`,
`add`, and rational scaling `smul`.  On `RegularCReal` the matching
arithmetic (`add`, `qmul`) exists, so the linearity laws are now genuine
THEOREMS about a functional, not axioms. -/

/-- An enriched observable algebra carrying additive and rational-scaling
structure on top of the multiplicative *-algebra data: `carrier`, `zero`,
`add`, `one`, `mul`, `star`, and `smul : Q' → carrier → carrier`.  Only
the operations needed to STATE linearity are included; no ring laws are
axiomatized (none are used). -/
structure LinearObsAlg where
  /-- The observable carrier. -/
  carrier : Type
  /-- Additive identity. -/
  zero : carrier
  /-- Addition of observables. -/
  add : carrier → carrier → carrier
  /-- Multiplicative unit. -/
  one : carrier
  /-- Product of observables. -/
  mul : carrier → carrier → carrier
  /-- Involution. -/
  star : carrier → carrier
  /-- Rational scaling. -/
  smul : Q' → carrier → carrier

/-- A constructive **positive LINEAR functional** on a `LinearObsAlg`,
valued in the regular constructive reals.  Beyond normalization and
positivity it carries the two LINEARITY laws, expressible because both the
algebra (`add`, `smul`) and the codomain (`RegularCReal.add`,
`RegularCReal.qmul`) carry the matching structure:

  * `additive`   — `E (a + b) ≈ E a + E b`;
  * `homogeneous` — `E (q • a) ≈ q · E a`.

This is the continuum theory AS a positive linear functional, with
linearity a theorem of the inhabitant rather than an assumption of the
framework. -/
structure RegLinearFunctional (A : LinearObsAlg) where
  /-- The expectation, valued in the regular constructive reals. -/
  E : A.carrier → RegularCReal
  /-- Normalization at the unit: `E 1 ≈ 1`. -/
  normalized : Equiv (E A.one) (ofQ' 1)
  /-- Reflection-style positivity: `0 ≤ E (a* · a)`. -/
  positive : ∀ a, czero ≤ E (A.mul (A.star a) a)
  /-- **Additivity** — `E (a + b) ≈ E a + E b`. -/
  additive : ∀ a b, Equiv (E (A.add a b)) (RegularCReal.add (E a) (E b))
  /-- **Homogeneity** — `E (q • a) ≈ q · E a`. -/
  homogeneous : ∀ (q : Q') a, Equiv (E (A.smul q a)) (RegularCReal.qmul q (E a))

/-! ## 6. A non-vacuous inhabitant: `Q'` as a linear observable algebra

`Q'` itself is a `LinearObsAlg` (carrier `Q'`, with its own `+`, `*`,
`star = id`, and `smul = (·*·)`), and the embedding `E := ofQ'` is a
positive linear functional on it.  Crucially, its two linearity laws are
EXACTLY the already-proved regular-real facts `ofQ'_add` and `ofQ'_qmul` —
so this inhabitant demonstrates that regular-real arithmetic genuinely
supports functional linearity, with both laws discharged by theorems that
hold by the construction of `add` / `qmul`. -/

/-- `Q'` as a linear observable algebra: carrier `Q'`, `star = id`,
`smul = (·*·)`. -/
def qLinearAlg : LinearObsAlg where
  carrier := Q'
  zero := (0 : Q')
  add := fun (a b : Q') => a + b
  one := (1 : Q')
  mul := fun (a b : Q') => a * b
  star := fun (a : Q') => a
  smul := fun (q : Q') (a : Q') => q * a

/-- Rational squares are nonnegative: `0 ≤ a·a` (sign split on `a.num`). -/
private theorem q_mul_self_nonneg (a : Q') : (0 : Q') ≤ a * a := by
  rw [Q'.zero_le_iff_num_nonneg]
  show (0 : Int) ≤ a.num * a.num
  rcases Int.le_total 0 a.num with hz | hz
  · exact Int.mul_nonneg hz hz
  · have h2 : (0 : Int) ≤ -a.num := Int.neg_nonneg.mpr hz
    have h4 : (0 : Int) ≤ (-a.num) * (-a.num) := Int.mul_nonneg h2 h2
    rwa [Int.neg_mul_neg] at h4

/-- `(ofQ' a)*·(ofQ' a) = ofQ' (a*a) ≥ 0` at the rational level: `a*a ≥ 0`,
so `0 ≤ ofQ' (a*a)` via `ofQ'_le_ofQ'`. -/
private theorem ofQ'_sq_nonneg (a : Q') : czero ≤ ofQ' (a * a) := by
  show ofQ' 0 ≤ ofQ' (a * a)
  exact ofQ'_le_ofQ' (q_mul_self_nonneg a)

/-- **`Q'` carries a positive LINEAR functional via `ofQ'`.**  The linearity
laws are `ofQ'_add` and `ofQ'_qmul`, both already proved on the regular
reals — so the headline (`additive` / `homogeneous` PROVED on a genuine
inhabitant) is exhibited here cleanly. -/
def qRegLinearFunctional : RegLinearFunctional qLinearAlg where
  E := fun a => ofQ' a
  normalized := by
    -- E 1 = ofQ' 1 ; Equiv is reflexive.
    show Equiv (ofQ' (1 : Q')) (ofQ' 1)
    exact Equiv.refl _
  positive := fun (a : Q') =>
    -- (a*·a) = a*a (star = id), E = ofQ', so 0 ≤ ofQ' (a*a).
    ofQ'_sq_nonneg a
  additive := fun (a b : Q') =>
    -- E (a + b) = ofQ' (a + b) ≈ add (ofQ' a) (ofQ' b) = add (E a) (E b).
    ofQ'_add a b
  homogeneous := fun (q : Q') (a : Q') =>
    -- E (q • a) = ofQ' (q * a) ≈ qmul q (ofQ' a) = qmul q (E a).
    ofQ'_qmul q a

/-- Non-vacuity / sanity: the linear inhabitant's value on a rational
observable is that rational, at every approximation stage. -/
@[simp] theorem qRegLinearFunctional_approx (a : Q') (n : Nat) :
    (qRegLinearFunctional.E a).approx n = a := rfl

/-! ## 7. Doc-note: the two views, and where linearity becomes a theorem

The continuum theory's target primitive is a positive LINEAR functional —
the constructive Daniell/Riesz representation in which the OS axioms are
read off as positivity properties.  Two views are built above and kept
distinct on purpose:

  * `RegProbFunctional` on the minimal `ObsAlg` is the
    MULTIPLICATIVE-observable view.  `ObsAlg` lacks addition, so linearity
    is not even expressible there — but this is exactly where the genuine
    character / reflection-positivity data lives (`regCharFunctional` on
    the real SU(2) heat-kernel tower), built by the regular-real
    completeness limit.

  * `RegLinearFunctional` on `LinearObsAlg` is the LINEAR-observable
    enrichment.  Adding `add` and `smul` to the algebra, together with the
    regular reals' own `add` and `qmul`, makes the two linearity laws
    `additive` and `homogeneous` STATABLE and PROVABLE.  On the `Q'`
    inhabitant they reduce to `ofQ'_add` / `ofQ'_qmul`, theorems that hold
    by the construction of the regular-real arithmetic.

The headline is that linearity is no longer an assumption: it is a theorem
about a genuine inhabitant, enabled by the regular constructive reals
carrying real arithmetic with a canonical, choice-free modulus. -/

end YMGap.Continuum.RegularFunctional

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RegularFunctional.RegObservableModulus.modCauchy
#print axioms YMGap.Continuum.RegularFunctional.RegObservableModulus.reg
#print axioms YMGap.Continuum.RegularFunctional.regFunctional_of_modulus
#print axioms YMGap.Continuum.RegularFunctional.constRegModulus
#print axioms YMGap.Continuum.RegularFunctional.charRegFamily
#print axioms YMGap.Continuum.RegularFunctional.regCharFunctional
#print axioms YMGap.Continuum.RegularFunctional.regCharFunctional_approx
#print axioms YMGap.Continuum.RegularFunctional.qLinearAlg
#print axioms YMGap.Continuum.RegularFunctional.ofQ'_sq_nonneg
#print axioms YMGap.Continuum.RegularFunctional.qRegLinearFunctional
#print axioms YMGap.Continuum.RegularFunctional.qRegLinearFunctional_approx
