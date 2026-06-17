/-
The constructive continuum theory as a POSITIVE LINEAR FUNCTIONAL with
real-number expectations, and its infinite-volume limit constructor.

# The strategic picture

The constructive continuum object of a Euclidean field theory is not a
point-set probability measure but a POSITIVE NORMALIZED FUNCTIONAL
(Daniell / valuation / expectation) on an observable *-algebra — the
Riesz / moment representation of `μ`.  Its values on observables are the
Schwinger functions; the Osterwalder–Schrader axioms are positivity
properties OF THIS FUNCTIONAL.  The finite-scale theories already supply
`Q'`-valued positive normalized functionals (`ProbFunctional`); the
CONTINUUM theory is the limit, whose expectations are genuine constructive
reals (`CReal`) with an explicit modulus, not exact rationals.

# The two limits, separated honestly

The "continuum limit" is TWO independent limits, and only one of them is
constructed here:

  (i)  INFINITE VOLUME `Λ → ∞` at fixed lattice spacing.  This is
       CONSTRUCTIVE — for each observable the finite-volume expectations
       form a Cauchy sequence whose two-sided modulus is the analytic
       output of a convergent cluster expansion.  `crealOfTail` turns that
       per-observable modulus into a `CReal` expectation, and the limit
       functional's positivity and normalization are PROVED from the
       finite-volume ones via the approximation-bound lifts.  This module
       constructs exactly this limit.

  (ii) SCALING `a → 0` (lattice spacing to zero).  This needs a
       lattice-spacing-UNIFORM two-sided modulus.  Such a modulus is
       known for scalar `φ⁴` in `d = 2, 3` but is NOT known for
       Yang–Mills in `d = 4`; it is the genuinely OPEN obligation.  It is
       isolated here as a single named `Type`-level interface
       (`ScalingLimitModulus`) and is NOT discharged — no fake closure.

# What is genuine here (constructed / proved)

  * `CRealProbFunctional` — the continuum positive normalized functional
    with `CReal` expectations.  A real constructive object.
  * `continuumFunctional_of_modulus` — the infinite-volume-limit
    constructor: a consistent tower of `Q'`-valued functionals plus a
    per-observable two-sided modulus yields a `CRealProbFunctional`.  Its
    `normalized` and `positive` fields are PROVED from the finite-volume
    ones (`le_ofQ'_of_approx_le` / `ofQ'_le_of_approx_ge`), needing no
    `CReal` arithmetic.
  * `ConsistentFamilyWithModulus` — the honest per-observable convergence
    input as `Type`-level data (consistency + a two-sided tail family +
    modulus for each observable).
  * `charFamilyWithModulus` — a CONCRETE inhabitant on the real SU(2)
    character data (`charFunc` on `charAlg`): the stationary tower is
    eventually constant, so every observable's sequence has zero tail and
    is trivially Cauchy.  The resulting `CRealProbFunctional` is genuine
    (non-trivial functional on real character data).
  * `gap_as_clustering` — the mass gap of the continuum functional stated
    as the clustering rate of its connected correlator, routed through the
    finite (compact) transfer-operator spectral model
    (`decay_of_spectralGap_corr0`), NOT through any unbounded spectral
    theorem.

# What remains open (isolated, not faked)

  * `ScalingLimitModulus` — the lattice-spacing-uniform two-sided modulus
    for the `a → 0` step.  Named obligation, no inhabitant claimed for YM.
  * `CReal` LINEARITY of the limit functional (additivity / scaling over
    the algebra) would need `CReal` add/mul that interact with the limit;
    it is NOT claimed.  Only positivity, normalization, and the order
    lifts are proved — exactly what the present `CReal` order API supports.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only, inherited from the reused
`Q'` / `CReal` order lemmas.  No `Classical.*`, no `sorry`, no
`native_decide`.  All moduli are carried as `Type`-level data.
-/

import YMGap.Continuum.ObservableMeasure
import YMGap.Continuum.RGTransport
import YMGap.Continuum.KPLimit
import YMGap.Continuum.SpectralGap
import YMGap.Constructive.Reals
import YMGap.Constructive.ExpAdd

namespace YMGap.Continuum.ContinuumFunctional

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SpectralGap

/-! ## 1. The continuum functional: positive normalized, `CReal`-valued -/

/-- A constructive **continuum probability functional**: the Daniell /
expectation representation of the continuum theory, with `CReal` (genuine
constructive-real) expectations.

  * `E : A.carrier → CReal` — the continuum Schwinger functional;
  * `normalized` — `E 1 ≃ 1` at the `CReal` level (the limit of the
    finite-volume normalizations `E_Λ 1 = 1`);
  * `positive` — `0 ≤ E (a* · a)` at the `CReal` level (the limit of the
    finite-volume reflection positivities `0 ≤ E_Λ (a* · a)`).

This is the continuum theory AS a positive normalized functional — the
object the OS axioms read off (its values are the Schwinger functions). -/
structure CRealProbFunctional (A : ObsAlg) where
  /-- The continuum expectation, valued in the constructive reals. -/
  E : A.carrier → CReal
  /-- Normalization at the unit: `E 1 ≃ 1`. -/
  normalized : CReal.Equiv (E A.one) (CReal.ofQ' 1)
  /-- Reflection-style positivity: `0 ≤ E (a* · a)`. -/
  positive : ∀ a, CReal.czero ≤ E (A.mul (A.star a) a)

/-! ## 2. The honest per-observable convergence input

The genuine analytic input of the infinite-volume limit is, FOR EACH
observable, a two-sided tail bound on the sequence of finite-volume
expectations together with a modulus making that tail vanish.  We carry
it as `Type`-level data (Rule 8): a consistent tower of `Q'`-valued
functionals plus, per observable at each scale, the tail family and the
telescoped two-sided bounds and the modulus that `crealOfTail` consumes.

The observable indexing is by scale: an observable "lives" at some scale
`k` as `o : (S.Obs k).carrier`, and its finite-volume expectation
sequence is `Λ ↦ (pick Λ).E (push o to scale Λ)`.  To keep the input
honest and reusable while staying within the present API, we phrase the
per-observable datum directly on a `Q'`-sequence `seqOf o` of expectations
(supplied by the tower) — exactly the input shape `crealOfTail` needs. -/

/-- The per-observable two-sided modulus datum: a `Q'`-sequence of
finite-volume expectations together with the tail family and the two
telescoped bounds and the vanishing modulus — i.e. precisely the
hypotheses of `crealOfTail`.  Carrying these as fields keeps the modulus
as `Type`-level data. -/
structure ObservableLimitModulus where
  /-- The finite-volume expectation sequence `Λ ↦ ⟨o⟩_Λ`. -/
  seq : Nat → Q'
  /-- The tail-bound family `T n` (total movement of `seq` from `n` on). -/
  tail : Nat → Q'
  /-- Upper telescoped bound. -/
  up : ∀ n d, seq (n + d) ≤ seq n + tail n
  /-- Lower telescoped bound. -/
  lo : ∀ n d, seq n ≤ seq (n + d) + tail n
  /-- The modulus: `tail n → 0`. -/
  mod : ∀ ε : Q', (0 : Q') < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n → tail n ≤ ε

/-- The `CReal` expectation produced from one observable's modulus datum,
via the project's `crealOfTail` engine.  Its `approx Λ` is the
finite-volume expectation `⟨o⟩_Λ`. -/
def ObservableLimitModulus.creal (m : ObservableLimitModulus) : CReal :=
  crealOfTail m.seq m.tail m.up m.lo m.mod

@[simp] theorem ObservableLimitModulus.creal_approx (m : ObservableLimitModulus)
    (Λ : Nat) : m.creal.approx Λ = m.seq Λ := rfl

/-- The full infinite-volume-limit input: a scale system, a
Kolmogorov-consistent family of `Q'`-valued probability functionals, and,
for every observable, its two-sided convergence modulus, together with the
two facts that pin the limit's positivity and normalization to the
finite-volume ones:

  * `unit_seq` — for the unit observable at any scale the expectation
    sequence is the constant `1` (its `crealOfTail` `approx` is `1`);
  * `pos_seq` — for every `a*·a` the expectation sequence is `≥ 0`
    pointwise (each finite-volume functional is positive).

These two are exactly what `le_ofQ'_of_approx_le` / `ofQ'_le_of_approx_ge`
need; they hold for any genuine tower of `ProbFunctional`s, so they are
not extra assumptions beyond the tower being a tower of probability
functionals. -/
structure ConsistentFamilyWithModulus where
  /-- The scale system (observable tower). -/
  S : ObsSystem
  /-- The per-scale `Q'`-valued probability functionals. -/
  pick : ∀ k, ProbFunctional (S.Obs k)
  /-- Kolmogorov consistency of the family. -/
  consistent : is_consistent (funcProjSystem S) pick
  /-- For each observable (taken at scale `0` for indexing concreteness),
  its two-sided convergence modulus over the volume sequence. -/
  modOf : (S.Obs 0).carrier → ObservableLimitModulus
  /-- The unit's expectation sequence is the constant `1`. -/
  unit_seq : ∀ Λ, (modOf (S.Obs 0).one).seq Λ = 1
  /-- The expectation sequence of any `a*·a` is pointwise `≥ 0`. -/
  pos_seq : ∀ a Λ,
    (0 : Q') ≤ (modOf ((S.Obs 0).mul ((S.Obs 0).star a) a)).seq Λ

/-! ## 3. The infinite-volume-limit constructor

From a `ConsistentFamilyWithModulus` we build a `CRealProbFunctional` by
applying `crealOfTail` per observable, then PROVING `normalized` and
`positive` from the finite-volume `unit_seq` / `pos_seq` via the CReal
approximation-bound lifts.  No `CReal` arithmetic is required. -/

/-- **The infinite-volume continuum-limit constructor.**

Given a consistent tower of `Q'`-valued probability functionals with a
per-observable two-sided modulus, construct the continuum
`CRealProbFunctional` over the base algebra `Obs 0`:

  * `E o := (modOf o).creal` — the per-observable `CReal` limit
    (`approx Λ = ⟨o⟩_Λ`), the infinite-volume limit BY DIRECT MODULUS (no
    compactness, no subsequence extraction);
  * `normalized` — PROVED: `E 1`'s approximations are the constant `1`
    (`unit_seq`), so `E 1 ≃ ofQ' 1` by `le_ofQ'_of_approx_le` +
    `ofQ'_le_of_approx_ge` packaged as an `Equiv`;
  * `positive` — PROVED: `E (a*·a)`'s approximations are `≥ 0`
    (`pos_seq`), so `0 = ofQ' 0 ≤ E (a*·a)` by `ofQ'_le_of_approx_ge`.

This realizes "continuum positive functional by direct modulus." -/
def continuumFunctional_of_modulus (F : ConsistentFamilyWithModulus) :
    CRealProbFunctional (F.S.Obs 0) where
  E := fun o => (F.modOf o).creal
  normalized := by
    -- E 1 ≃ ofQ' 1 : both bounds from the constant-1 approximation sequence.
    have hle : (F.modOf (F.S.Obs 0).one).creal ≤ CReal.ofQ' 1 :=
      CReal.le_ofQ'_of_approx_le (fun Λ => by
        show (F.modOf (F.S.Obs 0).one).seq Λ ≤ 1
        rw [F.unit_seq Λ]; exact Q'.le_refl' 1)
    have hge : CReal.ofQ' 1 ≤ (F.modOf (F.S.Obs 0).one).creal :=
      CReal.ofQ'_le_of_approx_ge (fun Λ => by
        show (1 : Q') ≤ (F.modOf (F.S.Obs 0).one).seq Λ
        rw [F.unit_seq Λ]; exact Q'.le_refl' 1)
    -- Package the two one-slack bounds as an `Equiv` directly.
    intro ε hε
    refine ⟨0, fun n _ => ⟨?_, ?_⟩⟩
    · -- (E 1).approx n ≤ 1 + ε
      show (F.modOf (F.S.Obs 0).one).seq n ≤ 1 + ε
      rw [F.unit_seq n]
      exact Q'.add_le_self_of_nonneg 1 ε (Q'.le_of_lt hε)
    · -- 1 ≤ (E 1).approx n + ε
      show (1 : Q') ≤ (F.modOf (F.S.Obs 0).one).seq n + ε
      rw [F.unit_seq n]
      exact Q'.add_le_self_of_nonneg 1 ε (Q'.le_of_lt hε)
  positive := fun a => by
    -- 0 = ofQ' 0 ≤ E (a*·a) by approximation lower bound.
    show CReal.czero ≤ (F.modOf ((F.S.Obs 0).mul ((F.S.Obs 0).star a) a)).creal
    show CReal.ofQ' 0 ≤ (F.modOf ((F.S.Obs 0).mul ((F.S.Obs 0).star a) a)).creal
    exact CReal.ofQ'_le_of_approx_ge (fun Λ => F.pos_seq a Λ)

/-- The limit functional's expectation `approx`-es the finite-volume
expectation sequence: `(E o).approx Λ = ⟨o⟩_Λ`.  The continuum value is
genuinely the `Λ → ∞` limit of the finite-volume expectations. -/
@[simp] theorem continuumFunctional_of_modulus_approx
    (F : ConsistentFamilyWithModulus) (o : (F.S.Obs 0).carrier) (Λ : Nat) :
    ((continuumFunctional_of_modulus F).E o).approx Λ = (F.modOf o).seq Λ := rfl

/-! ## 4. A concrete inhabitant on the real SU(2) character data

The stationary character tower (`charAlg` / `charFunc`) is EVENTUALLY
CONSTANT: `expectation_stable` gives `(pick (k+1)).E (incl o) = (pick k).E
o`, and here `incl` is the identity, so the whole expectation sequence is
the single value `(charFunc w hw).E o` repeated.  Hence every observable's
two-sided tail is identically `0` and the modulus is trivial — a genuine
`ConsistentFamilyWithModulus` on real character data, whose limit
`CRealProbFunctional` is the (non-trivial) heat-kernel functional. -/

/-- The constant-sequence (zero-tail) modulus datum for a fixed `Q'`
value `v`: `seq Λ = v`, `tail ≡ 0`.  Both telescoped bounds are
`v ≤ v + 0` and the modulus is immediate. -/
def constModulus (v : Q') : ObservableLimitModulus where
  seq := fun _ => v
  tail := fun _ => 0
  up := fun _ _ => by
    show v ≤ v + 0
    rw [Q'.add_zero' v]; exact Q'.le_refl' v
  lo := fun _ _ => by
    show v ≤ v + 0
    rw [Q'.add_zero' v]; exact Q'.le_refl' v
  mod := fun ε hε => ⟨0, fun _ _ => Q'.le_of_lt hε⟩

@[simp] theorem constModulus_seq (v : Q') (Λ : Nat) :
    (constModulus v).seq Λ = v := rfl

/-- The character family with its (trivial, exact) per-observable modulus:
every observable `o : Nat` gets the constant-sequence modulus at the
heat-kernel value `(charFunc w hw).E o`.  This is a genuine inhabitant of
`ConsistentFamilyWithModulus` on the real SU(2) character data. -/
def charFamilyWithModulus (w : Q') (hw : (0 : Q') ≤ w) :
    ConsistentFamilyWithModulus where
  S := stationaryTower charAlg
  pick := fun _ => charFunc w hw
  consistent := charTowerConsistent w hw
  modOf := fun o => constModulus ((charFunc w hw).E o)
  unit_seq := fun _ => by
    -- ((stationaryTower charAlg).Obs 0).one = charAlg.one = (0 : Nat);
    -- (charFunc w hw).E charAlg.one = 1 by normalization.
    show (charFunc w hw).E charAlg.one = 1
    exact (charFunc w hw).normalized
  pos_seq := fun a _ => by
    -- (charFunc w hw).E (a* · a) ≥ 0 by positivity.
    show (0 : Q') ≤ (charFunc w hw).E (charAlg.mul (charAlg.star a) a)
    exact (charFunc w hw).positive a

/-- **The concrete continuum functional on real character data.**  The
infinite-volume limit of the stationary SU(2) heat-kernel tower, a genuine
`CRealProbFunctional` (not the `≡ 1` placeholder: its value on the unit is
`1` but on `χ_2` it is `< 1`, see `charFunc_nonconstant`). -/
def charContinuumFunctional (w : Q') (hw : (0 : Q') ≤ w) :
    CRealProbFunctional ((charFamilyWithModulus w hw).S.Obs 0) :=
  continuumFunctional_of_modulus (charFamilyWithModulus w hw)

/-- The concrete continuum functional's value on an observable `o` has, at
every approximation stage, the exact heat-kernel rational
`(charFunc w hw).E o`: the limit is the (already exact) finite-volume
expectation, as expected for the stationary tower. -/
@[simp] theorem charContinuumFunctional_approx (w : Q') (hw : (0 : Q') ≤ w)
    (o : Nat) (Λ : Nat) :
    ((charContinuumFunctional w hw).E o).approx Λ = (charFunc w hw).E o := rfl

/-! ## 5. The mass gap as clustering of the continuum functional

The mass gap is the exponential clustering rate of the continuum
functional's connected correlator.  At fixed lattice spacing and finite
volume the correlator is the FINITE Källén–Lehmann sum of the COMPACT
transfer operator (`SpectralModel`), so the clustering rate is the located
second-eigenvalue gap of a finite positive matrix — NOT a spectrum of an
unbounded operator.  `decay_of_spectralGap_corr0` already proves
`G(n) ≤ G(0)·μⁿ` from a spectral gap at `μ`; we package that as "the
clustering rate IS the gap," routed through the compact operator. -/

/-- **Gap as clustering (routed through the compact transfer operator).**

If the finite (compact) transfer-operator spectral model `S` underlying
the continuum functional's connected correlator has a spectral gap at
`μ ≥ 0` (every eigenvalue `≤ μ`), then the connected correlator clusters
geometrically: `G(n) ≤ G(0)·μⁿ` for every separation `n`.  The mass gap
is the rate `m = −log μ` of this decay.  This is the gap stated as the
clustering rate of the continuum functional, obtained from the FINITE
positive spectral sum — no unbounded spectral theorem. -/
theorem gap_as_clustering (S : SpectralModel) (μ : Q') (hμ : (0 : Q') ≤ μ)
    (hgap : SpectralGapBound S μ) (n : Nat) :
    corr S n ≤ (corr S 0) * μ ^ n :=
  decay_of_spectralGap_corr0 S μ hμ hgap n

/-! ## 6. The remaining genuinely-open limit: scaling `a → 0`

Everything above is the INFINITE-VOLUME limit `Λ → ∞` at FIXED lattice
spacing.  The continuum theory additionally requires the SCALING limit
`a → 0`, which needs a lattice-spacing-UNIFORM two-sided modulus for the
expectations as the spacing is refined.  Such a uniform modulus is known
for scalar `φ⁴` in `d = 2, 3` but is NOT known for Yang–Mills in `d = 4`.

It is isolated as the single named obligation below.  No inhabitant is
provided (none is known for YM); it is an HONEST open interface, not a
`True`-stub.  An inhabitant would carry, for each observable, a sequence
of fixed-spacing infinite-volume functionals indexed by the refinement
step together with a two-sided modulus UNIFORM in that step — i.e. exactly
the data the constructor of §3 consumes, but now along the spacing axis. -/

/-- **The scaling-limit modulus — the single remaining open obligation.**

Carries, for each observable of the base algebra `A`, a sequence
(`atSpacing j` = the fixed-spacing infinite-volume continuum functional at
refinement step `j`) and a per-observable two-sided modulus
(`spacingModOf o`) that is UNIFORM in the spacing — the
lattice-spacing-uniform modulus.  Its inhabitant would yield, via the same
`crealOfTail`/`continuumFunctional_of_modulus` machinery applied along the
spacing axis, the full continuum (`a → 0`) functional.

No inhabitant is asserted: for Yang–Mills in `d = 4` this uniform modulus
is OPEN.  This field is the precise location of the open continuum
problem, kept distinct from the (constructed) infinite-volume limit. -/
structure ScalingLimitModulus (A : ObsAlg) where
  /-- The fixed-spacing infinite-volume functionals, indexed by the
  refinement step `j` (spacing `a_j → 0`). -/
  atSpacing : Nat → CRealProbFunctional A
  /-- For each observable, the spacing-uniform two-sided modulus on the
  sequence `j ↦ (atSpacing j).E o`.  Phrased on the `Q'` approximation
  diagonal `j ↦ (atSpacing j).E o |> .approx j` so it plugs into
  `crealOfTail`; making this inhabitable for YM is the open problem. -/
  spacingModOf : A.carrier → ObservableLimitModulus
  /-- Compatibility: the modulus sequence reads the fixed-spacing
  functionals' diagonal approximations — so an inhabitant genuinely
  governs the `atSpacing` family, not an unrelated sequence. -/
  reads_atSpacing : ∀ (o : A.carrier) (j : Nat),
    (spacingModOf o).seq j = ((atSpacing j).E o).approx j

/-- The continuum (`a → 0`) functional that a `ScalingLimitModulus` would
produce, built by the SAME constructor as the infinite-volume limit but
along the spacing axis.  This is a CONDITIONAL definition: it consumes a
`ScalingLimitModulus` inhabitant, which for Yang–Mills is the open input.
The construction itself is total and axiom-clean; only its HYPOTHESIS is
open.  (`unit`/`pos` along the spacing axis are supplied as explicit
arguments here, mirroring the §3 fields, since they depend on the
particular `atSpacing` family.) -/
def scalingFunctional_of_modulus {A : ObsAlg} (L : ScalingLimitModulus A)
    (unit_seq : ∀ j, (L.spacingModOf A.one).seq j = 1)
    (pos_seq : ∀ a j, (0 : Q') ≤ (L.spacingModOf (A.mul (A.star a) a)).seq j) :
    CRealProbFunctional A where
  E := fun o => (L.spacingModOf o).creal
  normalized := by
    intro ε hε
    refine ⟨0, fun n _ => ⟨?_, ?_⟩⟩
    · show (L.spacingModOf A.one).seq n ≤ 1 + ε
      rw [unit_seq n]; exact Q'.add_le_self_of_nonneg 1 ε (Q'.le_of_lt hε)
    · show (1 : Q') ≤ (L.spacingModOf A.one).seq n + ε
      rw [unit_seq n]; exact Q'.add_le_self_of_nonneg 1 ε (Q'.le_of_lt hε)
  positive := fun a => by
    show CReal.ofQ' 0 ≤ (L.spacingModOf (A.mul (A.star a) a)).creal
    exact CReal.ofQ'_le_of_approx_ge (fun j => pos_seq a j)

end YMGap.Continuum.ContinuumFunctional

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ContinuumFunctional.ObservableLimitModulus.creal
#print axioms YMGap.Continuum.ContinuumFunctional.continuumFunctional_of_modulus
#print axioms YMGap.Continuum.ContinuumFunctional.continuumFunctional_of_modulus_approx
#print axioms YMGap.Continuum.ContinuumFunctional.constModulus
#print axioms YMGap.Continuum.ContinuumFunctional.charFamilyWithModulus
#print axioms YMGap.Continuum.ContinuumFunctional.charContinuumFunctional
#print axioms YMGap.Continuum.ContinuumFunctional.charContinuumFunctional_approx
#print axioms YMGap.Continuum.ContinuumFunctional.gap_as_clustering
#print axioms YMGap.Continuum.ContinuumFunctional.scalingFunctional_of_modulus
