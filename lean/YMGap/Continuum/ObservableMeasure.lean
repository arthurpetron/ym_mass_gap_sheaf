/-
Track B1 (functional / Schwinger representation): `M_k = Prob(G^{E_k})`
as a constructive **positive normalized functional** on an observable
*-algebra — the Riesz / moment representation of a probability measure,
`E o = ∫ o dμ`.  This instantiates the projective-limit `ContinuumMeasure`
of `ContinuumMeasure.lean` with a *concrete* carrier (no longer abstract),
proves the Daniell–Kolmogorov coarsening at the functional level
(restriction preserves probability), exhibits a concrete inhabitant
(non-vacuity), and gives the per-observable "computable modulus" (exact
stabilization at the scale of definition).

# Why the functional representation

`G = SU(2) ≅ S³` is a *continuous* compact group, so a point-set
probability measure on `G^{E_k}` needs constructive measure theory on a
continuous group — which this repo (no Mathlib `ℝ`/measure theory)
deliberately avoids.  A measure is instead represented by what the OS
axioms (Track B2) actually read off it: its action on gauge-invariant
observables.  By Riesz/Peter–Weyl this is *faithful* for continuous `G`
(a measure is its moment functional), and it sets up B2 directly — e.g.
OS2 reflection positivity is a positivity property of this very functional.

# What is genuine here (constructed / proved)

  * `ProbFunctional A` — positive (`0 ≤ E(a*·a)`) and normalized
    (`E 1 = 1`) functional `E : A → Q'`.  A real constructive object.
  * `ProbFunctional.restrict` — coarsening of a measure = pullback of the
    functional along a unital *-hom; **preserves positivity and
    normalization** (proved).  This is the functional-level Daniell–
    Kolmogorov coarsening.
  * `funcProjSystem` / `continuumMeasure` — the projective system
    `M_k = ProbFunctional (Obs_k)` and the resulting `ContinuumMeasure`,
    whose `limit` is the constructed inverse-limit thread and whose
    `pushforward_limit_eq : π_k(μ_∞) = μ_k` is proved.
  * `trivContinuumMeasure` — a concrete inhabitant (the trivial functional
    on the one-point algebra): the construction is genuinely inhabitable,
    not a `True`/`Unit` placeholder.
  * `expectation_stable` — the "computable modulus": the expectation of any
    fixed observable is *stable* across finer scales (`(pick (k+1)).E
    (incl_k o) = (pick k).E o`) and exactly computed at its scale of
    definition.  For this `Q'`-valued inverse limit the modulus is exact.

# What remains open (the analysis, honestly isolated)

  * The *actual* YM data: the observable algebra of Wilson loops on
    `SU(2)^{E_k}`, and the Wilson/heat-kernel functional, whose positivity
    is the genuine reflection positivity (= OS2, Track B2).  Here `ObsAlg`
    and the per-scale functionals are parametric.
  * That the YM family is Kolmogorov-consistent (`restrict (pick (k+1))
    (incl k) = pick k`, the RG-transport claim) — an input hypothesis.
  * The Daniell–Kolmogorov *extension* to a σ-additive set function (only
    needed if one wants the point-set measure as well as the functional);
    in the functional picture the limit is already the coherent functional.

# Axiom-gate (AGENTS.md Rule 1)

Structural definitions and `rfl`/`congrArg` proofs; the `0 ≤ 1`
normalization positivity is `decide`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Continuum.ContinuumMeasure

namespace YMGap.Continuum.ObservableMeasure

open YMGap.Continuum.ContinuumMeasure
open YMGap.Constructive

/-! ## Observable algebras and probability functionals -/

/-- A minimal observable *-algebra: carrier + unit + product + involution —
just enough to state positivity `0 ≤ E(a*·a)` and normalization `E 1 = 1`. -/
structure ObsAlg where
  carrier : Type
  one : carrier
  mul : carrier → carrier → carrier
  star : carrier → carrier

/-- A constructive **probability functional** (expectation `E o = ∫ o dμ`):
positive on `a*·a`, normalized at the unit.  The moment/Riesz
representation of `μ ∈ Prob(G^{E_k})`. -/
structure ProbFunctional (A : ObsAlg) where
  E : A.carrier → Q'
  normalized : E A.one = 1
  positive : ∀ a, (0 : Q') ≤ E (A.mul (A.star a) a)

/-- A unital *-homomorphism (the embedding of coarse observables into fine
ones — coarse observables are functions of the block-spin variables). -/
structure ObsHom (A B : ObsAlg) where
  map : A.carrier → B.carrier
  map_one : map A.one = B.one
  map_mul : ∀ a b, map (A.mul a b) = B.mul (map a) (map b)
  map_star : ∀ a, map (A.star a) = B.star (map a)

/-- The identity *-hom. -/
def ObsHom.idHom (A : ObsAlg) : ObsHom A A where
  map := fun a => a
  map_one := rfl
  map_mul := fun _ _ => rfl
  map_star := fun _ => rfl

/-- **Restriction preserves probability.**  Pulling a functional back along
a unital *-hom yields again a positive, normalized functional — the
coarsening of measures at the functional level. -/
def ProbFunctional.restrict {A B : ObsAlg} (μ : ProbFunctional B) (φ : ObsHom A B) :
    ProbFunctional A where
  E := fun a => μ.E (φ.map a)
  normalized := by
    show μ.E (φ.map A.one) = 1
    rw [φ.map_one]; exact μ.normalized
  positive := fun a => by
    show (0 : Q') ≤ μ.E (φ.map (A.mul (A.star a) a))
    rw [φ.map_mul, φ.map_star]
    exact μ.positive (φ.map a)

/-! ## The projective system of functionals and its continuum limit -/

/-- A scale system: a tower of observable algebras with coarse→fine
embeddings `Obs_k ↪ Obs_{k+1}`. -/
structure ObsSystem where
  Obs : Nat → ObsAlg
  incl : ∀ k, ObsHom (Obs k) (Obs (k + 1))

/-- The projective system of probability functionals `M_k = ProbFunctional
(Obs_k)`, coarsened by restriction along `incl_k`. -/
def funcProjSystem (S : ObsSystem) :
    ProjectiveSystem (fun k => ProbFunctional (S.Obs k)) where
  coarsen := fun k μ => μ.restrict (S.incl k)

/-- The continuum measure `μ_∞` over a scale system, from a
Kolmogorov-consistent family of per-scale functionals.  Its `limit` is the
constructed inverse-limit thread (a coherent functional on `⋃_k Obs_k`),
and `pushforward_limit_eq` gives `π_k(μ_∞) = pick k`. -/
def continuumMeasure (S : ObsSystem)
    (pick : ∀ k, ProbFunctional (S.Obs k))
    (consistent : is_consistent (funcProjSystem S) pick) :
    ContinuumMeasure (fun k => ProbFunctional (S.Obs k)) :=
  su2_continuum_measure _ (funcProjSystem S) pick consistent

/-- **The "computable modulus": per-observable stabilization.**  The
expectation of any fixed observable `o ∈ Obs_k` is stable one step finer
(`(pick (k+1)).E (incl_k o) = (pick k).E o`), hence exactly computed at its
scale of definition — no approximation, for this `Q'`-valued inverse limit. -/
theorem expectation_stable (S : ObsSystem)
    (pick : ∀ k, ProbFunctional (S.Obs k))
    (consistent : is_consistent (funcProjSystem S) pick) (k : Nat)
    (o : (S.Obs k).carrier) :
    (pick (k + 1)).E ((S.incl k).map o) = (pick k).E o :=
  congrArg (fun μ => μ.E o) (consistent k)

/-! ## A concrete inhabitant (non-vacuity)

The trivial one-point observable algebra with the constant functional
`E ≡ 1`: a genuine `ContinuumMeasure` term, witnessing that the
construction is inhabitable (not a `True`/`Unit` placeholder).  The actual
SU(2) Wilson system replaces `trivSystem`/`trivFunc` with the Wilson
algebra and functional (the open analytic input). -/

/-- The trivial one-point observable algebra. -/
def trivAlg : ObsAlg where
  carrier := PUnit
  one := PUnit.unit
  mul := fun _ _ => PUnit.unit
  star := fun _ => PUnit.unit

/-- The trivial (point-mass) functional `E ≡ 1`. -/
def trivFunc : ProbFunctional trivAlg where
  E := fun _ => 1
  normalized := rfl
  positive := fun _ => by decide

/-- The trivial scale system (all `Obs_k = trivAlg`, identity embeddings). -/
def trivSystem : ObsSystem where
  Obs := fun _ => trivAlg
  incl := fun _ => ObsHom.idHom trivAlg

/-- The trivial family is Kolmogorov-consistent. -/
theorem trivConsistent :
    is_consistent (funcProjSystem trivSystem) (fun _ => trivFunc) :=
  fun _ => rfl

/-- A concrete continuum measure: the framework is genuinely inhabitable. -/
def trivContinuumMeasure :
    ContinuumMeasure (fun k => ProbFunctional (trivSystem.Obs k)) :=
  continuumMeasure trivSystem (fun _ => trivFunc) trivConsistent

/-- The trivial `μ_∞`'s projection to every scale is the trivial functional
(`π_k(μ_∞) = μ_k`), exhibiting the proved pushforward law on a concrete
instance. -/
theorem trivContinuumMeasure_proj (k : Nat) :
    trivContinuumMeasure.pushforward_to_stage k trivContinuumMeasure.limit = trivFunc :=
  trivContinuumMeasure.pushforward_limit_eq k

end YMGap.Continuum.ObservableMeasure

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ObservableMeasure.ProbFunctional.restrict
#print axioms YMGap.Continuum.ObservableMeasure.expectation_stable
#print axioms YMGap.Continuum.ObservableMeasure.trivConsistent
#print axioms YMGap.Continuum.ObservableMeasure.trivContinuumMeasure
#print axioms YMGap.Continuum.ObservableMeasure.trivContinuumMeasure_proj
