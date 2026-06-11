# RG transport / Kolmogorov consistency — concrete instances (E3)

This note records a genuine step on Track B / E3 (RG transport): turning the
Kolmogorov-consistency obligation from an *abstract input hypothesis* into a
*concrete, proved* statement on towers carrying real structure. All results
are fully proved and axiom-clean (`propext` / `Quot.sound` only; no
`sorryAx`, no `Classical.*`, no `native_decide`). Module:
`YMGap/Continuum/RGTransport.lean`.

## Background — where consistency lives

`Continuum/ObservableMeasure.lean` builds the projective system
`M_k = ProbFunctional (Obs_k)`, coarsened by restriction along the block-spin
embedding `incl_k : ObsHom (Obs_k) (Obs_{k+1})`. A family
`pick : ∀ k, ProbFunctional (Obs_k)` is **Kolmogorov-consistent** iff

    is_consistent (funcProjSystem S) pick  :=  ∀ k, (pick (k+1)).restrict (incl k) = pick k,

and a consistent family assembles into the inverse-limit continuum measure
`continuumMeasure S pick consistent`, with the proved Daniell–Kolmogorov law
`pushforward_limit_eq : π_k(μ_∞) = pick k`. Previously consistency was
witnessed only by `trivConsistent` — the one-point algebra `PUnit` with the
constant functional `E ≡ 1`, a `True`/`Unit`-grade placeholder.

## What was proved

### 1. The transport obligation, isolated (`restrict_eq_iff_transport`, `consistent_iff_transport`)

A `ProbFunctional` is determined by its `E` field (`ProbFunctional.ext`: the
`normalized`/`positive` fields are `Prop`, proof-irrelevant). Hence the
functional equation `(pick (k+1)).restrict (incl k) = pick k` is **equivalent**
to the value-level transport law

    ∀ o, (pick (k+1)).E ((incl k).map o) = (pick k).E o.

This is the `E ∘ map = E` form named in `expectation_stable`, now turned into a
working characterization (`consistent_iff_transport`) used to build and verify
the towers below. It precisely identifies what consistency *asks of the Wilson
functionals*: the fine-scale expectation of an embedded coarse observable
equals its coarse-scale expectation.

### 2. A non-trivial **stationary** tower on a genuine algebra

`stationaryTower A` is the constant tower (`Obs_k = A`, `incl_k = idHom A`,
`pick_k = μ`); `stationaryConsistent` proves it consistent for *any* `A`, `μ`.
The genuine content is the instance it is applied to:

- `charAlg` — the **SU(2)-character observable *-algebra**: carrier `Nat` (the
  spin index `s = 2j`), `one = χ_0` (trivial character), `star = id` (SU(2)
  characters are real / self-conjugate), `mul = ` Clebsch–Gordan lowest weight
  `χ_a·χ_b ↦ χ_{|a−b|}`. A real, non-`PUnit` algebra.

- `charFunc w` — the **diagonal heat-kernel functional** in `Q'`:
  `E χ_s = dimQ(s) · w^{C₄(s)}` with `dimQ(s) = s+1`, `C₄(s) = s(s+2) = 4·C₂(s)`,
  and `w = e^{−t/4} ∈ Q'` the per-Casimir-unit heat-kernel weight. Proved a
  genuine `ProbFunctional`: `normalized` (`E χ_0 = 1·w^0 = 1`) and `positive`
  (`star = id` ⇒ `a*·a = χ_0`, with `E ≥ 0` on the nonnegative cone via
  `Q'.mul_nonneg` and `qpow_nonneg`).

- `charFunc_nonconstant` — `charFunc` is **genuinely not** the `≡ 1`
  placeholder: at `w = 1/2`, `E χ_0 = 1` while `E χ_2 = 3·(1/2)^8 = 3/256 ≠ 1`
  (decidable, structural `Q'`).

`charTowerConsistent` gives consistency on this real data; `charContinuumMeasure`
inhabits `continuumMeasure` with it; `charContinuumMeasure_proj` exhibits the
pushforward law `π_k(μ_∞) = charFunc w`; and `charExpectation_stable`
instantiates the "computable modulus" — the heat-kernel character expectation is
stable one step finer and exactly equals the closed form `dimQ(s)·w^{C₄(s)}` at
its scale of definition.

### 3. A consistent tower with a **non-identity** embedding (`collapseConsistent`)

A stationary tower's transport equation is `rfl` (identity `incl`). To exhibit
consistency where `incl_k` genuinely *moves the argument*, `collapseTower` uses
`collapseHom : charAlg → charAlg`, the **vacuum projection** `χ_s ↦ χ_0` — a
genuine unital *-hom (`map_one`/`map_mul`/`map_star` all hold;
`collapseHom_ne_id` certifies it is *not* the identity, sending `χ_1 ↦ χ_0`).
Restriction along it reports the vacuum expectation, so the transport equation
`vacFunc.E (collapse o) = vacFunc.E o` is the genuine vacuum-vs-general
statement `vacFunc.E χ_0 = vacFunc.E o` — discharged by `collapseConsistent` /
`collapse_transport`, *not* by reflexivity of the argument. The residual
triviality here is in the *functional* (`vacFunc ≡ 1`, the collapse fixed
point), not in the algebra (`charAlg`) or the embedding (`collapseHom`).

## What this is / is not

The two towers genuinely inhabit `continuumMeasure` with non-vacuous data and
make `pushforward_limit_eq` say something concrete:

- The **stationary character tower** carries a real, non-constant, `Q'`-valued
  heat-kernel functional on a genuine character algebra, with identity
  inclusions (the honest model of an RG direction along which the per-scale
  data does not move).
- The **collapse tower** carries a genuine non-identity block-spin *-hom, with
  the consistency equation being real (vacuum-vs-general), at the cost of a
  constant functional.

Neither is the *full* SU(2) block-spin RG tower. The honest gap, in one line:
**we do not yet have a single tower that simultaneously has (a) a non-constant
genuine functional AND (b) a genuine non-identity coarse→fine embedding that the
functional transports across with strict `Q'` equality.** Section 2 has (a)
with identity `incl`; section 3 has (b) with a constant functional. Bridging
them is exactly the genuine block-spin-RG content below.

## OPEN — what genuinely remains

- **The genuine SU(2) block-spin RG map.** `incl_k` as the real coarse→fine
  Wilson embedding: block link variables = ordered products of fine link
  variables, inducing a *-hom on character/Wilson-loop observables that is
  neither the identity nor the vacuum projection. The induced functional
  transport `(pick (k+1)).E ∘ incl_k = pick k` would then be a non-trivial
  character-fusion identity, not a constant collapse.

- **Strict vs. `.eqv` equality.** `is_consistent` demands strict `Q'` `=`. The
  heat-kernel composition / semigroup law `w^{C(t)}·w^{C(s)} = w^{C(t+s)}` and
  the unital collapses (`1·v ≃ v`) hold only up to `Q'.eqv` (different
  unnormalized denominators), so a *moving* heat-kernel tower is consistent only
  up to `.eqv`. A strict-`=` moving tower needs either a normalized-`Q'`
  representation or `is_consistent` relaxed to `.eqv` (an honest interface
  question for `ObservableMeasure`).

- **Interacting (plaquette-coupled) functionals.** The functionals here are the
  free / diagonal heat-kernel data. The reflection-positive interacting
  functional (OS2) and its RG transport are open — see the E2 chain in
  `docs/e2-e3-notes.md` (plaquette coupling, interacting-measure positivity, KP
  infinite-volume convergence with modulus).

- **Quantitative transport (the σ̂-budget).** `RG/BlockSpin.lean`'s
  `step_obligation_*` are still the identity / zero-budget witnesses
  (`eps = delta = eta = 0`, certificates reused). The genuine per-step
  contraction `σ̂_{k+1} ≥ σ̂_k − η_k` with `η_k > 0`, and the global closure
  `Σ_k η_k < σ̂_0` / `inf_k σ̂_k > 0`, are not established — they are the named
  conjectures of `docs/track-b-continuum-plan.md` and require a constructive
  limit argument on `Q'` (see `Constructive/Rationals.lean` boundary note).

### Honest summary

This is a real, bounded step: the Kolmogorov-consistency obligation is now
concrete (`consistent_iff_transport`) and proved on two towers with genuine
structure (a non-`PUnit` character algebra with a non-constant heat-kernel
functional; a non-identity block-spin *-hom), replacing the `PUnit`/`≡ 1`
placeholder. It is *not* a closure of E3: the genuine SU(2) block-spin embedding,
strict-equality moving transport, interacting-measure positivity, and the
quantitative σ̂-budget all remain open exactly as listed.
