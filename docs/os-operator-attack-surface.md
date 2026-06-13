# OS reconstruction operator layer — attack surface

This note maps the Osterwalder–Schrader reconstruction operator layer:
exactly what became **genuine constructive content** at finite volume versus
what stays **irreducibly paper-level**, and where the boundary lies
(Pour-El–Richards).

It accompanies the new Lean modules
`lean/YMGap/Continuum/FiniteVolumeGNS.lean` and
`lean/YMGap/Continuum/OSContent.lean`. The pre-existing
`Continuum/OSReconstruction.lean` (the `True`-stub interface) is left
untouched; this note records how its Props would adopt the new content.

## Starting point

`Continuum/OSReconstruction.lean` exposes the reconstruction quintuple
`(H_∞, Ω_0, U(t), H_op)` and four laws as `True`-valued *interface* Props:

| Prop | meaning | pre-existing form |
|---|---|---|
| `VacuumNormalized Ω` | `⟨Ω, Ω⟩ = 1` | `True` |
| `HamiltonianNonneg H` | `σ(H) ⊆ [0, ∞)` | `True` |
| `SemigroupGenerated H U` | `U(t) = e^{−tH}` (Stone) | `True` |
| `HasSpectralGap rec` | `inf σ_+(H) ≥ m₀` | `True` |

The continuum statements need the spectral theorem for unbounded
self-adjoint operators, a constructive Stone theorem, and the thermodynamic
limit `Λ → ∞` — a constructive-analysis build-out the Q′/CReal stack does not
have.

## What became genuine (finite volume)

At fixed lattice volume the transfer matrix `T = e^{−aH}` is a finite
positive matrix and the GNS construction is elementary. The new content:

### The load-bearing lemma: `gns_inner_nonneg`

The GNS inner product is `⟨a, b⟩ := E_Λ(star a · b)`, where `E_Λ` is the
**already-constructed** interacting finite-volume expectation of
`Continuum/FiniteVolume.lean` (`ReferenceWeight.E_Λ`). Its Gram positivity

    ⟨a, a⟩ = E_Λ(star a · a) ≥ 0

**is reflection positivity** — exactly `ReferenceWeight.E_Λ_positive`, already
proved there — re-packaged as the GNS inner-product nonnegativity. The
quotient-by-nullspace and completion are trivial in finite dimension
(located, finite-dim ⇒ closed ⇒ completion = itself), so the pre-Hilbert
datum **is** the finite-volume Hilbert space.

Lean: `FiniteVolumeGNS A` (structure), `gnsOfReferenceWeight` (builds it from
`E_Λ`), `gns_inner_nonneg` (the named lemma). The `CReal` view is `cInner`
with `cInner_nonneg : czero ≤ cInner a a`.

### The three upgradeable Props

| `OSReconstruction` Prop | genuine finite-volume content | source |
|---|---|---|
| `VacuumNormalized Ω` | `⟨Ω, Ω⟩ ≃ 1`, with `Ω = [1]` | `FiniteVolumeGNS.cyclic_norm` ← `E_Λ_normalized` |
| `HamiltonianNonneg H` | `λ_i = e^{−E_i} ≥ 0` (so `σ(T) ⊆ [0, ∞)`) | `SpectralModel.lam_nonneg` |
| `HasSpectralGap rec` | gap ⇒ `G(n) ≤ G(0)·μ^n` (geometric clustering) | `SpectralGap.decay_of_spectralGap_corr0` |

These are realized in `OSContent.lean` as:

- `FiniteVolumeReconstruction A` — bundles the GNS space + finite spectral
  model + gap bound, every field content-bearing.
- `vacuumNormalized_genuine`, `hamiltonianNonneg_genuine`,
  `hasSpectralGap_genuine`, `gram_nonneg_genuine` — the four upgraded laws,
  proved on the datum.
- `trivReconstruction` — a concrete inhabitant (free product state, `Z = 1`)
  exhibiting all four end-to-end on a non-stub object.

### Critical modelling choice (avoiding a discontinuity trap)

The spectral gap is carried as a `SpectralGapBound` predicate on the
**positive-weight `SpectralModel`** (the repo's existing
`Källén–Lehmann` weights `w_i ≥ 0`, `λ_i ≥ 0`), **not** as a sorted-
eigenvalue difference `eigenvalue₂ − eigenvalue₁`. The latter is
discontinuous at eigenvalue collisions (the eigenprojections jump), so it is
not a constructively usable gap. The positive-sum model is.

## How the existing `OSReconstruction` Props would adopt this

`OSReconstruction.lean` stays untouched (the MassGap chain depends on its
signatures). The adoption recipe, when that file is eventually refactored:

1. Replace `def VacuumNormalized {H} (Ω) : Prop := True` with a field
   referencing a `FiniteVolumeGNS` whose `cyclic_norm` supplies `⟨Ω,Ω⟩ ≃ 1`
   — i.e. carry a `FiniteVolumeGNS` (or `FiniteVolumeReconstruction`) in the
   `OSReconstruction` structure and define `VacuumNormalized` as
   `gnsVacuumNormalizedContent gns`.
2. Replace `def HamiltonianNonneg {H} (op) : Prop := True` with
   `hamiltonianNonnegContent spec` (`∀ i, 0 ≤ spec.lam i`), `spec` the
   transfer-matrix `SpectralModel`.
3. Replace `def HasSpectralGap rec : Prop := True` with
   `hasSpectralGapContent spec μ` (`SpectralGapBound spec μ`), and expose
   `hasSpectralGap_genuine` as the decay consequence the mass-gap statement
   consumes.
4. Keep `SemigroupGenerated` and the continuum `HasSpectralGapAt` as the
   declared paper boundary (below).

Because the replacements are `Prop`s implied by the genuine content, the
downstream `cluster_implies_gap*` signatures keep type-checking; their bodies
gain real witnesses instead of `trivial`.

## What stays paper-level (the honest boundary)

The finite-volume content does **not** close the continuum OS reconstruction.
Four objects are irreducibly paper-level and are carried as **named
hypotheses** in `OSContent.ContinuumSpectralInterface` — never `sorry`:

1. **Thermodynamic limit `Λ → ∞`** — the inductive-limit completion of the
   finite GNS spaces with gap persistence. (The finite GNS spaces are genuine;
   their colimit + uniform-gap survival is the open analytic step.)
2. **Continuum self-adjointness** of `H` on a dense domain.
3. **Projection-valued spectral measure / functional calculus** for the
   unbounded `H`.
4. **Continuum Stone generator** `U(t) = e^{−tH}`
   (`OSReconstruction.SemigroupGenerated`).

### The Pour-El–Richards boundary

The line between genuine and paper is sharp and principled:

- **Individual eigenvalues** of the transfer matrix are computable — this is
  why `HamiltonianNonneg` and the finite gap are genuine.
- **The projection-valued spectral-measure / PVM sequence** of the unbounded
  continuum `H` is **not** computable in general (Pour-El–Richards): the
  spectral projections are discontinuous in the operator, so the
  measure-valued map is not a computable sequence. This is the irreducible
  obstruction to formalizing the continuum functional calculus, and the
  reason items 2–3 stay paper.

`OSContent.continuum_reconstruction_from_interface` proves the *reduction
shape*: given a genuine `FiniteVolumeReconstruction` and the four named
obligations, the continuum reconstruction follows. It makes the boundary a
theorem (finite-volume content reduces the continuum problem to exactly these
four inputs) **without faking any of them**.

## Files and theorems

- `lean/YMGap/Continuum/FiniteVolumeGNS.lean`
  - `FiniteVolumeGNS` (structure: `inner`, `inner_nonneg`, `inner_conj`,
    `cyclic`, `cyclic_norm`)
  - `gnsOfReferenceWeight`, `gns_inner_nonneg`
  - `FiniteVolumeGNS.cInner`, `cInner_nonneg`
  - `gnsVacuumNormalizedContent(_holds)`, `hamiltonianNonnegContent(_holds)`,
    `hasSpectralGapContent(_decay)`
  - `trivGNS`, `trivGNS_inner_nonneg`, `trivGNS_cyclic_norm` (concrete)
- `lean/YMGap/Continuum/OSContent.lean`
  - `FiniteVolumeReconstruction`
  - `vacuumNormalized_genuine`, `hamiltonianNonneg_genuine`,
    `hasSpectralGap_genuine`, `gram_nonneg_genuine`
  - `trivSpectralModel`, `trivReconstruction` (concrete inhabitant)
  - `ContinuumSpectralInterface`, `continuum_reconstruction_from_interface`

## Axiom status

Every new theorem passes the AGENTS.md Rule 1 gate: only `propext` and
`Quot.sound` appear (several depend on no axioms at all). No `Classical.*`,
no `sorryAx`, no `native_decide`. Zero `sorry`s added — all open content is
named structure fields / hypotheses.

## Honest bottom line

This upgrades the **finite-volume** OS-reconstruction pieces from `True`-stubs
to genuine constructive content (the GNS space, its reflection-positivity Gram
bound, the normalized vacuum, `H ≥ 0`, and gap ⇒ clustering), and leaves the
**continuum** spectral theorem, Stone generator, and thermodynamic limit as
the honest declared boundary at the Pour-El–Richards non-computability line.
It does **not** close the continuum OS reconstruction.
