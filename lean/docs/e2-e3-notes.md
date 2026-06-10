# E2 / E3 progress notes — the decoupled multi-edge product functional

This note records one genuine, fully-proved, axiom-clean rung of Track B
continuum existence (E2, the thermodynamic / finite-volume limit) and an
honest accounting of what remains open for E2 and E3.

## What was proved (module `YMGap/Continuum/E2ProductFunctional.lean`)

The single-edge heat-kernel Wilson functional already in the repo
(`Continuum/WilsonFunctional.lean`, `Continuum/ObservableMeasure.lean`) is
the `n = 1` piece of finite volume. The first honest rung toward finite
volume — *before* any plaquette coupling — is the **free (product) measure**
on `n` decoupled edges, whose moment functional factorizes:

    E_⊗(⊗_{i<n} a_i) = Π_{i<n} E_i(a_i).

This module constructs that object inside the existing `ObsAlg` /
`ProbFunctional` framework and proves it is again a genuine probability
functional.

Proved statements:

- `prodE`, `prodE_eq_one_of`, `prodE_nonneg`, `prodE_congr` — the `Q'`-level
  finite product fold and its two driving facts: an all-units product is `1`
  **strictly** (`(1 : Q') * 1 = 1` is definitional), and a product of
  nonnegatives is nonnegative (`Q'.mul_nonneg`).

- `prodAlg A n` — the product observable *-algebra on the first `n` edges
  (carrier `∀ i, (A i).carrier`, componentwise unit / mul / star).

- `prodFunctional A μ n : ProbFunctional (prodAlg A n)` — **the decoupled
  product functional** `E_⊗(a) = Π_{i<n} (μ i).E (a i)`, proved to be a
  genuine `ProbFunctional`:
    - `normalized` : `E_⊗ 1 = Π_{i<n} 1 = 1`, a **strict** `Q'` equality
      (this is why the unit fold was built strictly).
    - `positive` : `0 ≤ E_⊗(a*·a) = Π_{i<n} (μ i).E((a i)*·a i)`, a finite
      product of per-edge nonnegatives.
  So the free finite-volume measure is a genuine positive normalized
  functional, inheriting positivity/normalization edge-by-edge.

- `insertAt` / `prodFunctional_marginal` — **the decoupling /
  marginalization law**: for `j < n`,
      E_⊗(insertAt j a)  ≃  (μ j).E a    (`Q'.eqv`).
  Inserting a single-edge observable at edge `j` (unit elsewhere) and taking
  the joint expectation recovers edge `j`'s own expectation. This is the
  genuine statement that *the single-edge marginal of the free product
  measure is the single-edge measure* — i.e. statistical independence of the
  decoupled edges. The result is up to `Q'.eqv` (not strict `=`) only because
  `Q'` multiplication is unital merely up to `.eqv`; the unit fold collapses
  `1·v ≃ v`.

- `trivProdFunctional` / `trivProdFunctional_normalized` — a concrete
  `n`-edge inhabitant (the `n`-fold trivial product), exhibiting the
  construction is genuinely inhabitable, not a `True`/`Unit` placeholder.

### Axiom gate

All theorems are `[propext]` or `[propext, Quot.sound]` (the latter only
where `Nat`/`omega` enter via the `j < n` recursion). No `Classical.*`, no
`sorryAx`, no `native_decide`. Verified by the `#print axioms` block at the
end of the module. Builds green via `lake build
YMGap.Continuum.E2ProductFunctional`.

## How it fits E2 / E3

E2 (thermodynamic limit) asks for a coherent family of finite-volume
measures whose volume → ∞ limit exists. The chain is:

  single edge (`WilsonFunctional`)  →  **free n-edge product (this module)**
  →  interacting n-edge (plaquette coupling)  →  infinite volume (KP / cluster)
  →  RG-consistent tower (E3).

This module supplies the **free finite-volume functional** rigorously: it is
the correct `n`-edge base object, it is a genuine `ProbFunctional`, and its
single-edge marginals are exactly the single-edge measures (independence).
It is the honest "rung 1" of E2: the structure on which the plaquette
interaction is a *perturbation*, and which the Kotecký–Preiss / cluster
machinery (`Sheaf/Summability.lean`, `Sheaf/PolymerDomination.lean`) bounds
relative to.

It does **not** by itself give the thermodynamic limit: there is no coupling
yet, and no limit in `n`.

## OPEN — what genuinely remains

E2 (finite-volume → infinite-volume):

- **Plaquette coupling.** The interacting finite-volume functional is
  `E_β(o) = E_⊗(o · e^{−S_plaq}) / E_⊗(e^{−S_plaq})` (the reweighted free
  product). `e^{−S_plaq}` is a non-separable observable, so it lives OUTSIDE
  `prodAlg`'s separable carrier; the algebra must be enlarged to the full
  (non-separable) product algebra, and `e^{−S_plaq}` and the partition
  function `Z = E_⊗(e^{−S_plaq})` must be constructed as `CReal`/`Q'` data
  with `Z > 0`. None of this is done here.

- **Positivity of the interacting functional.** Reflection positivity (OS2)
  for the coupled measure — the genuine GNS positivity — is not implied by
  the free product positivity; it is the Wilson-action reflection-positivity
  theorem (`Continuum/WilsonFunctional.lean`'s `coneExp_nonneg` is only the
  nonnegative-cone partial result; full Gram-PSD is still open there).

- **KP / cluster infinite-volume convergence WITH a modulus.** The cluster
  expansion machinery exists (`Sheaf/Summability.lean`,
  `Sheaf/PolymerDomination.lean`, `Sheaf/SU2KP.lean`), and the SU(3)
  character-tail bound `Z_t < 1/16` is closed (`SU3CharFactor.lean`), giving
  the KP smallness input. But the actual statement "the reweighted product
  functionals `E_{β,n}` converge as `n → ∞` with an explicit Cauchy modulus"
  is not assembled. This is the heart of E2 and is genuinely open.

E3 (RG transport / Kolmogorov consistency):

- **Concrete Kolmogorov consistency for the Wilson tower.** `ObservableMeasure`
  proves `restrict` preserves probability and `expectation_stable` for *any*
  consistent family, but consistency `restrict (pick (k+1)) (incl k) = pick k`
  for the *actual* block-spin / RG tower is an input hypothesis, not proved.
  The free product here is one-scale only; it does not yet carry the
  coarse→fine block-spin embedding.

- **Quantitative RG transport (the named conjectures).** The `σ̂` pilot /
  block-spin contraction (`RG/SigmaHatPilot*.lean`, `RG/BlockSpin.lean`) and
  its limit (`Continuum/SigmaHatLimit.lean`) remain partly conjectural per
  `docs/track-b-continuum-plan.md`; the RG-transport claim that the coupled
  functionals form a consistent projective system is NOT established.

### Honest summary

This is a real, modest, fully-proved E2 base rung (the free finite-volume
product functional + its marginals/independence), not a closure of E2 or E3.
The hard analytic content — plaquette coupling, interacting-measure
positivity, KP infinite-volume convergence with modulus, and RG consistency —
remains open exactly as listed above.
