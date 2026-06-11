# Plaquette coupling notes — the reweighting (interacting) state

This note records one genuine, fully-proved, axiom-clean step BEYOND the
decoupled product functional (`YMGap/Continuum/E2ProductFunctional.lean`):
the **reweighting** that turns the free finite-volume measure into the
plaquette-coupled (interacting) one, and why it stays a positive normalized
state.

Module: `YMGap/Continuum/PlaquetteReweight.lean`
(namespace `YMGap.Continuum.PlaquetteReweight`).

## The math

The interacting finite-volume functional is the reweighted free product

    E_β(o) = E_⊗(o · W) / Z ,   W = e^{−S_plaq},   Z = E_⊗(W) > 0.

`W` is the (positive) plaquette Boltzmann weight; `Z` is the partition
function. The decoupled `E_⊗` is done (`prodFunctional`). The new content is
the **reweighting law**: dividing a positive normalized functional by a
positive weight with positive normalization yields again a positive
normalized functional. This is exactly *why the interacting measure stays a
state*, and it is reusable.

## What was proved (all axiom-clean: `[propext]` / `[propext, Quot.sound]`)

### A constructive reciprocal on the positive cone of `Q'`

`Q'` carries no field structure (no division), but a strictly positive
`z = n/d` has an honest inverse `d/n` (swap numerator/denominator, with the
swapped denominator `z.num.toNat` clamped `≥ 1` for totality):

- `recip z` — total; `recip_num`, `recip_den`, `recip_den_of_pos`.
- `recip_pos`           : `0 < z → 0 < recip z`.
- `mul_recip_eqv_one`   : `0 < z → (z · recip z) ≃ 1`.
- `recip_mul_eqv_one`   : `0 < z → (recip z · z) ≃ 1`.
- `recip_one`           : `recip 1 = 1` (strict).

This is a genuine constructive reciprocal — no `Classical`, no Mathlib
field — and it is what makes the normalization `Z·recip Z ≃ 1` available.

### The reweighting datum and the reweighted state

`Reweight A` packages exactly the data the reweighting positivity needs:

- `Ew : A.carrier → Q'`  — the weighted (unnormalized) expectation
  `o ↦ μ(W·o)` in the model;
- `Z : Q'`               — the partition function;
- `Ew_one : Ew 1 = Z`    — `Z = μ(W·1) = μ(W)`;
- `Z_pos  : 0 < Z`       — partition-function positivity;
- `Ew_pos : 0 ≤ Ew(a*·a)` — positivity of the weighted form.

`Ew_pos` is the genuine analytic input (in the real theory it is the
Wilson-action reflection positivity, OS2); here it is a hypothesis, and the
lemmas show it is *all* that is needed.

The reweighted state `E_β(o) := Ew(o) · recip Z` is then proved to be a
state:

- `Reweight.functional_positive`   : `0 ≤ E_β(a*·a)` (product of the
  nonnegative weighted form and the positive reciprocal).
- `Reweight.functional_normalized` : `E_β 1 ≃ 1` (`= Z·recip Z ≃ 1` via
  `mul_recip_eqv_one`).

The normalization is `≃ 1`, not strict `=`, because the unital collapse
`Z·recip Z ≃ 1` is `eqv`, not `rfl`. `ProbFunctional.normalized` demands a
*strict* equality, so:

- `ReweightStrict A` extends `Reweight A` with a strict normalization
  certificate `Ew_one_recip_strict : E_β 1 = 1`;
- `ReweightStrict.functional : ProbFunctional A` — the genuine
  `ProbFunctional` (positive + strictly normalized).

This is the honest split: the abstract reweighting always gives positivity
and `≃ 1`; landing a bona-fide `ProbFunctional` additionally needs the
strict normalization, which concrete instances supply.

### Concrete inhabitants (non-vacuity)

- `prodReweightStrict` / `prodReweight` — the **trivially-coupled** product:
  the decoupled product functional reweighted by `W ≡ 1`, `Z = 1`. Since
  `recip 1 = 1` strictly, this is a genuine `ProbFunctional`, and
  `prodReweight_eq_free` proves `E_β(o) = E_⊗(o)` strictly — *the
  interacting state at zero coupling IS the free state*.
- `scalarReweight` / `scalarReweight_normalized` / `scalarReweight_positive`
  — a **nontrivial-`Z`** reweighting (`W ≡ w`, `Z = w`, any `w > 0`):
  `E_β 1 = w·recip w ≃ 1` genuinely exercises the reciprocal at `w ≠ 1`.

## What this is / is NOT

This is the abstract reweighting *state* law — genuine, fully proved,
reusable. It is the precise reason the interacting finite-volume measure
remains a positive normalized functional once `W ≥ 0` and `Z > 0` are in
hand.

It is NOT a construction of the actual SU(2) plaquette weight, and the
weighted-form positivity `Ew_pos` is an INPUT HYPOTHESIS, not the proved
Wilson reflection positivity.

## OPEN — what genuinely remains (honestly isolated)

1. **The weight `W = e^{−S_plaq}` as a concrete observable.** `W` is a
   non-separable function of the plaquette Wilson loops (e.g. a single
   plaquette = 4 edges), so it lives OUTSIDE the separable `prodAlg`
   carrier. Constructing it as `Q'`/`CReal` data — via the character
   expansion `e^{−S_plaq} = Σ_λ c_λ(β) χ_λ(U_plaq)` with the heat-kernel /
   `wilsonCharExp` coefficients — and computing the partition function
   `Z = E_⊗(W) > 0` for a tiny lattice is NOT done here. `scalarReweight`
   exercises `Z ≠ 1` only with a constant scalar weight, not the genuine
   plaquette weight.

2. **`Ew_pos` is the genuine OS2 reflection positivity — and is assumed.**
   The reweighting lemma proves the interacting state is positive *given*
   `0 ≤ Ew(a*·a)`. That hypothesis is exactly the Wilson-action reflection
   positivity (OS2) for the coupled measure, which is NOT implied by the
   free-product positivity and is NOT proved here. The single-edge partial
   result (`WilsonFunctional.coneExp_nonneg`, nonnegative-cone only; full
   Gram-PSD still open) does not yet cover the coupled multi-edge form. This
   is the central remaining analytic input.

3. **Strict vs. `eqv` normalization.** The abstract reweighted state is
   normalized only up to `Q'.eqv`; a genuine `ProbFunctional` needs the
   strict certificate (`ReweightStrict`). For `Z = 1` this is free
   (`recip 1 = 1`); for general `Z` it is an `eqv`, matching the
   `prodFunctional_marginal` situation in `E2ProductFunctional` where `Q'`
   multiplication is unital only up to `eqv`.

4. **Linearity / `Ew = μ(W··)`.** Here `Ew` is an abstract map with only
   the positivity/normalization fields; the identification
   `Ew(o) = μ(W·o)` with `W` a genuine algebra element requires a richer
   observable structure carrying multiplication/linearity laws (the bare
   `ObsAlg` has none), exactly as flagged in `E2ProductFunctional` for
   `insertAt`. Establishing `Ew` as a *bona-fide* weighted expectation of a
   constructed `W` (rather than an abstract datum) is future work.

5. **Infinite-volume limit with modulus.** Even with the interacting
   finite-volume state in hand, the `n → ∞` (thermodynamic) limit with an
   explicit Cauchy modulus — the Kotecký–Preiss / cluster convergence — is
   the next rung and remains open (see `docs/e2-e3-notes.md`).

### Honest summary

A real, modest, fully-proved step: the constructive positive-cone reciprocal
and the abstract reweighting-state law (positive + normalized-up-to-`eqv`,
upgraded to a strict `ProbFunctional` when normalization is strict), with two
concrete inhabitants. The hard analytic content — constructing the actual
plaquette weight and proving its reflection positivity (`Ew_pos`) — remains
open exactly as listed.
