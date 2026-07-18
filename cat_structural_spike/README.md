# cat_structural_spike — categorical structure spike (2026-07-18)

Standalone Lake package answering: *what does formalizing the Yang–Mills
mass-gap program structurally, in category theory, actually buy?* — by
building the three mechanisms that clear the prior assessment's bar
(`docs/category-theory-lift-assessment.md`: ≥2 instances, transport, or
a universal property; nothing decorative).

**Deliberately isolated.** Own `lakefile.toml` and `lean-toolchain`
(`leanprover/lean4:v4.29.1`, same pin as `lean/`). Zero imports from and
zero edits to the main tree. Integration, if wanted, is a separate,
reviewed step.

## Verification status — read this first

Built **green from a clean slate in a sandboxed Linux container** with
the exact toolchain v4.29.1 (`lake build`, exit code 0, zero warnings):

- zero `sorry` / `sorryAx`
- `#print axioms` on all 10 audited declarations: `[propext]` only —
  strictly inside the `{propext, Quot.sound}` gate (`Quot.sound` never
  appears)
- no `Classical.*`, no `native_decide`, no Mathlib; kernel `decide`
  only, on closed integer propositions
- Mac parity is **green** on the M4 Max host (2026-07-18) under the
  repository session lock, one Lean worker, the package's pinned 20 GiB Lean
  ceiling, AC-aware sleep prevention, and reduced priority.  The exact command
  from the repository root was:

  ```text
  caffeinate -ms nice -n 10 ./scripts/with_lean_session_lock.sh cat_structural_spike env LEAN_NUM_THREADS=1 lake build
  ```

  Lake completed all 7 jobs in 5.2 seconds wall-clock, with zero warnings;
  all 10 printed axiom sets were exactly `[propext]`.  The canonical lock was
  absent after the final process scan.  The package is tiny (~600 lines, zero
  dependencies) and built in <3s in the container.

## Contents

| file | what it proves |
|---|---|
| `CatStructural/ECat.lean` | Proof-relevant setoid-Hom E-category framework (agda-categories discipline): `ECat`, `EFunctor`, `ENat`, thin categories from preorders, the scale category ω. No UIP, no equality-on-objects, no 2-cells, no univalence. Data as record fields. |
| `CatStructural/DominatedGrowth.lean` | The load-bearing instance `DomGrowth`: objects = nonnegative `Int` masses (denominator-cleared `Q'` surrogates), morphisms = witness-bearing dominations `(num, den, proof of num·a ≤ den·b)`, hom setoid = ratio equality (decidable). **Composition IS the telescoping single-step bound**: `chain_bound` extracts `∏nᵢ·m₀ ≤ ∏dᵢ·mₙ` from the composite morphism by projection; `gap_persists` is `(1−Σδ)·m₀ > 0 ⟹ mₙ > 0` in composite form. Kernel-`decide`d concrete anchor (`toy_composite_ratio`: composite ratio 405/600, tight). |
| `CatStructural/VolumeCone.lean` | The Clay volume-uniformity clause as a **cone**: `UniformGap` = strictly positive apex Δ + unit-ratio legs `Δ ⟶ G(L)` for every volume. Pinning-by-construction (one apex object ⇒ per-volume constants that secretly differ are a *type error*, Rule 9.7 mechanized). `transport` (uniform gap moves along unit-ratio ledger comparisons, proved once), `ofCofinal` (exhaustion argument at the index level), `le_all`/`pos_all` (payoff projections). |
| `CatStructural/NaturalityGuard.lean` | Normalization bugs (the `EigShiftOrder` class) as **failed naturality squares, kernel-refuted**: `square_fails_for_shifted_ledger` (a vacuum-shifted ledger whose every individual arrow typechecks, killed by `decide` at the square; banked as a `¬` theorem per Lakatos discipline) and the positive control `square_holds_for_correct_ledger`. |

## What the spike demonstrates (the benefits, each with a theorem)

1. **Telescoping = composition.** The per-assembly-point chain
   inductions of the spine collapse into the category's `comp` +
   `comp_assoc`, proved once (`chain_bound`, `gap_persists`).
2. **Uniformity = a cone; pinning = sharing an apex.** "Uniform in the
   volume" stops being a side condition to audit and becomes the shape
   of the data; a non-uniform assembly fails to *typecheck*
   (`UniformGap`).
3. **Transport theorems replace ε-chases.** Comparing two constructions
   of the finite-volume theory is one reusable theorem
   (`UniformGap.transport`), not a re-proof per comparison.
4. **Normalization audits become kernel refutations.** Naturality over
   exact rationals is decidable, so the "smuggled normalization" audit
   item converts to `decide`, and dead comparisons are banked as
   theorems (`square_fails_for_shifted_ledger`).
5. **The constructive discipline survives the abstraction.** Setoid-Hom,
   witnesses in `Type`, `[propext]`-only audit — the categorical layer
   costs no canonicity beyond what the substrate already pays.

## Honest non-claims

- Everything here is at the `Int`-cleared surrogate level (the same
  level of abstraction as the toy anchors, below `Q'`/`CReal`). It
  organizes bookkeeping the analytic layer must feed; it does **not**
  advance the analytic frontier (SU(N) uniform cap, OS reconstruction,
  continuum measure) — consistent with the prior assessment's §5.
- `VolumeLedger.toFunctor` packages the ledger as an `EFunctor`; the
  `UniformGap` machinery deliberately does not demand naturality it
  never uses (no decorative coherence obligations).
- Nothing here is on the critical path yet. Promotion would mean:
  re-instantiating `Dom` over `Q'`/CReal with the setoid `eqv` (the
  framework is written for exactly that — hom setoids are the CReal
  discipline), and wiring `chain` to the actual `singleStep` data.

## Next steps if promoted further

1. `Q'`-instantiate `Dom` (replace `Int`-cleared ratios with `Q'` and
   `eqv` with the project's rational setoid); the proofs are
   structurally identical.
2. Wire `chain` to the `singleStep` per-scale certificates and restate
   the anchor inequality as the composite's `bound` projection.
3. Decide whether `NaturalityGuard`-style square checks join the
   adversarial audit as a standing kernel guard over ledger
   comparisons.
