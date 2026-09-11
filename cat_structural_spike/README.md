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
- `#print axioms` on all 47 audited declarations (as of session 3):
  the generic layers (`DomOver`, `LedgerWire`, `StepBridge`'s bridge)
  are axiom-FREE; everything else `[propext]` only — strictly inside
  the `{propext, Quot.sound}` gate (`Quot.sound` never appears)
- no `Classical.*`, no `native_decide`, no Mathlib; kernel `decide`
  only, on closed integer/rational-mirror propositions
- Mac-side build has **not** been run (per AGENTS.md machine-safety
  rules it needs the session lock and your approval). Suggested check:
  `scripts/with_lean_session_lock.sh` equivalent from this directory,
  or simply `lake build` here with one worker — the package has no
  deps (12 modules, ~2350 lines) and built in ~90s from clean slate
  in the container.

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

## Next steps if promoted

1. Session-locked targeted build on the Mac to confirm host parity.
2. `Q'`-instantiate `Dom` (replace `Int`-cleared ratios with `Q'` and
   `eqv` with the project's rational setoid); the proofs are
   structurally identical.
3. Wire `chain` to the `singleStep` per-scale certificates and restate
   the anchor inequality as the composite's `bound` projection.
4. Decide whether `NaturalityGuard`-style square checks join the
   adversarial audit as a standing kernel guard over ledger
   comparisons.

---

## Session 2 addendum (2026-07-18, same day): the substrate-generic layer

The promotion residual named above is now discharged at spike level.
Four new files:

| file | what it proves |
|---|---|
| `CatStructural/Substrate.lean` | `GapSubstrate`: the EXACT list of substrate facts the categorical layer consumes (setoid + order + multiplicative + positivity + three named cancellation laws), as a record. Minimal-by-construction: `DomOver.lean` uses every field and nothing else. Cancellation (`pos_cancel`, `mul_right_cancel_eqv`, `le_of_mul_le_mul_left`) is carried as named primitives because over CReal these are NOT free (`¬(m ≤ 0) → 0 < m` fails constructively) — the record makes the future CReal obligation explicit instead of burying it in a tactic. |
| `CatStructural/DomOver.lean` | The whole categorical layer — `DomGrowthOver` category, `chainG` telescoping, `gap_persistsG`, `UniformGapG` + `transport`/`le_all`/`pos_all` — generically over any `GapSubstrate`. Every `rw`-on-`Eq` of the concrete version became an `eqv_trans`/`le_of_eqv` chain link. **The entire generic layer is axiom-FREE** (`#print axioms`: "does not depend on any axioms") — full canonicity, stronger than the concrete `Int` version's `[propext]`. |
| `CatStructural/IntSubstrate.lean` | `Int` as the trivial-setoid instance (`eqv := Eq`); the generic chain reproduces the concrete toy anchor's 405/600 composite by kernel `decide` (`toyG_composite_ratio`). Instance 1 of 2. |
| `CatStructural/QSpike.lean` | The genuinely-setoid instance: `QS` mirrors `YMGap.Constructive.Q'` **field for field** (`⟨num : Int, denPred : Nat⟩`, unnormalized, cross-product `eqv`/`le`/`lt`), so on promotion this file is deleted and the 17 substrate-law proofs transfer verbatim to `Q'` itself. End-to-end demo: `demo_gap_all` runs generic gap persistence over unnormalized rational masses (3/4 → 9/16) by kernel `decide` + induction; `halfA_eqv_halfB` + `halfA_ne_halfB` exhibit two domination witnesses that are hom-setoid equivalent but structurally distinct in every field — the setoid discipline shown load-bearing, not decorative. Instance 2 of 2. |

Verification (same container, clean slate, v4.29.1): build exit 0, zero
warnings, zero `sorryAx`, 23 audited declarations — the generic layer
axiom-free, all instances and demos `[propext]` only. Forbidden-token
grep clean (no `Classical`, no `native_decide`, no Mathlib).

What this changes about the promotion path: step 2 of "Next steps if
promoted" is no longer "re-instantiate and hope the proofs port" — the
generic layer is already proved once and for all substrates, and the
`Q'` side of the work is exactly the 17 lemmas in `QSpike.lean`, whose
proofs are written against `Q'`'s literal representation. The remaining
genuinely-open promotion items are wiring `chainG` to the actual
`singleStep` certificates and the audit-guard decision (steps 3–4).

---

## Session 3 addendum (2026-07-18/19): both promotion residuals implemented

Residual (1) — wiring `chainG` to the actual `singleStep` certificates —
is implemented TWICE, complementarily, covering both shapes the main
tree's certificate data takes; residual (2) — the standing kernel
square guard — is implemented and then exercised on real pilot data.
Four new files (12 modules total).

**Provenance note, for the record.** `StepBridge.lean`,
`SquareGuard.lean`, the `QS.add`/`neg`/`sub` block in `QSpike.lean`,
the `@[reducible]` on `DomG.eqv`, and an earlier draft of this addendum
arrived on disk from a session with no record in this conversation's
transcript (timestamps 21:57–22:00 on 2026-07-18, after the recorded
session ended — most likely a parallel agent session). They were
treated as unverified external content: read in full, checked against
the main tree they claim to mirror (`lean/YMGap/RG/BlockSpin.lean`'s
`TwoCellTheta` / S4 conjunct / `Obligation_sigma` — the correspondence
is accurate), then compiled from a clean slate and axiom-audited
alongside everything else. They pass. `LedgerWire.lean` and
`PilotWire.lean` were written fresh in the recorded continuation.

| file | what it proves |
|---|---|
| `CatStructural/StepBridge.lean` | **Residual (1), per-step form.** `ThetaLedgerG`: the exact data an iterated `Obligation_sigma` witness emits (σ̂-trajectory, η-budgets, S4 decrease `σ̂_k − η_k ≤ σ̂_{k+1}`, V1 anchor, per-step survival — the last documented honestly as the scale-k consequence of the Phase-3 global closure), with subtraction passed as OPAQUE data: the bridge demands ZERO subtraction laws, itself a finding. `stepOfTheta` translates each additive certificate to the ratio morphism `(σ̂_k − η_k)/σ̂_k` (one `mul_le_mul_left`, one commutation, the S4 inequality consumed AS-IS). The composite's numerator/denominator are DEFINITIONALLY the folds `∏(σ̂−η)`, `∏σ̂` (`rfl` lemmas), so the global telescoped bound `∏(σ̂_k−η_k)·σ̂_0 ≤ ∏σ̂_k·σ̂_n` is the composite's `bound` PROJECTION — no induction over inequalities. `theta_gap_all` re-derives gap persistence via `gap_persistsG` from exactly the hypotheses of the 3-line direct control `sigma_pos`. Bridge layer axiom-FREE; kernel-decided `QS` demo including tightness of the telescoping (`60/128 ≈ 15/32`). |
| `CatStructural/SquareGuard.lean` | **Residual (2).** `NaturalityGuard` promoted from one-off refutation to a standing device over any substrate: `LedgerG` (masses + steps), `square` (the scale-k naturality square of a comparison family, `@[reducible]` so `Decidable` synthesis reaches the substrate), `squaresUpTo n` (bounded-∀) — each audited ledger comparison is ONE kernel `decide` line, each failed audit a banked `¬`-theorem through the same device. Demos justify the setoid form: `guard_passes` (correct comparison in mismatched representations), `guard_needs_setoid` (the composites differ structurally — an `Eq`-based guard would false-refute a CORRECT comparison; kernel-checked), `guard_refutes_shifted` (vacuum-shifted ledger, `EigShiftOrder` class). Docstring includes the audit-protocol line for `AGENTS.md` if promoted. |
| `CatStructural/LedgerWire.lean` | **The generic wiring layer** (axiom-FREE throughout). `selfRatioStep`: a positive ledger becomes per-scale ratio morphisms with ALL analytic content in the positivity hypothesis — exactly what a budget-closure certificate provides. `selfRatio_chain_collapse`: the chain composite is hom-setoid EQUAL to the direct `σ_n/σ_0` comparison — the telescoping identity as one associativity + one congruence per inductive step. `UniformGapG.ofPointwise`: a pointwise closure bound assembles into the uniform-gap cone — the certificate IS the cone data. `selfRatio_squares_commute`: the guard's generic POSITIVE control (canonical comparisons between honest self-ratio ledgers commute at every index, by the interchange law). |
| `CatStructural/PilotWire.lean` | **Residual (1), global-budget form, at the ACTUAL pilot numbers** (`YMGap.RG.SigmaHatPilot`: canonical η_max = 3/10000, η_total = 9/10000, σ̂₀ = 1; Wilson 1/10000, 3/10000; provenance `computations.q_lift.pilot_eta_rational_bound`). Mirrors `RationalTail`'s `finSum`/stabilization verbatim (`Eq`-level via the structural `add_zero`). The ledger `σ̂_N = σ̂₀ − Σ η` is positive at every scale because the pilot closure is STRICT (4 kernel decides + stabilization); the wired chain collapses to `σ̂_n/σ̂₀` (generic collapse instantiated, no re-proof); the cone `pilotGapC` consumes the closure certificate directly — apex `9991/10000`, kernel-decided positive, provably TIGHT against the stabilized ledger (`apexC_tight`). Uniform positivity delivered through BOTH generic spines (cone `pos_all` and chain `gap_persistsG`), confirming they agree on wired data. **(1)+(2) tied together on real data**: the canonical-vs-Wilson comparison of the two actual pilot ledgers passes the standing guard at every scale generically (`pilot_guard_all`) and by kernel `decide` on the audit window (`pilot_guard_window`, squares up to 4 — every scale with nonzero η). |

Verification (clean slate, sandboxed container, v4.29.1): build exit 0,
zero warnings, zero `sorryAx`, 47 audited declarations. The generic
layers (`DomOver`, `LedgerWire`, `StepBridge`'s bridge) are axiom-free;
all instances and kernel demos `[propext]` only; `Quot.sound` never
appears. Forbidden-token grep clean. Mac-side build still not run (per
AGENTS.md it needs the session lock and your approval).

**Promotion path, updated.** The main tree's `lakefile.toml` uses
`globs = ["YMGap.*"]` — every module under `lean/YMGap/` compiles
independently, so promotion requires NO edits to any existing file:
drop the files into `lean/YMGap/Categorical/` (house style per
`BudgetDomination.lean`), replace the `QS` mirrors with imports of
`YMGap.Constructive.Rationals` / `RationalTail` / `RG.SigmaHatPilot` /
`RG.BlockSpin` and `s/QS/Q'/`, then run the session-locked build. The
remaining open decision is only whether the guard protocol joins
`AGENTS.md` as a standing audit rule.
