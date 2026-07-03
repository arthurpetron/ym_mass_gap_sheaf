# Classical Ledger

This ledger lists every quarantined classical input the Lean
formalization relies on, per `AGENTS.md` Rule 4.

A use of a classical axiom (`Classical.choice`, `Classical.em`, etc.)
is permitted only when:

1. It lives in a file under `lean/YMGap/Classical/`.
2. It is re-exported through a constructive interface that recovers
   an explicit witness, so downstream constructive code never sees
   the classical axiom.
3. It is logged here with one entry per quarantined use.

If a needed result genuinely cannot be reconstructed constructively,
the corresponding load-bearing theorem must use `sorry` (logged in
`SORRY_LEDGER.md`) rather than reach for the classical axiom.

## Entries

> **Two categories live here.** The preamble conditions (1–3) above govern
> uses of a *Lean* classical axiom (`Classical.choice`, `Classical.em`, …).
> A second category — **cited-external-classical interfaces** — also homes
> here: uninhabited `Type`-level tokens whose *documented meaning* cites an
> external classical theorem, but which introduce **no** Lean classical axiom
> and **no** raw `axiom`. These are interface-only (deliberately uninhabited)
> and are tagged `[P0.x]`. Entry [P0.1] is of this second kind.

_No Lean classical-axiom (`Classical.choice`/`Classical.em`) quarantines yet.
Milestone 1.1 is fully constructive using `Nat`-only arithmetic. Lean 4 core's
`Rat` was rejected for load-bearing use because `Rat.decEq` depends on
`Classical.choice`; the Casimir is represented as `4 · C_2(j) ∈ ℕ` instead (see
`YMGap/RepTheory/SU2.lean` file docstring)._

### [P0.1] Bochner–Minlos σ-additive continuum lift (Input B)

- **category**: cited-external-classical **interface** — NOT a Lean
  `Classical.choice` quarantine, NOT a raw `axiom`.
- **milestone**: 7–9 (continuum / OS / mass gap), `work_plan.md`.
- **file**: `lean/YMGap/Classical/MinlosQuarantine.lean`
  (re-exports `YMGap/Rubric/ContinuumScorecard.CitedMinlosLift`
  = `YMGap/Rubric/ClayScorecard.ClayContinuumExistence`).
- **classical input**: the `a → 0` σ-additive continuum-measure existence with
  tightness, discharged classically in the external GFF / constructive-QFT
  literature by **Bochner–Minlos + Daniell–Kolmogorov**. Not transferable to
  this Mathlib-free constructive substrate; not re-proved here.
- **Lean axiom used**: **none.** `CitedMinlosLift` is an UNINHABITED `structure`;
  the module introduces no `Classical.*`, no `axiom`, no `sorry`. `#print axioms`
  on its declarations shows at most `propext`/`Quot.sound` (Rule 1 clean; in fact
  the re-exports depend on *no* axioms).
- **critical-path role**: Input B of the two-input continuum reduction
  `ContinuumTargetReduction` (`ContinuumScorecard.lean`), orthogonal to Input A
  (the discrete SU(2) heat-kernel-fusion local-CLT). Supplying an inhabitant
  WITHOUT `sorry`/`axiom`/`Prop := True` is part of the OPEN continuum Clay
  problem; the fixed-spacing half is the only line already PROVED.
- **constructive re-exports**: `MinlosContinuumLift` and the conditional
  projections `tightnessRateOf` / `tightnessRateOf_nonneg` in
  `lean/YMGap/Classical/MinlosQuarantine.lean` — each of the honest form
  "GIVEN a hypothetical inhabitant, here is the witness it carries."
- **why the witness is recoverable**: it is **not** — and the interface says so.
  No inhabitant is asserted; this entry records a *named, cited, uninhabited*
  dependency, not a discharged obligation. It exists so the cited-classical
  reliance is auditable in one place, never to present Input B as closed.

## How to add an entry

```markdown
### [P1.x] short title

- **milestone**: 1.x (work_plan.md)
- **file**: `lean/YMGap/Classical/foo.lean`
- **classical input**: `Classical.choice` / `Classical.em` / ...
- **constructive re-exports**: `theorem bar` in `lean/YMGap/.../bar.lean`
- **why the witness is recoverable**: <one sentence>
```
