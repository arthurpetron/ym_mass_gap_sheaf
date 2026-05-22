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

_No classical quarantines yet. Milestone 1.1 is fully constructive
using `Nat`-only arithmetic. Lean 4 core's `Rat` was rejected for
load-bearing use because `Rat.decEq` depends on `Classical.choice`;
the Casimir is represented as `4 · C_2(j) ∈ ℕ` instead (see
`YMGap/RepTheory/SU2.lean` file docstring)._

## How to add an entry

```markdown
### [P1.x] short title

- **milestone**: 1.x (work_plan.md)
- **file**: `lean/YMGap/Classical/foo.lean`
- **classical input**: `Classical.choice` / `Classical.em` / ...
- **constructive re-exports**: `theorem bar` in `lean/YMGap/.../bar.lean`
- **why the witness is recoverable**: <one sentence>
```
