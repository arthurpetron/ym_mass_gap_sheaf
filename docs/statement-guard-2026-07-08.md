# Statement-hash drift guard — item 5 CLOSED

## The gap (confirmed)

`lean/YMGapGuard.lean` only checks **inhabitation** (no unconditional inhabitant of
a Clay-frontier type). It reflects on inhabitants, never on the *types themselves*.
So silently **weakening a frontier statement** — dropping a field of
`ClayTargetPinned`/`FrontierDAG`, loosening a bound, `∀→∃`, or gutting a shared
parameter def (`RubricO4Restoration := True`) — makes the type easier/trivially
inhabitable and passes the inhabitation guard undetected. That is the exact
vacuous-weakening attack the pinning exists to prevent.

## What was built

New sibling guard `lean/YMGapStatementGuard.lean` (a separate `lean_lib` root,
added to `defaultTargets` + Makefile `lean-statement-guard`). It is **in-Lean**,
fails `lake build` directly, and is independent of both `AXIOM_AUDIT.md` (it hashes
the type, not axioms) and `YMGapGuard.lean` (it hashes the statement, not
inhabitants).

Mechanism, per pinned declaration `d`:
- **structural serialization** `canon : Expr → String` — a pure fold over the
  elaborated env `Expr` (no `whnf`, no reduction): binder **names** + domain +
  body for `∀`/`λ`/`let`, full const names with universe levels, sorts, bvars,
  literals; `.mdata` stripped; macro scopes erased from every name. Deterministic.
- serialized content = `d`'s **type** telescope, PLUS
  - structure/inductive → **every constructor type** (its `∀`-binder names ARE the
    field names, its domains ARE the field types), so a field rename / removal /
    type change / bound loosening / `∀→∃` all perturb the string;
  - def/abbrev → its **value** too, so `RubricO4Restoration := True` changes it.
- digest = **FNV-1a/64** (fully specified in-file: offset `14695981039346656037`,
  prime `1099511628211`), rendered as 16-hex. Does **not** rely on `Expr.hash`
  (whose binder-name treatment is not contractual).
- driver `run_cmd`: compares each computed hash to a pinned literal; `throwError`
  (fails build) on any drift or missing decl; `logInfo "statement-guard OK: N …"`
  when clean.

## Frontier statements pinned (10)

| declaration | kind | pinned hash |
|---|---|---|
| `Rubric.ClayTargetPinned.ClayTargetPinned` | structure (type+ctor) | `a626368409b9a5a4` |
| `Rubric.ClayScorecard.ClayTarget` | structure | `cc27a2da027c4a06` |
| `Rubric.FrontierDAG.FrontierDAG` | structure | `90dd24877aae84ce` |
| `Continuum.Tier0Scorecard.Tier0Scorecard` | structure | `ce2b66cc5711b963` |
| `Continuum.UnifiedContinuumFloor.UniformSpacingFloor` | structure | `414cbe2aaf2c2d53` |
| `Rubric.ClayScorecard.RubricO4Restoration` | def (type+value) | `55e2457c6dc7ecd4` |
| `Rubric.ClayScorecard.RubricUniformInCoupling` | def | `151c42424d3d51a7` |
| `Rubric.ClayScorecard.ClayFixedSpacingMet` | def | `ed4d40a75b442374` |
| `Rubric.ClayScorecard.ClayContinuumExistence` | structure | `8e722e3552788163` |
| `Continuum.Tier0Scorecard.SubWallA` | structure | `d34770c151ca6430` |

First five = the deliberately-uninhabited frontier structures. Last five = the
shared parameter defs/structures their fields are built from — pinned separately
because weakening a shared param (`RubricO4Restoration := True`) would NOT change
the referencing structure's constructor serialization (it references the param by
name), so it needs its own pin. That is the shared-parameter attack, covered.

## Drift demonstration (before/after hash)

Scratch mirror `DriftDemo.Target` (fixed decl name, so only the field change moves
the hash), built with `lake env lean`; scratch file removed afterward:

| variant | hash |
|---|---|
| faithful mirror of `ClayTarget` (4 fields) | `a7a7b6d2d4e92e31` |
| **weakened**: `o4Restoration` field DROPPED | `f19bf2b0a9bed1ec` |
| **weakened**: `o4Restoration : True` (gutted) | `73ed13616506caa5` |

All three distinct → removing a hypothesis and gutting a field type each change the
hash. The serialization genuinely covers field names + field types.

**End-to-end build failure:** temporarily corrupting the pinned
`RubricO4Restoration` hash to `deadbeefdeadbeef` (simulating a drifted statement)
→ `lake build YMGapStatementGuard` exits **1** with:
```
error: STATEMENT DRIFT — a pinned Clay-frontier STATEMENT changed:
  YMGap.Rubric.ClayScorecard.RubricO4Restoration
    pinned : deadbeefdeadbeef
    actual : 55e2457c6dc7ecd4
```
Reverted. So a real weakening breaks the build.

## Stability check

Two builds (rebuild after `touch`) → identical hashes, both report
`statement-guard OK: 10 frontier statements pinned (no drift)`. The fold is a pure
structural pass over closed env `Expr`s (no metavars/fvars, metadata stripped,
macro scopes erased), hence deterministic.

## Axiom gate

`#print axioms`:
- `canon`, `canonLevel` — no axioms;
- `fnv1a64`, `toHex16` — `[propext, Quot.sound]`;
- `constStatementString`, `constStatementHash` — `[propext, Classical.choice,
  Quot.sound]`. The `Classical.choice` enters only through Lean core's
  `Environment.find?`; there is **no `sorryAx`, no new `axiom`, no `sorry`**. This
  is a **tooling metaprogram** (a hash check, not analytic content) and it adds
  **zero** axioms to any gated analytic YMGap declaration — it is a separate root
  that merely `import YMGap`. This is the documented tooling exemption.

## Build + guard status

- `lake build` (all default targets: `YMGap`, `YMGapGuard`, `YMGapStatementGuard`)
  → **exit 0**.
- existing inhabitation guard: `frontier-guard OK: 5 Clay-frontier types
  unconditionally uninhabited` (unchanged).
- new statement guard: `statement-guard OK: 10 frontier statements pinned (no
  drift)`.

## Honest verdict

**Yes — the gap is closed for its stated attack surface.** Any direct weakening of
a pinned frontier type's **field structure** (rename/drop/retype a field, loosen a
bound, `∀→∃`) or of a pinned **shared parameter def's value** (`:= True`) changes
the structural serialization → changes the FNV-1a hash → `throwError` → build fails.
Demonstrated concretely (3 distinct hashes for faithful/dropped/gutted; a live
exit-1 build failure on a drifted pin). The inhabitation guard can no longer be
bypassed by first weakening the type.

**Honest scope limits (not hidden):**
1. Pinning is a **curated one-hop list**, not a full transitive Merkle closure over
   `YMGap.*` (deliberate — a full closure would false-alarm on every unrelated
   refactor). A weakening reached only **two hops** away — via the *value* of an
   already-pinned def that references a *further* def not on the list — is out of
   scope. The direct field-level and shared-param-level weakenings that are the
   stated attack ARE covered. Extend `pinnedFrontierStatements` when a new shared
   parameter becomes load-bearing.
2. The hash includes the decl's own name, so it flags any change but a benign
   value-preserving refactor (e.g. `1/2` ↦ `2⁻¹`) also flags and needs a reviewed
   re-pin — same err-on-the-side philosophy as `AXIOM_AUDIT.md`. This is
   conservative, not unsound.

This is a **guard/tooling** deliverable, not a step toward inhabiting the frontier:
the Clay mass gap remains OPEN, and this guard hardens the pin that keeps it
honestly open.

## Files

- NEW `lean/YMGapStatementGuard.lean` (owned by this task).
- `lean/lakefile.toml` — added `YMGapStatementGuard` lean_lib + defaultTarget.
- `Makefile` — added `lean-statement-guard` target (+ .PHONY + help).
- `lean/YMGapGuard.lean` — NOT edited (sibling guard, as instructed).
- Nothing committed.
