# FusionCoreStepRound[A–M] consolidation — report

## Verdict

The `FusionCoreStepRound*` family (13 files, A–M) is consolidated into **2**
navigable, clearly-sectioned files — **not 1**. A single all-13 file is
**impossible** by a mechanical merge because of a genuine import cycle (below).
The result is the maximal clean merge: **13 → 2**, zero content loss, build
green, guard 5, axioms unchanged.

- `lean/YMGap/Continuum/FusionCoreStep.lean`   — Rounds **A–K** (11→1), 134 decls
- `lean/YMGap/Continuum/FusionCoreStepLM.lean` — Rounds **L–M** (2→1), 16 decls

## The obstruction (why not one file)

Rounds A–K form a strict linear chain A→B→…→K (each imports only its
predecessor + a few base modules). Rounds L, M do not fit with them:

```
FusionCoreStepRoundL  imports  AutoconvGershgorin
AutoconvGershgorin    imports  LocalCLTSteepestDescent
LocalCLTSteepestDescent imports FusionCoreStepRoundJ      (∈ Rounds A–K)
```

So `J` and `L` sit on opposite sides of `AutoconvGershgorin`. Folding L (and M,
which imports L) into the same module as J would close the import cycle

```
merged → AutoconvGershgorin → LocalCLTSteepestDescent → merged
```

Lean forbids module import cycles, so L/M must remain downstream of the A–K
module. `FusionCoreStepLM.lean` therefore imports `FusionCoreStep` (Round M uses
Round C's declarations) and `AutoconvGershgorin`. No cycle: nothing in the
A–K module imports `AutoconvGershgorin`. This is the sharp obstruction, reported
rather than forced.

## Method (lossless)

Each original file has: header comment → `import` lines → `namespace … end` +
trailing `#print axioms` block. The merge strips **only** the `import` lines
(those before the first `namespace`), hoists the deduped union of non-Round
imports to the top, and concatenates the remainder verbatim in dependency order
with `/-! ## Round X … -/` section banners. Every namespace
`YMGap.Continuum.FusionCoreStepRound{A…M}` is preserved intact, so all
downstream references resolve unchanged (no decl was renamed).

Union of base imports hoisted into `FusionCoreStep.lean`:
`FusionCoreInduction`, `FusionLogConcave`, `HeatKernelGap`, `FusionGenFunction`,
`FusionResidualBound`.

## Content-preservation proof (before/after)

| metric | original A–M | merged (Step + StepLM) | match |
|---|---|---|---|
| declarations (theorem/def/lemma) | 150 | 134 + 16 = 150 | ✅ |
| `#print axioms` command lines | 119 | 119 | ✅ (identical sorted target set) |
| declaration names | — | — | ✅ diff = empty (all 150 names identical) |
| namespaces | 13 | 13 | ✅ |

`diff` of the sorted declaration-name lists is empty; `diff` of the sorted
`#print axioms` target lists is empty.

## Build / guard / axioms

- `lake build` → **exit 0**, `Build completed successfully (779 jobs)`
  (was ~790; job count dropped by 11 = the 13 merged files − 2, as expected).
- Frontier guard: `frontier-guard OK: 5 Clay-frontier types unconditionally
  uninhabited across YMGap.*` → **guard 5** ✅.
- Axioms: all 119 gated decls from the merged files report only
  `[propext, Quot.sound]` (60), `[propext]` (38), or "does not depend on any
  axioms" (21). **No forbidden axiom** (no Classical/choice/etc.). ⊆ {propext,
  Quot.sound} ✅.
- No `sorry` / `native_decide` introduced: every match in the merged files is
  backticked prose inside docstrings; strict term/tactic grep = NONE.

## Import repointing (downstream)

`YMGap.lean` (own import block only): the 13 `FusionCoreStepRound*` import lines
were replaced by `import YMGap.Continuum.FusionCoreStep` (line 279) and
`import YMGap.Continuum.FusionCoreStepLM` (line 299). No other agents' import
lines (TwoDYangMills*) were touched.

9 downstream external importers repointed from a specific Round to the merged
module `FusionCoreStep`:

- `Continuum/AcNReserveAnalytic.lean`      (was C)
- `Continuum/DiscreteLaplaceMargin.lean`   (was E)
- `Continuum/FormPreservationCluster.lean` (was B)
- `Continuum/FusionUTuranTrunc.lean`       (was H)
- `Continuum/LocalCLTSteepestDescent.lean` (was J)
- `Continuum/MovingWindowEdgeClose.lean`   (was I)
- `Continuum/ThetaExponentConvexity.lean`  (was F)
- `Continuum/WHTailCeilingsClose.lean`     (was H)
- `Rubric/FrontierDAGBridges.lean`         (was A)

No `import …FusionCoreStepRound[A-M]` remains anywhere in the source tree (only
backticked prose mentions inside the two new docstrings).

## Deleted files (13, backups in scratch)

FusionCoreStepRound{A,B,C,D,E,F,G,H,I,J,K,L,M}.lean — content fully present in
the two merged files before deletion. Backups: `/Users/darthur/.claude/jobs/1c30fec5/tmp/`.

## Nothing committed (per instructions).
