# Continuum import map — a curated guide to `lean/YMGap/Continuum/`

> **Purpose.** `lean/YMGap/Continuum/` is a large source tree. Many declarations
> retain iteration-family namespaces (`FusionCoreStepRound[A–M]`, dozens of
> `*Close`, `*Progress`), which can read like superseded scratch. Dependency
> audits show that most are cumulative proof chains or current frontier leaves,
> not dead iterations. The former Fusion round files have since been consolidated
> namespace-preservingly into `FusionCoreStep.lean` (A–K) and
> `FusionCoreStepLM.lean` (L–M). This document is the read-first map; use the
> static affected-target planner for the current graph rather than relying on
> historical reverse-dependency counts.

## How the build sees these files

- `lean/lakefile.toml` explicitly sets `globs = ["YMGap.*"]`. A full `YMGap`
  library build therefore compiles every `YMGap/**.lean` module independently,
  whether or not another module imports it. This is compile coverage, not a
  claim that all declarations coexist in one Lean environment.
- `lean/YMGap.lean` is the selective semantic/reflection-audit root. Its import
  closure is the coherent environment inspected by the frontier, statement,
  and axiom-audit machinery.
- `lean/SEMANTIC_ROOT_EXCLUSIONS.txt` is the only review surface for modules
  intentionally compiled outside that environment. Its current roots are
  exactly:
  - `YMGap.ModuliAlgebra` and `YMGap.PolyAtlas` (non-load-bearing expository
    scaffolding);
  - `YMGap.Continuum.ScratchGraphFour` (compile-checked scratch calculation);
  - `YMGap.Continuum.HarmonicLowerSixTailBaseSemanticFactors` (dormant generated
    factor table); and
  - `YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartA` and
    `YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartAXPascal`
    (declaration-colliding alternative certificate realizations that cannot be
    imported together).

Thus there are two independent questions: whether Lake compiles a module, and
whether the semantic guards can see it. `make lean-import-guard` fails if the
glob misses a source, a local import is unresolved/cyclic, or a module falls
outside the semantic root without a non-stale, reasoned manifest entry.

For archivability and local change impact, the meaningful graph is still
**cross-module reverse dependencies**: how many other Continuum/Rubric modules
import a file.
  - **x ≥ 1 → CHAIN-LIVE**: a genuine dependency; removing it breaks a build.
  - **x = 0 → LEAF**: a DAG root. Either a *canonical capstone* (everything
    funnels in) or a *frontier-leaf* (the latest reduction, nothing built on it
    yet). **Leaf ≠ dead** — most leaves are current frontier results.

## Safe consistency workflow

From the repository root, first run the static guard and reverse-dependency
planner; neither command invokes Lean:

```sh
make lean-import-guard
make lean-affected LEAN_BASE=<base-ref>
```

Then build the printed maximal reverse-dependent targets—not the whole tree—at
one worker, for example:

```sh
cd lean
LEAN_NUM_THREADS=1 lake build +YMGap.Continuum.SomePrintedTarget
```

This checks every downstream consumer represented by the guard's accepted
local-import syntax and declared inputs while avoiding unrelated branches. It
cannot replace integration across independent branches or account for
undeclared generated/foreign inputs. Changes to the Lake configuration,
manifest, or pinned toolchain require a full build. On the development host a
full build is a separately approved high-load operation, after targeted checks
and a process/memory check:

```sh
make lean-build LEAN_JOBS=1
```

Do not run a bare full build locally. CI is the definitive integration path: it
builds the complete `YMGap.*` module glob with one worker, includes both
semantic guard roots, and audits the captured build log. The workflow refuses
to start Lean below 24 GiB RAM; repository variable `YMGAP_LEAN_RUNNER` must
name a provisioned high-memory Linux runner. No commit has the definitive
guarantee until that workflow exits zero, and strict namespace-digest drift
remains informational.

## Read-first: canonical capstones (DAG roots, x = 0)

Start here; everything funnels into these.

| Capstone | Subsystem it caps |
|---|---|
| `Continuum/Tier0Scorecard` | the a→0 gap-survival 6-atom frontier scorecard (Tier-0) |
| `Continuum/DiffJTPResult`, `Continuum/DiffJTPFinal` | the θ / Jacobi-triple-product `K_t≥0` machinery (off the OS2 path) |
| `Rubric/LoopScorecard` | the parallel-loop frontier mirror (Core A / Core B) |
| `Rubric/ReconstructionScorecardFinal` | OS reconstruction (GNS / transfer op / FC) |
| `Continuum/ContinuumFrontierScorecard`, `Continuum/ConstructiveShellBridge`, `Continuum/WilsonFCHead` | additional continuum / FC roots |

`Rubric/ClayScorecard` is **not** a root—it is a dependency of other scorecards.
It holds `ClayTarget` (the frontier type guarded by `YMGapGuard.lean`) and
`ClayFixedSpacingMet` (proved). Keep it.

## The four live reduction chains (do NOT archive — load-bearing)

1. **Local-CLT / Core B**: `FusionCoreStep.lean` preserves the former round
   namespaces A–K in dependency order. Branch consumers include
   `AcNReserveAnalytic`, `DiscreteLaplaceMargin`, `ThetaExponentConvexity`,
   `WHTailCeilingsClose`, and `MovingWindowEdgeClose`; the main route continues
   through `LocalCLTSteepestDescent → AutoconvGershgorin` and then the separate
   `FusionCoreStepLM.lean` (rounds L–M, kept downstream to avoid an import
   cycle). The chain feeds `SaddleFloor`, `LineSumLogConcave`, and
   `FusionMarginMonotone` (Core B).
2. **DiffJTP / θ**: the `*Close` cluster
   (`ThetaProdDprodClose`, `ThetaSeriesFieldsClose`, `HdconvClose`,
   `DiffJTPClose`, `ProdSecondDiffClose`, `ChebTFwdBoundClose`, …) →
   `DiffJTPWireFinal` → `DiffJTPResult` (and `DiffJTPFinal`).
3. **Reconstruction**: `RCScaleClose` →
   `SymbolTypedParsevalClose` / `WilsonFCHead` / `FCNormBoundLimit` /
   `CharacterDiagResolutionProof` → `ReconstructionCapstone` →
   `ReconstructionScorecard` → `ReconstructionScorecardFinal`.
4. **Tier-0**: `MultiComponentKPProgress`, `Ursell4DProgress`,
   `ClusterCount4DProgress`, `SixJRecouplingProgress`, `BalabanExactProgress`,
   `TransmutationAFProgress` → `Stage1LoopyReduction` / `Stage2ConvergesToMargin`
   → `Tier0FrontierCorrected` → `Tier0Scorecard`.
   (`ChebOrthoGradedClose` is a hub of the ChebOrtho sub-family.)

**Surprising cross-deps** (a `Progress`/`Close` a capstone rests on directly):
`Ursell4DProgress` is imported by the root `Tier0Scorecard`;
`SixJRecouplingProgress` by `Tier0FrontierCorrected`; `WHTailCeilingsClose` by
three frontiers (`LoopScorecard`, `Tier0FrontierCorrected`, `SaddleFloor`).

## Frontier leaves from the dependency survey

The 2026-07-03 dependency survey classified the following as then-current
leaves. Treat this list as a navigation record, not a current `x = 0` assertion;
run `make lean-affected` or inspect the live graph before archiving anything:

- Tier-0 two-atom attack: `PenroseDomInduction` (penroseDom via deletion-
  contraction), `MeanComplementLogConcave` (complement half → agg-curvature),
  `MeanComplementCovariance` (covariance recast).
- Tier-0 r1–r4 leaves: `SepLatticeZ4Close` (D2 closed), `ScaledBulkShiftClose`,
  `HptProductPtwiseClose`, `MeanToCrossRatioClose`, `PinnedBridgeProgress`,
  `DefectGapRecursionProgress`, `PenroseUrsellProgress`, `TransmutationAFProgress`.
- DiffJTP leaves: `DerivStepPropClose`, `RcRingResidualClose`,
  `ProductFormLOGDClose`, `HinRunningCapClose`, `SpectralDiffBoundClose`.
- Other: `ChebOrthoBudgetClose`, `CosNodeFamilyClose`, `MovingWindowEdgeClose`,
  `RefinedQuadraticClose`.

## The guarded frontier types (must stay UNINHABITED)

`YMGapGuard.lean` is a separate default library root. It is included by the
definitive CI build (and by an explicitly approved `make lean-build
LEAN_JOBS=1`), reflects over the selective `YMGap.lean` semantic environment,
and fails if any of these acquires an *unconditional* inhabitant — the
anti-vacuity check for an agent "accidentally" closing Clay:

- `Continuum/Tier0Scorecard.Tier0Scorecard`
- `Continuum/UnifiedContinuumFloor.UniformSpacingFloor`
- `Rubric/ClayScorecard.ClayTarget`
- `Rubric/ClayTargetPinned.ClayTargetPinned`
- `Rubric/FrontierDAG.FrontierDAG`

Conditional reductions (`… → F`) are allowed; a genuine closure goes through
`YMGapFrontierGuard.frontierAllowlist` under human review. Independent of
`AXIOM_AUDIT.md` (a vacuous term is axiom-clean, so the baseline can't catch it).

## Archive

- `lean/archive/Tier0ReductionCapstone.lean` — the r2 Tier-0 capstone, superseded
  by `Tier0FrontierCorrected` (r3) → `Tier0Scorecard` (r4). Confirmed orphan
  (only `YMGap.lean` imported it). Moved out of the `YMGap` glob (not built),
  kept for provenance.

## Bookkeeping notes for future consolidation

- **What is safely archivable**: only genuinely-superseded roots (like the r2
  capstone above). The round/Close/Progress *chains* are live — archiving them
  breaks the build; the frontier *leaves* are the newest work — archiving them
  loses the frontier. So mass-archival is NOT available; this map is the
  drift-reduction tool instead.
- **Completed namespace-preserving consolidation:** the former round A–K files
  now live in `FusionCoreStep.lean`; rounds L–M live in `FusionCoreStepLM.lean`
  because folding them into the first file would create the documented
  `AutoconvGershgorin → LocalCLTSteepestDescent → FusionCoreStep` import cycle.
  The original `FusionCoreStepRound{A..M}` namespaces and declarations remain
  available to downstream modules.
- After any archival/merge: run `make lean-import-guard`, plan and check the
  affected maximal consumers with one worker, and let CI perform the definitive
  all-module build and captured-log axiom gate; CI also reports strict digest
  drift for review. A local full build or audit is allowed only after explicit
  host approval and uses `LEAN_JOBS=1`; update the axiom baseline only after
  reviewing the resulting drift.
