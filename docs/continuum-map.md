# Continuum import map — a curated guide to `lean/YMGap/Continuum/`

> **Purpose.** `lean/YMGap/Continuum/` holds ~487 files and `lean/YMGap.lean`
> imports every one of them. Many are named as iteration families
> (`FusionCoreStepRound[A–J]`, dozens of `*Close`, `*Progress`) and that reads
> like superseded scratch — but a full reverse-dependency pass (below) shows the
> opposite: **the round/Close/Progress families are LIVE cumulative dependency
> chains, not dead iterations.** This document is the read-first map so an agent
> or human reviewer can navigate without re-deriving the graph.

## How the build sees these files

- `lean/lakefile.toml` declares `lean_lib YMGap` with the default submodule glob,
  so **every** `YMGap/**.lean` compiles regardless of who imports it.
- `lean/YMGap.lean` is a flat aggregator that `import`s all of them.
- Therefore "is it imported by `YMGap.lean`?" is uninformative (everything is).
  The only meaningful archivability axis is **cross-module reverse-deps**: how
  many *other* Continuum/Rubric modules import a file.
  - **x ≥ 1 → CHAIN-LIVE**: a genuine dependency; removing it breaks a build.
  - **x = 0 → LEAF**: a DAG root. Either a *canonical capstone* (everything
    funnels in) or a *frontier-leaf* (the latest reduction, nothing built on it
    yet). **Leaf ≠ dead** — most leaves are current frontier results.

## Read-first: canonical capstones (DAG roots, x = 0)

Start here; everything funnels into these.

| Capstone | Subsystem it caps |
|---|---|
| `Continuum/Tier0Scorecard` | the a→0 gap-survival 6-atom frontier scorecard (Tier-0) |
| `Continuum/DiffJTPResult`, `Continuum/DiffJTPFinal` | the θ / Jacobi-triple-product `K_t≥0` machinery (off the OS2 path) |
| `Rubric/LoopScorecard` | the parallel-loop frontier mirror (Core A / Core B) |
| `Rubric/ReconstructionScorecardFinal` | OS reconstruction (GNS / transfer op / FC) |
| `Continuum/ContinuumFrontierScorecard`, `Continuum/ConstructiveShellBridge`, `Continuum/WilsonFCHead` | additional continuum / FC roots |

`Rubric/ClayScorecard` is **not** a root (x = 6 — a dependency of the scorecards
above); it holds `ClayTarget` (the frontier type guarded by `YMGapGuard.lean`)
and `ClayFixedSpacingMet` (proved). Keep it.

## The four live reduction chains (do NOT archive — load-bearing)

1. **Local-CLT / Core B**: `FusionCoreStepRoundA → B → … → J`
   (each imports the previous; branch consumers `AcNReserveAnalytic` ⊂ C,
   `DiscreteLaplaceMargin` ⊂ E, `ThetaExponentConvexity` ⊂ F,
   `WHTailCeilingsClose` ⊂ H, `MovingWindowEdgeClose` ⊂ I) →
   `LocalCLTSteepestDescent → AutoconvGershgorin`. Feeds `SaddleFloor`,
   `LineSumLogConcave`, `FusionMarginMonotone` (Core B).
2. **DiffJTP / θ**: the `*Close` cluster
   (`ThetaProdDprodClose`, `ThetaSeriesFieldsClose`, `HdconvClose`,
   `DiffJTPClose`, `ProdSecondDiffClose`, `ChebTFwdBoundClose`, …) →
   `DiffJTPWireFinal` → `DiffJTPResult` (and `DiffJTPFinal`).
3. **Reconstruction**: `RCScaleClose` (x = 7) →
   `SymbolTypedParsevalClose` / `WilsonFCHead` / `FCNormBoundLimit` /
   `CharacterDiagResolutionProof` → `ReconstructionCapstone` →
   `ReconstructionScorecard` → `ReconstructionScorecardFinal`.
4. **Tier-0**: `MultiComponentKPProgress`, `Ursell4DProgress`,
   `ClusterCount4DProgress`, `SixJRecouplingProgress`, `BalabanExactProgress`,
   `TransmutationAFProgress` → `Stage1LoopyReduction` / `Stage2ConvergesToMargin`
   → `Tier0FrontierCorrected` → `Tier0Scorecard`.
   (`ChebOrthoGradedClose`, x = 9, is the hub of the ChebOrtho sub-family.)

**Surprising cross-deps** (a `Progress`/`Close` a capstone rests on directly):
`Ursell4DProgress` is imported by the root `Tier0Scorecard`;
`SixJRecouplingProgress` by `Tier0FrontierCorrected`; `WHTailCeilingsClose` by
three frontiers (`LoopScorecard`, `Tier0FrontierCorrected`, `SaddleFloor`).

## Frontier leaves (x = 0, but LATEST — keep, do not archive)

These are the newest reductions from the DiffJTP / Tier-0 / two-atom work;
nothing imports them *yet* because they are the current edge:

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

`YMGapGuard.lean` (a separate lib root, run every `lake build`, fail-on-error in
CI) reflects over `YMGap.*` and fails if any of these acquires an *unconditional*
inhabitant — the anti-vacuity check for an agent "accidentally" closing Clay:

- `Continuum/Tier0Scorecard.Tier0Scorecard`
- `Continuum/UnifiedContinuumFloor.UniformSpacingFloor`
- `Rubric/ClayScorecard.ClayTarget`

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
- **File-count reduction that IS available** (risk-flagged, not yet done): the
  `FusionCoreStepRound[A–J]` chain (10 files, ~3.4k lines, each in its own
  `FusionCoreStepRound{X}` namespace) could be MERGED into one
  `FusionCoreStep.lean` preserving all namespaces/theorems, updating the ~6
  external importers. Cross-references are qualified (`FusionCoreStepRoundA.foo`
  from within `RoundB`), so a namespace-preserving concatenation is sound; the
  risk is `open`-scoping during the merge silently changing name resolution.
  Requires `make lean-audit-update` + build verification afterward. Do this only
  as a deliberate, reviewed step.
- After ANY archival/merge: `make lean-build` (runs the guard) **and**
  `make lean-audit-update` then `make lean-audit-strict` must be green.
