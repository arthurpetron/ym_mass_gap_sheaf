# Codynamic-tool uplift — master map of the entire YM proof tree (2026-07-07)

Node-by-node walk of all **741 imported modules** by five parallel surveyors
(detail tables in `docs/uplift-tables/`). Calibration: the D/F/C metric
(`PROGRESS-LEDGER.md`, F=1 atomic core = `singleStep`), the application map, and
the recast (composition is a *free* nonlinear-modulus Grönwall fold; the `2w³→2`
propagation walls were linear-modulus artifacts; `defect ⊥ modulus`; the sole
binding obstruction is the per-block **defect**).

## The 7 tools
T1 reflection-unit defect · T2 nonlinear monotone modulus · T3 compositional
error law · T4 n-step Grönwall fold · T5 islands · T6 evolution monad
(defect-free) · T7 complexity-budget.

## Verdict distribution (741 nodes)
- **GENUINE-GAIN: ~16 nodes**, *all* clustered at one place — **SITE-1**, the
  intra-block per-move decomposition of the atomic `singleStep` — plus a handful
  of consolidation/island organizational gains. **None discharges `singleStep`.**
- **DEDUP/BOOKKEEPING: ~150** — the codynamic fold is already hand-rolled twice
  (`DefectGapRecursion.prodPrefix_le_physGap`, `Codynamic.InductiveBoundWitnessSystem.
  terminal_invariant_bound`); the 18 C-alias loop-closed tool modules; every
  Mayer/KP/polymer/AF/Anchor/Crossover fold; the curvature/Birkhoff linear-modulus route.
- **MISMATCH: ~45** — T6 defect-free monad/coarsening objects (`RGCategory`,
  `RGTransport`, `WilsonConsistency`, `WilsonRGTower`, `HigherCategorical`, the
  `ScaleSheaf` monad view): a category error for gap *magnitude*.
- **N/A: ~530** — the finite/analytic bulk (Chebyshev-orthogonality ~60 C-modules,
  theta/Wall-2, Bernstein/local-CLT, Turán/Racah/6j/Penrose, GNS/FC/positivity,
  reconstruction/spectral, continuum-measure construction) — no per-step
  defect/flow/modulus/island structure.

## The one core-moving surface: SITE-1 (intra-block per-move defect), fully located

`singleStep` (`realδ_block ≤ 6(1−w)²`) is the T1 per-**block** reflection-unit
defect. The ledger-legal codynamic move is to go one scale finer — one block-spin =
several MK bond-moves — and derive the block defect as a *free* nonlinear Grönwall
fold of per-**move** defects, **iff** the per-move object is certified strictly
weaker (else it re-sums to `singleStep`: the loop trap the adjudication + recast
already caught once).

**Materials (all already in-tree; the fold over them is what's missing):**

| role | module(s) | content |
|---|---|---|
| per-move **trajectory** | `BondMovingStep` (`fusionPow`), `MKBondMovingControl` | p-fold Clebsch–Gordan fusion = the intra-block move chain; literal MK bond-move sequence (`mkDefect_le_sixQuad`) |
| per-move **defect seed** (T1) | `BondMovingStep` (`coeffW_dev`, `bondMovingDelta_to_zero`), `HeatKernelSecondCumulant` | the per-move/per-channel 2nd-cumulant defect |
| **quadratic** summability | `RenDefectQuadFactor` (`(1−w)²(2+w)`), `FullModeQuadratic`, `FusionKernelStatement` (`≤1/12`) | the defect is quadratic not linear — the fact SITE-1's summability rests on |
| deep-UV **counterterm** | `RenormalizedDefectCounterterm` | per-step defect bounded uniformly up to `w→1` |
| **independence device** | `GradedBondMovingBudget` | C₄-graded per-mode `≤(1−w)²`, summable — the grading is what could make pieces independent (not re-summing) |
| **concentration teeth** (T5) | `MultiLinkFusionDefect` (`ρ_m/m ↓`), `InteractingMFoldDefect` (`2−ρ_m=(6/m)ε`) | m-fold *concentrates* → strictly sub-additive `ρ_m < m·ρ_1`; the candidate strict-weakness certificate |
| **island base** (T5) | `CodynamicHierarchical` (`exactLoss=0`), `HierarchicalGap` (δ=0), `IsserlisGaussianBase` (free Wick) | the `η_move=0` free base case of the fold |
| **host** | `CodynamicBondMoving`, `SingleStepDefectReduction` | the SITE-1 host (currently per-*mode*, wrong granularity) + the atomic core |

**Two machine-certified steers (must be respected):**
1. `RenormPerSBudget` — the per-**mode** bulk sum **diverges** ⟹ the decomposition
   must be per-**move**, not per-mode.
2. `MKBondMovingControl.mkVariational_bounds_freeEnergy_not_gapDefect` — the MK
   Jensen bound controls **free energy, not the gap defect**; the real-4D↔MK
   gap-defect transfer is still ≡ `singleStep`. The loop trap lives here.

## The SITE-1 attack (once the transposed Lean tools land)

Build the per-**bond-move** nonlinear Grönwall fold (new `Trajectory.nstep-d` tool)
`realδ_block ≤ ⊕_moves scale_move(·) + η_move` over `BondMovingStep.fusionPow`,
base case `CodynamicHierarchical.exactLoss=0`, per-move seed from `coeffW_dev`,
summability from `RenDefectQuadFactor` + `RenormalizedDefectCounterterm`,
**independence from `GradedBondMovingBudget`'s C₄-grading**, **strict-weakness
from the concentration** `MultiLinkFusionDefect`/`InteractingMFoldDefect`
(`ρ_m < m·ρ_1`). **Hard criterion:** certify the per-move object strictly weaker
than the block `singleStep` (a new F-node, `progress_metric.sh` shows F move below
the core) — or record a machine-checked collapse. Maximal adversarial guard: the
free-energy-vs-gap-defect caveat + the per-mode divergence.

## Secondary (non-core-moving) uplifts
- **SITE-2 consolidation:** one nonlinear-modulus `nstep-d` subsumes both hand-rolled
  folds (`Codynamic.terminal_invariant_bound` additive, which fails the middle window
  `Σδ≈2.54>1`, + the Continuum product fold) under one calculus surviving on `Σδ<∞`.
  Axiom-clean hardening, not new analysis.
- **SITE-3 islands:** `ScaleSheaf`'s `∏tₖ` cocycle = T5 island boundary; AF tail
  (δ~1/k²) + hierarchical (δ=0) = free islands → "free UV island ⊕ finite Bałaban core"
  split. Organizational.
- **Costs/MetricVal instance:** reuse `Rationals.lean` + `RegularCRealArith.lean`
  (join-lattice) + `AbsQ`/`CRealAbs` (metric) — the tools plug into these.

## Bottom line
The metric layer gives the fold a principled home, names the core correctly, and —
via the nonlinear modulus — dissolves the propagation walls, but supplies **no new
analytic input at the top level**. The atomic 4D defect bound is the fold's permanent
hypothesis **unless SITE-1 genuinely splits it**. SITE-1 is the single place in the
entire 741-node tree with a ledger-legal chance to move F below `singleStep`, and its
materials are all in hand; the open question is strict-weakness vs the loop trap.
