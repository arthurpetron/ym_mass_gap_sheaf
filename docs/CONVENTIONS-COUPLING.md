# Coupling conventions (reconciled 2026-10-06)

This page is the single reference for the relation between the SU(2) nome `w`, the
heat-kernel time, and the coupling `g²` in this repository.

## The conventions

| quantity | definition | where |
|---|---|---|
| carrier weight | `w = e^{−t/4}` per Casimir unit `C4 = 4 C2`; heat kernel `e^{−t C2}` | `RGTransport.lean:45`, `WilsonConsistency.lean:129`, `WilsonFunctional.lean:68` |
| carrier heat-kernel time | **`t = −4 log w`** | Lean carrier |
| repo label | "`g² = t`" (a LABEL, not the standard coupling) | `NonpertActivityHeatKernel.lean` and others |
| **standard coupling** | **`g² = 2t = −8 log w`**: Wilson-normalized, continuum action `(1/4g²)∫F^aF^a`, SU(2) `β = 4/g²` | paper (leading-order matching) |
| two-loop coefficients | `b0 = 11/(24π²)`, `b1 = 17/(96π⁴)` refer to the **standard** `g²` | paper |
| older normalization | `w = e^{−t}`, so `t = −log w` (single weight; some files also write `g² = −log w`) | the docstrings listed below |

**Why `g² = 2t`.**
- The carrier heat kernel is the unit-`S³` heat kernel at time `t/4`, because the
  unit-`S³` Laplacian eigenvalues are `ℓ(ℓ+2) = 4 j(j+1) = 4 C2`.
- So near the identity, `U = exp(iθ n·σ)`, it behaves like `exp(−θ²/t)`.
- The Wilson weight is `exp((β/2) tr U) = exp(β cos θ) ≈ exp(−βθ²/2)`.
- Matching the two gives `t = 2/β = g²/2`.
- The Λ-parameter ratio and higher orders shift only the O(1) offset `C` of an AF
  schedule.

**Consequences.**
- The two-loop AF constant for the carrier is `A = 1/(16 b0 ln 2) = 24π²/(176 ln 2) = 1.9416585…`.
  The value `3.883` is what you get by treating the label `t` as the standard `g²`.
- `κ = b1/(2 b0²) = 51/121` is the same in every convention.
- `afNomeSchedule` uses `A = 1942/1000`
  (`lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean`).
- No Lean conclusion depends on `A`.
- Bounds of the form "`… ≤ g²`" proved in the older-normalization files are statements
  about that file's own `t`. The relabelling does not change them.

## Docstrings already reconciled (2026-10-06)

- `BF4WilsonAllNomeAFPaddedTrajectory.lean` (module header and `afA`).
- `BF4WilsonAllNomeShiftedH1Anchor.lean`, the `NomeScheduleAFCalibrated` docstring.
- `NonpertActivityHeatKernel.lean` (module header and the `charMoment_le_g2` line).
- `ExactSinglePolymerActivity.lean` (module header).

## Docstrings NOT edited (older `w = e^{−t}` normalization)

These were left untouched because editing them would force large rebuilds. Their
transitive reverse-dependency chains, from the import graph on 2026-10-06, are:
`FieldSpaceCluster` 30 modules, `SinglePolymerGaussian` 19, `FieldSpaceRenormalonZ1`
8994. Read them with the table above.

States `g² = −log w` or `g² = t = −log w` (older normalization; the label `g²` is the
heat-kernel time):
- `lean/YMGap/Continuum/FieldSpaceCluster.lean:26`, `:27`, `:31`, `:133`
- `lean/YMGap/Continuum/FieldSpaceRenormalonZ1.lean:3`, `:104`, `:110`, `:270`
- `lean/YMGap/Continuum/SinglePolymerGaussian.lean:21`
- `lean/YMGap/Continuum/SubdominanceWindow.lean:18` (refers to the
  `FieldSpaceRenormalonZ1` coupling)

Writes `w = e^{−t}` / `t = −log w`. These were not part of the 2026-10-06 rebuild
review, so no rebuild-chain counts were taken.
- Where `coeffW w 1 = 2w³ = 2e^{−3t}`, this `t` is the time per `C4` unit, i.e.
  carrier `t/4`.
- Files:
  - `lean/YMGap/Continuum/CharFunCumulantDefect.lean:10`, `:110`
  - `lean/YMGap/Continuum/FusionMarginScope.lean:18`
  - `lean/YMGap/Continuum/LargeFieldSuppression.lean:30`, `:38`
  - `lean/YMGap/Continuum/RefinedRetune.lean:35`
  - `lean/YMGap/Continuum/WeakCouplingGap.lean:32`
  - `lean/YMGap/Continuum/WeakRegionNoGo.lean:21`

## Docs that state the reconciled conventions

- `docs/fieldspace-2026-07-06.md` (§1 box)
- `audits/AUDIT-AF-PADDED-TRAJECTORY-2026-10-06.md` (top box)
- `audits/AUDIT-SHIFTED-H1-ANCHOR-2026-10-05.md` (§5)
