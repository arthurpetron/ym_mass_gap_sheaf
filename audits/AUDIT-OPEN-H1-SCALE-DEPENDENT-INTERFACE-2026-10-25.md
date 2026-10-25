# AUDIT: open H1 / Clay dimensional-transmutation conjecture interface (2026-10-25 ET)

**Labels: CONDITIONAL / OPEN Clay-level dimensional-transmutation input. NOT a proof of the conjecture; NOT mass-gap evidence.**
File: `lean/YMGap/Continuum/BF4WilsonAllNomeScaleDependentContractionInterface.lean` (249 lines).

## Interface & Statements
* `PathScaleDependentShiftedContraction tr r c0`: for all `j ≥ 1`, `r_j ≤ 1`,
  `r_j · R_j(side_j) ≤ R_j(side_j + 1)`, and `side_j · (1 - r_j) ≤ c0`.
* `ScaleDependentShiftedH1Conjecture tr c0`: audited open conjecture structure packaging
  `1 ≤ c0` and `∃ r, PathScaleDependentShiftedContraction tr r c0`.
* `conjecture_iff_pathShiftedEpsBound`: for `1 ≤ c0`, `ScaleDependentShiftedH1Conjecture tr c0 ↔ PathShiftedEpsBound tr c0` (via `pathShiftedEpsBound_of_scaleDependentContraction` and `scaleDependentContraction_of_pathShiftedEpsBound` with `canonicalShiftedRate c0 j = 1 - c0 / side_j`).
* `conjecture_closes_shifted_anchor` & `conjecture_closes_padded_shifted_anchor`: closes `ShiftedAnchorPackage` (with nondegeneracy discharged automatically on `PathFacesPadded tr`).
* `conjecture_forces_rayleigh_rate` & `conjecture_forbids_uniform_rayleigh_rate`: compatible with `shiftedH1_forbids_uniformRate` (`side_j(1 - rj_j) ≤ c0` for `j ≥ 1`, excluding any uniform `r < 1`).
* `afPadded_closed_by_conjecture`: concrete closure on `afPaddedZeroMomentumTrajectory` (`c0 = 2`, `a = 2`, `delta = afHalf = 1/2`), pairing `NomeScheduleAFCalibrated` with `ShiftedAnchorPackage`.

## Scope & Limits
Conditional / open interface only: the `O(1/side_j)` shifted one-step retention rate along an AF-calibrated trajectory is the open Clay-level dimensional-transmutation input and is NOT proved here.

## Gates
Capped single-file `--check` (`-j1`, `LEAN_NUM_THREADS=1`, 3.4 GiB worker cap), zero warnings. `#print axioms` on all 12 declarations: `{propext, Quot.sound}`. Banned-token scan clean.
