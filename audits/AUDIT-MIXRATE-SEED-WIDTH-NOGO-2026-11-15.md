# Audit — V3 no-go: the mixRate seed of the r49 scale chain is not width-uniform (2026-11-15)

## Scope & honest label
- Module: `lean/YMGap/RG/MixRateSeedWidthNoGo.lean` (new), importing `BF4ExactSlabFixedSpatialRateWidthObstruction`, `RG/RelativeDissipationScaleChain` (r49) and `DefectRecursionPrimary` (all unchanged).
- Label: **NO-GO for one route. Not gap evidence.** A statement about the computed rate `mixRate`, not about the transfer operator's actual spectral gap. No chart-closure claim; no frontier bundle touched.

## Source
- The no-go is `BF4ExactSlabFixedSpatialRateWidthObstruction` (existing repo theorem). arXiv 2611.17119 (Duch–Gubinelli, fractional Φ⁴₂ mass gap) is cited only as motivating context; it does not discuss this repo's `mixRate`.

## Premise check (YM Bot's description vs the code)
- `mixRate hw0 hw1 width = 1 + -mixFraction` (`BF4ExactSlabFixedSpatialTransferMixingRate.lean:110`).
- `mixFraction = kineticFloor · recipPos kineticCap` (`…MixingRate.lean:81`), with `kineticFloor w width = headFloor w ^ F`, `kineticCap w width = prefixCap w ^ F`, `F = (temporalFaces width).length` (`BF4ExactSlabFixedSpatialTransferSandwich.lean:57,61`).
- `F ≥ width` (`BF4ExactSlabFixedSpatialRateWidthObstruction.width_le_temporalFaces_length`). The exponent IS width-dependent; the premise is true.
- The r49 seed slot is `hseed : WilsonVacuumSqContraction … (width j0) seed` in `scaleChain_afBudget_floor` (`RelativeDissipationScaleChain.lean:256`); `scaleChain_contraction_mixRate` fills it with `seed = mixRate(width j0)`.

## Already in the repo (not new)
`BF4ExactSlabFixedSpatialRateWidthObstruction` already proves, with no extra hypothesis (it uses `headFloor ≤ 1/32` and `prefixCap ≥ 1`, so `headFloor < prefixCap` is not needed as an assumption): `mixFraction ≤ (1/32)^width`, `mixFraction_le_epsilon` beyond `widthModulus ε`, and `no_width_uniform_computed_rate`. This file only transports that bound to the r49 floor.

## Proved (new)
- `seedWidth ε := widthModulus (ε/2)`.
- `one_sub_mixRate_eqv`: `1 - mixRate ≈ mixFraction` (ring identity).
- `one_sub_mixRate_lt`: `seedWidth ε ≤ width ⟹ 1 - mixRate(width) < ε` (strict, every `ε > 0`).
- `exists_width_one_sub_mixRate_lt`: `∀ ε > 0, ∃ width, 1 - mixRate(width) < ε`.
- `mixRate_floor_lt`: `0 ≤ Dq`, `seedWidth ε ≤ width ⟹ (1 - mixRate)(mixRate - Dq) < ε`.
- `no_width_uniform_mixRate_floor`: no `m > 0` lies below that floor at every width.
- `scaleChain_mixRate_floor_lt`: the r49 instance `Dq = C·afA²·inv(j0+2)` with `C ≥ 0`: the floor from the mixRate seed is `< ε` once `width j0 ≥ seedWidth ε`.
- Everything is stated with `<`/`≤` and multiplications; the only reciprocals are the existing `recipPos` inside `mixFraction`.

## Not proved / not claimed
- Nothing about the actual operator's gap; a better seed may exist (see `UniformSeedGap`, OPEN along AF schedules).
- Not that the r49 floor is useless at FIXED width: for each fixed `width j0` it is positive. The no-go is about uniformity in width.

## Verification
- Box only (never the Mac), worktree `/workspace/ym_v3seed_wt` at branch `ym-prover-v3-seed`, Lean 4.29.1. All 3,364 transitive dependencies have up-to-date lake oleans on the box except `YMGap.Continuum.BF4ExactSlabOriginalTubeHeatValue`. Its `compact_upper_variance := by decide +kernel` (line 63) needs more heap than the box has: it failed twice under `safe_lean_build.py` at `-M 9216` and `-M 11776`, with peak RSS equal to the cap and the error `maximum recursion depth` / `sorryAx`. The Mac built it at `-M 32768`. So this file was compiled by a direct `lean -s 65536 -M 6144` call (`LEAN_NUM_THREADS=2`), not by lake. The call used an overlay `LEAN_PATH` made of the box lake oleans plus the Mac-built `BF4ExactSlabOriginalTubeHeatValue.olean`. That olean has output hash `738aabd667d00f10`. It was built on 2026-09-27 from the Dropbox checkout, and the module's source has been unchanged in git since 4df39db1 (2026-09-14). The box did not independently re-check that olean. Result: rc 0, zero warnings and zero errors. `lake build` of this module on the box remains blocked by that dependency.
- No `sorry`/`admit`/`Classical`/`native_decide`/`omega`/`simpa`/Mathlib in the new file.
- Axioms (temp-file `#print axioms`, file deleted afterwards):
```
'YMGap.RG.MixRateSeedWidthNoGo.seedWidth' does not depend on any axioms
'YMGap.RG.MixRateSeedWidthNoGo.one_sub_mixRate_eqv' depends on axioms: [propext, Quot.sound]
'YMGap.RG.MixRateSeedWidthNoGo.one_sub_mixRate_lt' depends on axioms: [propext, Quot.sound]
'YMGap.RG.MixRateSeedWidthNoGo.exists_width_one_sub_mixRate_lt' depends on axioms: [propext, Quot.sound]
'YMGap.RG.MixRateSeedWidthNoGo.mixRate_floor_lt' depends on axioms: [propext, Quot.sound]
'YMGap.RG.MixRateSeedWidthNoGo.no_width_uniform_mixRate_floor' depends on axioms: [propext, Quot.sound]
'YMGap.RG.MixRateSeedWidthNoGo.scaleChain_mixRate_floor_lt' depends on axioms: [propext, Quot.sound]
```

