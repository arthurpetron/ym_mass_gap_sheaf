# Audit — `UniformSeedGap`: the width-uniform seed input of the r49 scale chain (2026-11-15)

## Scope & honest label
- Module: `lean/YMGap/RG/UniformSeedGap.lean` (new), importing `RG/MixRateSeedWidthNoGo` (new, previous commit). No existing proof edited.
- Label: **OPEN hypothesis interface along AF schedules; PROVED only at the strong-coupling pilot nome `w = 1/1024`.** Not gap evidence. No chart-closure claim.

## Definition
`UniformSeedGap hw0 hw1 budget := ∃ s, budget < s ∧ s < 1 ∧ ∀ width, WilsonVacuumSqContraction hw0 hw1 width s`.

## Proved
- `uniformSeedGap_iff_chainSeedSlot` (`budget ≥ 0`): `UniformSeedGap` ⇔ `∃ s, 0 ≤ s ∧ s < 1 ∧ budget < s ∧ ∀ width, hseed`. These are exactly the hypotheses `hs0`, `hs1`, `hbudget`, `hseed` of `RelativeDissipationScaleChain.scaleChain_afBudget_floor` (`RelativeDissipationScaleChain.lean:256`), made uniform in width.
- `scaleChain_afBudget_floor_of_uniformSeedGap`: given `UniformSeedGap` at `w_{j0}` with `budget = C·afA²·inv(j0+2)`, there is ONE `s`, chosen before any width function, with `0 < (1-s)(s-budget)` (strict), and for EVERY `width : Nat → Nat` (and every `delta`, `Phi`, `D`) the capstone gives contraction at all scales plus `(1-s)(s-budget) ≤ 2^n·latticeMargin_n`. Still conditional on `hupper_OPEN`, `hschur_OPEN`, `hafδ_OPEN`.
- `mixRate_cannot_witness_uniformSeed`: no `s < 1` dominates `mixRate(width)` at every positive width (from the existing `no_width_uniform_computed_rate`). The proved mixRate contraction cannot be lifted to `UniformSeedGap`.
- `uniformSeedGap_existingNome`: at `existingPilotNome = 1/1024`, `UniformSeedGap` holds for every `budget < timeRate`, from the existing `BF4WilsonAllNomeStrongCouplingUniformRate.existingNome_allNome_strongCoupling` (`…StrongCouplingUniformRate.lean:453`; width-independent rate `timeRate`, docstring value 1/4). `uniformSeedGap_existingNome_afBudget`: the r49 example budget `C = 1/10`, `j0 = 8` fits (decide).

## Honest scope correction (r44)
The brief asked to show that `UniformSeedGap` is "exactly what r44 needs". **It is not, and no such theorem is stated.**
- r44 (`BF4WilsonAllNomeScaleDependentContractionInterface.lean:88,98`) asks for retention `r_j·R_j(side_j) ≤ R_j(side_j+1)` and an UPPER bound `side_j·(1 - r_j) ≤ c0`.
- The r49 chain fed by `UniformSeedGap` gives an all-vector contraction (an upper bound on decay) and a LOWER margin `2^n(1 - r_n) ≥ floor`.
- These are opposite directions. `UniformSeedGap` is exactly the width-uniform seed slot of r49, not r44's input.

## Satisfiability / U(1)
- Strong coupling: **PROVED** at `w = 1/1024` (above), SU(2) heat-kernel all-nome carrier, every width.
- AF schedules (`w_j → 1`): **OPEN**. The pilot-nome guards (`heatRatio ≤ 1/2`, …) fail there.
- U(1): **expected** to satisfy the analogous statement at strong coupling (an abelian cluster expansion gives a width-uniform contraction there; per the numerics U(1) is confined only for `w ≤ 1/8`, YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved). Not formalized; the repo carrier is SU(2) only.

## Verification
- Box only (never the Mac), worktree `/workspace/ym_v3seed_wt` at branch `ym-prover-v3-seed`, Lean 4.29.1. All 3,364 transitive dependencies have up-to-date lake oleans on the box except `YMGap.Continuum.BF4ExactSlabOriginalTubeHeatValue`. Its `compact_upper_variance := by decide +kernel` (line 63) needs more heap than the box has: it failed twice under `safe_lean_build.py` at `-M 9216` and `-M 11776`, with peak RSS equal to the cap and the error `maximum recursion depth` / `sorryAx`. The Mac built it at `-M 32768`. So this file was compiled by a direct `lean -s 65536 -M 6144` call (`LEAN_NUM_THREADS=2`), not by lake. The call used an overlay `LEAN_PATH` made of the box lake oleans plus the Mac-built `BF4ExactSlabOriginalTubeHeatValue.olean`. That olean has output hash `738aabd667d00f10`. It was built on 2026-09-27 from the Dropbox checkout, and the module's source has been unchanged in git since 4df39db1 (2026-09-14). The box did not independently re-check that olean. Result: rc 0, zero warnings and zero errors. `lake build` of this module on the box remains blocked by that dependency.
- No `sorry`/`admit`/`Classical`/`native_decide`/`omega`/`simpa`/Mathlib in the new file.
- Axioms (temp-file `#print axioms`, file deleted afterwards):
```
'YMGap.RG.UniformSeedGap.UniformSeedGap' depends on axioms: [propext, Quot.sound]
'YMGap.RG.UniformSeedGap.uniformSeedGap_iff_chainSeedSlot' depends on axioms: [propext, Quot.sound]
'YMGap.RG.UniformSeedGap.scaleChain_afBudget_floor_of_uniformSeedGap' depends on axioms: [propext, Quot.sound]
'YMGap.RG.UniformSeedGap.mixRate_cannot_witness_uniformSeed' depends on axioms: [propext, Quot.sound]
'YMGap.RG.UniformSeedGap.uniformSeedGap_existingNome' depends on axioms: [propext, Quot.sound]
'YMGap.RG.UniformSeedGap.uniformSeedGap_existingNome_afBudget' depends on axioms: [propext, Quot.sound]
'YMGap.RG.UniformSeedGap.uniformSeedGap_of_eq_pilot' depends on axioms: [propext, Quot.sound]
```


## Doc-only addendum (2026-11-15, later commit)
I added a one-line U(1) note to the docstring of the `UniformSeedGap` def and of each of its six theorems: "the strong-coupling witness is abelian-valid, so it is not non-abelian evidence." There is no change to any statement or proof; the diff is docstring text only.
- Recompiled on the box by direct `lean` against the overlay, as above: rc 0, zero warnings. Peak RSS 1,689 MiB, minimum free RAM 12,448 MiB.
- The dependent `PilotScheduleGap` was also recompiled: rc 0.

## U(1) note, sharpened (doc-only addendum, 2026-11-15)

Input: YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved. The repo nome `w` matches the Numerics convention `t = −4 ln w`. At matched β, 4D U(1) is already in the Coulomb (massless) phase at `w = 1/2` and at `w = 0.5145`; only `w ≤ 1/8` is confined for U(1).

- The seed witness at `w ≤ 1/55` is abelian-valid, so it isn't non-abelian evidence.
- Any uniform gap at `w ≳ 1/8` would NOT hold for U(1), so it would be genuine non-abelian content. That covers `hcross_OPEN` beyond `1/8` and the AF-regime hypotheses (`hafδ_OPEN`, `hupper_OPEN`, `hschur_OPEN`).
- Every earlier phrase "the crossover is where U(1) has its phase transition" is replaced by: per the numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover (YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved).

Lean change: docstrings only (the module header and every theorem docstring now carry the sharpened note). No statement or proof changed. Recompiled with the same direct-`lean` method against the overlay (`LEAN_PATH=/workspace/v3logs/overlay`, `-M 6144`), because the box can't rebuild `BF4ExactSlabOriginalTubeHeatValue`: rc 0, zero warnings, peak Lean RSS ≈ 1.7 GiB. `#print axioms` for all 64 theorems in the seven files (plus the 7 in `MixRateSeedWidthNoGo`, 71 total) is identical to before (71 total: 53 `[propext, Quot.sound]`, 5 `[propext]`, 13 none).
