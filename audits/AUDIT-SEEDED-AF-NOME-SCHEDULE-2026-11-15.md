# AUDIT — SeededAfNomeSchedule (2026-11-15)

File: `lean/YMGap/RG/SeededAfNomeSchedule.lean` (164 lines). Label: **PROVED construction and PROVED seed, plus OPEN crossover inputs. NOT gap evidence. No chart closure and no mass-gap claim.**

U(1) note: the seed is abelian-valid strong-coupling work, so it is not non-abelian evidence. Every theorem docstring carries this note.

## 1. What `NomeSchedule` requires
`BF4WilsonAllNomeDyadicSmoothedTrajectory.lean:266` has these fields:
- `nome : Nat → Q'`;
- `nome_pos` (`0 < w_j`) and `nome_lt_one` (`w_j < 1`);
- `nome_mono` (`w_j ≤ w_{j+1}`);
- `limitModulus` and `nome_limit` (`w_j ≥ 1 − ε` beyond the modulus).

It has **no** step relation `w_{j+1} = f(w_j)`, **no** AF growth rate and **no** lower bound on `w_0`. So `w_0 ≥ 1/2` is a property of the three concrete schedules only. It is not forced (`seeded_nome_zero_lt_half`, :98).

The r49 capstone `scaleChain_afBudget_floor` (`RelativeDissipationScaleChain.lean:256`) takes an arbitrary `ns : NomeSchedule`. Its AF content is the **fixed** function `afGap (j0+k)` in `hafδ_OPEN` and the budget `C·afA²·inv(j0+2) < seed`. Neither depends on the schedule. No specific schedule is baked into its statement. Task 3's no-go therefore does not apply.

## 2. Construction
- `seededNome w0 j0 j := if j ≤ j0 then w0 else afNomeSchedule.nome j` (:46). It joins the AF schedule at the same index, so for `j > j0` the gap is exactly `afGap j`, the gap `hafδ_OPEN` refers to (`seeded_nome_af`, :116).
- `seededSchedule` (:67) proves all `NomeSchedule` obligations for any `0 < w0 ≤ 1/55`:
  - monotonicity uses `w0 ≤ 1/55 ≤ afNomeSchedule.nome k` for every `k`;
  - the limit modulus is `(j0+1) + 4·ε.den`.
- `seededAfNomeSchedule j0` (:93) is the case `w0 = 1/64`.
- `seeded_nome_le_inv55` (:107): every index `≤ j0` lies in the proved region.
- `seeded_uniformSeedGap` (:124): `UniformSeedGap` at `j0`, for any `budget < timeRate = 1/4`, from `uniformSeedGap_of_le_inv55`.
- `seeded_budget_example` (:131): `C = 1/10`, `j0 = 8` gives `0.1·afA²/10 ≈ 0.038 < 1/4`, by `decide`.
- `seeded_r49_floor` (:138) is the exact statement of what is left. Given the budget condition, the r49 floor holds once `hafδ_OPEN`, `hupper_OPEN` and `hschur_OPEN` are supplied for every `n`.

## What is left, honestly
- The crossover is the single step `j0 → j0+1`. For `j0 = 8` it goes from `w = 1/64` to `w_9 = 1 − afGap 9 ≈ 0.864`.
- The structure allows the jump. The inputs at `n = 0` must carry the whole intermediate-coupling regime:
  - `hupper_OPEN 0`;
  - `hschur_OPEN 0`;
  - `hafδ_OPEN 0`, which says `delta 0 ≤ C·afGap(8)² ≈ 0.0021` for `C = 1/10`.
- Analysis, not a theorem: an AF-sized defect across the largest coupling jump is a very strong demand. As stated, `hafδ_OPEN` is plausibly false at `n = 0`. A realistic route would replace the AF-shaped budget on the first few steps with a crossover budget, which changes the r49 statement. This is not done here.
- This crossover sits at intermediate coupling: per the numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover (YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved). A uniform gap past `w ≈ 1/8` would fail for U(1), so abelian-valid arguments alone cannot carry the seed through. **Non-abelian input must enter there.**

## Verification
- Box only. Nothing was run on the Mac.
- Compiled by a direct `lean -s 65536 -M 6144` call (`LEAN_NUM_THREADS=2`), not by lake. The call used the overlay `LEAN_PATH` (`/workspace/v3logs/overlay`): the box lake oleans plus the Mac-built `BF4ExactSlabOriginalTubeHeatValue.olean`, output hash `738aabd667d00f10`. See `AUDIT-MIXRATE-SEED-WIDTH-NOGO-2026-11-15.md`.
- Compiles:

| Attempt | Result | Peak RSS | Min free RAM | Notes |
|---|---|---|---|---|
| 1 | rc 1 | 1,678 MiB | 12,721 MiB | missing `open … CReal`; untyped example theorem, removed |
| 2 | rc 0, zero warnings | 1,690 MiB | 12,781 MiB | |

- No `sorry`/`admit`/`Classical`/`native_decide`/`omega`/`simpa`/Mathlib. `by_cases` is on decidable `Nat` `≤`.
- Axioms (temp-file `#print axioms`, file deleted afterwards):
```
'YMGap.RG.SeededAfNomeSchedule.seededNome' depends on axioms: [propext, Quot.sound]
'YMGap.RG.SeededAfNomeSchedule.seededSchedule' depends on axioms: [propext, Quot.sound]
'YMGap.RG.SeededAfNomeSchedule.inv64' does not depend on any axioms
'YMGap.RG.SeededAfNomeSchedule.seededAfNomeSchedule' depends on axioms: [propext, Quot.sound]
'YMGap.RG.SeededAfNomeSchedule.seeded_nome_zero_lt_half' depends on axioms: [propext, Quot.sound]
'YMGap.RG.SeededAfNomeSchedule.seeded_nome_le_inv55' depends on axioms: [propext, Quot.sound]
'YMGap.RG.SeededAfNomeSchedule.seeded_nome_af' depends on axioms: [propext, Quot.sound]
'YMGap.RG.SeededAfNomeSchedule.seeded_uniformSeedGap' depends on axioms: [propext, Quot.sound]
'YMGap.RG.SeededAfNomeSchedule.seeded_budget_example' does not depend on any axioms
'YMGap.RG.SeededAfNomeSchedule.seeded_r49_floor' depends on axioms: [propext, Quot.sound]
```

## U(1) note, sharpened (doc-only addendum, 2026-11-15)

Input: YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved. The repo nome `w` matches the Numerics convention `t = −4 ln w`. At matched β, 4D U(1) is already in the Coulomb (massless) phase at `w = 1/2` and at `w = 0.5145`; only `w ≤ 1/8` is confined for U(1).

- The seed witness at `w ≤ 1/55` is abelian-valid, so it isn't non-abelian evidence.
- Any uniform gap at `w ≳ 1/8` would NOT hold for U(1), so it would be genuine non-abelian content. That covers `hcross_OPEN` beyond `1/8` and the AF-regime hypotheses (`hafδ_OPEN`, `hupper_OPEN`, `hschur_OPEN`).
- Every earlier phrase "the crossover is where U(1) has its phase transition" is replaced by: per the numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover (YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved).

Lean change: docstrings only (the module header and every theorem docstring now carry the sharpened note). No statement or proof changed. Recompiled with the same direct-`lean` method against the overlay (`LEAN_PATH=/workspace/v3logs/overlay`, `-M 6144`), because the box can't rebuild `BF4ExactSlabOriginalTubeHeatValue`: rc 0, zero warnings, peak Lean RSS ≈ 1.7 GiB. `#print axioms` for all 64 theorems in the seven files (plus the 7 in `MixRateSeedWidthNoGo`, 71 total) is identical to before (71 total: 53 `[propext, Quot.sound]`, 5 `[propext]`, 13 none).
