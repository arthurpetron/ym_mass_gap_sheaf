# AUDIT — PilotScheduleGap (2026-11-15)

File: `lean/YMGap/RG/PilotScheduleGap.lean` (140 lines). Label: **PROVED no-go for the shortcut, plus an OPEN interpolation input. NOT gap evidence. No chart closure and no mass-gap claim.**

## Question
Does `UniformSeedGap.uniformSeedGap_of_eq_pilot` fire on a real schedule? In other words, is `w_{j0} = existingPilotNome = 1/1024` for some existing `NomeSchedule` and some `j0`, possibly after shifting `j0`?

## Answer: no (PROVED)
- Schedule inventory (`rg 'NomeSchedule where'`, plus `schedule :=` / `: NomeSchedule` uses): there are exactly three concrete schedules.
  - `dyadicNomeSchedule`. This is the dyadic smoothed trajectory's schedule. Its own docstring calls it "non-vacuity witness, NOT a physical schedule".
  - `afNomeSchedule`. Used by `afPaddedZeroMomentumTrajectory` and `afPaddedZeroMomentumExpr`.
  - `precisionNomeSchedule`.
  - Other `nome :=` fields in the repo belong to different structures (dynamic families), not `NomeSchedule`. `ExprAnchorTrajectory.schedule` and `DyadicSmoothedTrajectory.schedule` are abstract fields.
- `pilot_lt_of_start` (:53): if `1/1024 < w_0`, then `1/1024 < w_j` for all `j`, because `nome_mono` holds for every `NomeSchedule`. So shifting `j0` cannot reach the pilot.
- Starting values:
  - `dyadic_pilot_lt_start` (:67): `w_0 = 1/2`, by `decide`.
  - `af_pilot_lt_start` (:70): `w_0 = 1 − 234982/484000 ≈ 0.5145`, by `decide`.
  - `precision_pilot_lt_start` (:73): `w_0 ≥ 1/2`, from `gap_le_half`.
- `dyadic_nome_ne_pilot` (:80), `af_nome_ne_pilot` (:84), `precision_nome_ne_pilot` (:88): for all `j`, `w_j ≠ 1/1024`. In fact every `w_j ≥ 1/2`.

## OPEN input recorded
- `PilotToScheduleSeedInterpolation ns j0 budget` (:93): transfer of the width-uniform seed from `w = 1/1024` to `w_{j0}`.
- `interpolation_iff` (:99), honesty check: for `budget < timeRate` it is **equivalent** to `UniformSeedGap` at `w_{j0}`. It names the gap and does not weaken it. The strong-to-intermediate-coupling step from `1/1024` to a value of at least `1/2` is entirely open.
- `scaleChain_floor_of_pilotInterpolation` (:110) is the precise statement of what the r49 capstone still needs:
  - the budget condition `C·afA²/(j0+2) < timeRate`,
  - the OPEN interpolation,
  - `hafδ_OPEN`, `hupper_OPEN` and `hschur_OPEN` at every scale `j0+n`.
- `budget_lt_timeRate_example` (:137): the budget condition is decidable for concrete data, e.g. `C = 1/10`, `j0 = 8`.
- U(1) note: the pilot witness is the strong-coupling estimate, which is abelian-valid. It is not non-abelian evidence.

## Verification
- Box only. Nothing was run on the Mac.
- Compiled by a direct `lean -s 65536 -M 6144` call (`LEAN_NUM_THREADS=2`), not by lake. The call used the overlay `LEAN_PATH` (`/workspace/v3logs/overlay`): the box lake oleans plus the Mac-built `BF4ExactSlabOriginalTubeHeatValue.olean`, output hash `738aabd667d00f10`. That module needs about 32 GiB of heap for `decide +kernel` and cannot be built on the box; see `AUDIT-MIXRATE-SEED-WIDTH-NOGO-2026-11-15.md`.
- Result: rc 0, zero warnings and zero errors. Peak RSS 1,687 MiB, minimum free RAM 12,877 MiB.
- No `sorry`/`admit`/`Classical`/`native_decide`/`omega`/`simpa`/Mathlib.
- Axioms (temp-file `#print axioms`, file deleted afterwards):
```
'YMGap.RG.PilotScheduleGap.pilot_lt_of_start' depends on axioms: [propext]
'YMGap.RG.PilotScheduleGap.nome_ne_pilot_of_start' depends on axioms: [propext]
'YMGap.RG.PilotScheduleGap.dyadic_pilot_lt_start' depends on axioms: [propext, Quot.sound]
'YMGap.RG.PilotScheduleGap.af_pilot_lt_start' depends on axioms: [propext, Quot.sound]
'YMGap.RG.PilotScheduleGap.precision_pilot_lt_start' depends on axioms: [propext, Quot.sound]
'YMGap.RG.PilotScheduleGap.dyadic_nome_ne_pilot' depends on axioms: [propext, Quot.sound]
'YMGap.RG.PilotScheduleGap.af_nome_ne_pilot' depends on axioms: [propext, Quot.sound]
'YMGap.RG.PilotScheduleGap.precision_nome_ne_pilot' depends on axioms: [propext, Quot.sound]
'YMGap.RG.PilotScheduleGap.PilotToScheduleSeedInterpolation' depends on axioms: [propext, Quot.sound]
'YMGap.RG.PilotScheduleGap.interpolation_iff' depends on axioms: [propext, Quot.sound]
'YMGap.RG.PilotScheduleGap.scaleChain_floor_of_pilotInterpolation' depends on axioms: [propext, Quot.sound]
'YMGap.RG.PilotScheduleGap.budget_lt_timeRate_example' does not depend on any axioms
```
