# AUDIT — CrossoverInstance (2026-11-15)

File: `lean/YMGap/RG/CrossoverInstance.lean` (142 lines). Label: **PROVED decidable instance plus PROVED converse. NOT gap evidence. No chart closure and no mass-gap claim.**

U(1) note: the seed is abelian-valid strong coupling. Every theorem docstring carries the note.

## Instance (`smoothAfNomeSchedule 8 4`, `C = 1/10`, `s = timeRate = 1/4`)
- Nomes: `w_8 = 1/64`; `w_9, w_10, w_11 ≈ 0.452, 0.670, 0.779` (geometric crossover); `w_12 = 1 − afGap 12 ≈ 0.8875`; AF after that.
- The seed is `smooth_seed` (:85), width-uniform contraction at `timeRate`. It comes from `uniformRate_of_guards` at `w_8 = 1/64 ≤ 1/55`. This is the same witness that `seeded_uniformSeedGap` packages existentially; it is taken directly here so that `s` is concrete.
- **`η_n = 1/16` fails** (`budget_eta16_fails`, :63). `E = 4/16 = 1/4 = s`, so `E + B < s` is false.
- **`η_n = 1/32` works:**
  - `eta32_budget` (:54): every prefix of the crossover part is `≤ 1/8`.
  - `budget_eta32_ok` (:69): `1/8 + B < 1/4`, with `B = (1/10)·afA²·inv(10) = 942841/27500000 ≈ 0.0343`.
  - `floor_eta32_value` (:75): the floor is exactly `7483977/110000000 ≈ 0.068 > 0`.
- `crossover_instance` (:96) is the instance of `scaleChain_crossover_floor`. What remains is exactly `hcross_OPEN` (`δ_n ≤ 1/32` for `n < 4`), plus `hafδ_OPEN` for `n ≥ 4`, `hupper_OPEN` and `hschur_OPEN`.

## Converse: why the relaxation is needed
- `old_first_step_bound` (:128): `(1/10)·afGap(8)² = 13804135081/6440062500000 ≈ 0.00214`, exact and decidable, and strictly below `1/32`.
- `old_budget_forces_small_first_step` (:137): under the old r49 budget (`hafδ` from `n = 0`), the first defect must satisfy `δ_0 < 1/32`. The old budget asks for an AF-sized defect (≈ 0.0021) on the step from `1/64` toward `≈ 0.45`. The crossover budget instead allows `1/32` per step for 4 steps.

## Honest summary
- The **seed is now proved** on a legitimate `NomeSchedule` (`w ≤ 1/55`, rate 1/4). It is abelian-valid strong-coupling work.
- **All non-abelian content is concentrated** in two places:
  - `hcross_OPEN`, the crossover from `1/64` to `≈ 0.89`, where 4D U(1) has its phase transition. Abelian-valid arguments cannot cross it; non-abelian input must enter here.
  - `hafδ_OPEN`, `hupper_OPEN` and `hschur_OPEN` in the AF regime, plus `hupper_OPEN`/`hschur_OPEN` on the crossover steps themselves.
- No gap claim and no chart closure.
- r49 (`scaleChain_afBudget_floor`) and every existing file are untouched. The new statements are additive.

## Verification
- Box only. Nothing was run on the Mac.
- Compiled by a direct `lean -s 65536 -M 6144` call (`LEAN_NUM_THREADS=2`), not by lake. The call used the overlay `LEAN_PATH` (`/workspace/v3logs/overlay`): the box lake oleans plus the Mac-built `BF4ExactSlabOriginalTubeHeatValue.olean`, output hash `738aabd667d00f10`.
- Compile: rc 0, zero warnings, first attempt. Peak RSS 1,691 MiB, minimum free RAM 12,879 MiB.
- No `sorry`/`admit`/`Classical`/`native_decide`/`omega`/`simpa`/Mathlib.
- Axioms (temp-file `#print axioms`, file deleted afterwards):
```
'YMGap.RG.CrossoverInstance.eta32' does not depend on any axioms
'YMGap.RG.CrossoverInstance.eta32_budget' depends on axioms: [propext]
'YMGap.RG.CrossoverInstance.budget_eta16_fails' does not depend on any axioms
'YMGap.RG.CrossoverInstance.budget_eta32_ok' does not depend on any axioms
'YMGap.RG.CrossoverInstance.floor_eta32_value' depends on axioms: [propext]
'YMGap.RG.CrossoverInstance.smooth_seed' depends on axioms: [propext, Quot.sound]
'YMGap.RG.CrossoverInstance.crossover_instance' depends on axioms: [propext, Quot.sound]
'YMGap.RG.CrossoverInstance.old_first_step_bound' depends on axioms: [propext, Quot.sound]
'YMGap.RG.CrossoverInstance.old_budget_forces_small_first_step' depends on axioms: [propext, Quot.sound]
```
