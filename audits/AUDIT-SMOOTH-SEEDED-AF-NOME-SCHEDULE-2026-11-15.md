# AUDIT — SmoothSeededAfNomeSchedule (2026-11-15)

File: `lean/YMGap/RG/SmoothSeededAfNomeSchedule.lean` (162 lines). Label: **PROVED construction. NOT gap evidence. No chart closure and no mass-gap claim.**

U(1) note: the seed region is abelian-valid strong coupling. Nothing here is non-abelian evidence. Every theorem docstring carries the note.

## Content
`smoothNome w0 j0 k j` (:35), with `A := afNomeSchedule.nome (j0+k)`, has three regions:
- `j ≤ j0`: `w0`;
- `j0 < j < j0+k`: `cross w0 A (j−j0) = w0 + (A−w0)(1−2^−(j−j0))` (:32), geometric in `A − w`;
- `j ≥ j0+k`: `afNomeSchedule.nome j`, at the same index, so the gap there is `afGap j`.

The theorems:
- `smoothSchedule` (:106): all `NomeSchedule` obligations for every `j0`, `k` and `0 < w0 ≤ 1/55`.
  - Positivity: `w0 ≤ cross`.
  - Upper bound below 1: `cross ≤ A < 1`.
  - Monotonicity has five index cases. In the crossover, `cross` increases in `i`; at the junction, `cross ≤ A = w_{j0+k}`.
  - Limit modulus: `(j0+k+1) + 4·ε.den`.
- `smoothAfNomeSchedule j0 k` (:142): the case `w0 = 1/64`.
- `smooth_nome_le_inv55` (:147): every index `≤ j0` lies in the proved region.
- `smooth_nome_af` (:156): from `j0+k` on, the schedule is the AF schedule.

The `k` chain steps `n < k` (scales `j0+n → j0+n+1`) are the crossover. That is where 4D U(1) has its phase transition, so non-abelian input must enter there.

## Verification
- Box only. Nothing was run on the Mac.
- Compiled by a direct `lean -s 65536 -M 6144` call (`LEAN_NUM_THREADS=2`), not by lake. The call used the overlay `LEAN_PATH` (`/workspace/v3logs/overlay`): the box lake oleans plus the Mac-built `BF4ExactSlabOriginalTubeHeatValue.olean`, output hash `738aabd667d00f10`. See `AUDIT-MIXRATE-SEED-WIDTH-NOGO-2026-11-15.md`.
- Compiles:

| Attempt | Result | Peak RSS | Min free RAM | Notes |
|---|---|---|---|---|
| 1 | rc 0 | 1,694 MiB | 12,901 MiB | |
| 2 | rc 0, zero warnings | 1,695 MiB | 12,952 MiB | final, after adding the instance |

- An intermediate edit (modulus `+1`, `q_lt_of_lt_of_le` name) was made before attempt 1, with no failed compile in between.
- No `sorry`/`admit`/`Classical`/`native_decide`/`omega`/`simpa`/Mathlib.
- Axioms (temp-file `#print axioms`, file deleted afterwards):
```
'YMGap.RG.SmoothSeededAfNomeSchedule.cross' does not depend on any axioms
'YMGap.RG.SmoothSeededAfNomeSchedule.smoothNome' depends on axioms: [propext, Quot.sound]
'YMGap.RG.SmoothSeededAfNomeSchedule.smoothSchedule' depends on axioms: [propext, Quot.sound]
'YMGap.RG.SmoothSeededAfNomeSchedule.smoothAfNomeSchedule' depends on axioms: [propext, Quot.sound]
'YMGap.RG.SmoothSeededAfNomeSchedule.smooth_nome_le_inv55' depends on axioms: [propext, Quot.sound]
'YMGap.RG.SmoothSeededAfNomeSchedule.smooth_nome_af' depends on axioms: [propext, Quot.sound]
```
