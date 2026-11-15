# AUDIT — CrossoverScaleChain (2026-11-15)

File: `lean/YMGap/RG/CrossoverScaleChain.lean` (136 lines). Label: **PROVED reduction from explicit OPEN inputs. This is a NEW statement next to r49; r49 (`scaleChain_afBudget_floor`) and all existing files are untouched. NOT gap evidence. No chart closure and no mass-gap claim.**

U(1) note: the seed is abelian-valid. The non-abelian content sits in `hcross_OPEN` (the crossover, where 4D U(1) has its phase transition) and in `hafδ_OPEN`, `hupper_OPEN` and `hschur_OPEN` in the AF regime.

## Statement
`scaleChain_crossover_floor` (:101):
- Steps `n < k` satisfy `δ_n ≤ η_n` (`hcross_OPEN`).
- Steps `n ≥ k` satisfy the old `δ_n ≤ C·afGap(j0+n)²` (`hafδ_OPEN`).
- The crossover budget is `hE : ∀ n, finSum (crossPart k η) n ≤ E`, which encodes `∑_{n<k} η_n ≤ E`.
- With these, plus `hupper_OPEN`, `hschur_OPEN` and the seed, there is contraction at every scale, and `(1−s)(s − (E + C·afA²·inv(j0+2))) ≤ 2^n (1 − r_n)`.

## Loss factor: derived, not guessed
- The floor reuses the existing `relativeRate_side_floor`, which is built on `relativeRate_margin_lower`. That lemma's only defect input is a uniform bound on the prefix sums, `finSum δ n ≤ Dq < seed`. So the loss the actual recursion gives is **additive**: `Dq = E + C·afA²·inv(j0+2)`. It is not a product `∏(1−η_n)`.
- `crossover_prefix_budget` (:81) splits `δ_m ≤ crossPart + afPart` and bounds the AF part with the existing `afQuadratic_prefix_budget` (applied to `afPart`, which satisfies `hafδ` with zeros on `n < k`). The AF tail bound is not tightened to `inv(j0+k+2)`.
- Positivity condition (`crossover_floor_pos`, :92): `E + C·afA²·inv(j0+2) < s < 1`.
- Contraction comes from the existing `scaleChain_contraction`.
- Existing lemmas reused: `scaleChain_contraction`, `relativeRate_side_floor`, `afQuadratic_prefix_budget`, `inv_nonneg`.

## Verification
- Box only. Nothing was run on the Mac.
- Compiled by a direct `lean -s 65536 -M 6144` call (`LEAN_NUM_THREADS=2`), not by lake. The call used the overlay `LEAN_PATH` (`/workspace/v3logs/overlay`): the box lake oleans plus the Mac-built `BF4ExactSlabOriginalTubeHeatValue.olean`, output hash `738aabd667d00f10`.
- Compiles:

| Attempt | Result | Peak RSS | Min free RAM | Notes |
|---|---|---|---|---|
| 1 | rc 0 | 1,695 MiB | 12,562 MiB | |
| 2 | rc 0, zero warnings | 1,695 MiB | 12,114 MiB | docstring wording only |

- No `sorry`/`admit`/`Classical`/`native_decide`/`omega`/`simpa`/Mathlib.
- Axioms (temp-file `#print axioms`, file deleted afterwards):
```
'YMGap.RG.CrossoverScaleChain.crossPart' does not depend on any axioms
'YMGap.RG.CrossoverScaleChain.afPart' depends on axioms: [propext, Quot.sound]
'YMGap.RG.CrossoverScaleChain.crossover_prefix_budget' depends on axioms: [propext, Quot.sound]
'YMGap.RG.CrossoverScaleChain.crossover_floor_pos' depends on axioms: [propext]
'YMGap.RG.CrossoverScaleChain.scaleChain_crossover_floor' depends on axioms: [propext, Quot.sound]
```
