# AUDIT — DyadicCrossoverInstance (2026-11-15)

File: `lean/YMGap/RG/DyadicCrossoverInstance.lean` (154 lines, new). Label: **PROVED decidable instance of `scaleChain_crossover_floor` (a reduction to explicit OPEN inputs). NOT gap evidence. No chart closure.**

U(1) note: the seed witness at `w ≤ 1/55` is abelian-valid, so it isn't non-abelian evidence. Any uniform gap at `w ≳ 1/8` would NOT hold for U(1), so it would be genuine non-abelian content. That covers `hcross_OPEN` beyond 1/8 (crossover steps 2–11) and the AF-regime inputs. Per the numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover (YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved).

## Instance
- Schedule `dyadicCrossoverSchedule`: `j0 = 0`, `k = 12`, every step one dyadic RG step (see `AUDIT-DYADIC-CROSSOVER-SCHEDULE-2026-11-15.md`). Join index `J = j0 + k = 12`, at `afNome 12 = 927009/1044500 ≈ 0.88751`.
- Seed: `dy_seed` (:112), `timeRate = 1/4` at `w_0 = 1/64 ≤ 1/55`, via `uniformRate_of_guards` + `scGuards_of_le_inv55`.
- `C = 1/10` (same as the old instance). `B = C·afA²·inv(0+2) = (1/10)·afA²/3 = 942841/7500000 ≈ 0.125712`. Note `inv m = 1/(m+1)` (`RelativeDissipationScaleChain.lean:178`).
- Per-step budget: `η_n = 1/128` for each `n = 0,…,11` (`etaDy` :44). `Ση = E = 12/128 = 3/32 = 0.09375` (`etaDy_budget` :65, every prefix).
- `E + B = 0.219462 < s = 1/4` (`budget_dy_ok` :75).
- `η_n = 1/96` fails: `1/8 + B = 0.250712 ≥ 1/4` (`budget_dy96_fails` :83). The largest uniform η is `(1/4 − B)/12 ≈ 0.01036`.
- Floor `(1−s)(s − E − B) = (3/4)(1/4 − 3/32 − B) = 114517/5000000 = 0.0229034 > 0` (`floor_dy_value` :91, exact `Q'.eqv` plus positivity).
- Main theorem `dyadic_crossover_instance` (:126): contraction at every scale and `floor ≤ 2^n (1 − r_n)`, given `hcross_OPEN` (`δ_n ≤ 1/128`, `n < 12`), `hafδ_OPEN` (`δ_n ≤ (1/10)·afGap(n)²`, `n ≥ 12`, index-aligned with the schedule's own nome), `hupper_OPEN` and `hschur_OPEN`.
- Side check `forced_margin_below_literature` (:104): at the join (`n = 12`) the conclusion forces only `1 − r_12 ≥ floor/4096 ≈ 5.6·10⁻⁶`. That is well below the literature estimate `0.0024` quoted by Numerics, so this instance's conclusion does not contradict it (the old one did: `≥ 0.00425`).

## Comparison with the old instance (`CrossoverInstance`, numerically implausible)

| | old (`smoothAfNomeSchedule 8 4`) | new (`dyadicCrossoverSchedule`) |
|---|---|---|
| `j0, k`, join index | 8, 4, 12 | 0, 12, 12 |
| last crossover step | 0.779 → 0.8875 (ΔD ≈ 8.5, about 8 scales skipped) | 0.877 → 0.8875 (ΔD ≈ 1.48) |
| η_n, E | 1/32, 1/8 | 1/128, 3/32 |
| B | (1/10)afA²/11 ≈ 0.0343 | (1/10)afA²/3 ≈ 0.1257 |
| floor | ≈ 0.0680 | ≈ 0.0229 |
| forced margin at w ≈ 0.8875 | ≥ 0.00425 (contradicts 0.0024) | ≥ 5.6·10⁻⁶ |

- The cost of `j0 = 0` is a larger AF budget B, since `inv(j0+2)` grows as `j0` shrinks. The per-step crossover allowance drops from 1/32 to 1/128.
- Whether `δ_n ≤ 1/128` is plausible for each dyadic step is for Numerics to check with `δ_min`. Their earlier numbers give `δ_min ≈ 0` for dyadic-scale steps; that is numerical, not proof.

## Nome sequence for Numerics (exact, decimal)
`1/64 = 0.015625`, `1/8 = 0.125`, `7/20 = 0.35`, `14/25 = 0.56`, `67/100 = 0.67`, `147/200 = 0.735`, `779/1000 = 0.779`, `81/100 = 0.81`, `5/6 ≈ 0.833333`, `17/20 = 0.85`, `173/200 = 0.865`, `877/1000 = 0.877`, then `afNome 12 = 927009/1044500 ≈ 0.887515` and `afNome j` onward.

## Verification
- Box only. Direct `lean -s 65536 -M 6144` against the overlay `LEAN_PATH=/workspace/v3logs/overlay` (box lake oleans plus the Mac-built `BF4ExactSlabOriginalTubeHeatValue.olean`, not buildable on the box), not lake.
- Attempt 1: rc 1. Two `decide` refutations: I had assumed `inv 2 = 1/2`, but it is `1/3`, so my `η = 1/128` "fails" claim and the first floor value were wrong. I re-derived the numbers and chose `η = 1/128` (proved fits) and `1/96` (proved fails). Proof and number changes only, in this new file.
- Attempt 2: rc 0, zero warnings, peak Lean RSS 1,688 MiB, min free RAM 13,009 MiB.
- `#print axioms` (temp file, deleted):
  - `dy_seed` and `dyadic_crossover_instance`: `[propext, Quot.sound]`;
  - `etaDy_budget` and `floor_dy_value`: `[propext]`;
  - `budget_dy_ok`, `budget_dy96_fails` and `forced_margin_below_literature`: none.
- No `sorry`, `admit`, `Classical`, `native_decide`, `omega` or `simpa`.
