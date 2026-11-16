# AUDIT — DyadicCrossoverSchedule (2026-11-15)

File: `lean/YMGap/RG/DyadicCrossoverSchedule.lean` (160 lines, new). Label: **PROVED construction plus PROVED decidable step checks. NOT gap evidence. No chart closure.**

U(1) note: the seed witness at `w ≤ 1/55` is abelian-valid, so it isn't non-abelian evidence. Any uniform gap at `w ≳ 1/8` would NOT hold for U(1), so it would be genuine non-abelian content. Per the numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover (YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved). Every docstring carries the note.

## Why
YM Numerics (README §4, numerical only) found that the old `smoothAfNomeSchedule 8 4` joins `afNome` at index 12 in one step (`0.779 → 0.8875`), skipping about 8 dyadic scales. This file builds a replacement with no such step. The old files are untouched.

## Choice: option (b) over option (a)
- `scaleChain_crossover_floor` ties three things to the same index `j0 + n`: the schedule index, the AF bookkeeping `afGap(j0+n)` in `hafδ` and the budget `C·afA²·inv(j0+2)`.
- A join "at the matching nome" (option a) therefore has to be index-aligned: `afNome J` sits at schedule index `J = j0 + k`.
- `afNome 4 ≈ 0.7804` would force `j0 + k = 4`. From `1/64`, that is at most 4 steps covering `D(w) = afA/(1−w)` from 1.973 to 8.843. That needs 1.72 per step, beyond the 3/2 allowed, and the SC part fails too: `1/64 → 1/8 → 0.354 → 0.595 → 0.771 < 0.78`.
- The smallest join index for which both parts can hold is `J ≈ 11–12`. So (a) and (b) coincide in practice: about 12 dyadic steps from `1/64` up to `afNome 12`.
- I picked `J = 12` (`j0 = 0`, `k = 12`). It reaches the same endpoint as the old instance (`afNome 12 ≈ 0.8875`), so the two are directly comparable. A non-aligned join (`w_j = afNome(j − offset)`) would make the `hafδ` bookkeeping refer to the wrong scale, so I rejected it.

## Definition: one dyadic RG step (`DyadicRGStep wc wf`, :47)
Both parts must hold:
- **(SC)** `wf² ≤ wc`, equivalently `t_f ≥ t_c/2` with `t = −4 ln w`. At strong coupling the mass is `m ≈ 3t` (Numerics: `m(1/64) = 49.9 ≈ 3·16.6`), so the mass at most halves.
- **(AF)** `2·afA·((1−wc) − (1−wf)) ≤ 3·(1−wc)(1−wf)`, equivalently `D(wf) − D(wc) ≤ 3/2` with `D(w) := afA/(1−w)`. For `afNome`, `D(w_j) = j + (51/121)⌊log₂(j+1)⌋ + 4` exactly (`afDen_gap`), so one AF index is one unit of `D`. The largest `afNome` increment is `1 + 51/121 ≈ 1.42 < 3/2`.
- Note: `afNome` does **not** satisfy `w_{j+1} = w_j^{1/2}`. That relation is the (SC) part only.
- The conjunction is conservative. All four old steps fail it (`old_steps_not_dyadic`, :153): steps 0 and 3 fail both parts, steps 1 and 2 fail only (AF). Numerics found steps 0–2 harmless (`δ_min ≈ 0`), so in the strong and intermediate region this definition is stricter than needed. It is a schedule-internal proxy, not a physics theorem.

## The schedule (`dyTable` :55, `dyNome` :70, `dyadicCrossoverSchedule` :96)

| index | nome (exact) | decimal | `D = afA/(1−w)` | ΔD |
|---|---|---|---|---|
| 0 | 1/64 | 0.015625 | 1.9728 | — |
| 1 | 1/8 | 0.125 | 2.2194 | 0.2466 |
| 2 | 7/20 | 0.35 | 2.9877 | 0.7683 |
| 3 | 14/25 | 0.56 | 4.4136 | 1.4259 |
| 4 | 67/100 | 0.67 | 5.8848 | 1.4712 |
| 5 | 147/200 | 0.735 | 7.3283 | 1.4435 |
| 6 | 779/1000 | 0.779 | 8.7873 | 1.4590 |
| 7 | 81/100 | 0.81 | 10.2211 | 1.4337 |
| 8 | 5/6 | 0.833333 | 11.652 | 1.4309 |
| 9 | 17/20 | 0.85 | 12.9467 | 1.2947 |
| 10 | 173/200 | 0.865 | 14.3852 | 1.4385 |
| 11 | 877/1000 | 0.877 | 15.7886 | 1.4034 |
| 12 | afNome 12 = 927009/1044500 | 0.8875146 | 17.2645 | 1.4758 |
| j ≥ 12 | afNome j | | j + (51/121)⌊log₂(j+1)⌋ + 4 | 1 or 1.42 |

- `NomeSchedule` obligations: positivity, `< 1` and monotonicity on the table are proved by bounded `decide`. The join `877/1000 ≤ afNome 12` is decidable. The tail and the limit come from `afNomeSchedule`.
- `dy_nome_zero_le_inv55` (:121): `w_0 = 1/64 ≤ 1/55`, the proved seed region.
- `dy_nome_af` (:127): `nome j = afNome j` for `j ≥ 12`.

## Step checks
- `dyadic_steps_crossover` (:136): all 12 steps `n → n+1` for `n < 12`, including the join `11 → 12`, satisfy `DyadicRGStep`, by bounded `decide`.
- `dyadic_steps_af_prefix` (:144): the AF steps `12 → … → 28` satisfy it, by `decide`. This is a spot check, not all `j`.
- **Not proved (stated honestly):** the AF tail for every `j`. On paper: (AF) reduces to `afE(j+1) − afE(j) ≤ 172 < 181.5`, and (SC) to `afE(j+1)/afE(j) ≤ 2 − afGap(j+1)`, which holds since the ratio is ≤ 1.36 and the right side is ≥ 1.51. Formalizing it needs nonlinear Int arithmetic without `omega`; deferred.

## Verification
- Box only. Direct `lean -s 65536 -M 6144` (`LEAN_NUM_THREADS=2`) against the overlay `LEAN_PATH=/workspace/v3logs/overlay` (box lake oleans plus the Mac-built `BF4ExactSlabOriginalTubeHeatValue.olean`, which the box can't rebuild), not lake.
- Attempt 1: rc 1. Two errors (no `Decidable` instance for a `j + 1 < 12` bound, and a Nat lemma mismatch). Both fixed proof-only.
- Attempt 2: rc 0, zero warnings, peak Lean RSS 1,697 MiB, min free RAM 11,096 MiB.
- `#print axioms`, run in a temp file that was then deleted: all six (`dyadicCrossoverSchedule`, `dy_nome_zero_le_inv55`, `dy_nome_af`, `dyadic_steps_crossover`, `dyadic_steps_af_prefix`, `old_steps_not_dyadic`) give `[propext, Quot.sound]`.
- No `sorry`, `admit`, `Classical`, `native_decide`, `omega` or `simpa`.
