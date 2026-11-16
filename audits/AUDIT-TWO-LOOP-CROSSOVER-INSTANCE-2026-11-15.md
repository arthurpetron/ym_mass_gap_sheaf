# AUDIT: crossover instance on the two-loop schedule (`lean/YMGap/RG/TwoLoopCrossoverInstance.lean`), 2026-11-15

**Compiled with direct `lean -M 6144` against the overlay**: rc 0, zero warnings, peak Lean RSS
1,692 MiB, min free RAM 10,933 MiB. Axioms (temp file, deleted): `twoLoop_crossover_instance` and
`tl_seed` use `[propext, Quot.sound]`; `etaTL_budget` uses `[propext]`. New file only, 124 lines.

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β; YM
Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be
genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the numerics, the U(1)
transition lies between 1/8 and 1/2, inside the crossover.

## Statement (PROVED reduction, not gap evidence)
`twoLoop_crossover_instance` (line 94) applies `scaleChain_crossover_floor` to `twoLoopSchedule` with:
* `j0 = 0`, `k = 6`, `η_n = 1/64`, `s = 1/4`, `C = 1/10`;
* `E = 3/32 = eDy`, reusing `DyadicCrossoverInstance.budget_dy_ok`;
* floor `114517/5000000 ≈ 0.0229` (unchanged from the dyadic instance; `floor_dy_value`);
* `η_n = 1/48` fails by the same inequality (`budget_dy96_fails`).

Remaining OPEN hypotheses:
* `hcross_OPEN`: δ_n ≤ 1/64 on the 6 steps 1/64 → 1/8 → 7/20 → 14/25 → 67/100 → 147/200 → 779/1000.
* `hafδ_OPEN`: δ_n ≤ (1/10)·afGap(n)² for n ≥ 6.
* `hupper_OPEN` and `hschur_OPEN`.

## Index consistency
No offset is needed. `hafδ_OPEN` indexes `afGap` by the chain index, not the nome. Numerically,
`afGap n / (1 − w_n)` is 0.81 at n = 6, 0.89 at n = 14, 0.94 at n = 30 and 0.98 at n = 100, tending
to 1, so the budget is somewhat tighter than C·(1 − w_n)². Unlike afNome, the two-loop schedule has
no ⌊log₂⌋ jumps; each step changes D(w) = A/(1 − w) by 1.02–1.07. The `AfDeltaJumpAllowance`
obstruction (a single step needing δ ≈ 0.23) therefore does not arise from the schedule. Whether
δ_n ≤ (1/10)·afGap(n)² actually holds remains for Numerics to check.
