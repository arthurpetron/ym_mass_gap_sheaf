# AUDIT — AfDeltaJumpAllowance (2026-11-15)

File: `lean/YMGap/RG/AfDeltaJumpAllowance.lean` (155 lines, new). Label: **PROVED allowance bounds plus a PROVED scalar necessary condition. NOT gap evidence. NOT a Lean refutation of `hafδ`: that needs spectral data, which here is numerical only.**

U(1) note: the seed witness at `w ≤ 1/55` is abelian-valid, so it isn't non-abelian evidence. Any uniform gap at `w ≳ 1/8` would NOT hold for U(1), so it would be genuine non-abelian content. The AF-regime input `hafδ` is such content. YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved.

## What `hafδ` states exactly
`hafδ_OPEN : ∀ k, δ_k ≤ C·afGap(j0+k)²` (`RelativeDissipationScaleChain.lean:259`, also `afQuadratic_prefix_budget` :227 and `CrossoverScaleChain` for `n ≥ k`). Chain step `k` goes from coarse scale `j0+k` to fine scale `j0+k+1`, and `SchurDecomposition` compares `T_F(2)` with `T_C(1)`. The ⌊log₂(j+1)⌋ term in `D_j` jumps on the step from `j = 2^m − 2` to `j+1 = 2^m − 1`. So for jump steps the coarse index is `2, 6, 14, 30, 62` and the fine index is `3, 7, 15, 31, 63`. Both are tabulated.

## Allowance table (exact from `afGap j = 234982/(1000·afE j)`; decimals rounded)

| m | j (coarse / fine) | D_j | afGap(j) | C = 1/10 | C = 1 | any budget-admissible C: ≤ 1/(j+4) | C needed for 0.2 |
|---|---|---|---|---|---|---|---|
| 2 | 2 | 6.42 | 0.3024 | 0.00915 | 0.0915 | 0.1667 | 2.2 |
| 2 | 3 | 7.84 | 0.2476 | 0.00613 | 0.0613 | 0.1429 | 3.3 |
| 3 | 6 | 10.84 | 0.1791 | 0.00321 | 0.0321 | 0.1000 | 6.2 |
| 3 | 7 | 12.26 | 0.1583 | 0.00251 | 0.0251 | 0.0909 | 8.0 |
| 4 | 14 | 19.26 | 0.1008 | 0.00102 | 0.0102 | 0.0556 | 19.7 |
| 4 | 15 | 20.69 | 0.0939 | 0.00088 | 0.0088 | 0.0526 | 22.7 |
| 5 | 30 | 35.69 | 0.0544 | 0.00030 | 0.0030 | 0.0294 | 67.5 |
| 5 | 31 | 37.11 | 0.0523 | 0.00027 | 0.0027 | 0.0286 | 73.0 |
| 6 | 62 | 68.11 | 0.0285 | 0.00008 | 0.0008 | 0.0152 | 246 |
| 6 | 63 | 69.53 | 0.0279 | 0.00008 | 0.0008 | 0.0149 | 256 |

- `C = 1/10` is the only `C` used in the repo instances (`afBudget_example`, `UniformSeedGap`, `PilotScheduleGap`, `CrossoverInstance`, `DyadicCrossoverInstance`).
- The "any admissible C" column is proved, not estimated. It is `allowance_le_inv`: from `C·afA²·inv(j0+2) < seed ≤ 1`, every allowance is `≤ inv(j0+k+3) = 1/(j+4)`. The budget caps `C ≤ (j0+3)/afA²`, while reaching 0.2 at the jump `j` needs `C ≈ 0.053·D_j²`. That grows quadratically while the cap grows linearly, so no `C` works at all jumps.

## Proved (file:line)
- `inv_anti` (:43): `inv` is antitone.
- `allowance_le_inv` (:52): `C·afGap(j0+k)² ≤ 1/(j0+k+4)` under the budget, for every `C ≥ 0`, every `seed ≤ 1` and every `k`.
- `allowance_le_inv17` (:84): `≤ 1/18` at coarse index `≥ 14`. `allowance_le_inv5` (:94): `≤ 1/6` at coarse index `≥ 2`. `inv17_lt_inv5_lt_fifth` (:101): `1/18 < 1/6 < 1/5`.
- `allowance_tenth_jumps` (:108): for `C = 1/10`, `< 1/100` at all ten indices (decidable).
- `rho_le_of_relative` (:118): the scalar necessary condition. If `a > 0`, `δ ≤ ε`, `ρC ≤ 1` and `a·ρF ≤ a·(δ + (1−δ)ρC)`, then `ρF ≤ ε + (1−ε)ρC`, i.e. `1 − ρF ≥ (1−ε)(1−ρC)`.
  - This is the scalar shadow of `twoStepFactor_of_relative_comparison` on a test vector `y`, with `a = ‖y‖²`, `ρF·a = ‖T_F(2)y‖²` and `‖T_C(1)Φy‖² ≤ ρC‖Φy‖² ≤ ρC·a` (coarse contraction plus `hupper`).
  - It is stated over `Q'` scalars, not on the carrier.
- `hafδ_forces_near_halving` (:144): under the budget, `hafδ` at step `k` plus the scalar comparison force `ρF ≤ 1/(j+4) + (1 − 1/(j+4))·ρC`. With `ρF = e^{−4m_F}` and `ρC = e^{−2m_C}` (slowest modes), that gives `1 − e^{−4m_F} ≥ (1 − 1/(j+4))(1 − e^{−2m_C})`. For small masses this is roughly `m_F ≥ (1 − 1/(j+4))·m_C/2`, i.e. near exact halving (that last step is analysis, not proved).

## V3 verdict: numerical, not proof
- YM Numerics (README §7, numerical only): on the `afNome` tail the jump step `14 → 15` has `log₂(m_C/m_F) ≈ 1.38–1.40` and needs `δ ≈ 0.23–0.24`. The `D` increment there is `1 + 51/121 ≈ 1.42`, so the same pattern recurs at every `j = 2^m − 2 → 2^m − 1`.
- The proved allowance at `j = 14` is `≤ 1/18 ≈ 0.056` for ANY admissible `C`, and `≈ 0.0010` for `C = 1/10`. That is 4× (resp. about 230×) below the numerical requirement.
- **So `hafδ` on `afNome` is very likely FALSE at the jump steps (numerical evidence, not proof).** This affects `scaleChain_afBudget_floor` (r49) on `afNome` with every `j0 ≤ 14`, and both crossover instances for `n ≥ k` (their AF tails include `14 → 15`, `30 → 31`, …).
- Not proved: Lean has no spectral data for the carrier, so `hafδ` is not refuted in Lean. The file isolates exactly what a refutation would need: a test vector with `ρF > 1/(j+4) + (1 − 1/(j+4))·ρC`.
- Structural cause (analysis): the chain's factor 2 (`T_F(2)` vs `T_C(1)`, and `2^n` in the floor) makes `δ` measure deviation from exact halving per step. `afNome`'s floor function ⌊log₂(j+1)⌋ makes some steps shrink the mass by about 2^1.42. Possible fixes: a schedule with a smooth log term, or the `q_n` chain (see `ROUTE-SCOPE-QN-SCALE-CHAIN-2026-11-15.md`).

## Verification
- Box only. Direct `lean -s 65536 -M 6144` against the overlay `LEAN_PATH=/workspace/v3logs/overlay` (box lake oleans plus the Mac-built `BF4ExactSlabOriginalTubeHeatValue.olean`, not buildable on the box), not lake.
- Attempt 1: rc 1. I used `≈` without the local notation, and one Nat inequality proof was wrong. Both fixed proof-only.
- Attempt 2: rc 0, zero warnings, peak Lean RSS 1,691 MiB, min free RAM 13,067 MiB.
- `#print axioms` (temp file, deleted): `inv_anti` uses `[propext]`, `inv17_lt_inv5_lt_fifth` uses none, and the other six use `[propext, Quot.sound]`.
- No `sorry`, `admit`, `Classical`, `native_decide`, `omega` or `simpa`.
