# AUDIT: undershoot crossover instance and physical floor (`lean/YMGap/RG/UndershootCrossoverInstance.lean`), 2026-11-15

**Compiled with direct `lean -M 6144` against the overlay**: rc 0, zero warnings, peak Lean RSS 1,745 MiB,
min free RAM 13,371 MiB. **Stale-trace caveat:** this is direct lean against copied oleans (Mac scratch build at
e57df53c with source sha1s matched, plus the box partial build), NOT lake-verified.
Axioms (temp file, deleted): `undershoot_crossover_instance`, `undershoot_physical_floor` and `us_seed` use
`[propext, Quot.sound]`; `etaUS_budget` uses `[propext]`. New file only, 164 lines.
**δ_min = 0 is only a NECESSARY condition: it removes the obstruction but does not prove `hafδ`.**

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence. Any uniform
gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β; YM Numerics interim report
(numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content
(hcross_OPEN beyond 1/8, AF-regime inputs). Per the numerics, the U(1) transition lies between 1/8 and 1/2,
inside the crossover.

## PROVED (reductions)
* `undershoot_crossover_instance` (:93): `scaleChain_crossover_floor` on `undershootSchedule` with
  j0 = 0, k = 6, η_n = 1/64 (`etaUS` :48, `etaUS_budget` :67), s = 1/4, C = 1/10, E = 3/32 (`budget_dy_ok`),
  and seed `us_seed` (:78) at w₀ = 1/64. The floor `114517/5000000 ≈ 0.0229` is unchanged.
* `undershoot_physical_floor` (:132), for every n:
  `floor·a_n ≤ (P·a_0)·latticeMargin_n`, with P = 96256076646951/2500000000000 ≈ 38.50.
  In physical units: **latticeMargin_n / a_n ≥ 114517/(5000000·P·a_0) ≈ 5.95·10⁻⁴ / a_0**.
  Its OPEN hypotheses are all named:
  * `hcross_OPEN`: δ_n ≤ 1/64 on the 6 crossover steps;
  * `hafδ_OPEN`: δ_n ≤ (1/10)·afGap(n)² for n ≥ 6;
  * `hupper_OPEN` and `hschur_OPEN`;
  * `hspacing_OPEN`: 2·a_{i+1} ≤ (1+u_i)·a_i. By convexity 2^u ≤ 1+u, it is implied by ℓ_i ≥ 1 − u_i;
  * `hmargin_OPEN`: latticeMargin_n ≥ 0. It follows from floor > 0 together with the instance, but that step is
    not formalised.

## Caveats
* The hafδ allowance (1/10)·afGap(n)² is still indexed by the chain index. On this schedule the undershoot
  makes `afGap(n)` relative to the actual nome somewhat smaller than on the two-loop schedule; that was not
  checked here.
* Numerics should re-run their §8 δ_min check on `undershootSchedule`.
