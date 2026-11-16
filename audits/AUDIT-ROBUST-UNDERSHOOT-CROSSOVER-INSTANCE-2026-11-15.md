# Audit: RobustUndershootCrossoverInstance (2026-11-15)

File: `lean/YMGap/RG/RobustUndershootCrossoverInstance.lean` (169 lines, new).

## What is PROVED
- `etaRU` :49 (η = 1/64), `etaRU_budget` :69 (Σ ≤ E = 3/32), `ru_seed` :81 (w_0 = 1/64 ≤ 1/55).
- `robust_crossover_instance` :97: j0 = 0, k = 6, s = 1/4, C = 1/10, floor 114517/5000000 > 0. Remaining:
  hcross_OPEN, hafδ_OPEN, hupper_OPEN, hschur_OPEN.
- `robust_physical_floor` :137: adds hspacing_OPEN (2·a_{i+1} ≤ ruRho i·a_i) and hmargin_OPEN
  (latticeMargin_n ≥ 0); conclusion floor·a_n ≤ (P'·a_0)·latticeMargin_n, P' ≈ 55.07, i.e.
  margin_n/a_n ≥ 4.16·10⁻⁴/a_0 (old: 5.95·10⁻⁴/a_0).
- hspacing_OPEN and hmargin_OPEN fit exactly as before (same hypothesis shapes; hmargin still follows from
  floor > 0 plus the instance, not formalised here).
- Axioms: etaRU_budget {propext}; ru_seed, robust_crossover_instance, robust_physical_floor ⊆ {propext, Quot.sound}.
  Zero warnings.

**δ_min = 0 is only a necessary condition: it removes the obstruction but does not prove hafδ.**

**Build caveat:** compiled with direct `lean -M 6144` against the box overlay (`/workspace/v3logs/overlay`). This is direct lean against copied oleans, not lake-verified (stale-trace caveat).

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence. Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β; YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover.
