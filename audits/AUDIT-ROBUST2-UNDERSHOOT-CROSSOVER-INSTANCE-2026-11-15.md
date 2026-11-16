# Audit: Robust2UndershootCrossoverInstance (2026-11-15)

File: `lean/YMGap/RG/Robust2UndershootCrossoverInstance.lean` (169 lines, new).

## What is PROVED
- `etaR2` :49 (η = 1/64), `etaR2_budget` :69 (Σ ≤ 3/32), `r2_seed` :81 (w_0 = 1/64 ≤ 1/55).
- `robust2_crossover_instance` :97: j0 = 0, k = 6, s = 1/4, C = 1/10, floor 114517/5000000 > 0. Remaining:
  hcross_OPEN, hafδ_OPEN, hupper_OPEN, hschur_OPEN.
- `robust2_physical_floor` :137: adds hspacing_OPEN (2·a_{i+1} ≤ r2Rho i·a_i, exactly ρ ≥ 2^{1−ℓ}) and
  hmargin_OPEN (latticeMargin_n ≥ 0). Conclusion: floor·a_n ≤ (P₂·a_0)·latticeMargin_n with P₂ ≈ 81.92, i.e.
  margin_n/a_n ≥ 2.80·10⁻⁴/a_0.
- hspacing/hmargin fit exactly as before: same shapes, only ρ and P change. hmargin still follows from
  floor > 0 plus the instance, but that is not formalised.
- Axioms: etaR2_budget {propext}; r2_seed, robust2_crossover_instance, robust2_physical_floor ⊆ {propext, Quot.sound}.
  Zero warnings.

**δ_min = 0 is only a necessary condition: it removes the obstruction but does not prove hafδ.**

**Build caveat:** compiled with direct `lean -M 6144` against the box overlay (`/workspace/v3logs/overlay`). This is direct lean against copied oleans, not lake-verified (stale-trace caveat).

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence. Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β; YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover.
