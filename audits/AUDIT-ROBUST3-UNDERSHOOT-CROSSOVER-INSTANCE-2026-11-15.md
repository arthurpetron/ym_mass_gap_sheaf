# Audit: Robust3UndershootCrossoverInstance (2026-11-15)

File: `lean/YMGap/RG/Robust3UndershootCrossoverInstance.lean` (169 lines, new). Compile 1.0 s, 1715 MiB.

## What is PROVED
- `etaR3` :49 (η = 1/64), `etaR3_budget` :69 (Σ ≤ 3/32), `r3_seed` :81 (w_0 = 1/64 ≤ 1/55).
- `robust3_crossover_instance` :97: j0 = 0, k = 6, s = 1/4, C = 1/10, floor 114517/5000000 > 0 on the exact-rational
  schedule. Remaining: hcross_OPEN, hafδ_OPEN, hupper_OPEN, hschur_OPEN.
- `robust3_physical_floor` :137: adds hspacing_OPEN (2·a_{i+1} ≤ r3Rho i·a_i, exactly ρ ≥ 2^{1−ℓ}) and hmargin_OPEN
  (latticeMargin_n ≥ 0). Conclusion: floor·a_n ≤ (P₃·a_0)·latticeMargin_n with P₃ ≈ 81.92, i.e.
  margin_n/a_n ≥ 2.80·10⁻⁴/a_0.
- hspacing/hmargin fit exactly as before: same shapes, same ρ and P as Robust2. hmargin still follows from
  floor > 0 plus the instance, but that step is not formalised. Spacing is now supported for ALL j by the
  analysis (limit ratio 1.0655), not only for j ≤ 2000.
- Axioms: etaR3_budget {propext}; r3_seed, robust3_crossover_instance, robust3_physical_floor ⊆ {propext, Quot.sound}.
  Zero warnings.

## Erratum to AUDIT-ROBUST3-ANALYSIS item 6
The bound "κ'²(H_m+1)/m²" should read κ'²(H_m + 1/(m+1))/(m(m+1)), the exact term of item 1. At m = 4 that is
0.042, not ≤ 0.06 via the looser form, which would give 0.071. The conclusion is unchanged: ΔD ≥ 1 − 0.191 −
0.042 − 0.01 > 0.7 at m = 4, and the term decreases for larger m.

**δ_min = 0 is only a necessary condition: it removes the obstruction but does not prove hafδ.**

**Build caveat:** compiled with direct `lean -M 6144` against the box overlay (`/workspace/v3logs/overlay`). This is direct lean against copied oleans, not lake-verified (stale-trace caveat).

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence. Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β; YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover.
