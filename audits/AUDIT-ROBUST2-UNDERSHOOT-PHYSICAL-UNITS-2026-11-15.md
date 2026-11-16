# Audit: Robust2UndershootPhysicalUnits (2026-11-15)

File: `lean/YMGap/RG/Robust2UndershootPhysicalUnits.lean` (137 lines, new). Reuses the generic
`UndershootPhysicalUnits.spacing_bound` (imported, unchanged).

## What is PROVED
- `r2RhoTab` :40 (same head ρ as the robust variant), `r2OmegaTab` :54 (exact backward products from ω_11 = 17/4).
- `r2RhoTail` :70: with m = k+4, ρ = (m+13)(m+1)/(m(m+14)), i.e. u = 13/(m(m+14)), m = i − 7.
  `r2OmegaTail` :75: (m+13)/m. The profile keeps the same telescoping form, so no piecewise family is needed.
- `r2_tail_weight` :80 (equality, ac_rfl), `r2OmegaTail_ge_one` :91, `r2_weight` :103, `r2_omega_ge_one` :112.
- `r2P = 127996107199191/1562500000000` :118. `r2P_value` :120: r2Omega 0 = r2P and 81 < r2P < 82 (decide).
- `robust2_spacing_bound` :130: under hspacing_OPEN (2·a_{i+1} ≤ r2Rho i·a_i), 2ⁿ·a_n ≤ P₂·a_0.
- P₂ = 127996107199191/1562500000000 ≈ 81.9175, U₂ = log₂ P₂ ≈ 6.356. Factors: crossover 5.590 and window
  3.454 (both unchanged), tail 17/4 (was 20/7). P₂ < 100, so this was committed.
- Axioms: r2P_value none; r2_weight, robust2_spacing_bound ⊆ {propext, Quot.sound}. Zero warnings.

## OPEN / numerical
- hspacing_OPEN keeps the same form. It is exactly ρ_i ≥ 2^{1−ℓ_i}. Numerically ρ_i ≥ 2^{1−ℓ_lo,i}, with ℓ_lo the
  minimum of ℓ − 2σ over the 15 models (exact β_char), at every j from 6 to 2000. Min ratio (ρ−1)/(2^{1−ℓ_lo}−1)
  per region: 1.033 (j6), 1.180 (j11–20), 1.120 (j21–41), 1.089 (j42–80), 1.061 (j81–300), 1.053 (j301–1000),
  1.051 (j1001–2000, at j2000). The ratio is still slowly decreasing at j2000 (asymptotically need ≈ 0.0513·g⁴);
  not checked beyond.
- Tradeoff (P₂ vs margin): this tail fit (K_p = 13, offset 4, factor 17/4) is the cheapest single telescoping
  family with ratio ≥ 1.05; (16, 5) gives 4.2 but only 1.009 slack. A deeper tail (coefficient 17/((i+4)(i+22)))
  would raise the matched + c-held margin to ≈ 0.0079·g⁴ at the cost of P ≈ 86.7. Shallower tails (K ≤ 15) fail
  0.005·g⁴. Relative to the robust variant: P' 55.07 → 81.92 (+49%), floor/(P·a_0) 4.16e-4 → 2.80e-4.

**δ_min = 0 is only a necessary condition: it removes the obstruction but does not prove hafδ.**

**Build caveat:** compiled with direct `lean -M 6144` against the box overlay (`/workspace/v3logs/overlay`). This is direct lean against copied oleans, not lake-verified (stale-trace caveat).

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence. Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β; YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover.
