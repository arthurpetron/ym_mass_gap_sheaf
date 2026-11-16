# Audit: RobustUndershootPhysicalUnits (2026-11-15)

File: `lean/YMGap/RG/RobustUndershootPhysicalUnits.lean` (137 lines, new). Reuses the generic
`UndershootPhysicalUnits.spacing_bound` (imported, unchanged).

## What is PROVED
- `ruRhoTab` :40, `ruOmegaTab` :54, `ruRhoTail` :70 (m = k+7: (m+13)(m+1)/(m(m+14))), `ruOmegaTail` :75 ((m+13)/m).
- `ru_tail_weight` :80 (telescoping identity, equality via ac_rfl), `ruOmegaTail_ge_one` :91, `ru_weight` :103,
  `ru_omega_ge_one` :112.
- `ruP = 1075597539489/19531250000` :118; `ruP_value` :120: ruOmega 0 = ruP, 55 < ruP < 56 (decide).
- `robust_spacing_bound` :130: under `hspacing_OPEN : ∀ i, 2·a_{i+1} ≤ ruRho i·a_i`, 2ⁿ·a_n ≤ P'·a_0 for every n.
- P' = 1075597539489/19531250000 ≈ 55.0706, U' = log₂ P' ≈ 5.783 (old schedule: 38.502, U ≈ 5.27).
  Factors: crossover 5.590 (unchanged ρ), data window 36/25·33/25·63/50·61/50·59/50 ≈ 3.454, tail 20/7 ≈ 2.857.
- Axioms: ruP_value none; ru_weight, robust_spacing_bound ⊆ {propext, Quot.sound}. Zero warnings.

## OPEN / numerical
- hspacing_OPEN keeps the same form (only ρ changes). Since a_{i+1} = 2^{−ℓ_i}a_i, it is EXACTLY ρ_i ≥ 2^{1−ℓ_i}:
  no convexity step is needed (the old 2^u ≤ 1+u link is not used). Numerically ρ_i ≥ 2^{1−ℓ_lo,i} with
  ℓ_lo = min over §9 models of ℓ − 2σ: min ratio (ρ−1)/(2^{1−ℓ_lo}−1) = 1.031 (j6), ≈ 1.16 deep in the tail
  (sampled to j = 1580). Crossover ρ vs TM 2^{1−ℓ}: 1.01/1.000, 1.025/1.010, 1.2/1.118, 1.5/1.407, 1.667/1.539,
  1.8/1.677 (TM has no error bars).
- Tradeoff: P' is 43% larger than P = 38.50; this is the price of a deeper window (map-robust) and tail c ≈ 0.05.

**δ_min = 0 is only a necessary condition: it removes the obstruction but does not prove hafδ.**

**Build caveat:** compiled with direct `lean -M 6144` against the box overlay (`/workspace/v3logs/overlay`). This is direct lean against copied oleans, not lake-verified (stale-trace caveat).

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence. Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β; YM Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the numerics, the U(1) transition lies between 1/8 and 1/2, inside the crossover.
