# Audit: necessary denominator growth for a spacing-to-zero band (2026-09-26 UTC)

## Scope

This increment proves a necessary condition for the still-open physical
calibration input.  It does not estimate the concrete BF4 denominator, inhabit
the changing-nome denominator band, or claim a spatially uniform rate,
continuum limit, OS/GNS identification, physical mass, all-group result, or
Clay theorem.

## Checked declaration

| declaration | source | role |
|---|---|---|
| `ExplicitMarginDenominatorBand.denominator_unbounded` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorExplicitMarginBand.lean:80--145` | For every positive `bound : Q'`, constructs a scale with `bound ≤ law.denominator scale` from an inhabited two-sided denominator band over a spacing-to-zero family. |

The witness is the spacing modulus at the positive threshold
`(1/2) / (band.ceiling * (1 + bound))`.  If the denominator were below
`1 + bound`, monotonicity would force the upper raw product to be at most
`1/2`, contradicting the band’s lower product inequality `1 ≤ ...`.

## Verification

The source was checked with the monitored wrapper, one worker, an 8 GiB
worker ceiling, and an 8 GiB reserve:

```text
python3 scripts/safe_lean_build.py --jobs 1 --reserve-gib 8 \
  --check-worker-limit-gib 8 --check \
  lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorExplicitMarginBand.lean
```

The declaration depends only on `[propext, Quot.sound]`.  No `sorryAx`,
`Classical.*`, `native_decide`, custom axiom, or `noncomputable` declaration
was introduced.

## Boundary

The theorem rules out any bounded-denominator shortcut.  It does not prove
that the actual
`gapDenominator (changingNome scale)` has the required lower and upper
products against `changingSpacing.spacing scale`; those two fields remain the
active B04 obligation.
