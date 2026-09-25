# Audit: fixed-family rate-power arithmetic

## Scope

The fixed `w = 1/2` completed physical family attaches the exact spacing
`(1/2)^scale`. The sampler therefore computes the lattice index literally as
`time * 2^scale`. This is an arithmetic input for the positive-time
rate-power variation frontier; it is not itself a rate limit or a physical
mass-gap statement.

## Declaration

| declaration | location | result |
|---|---|---|
| `marginalHalfGeometric_latticeSteps_eq` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerArithmetic.lean:26` | The exact floor sampler for the fixed geometric spacing is `time * 2^scale`. |

The proof unfolds the actual `PhysicalSpacing` and floor sampler, uses the
constructive dyadic numerator/denominator identities
`DyadicTimeRationals.half_power_num` and `half_power_den`, and reduces the
remaining natural-number division by one.

## Verification

Focused monitored check:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 30 \
  --check lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerArithmetic.lean \
  --check-output /tmp/ym-gap-fixed-family-rate-power-arithmetic.olean --status-seconds 30
```

The check completed successfully. The declaration reports only
`{propext, Quot.sound}`; it has no `sorryAx`, classical input, custom axiom,
or `noncomputable` declaration.

## Boundary

The exact fixed rate is already pinned by
`BF4PhysicalMarginalGeometricCompletedFamily.marginalHalfGeometricCompletedFamily_rate`
(`:79`). Combining that rate with this sampler identifies the positive-time
stream arithmetically, but a constructive antitone-tail/variation certificate
for that stream is still open. Raw representative variation, a physical-rate
band, thermodynamic and continuum passage, OS/QFT reconstruction, physical
mass, and the all-group Clay theorem remain open.
