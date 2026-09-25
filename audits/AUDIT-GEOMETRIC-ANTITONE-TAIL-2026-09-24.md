# Audit: geometric antitone tail control

## Scope

For any rational base `0 < r < 1`, the exact geometric variation stream
`r^scale` now has a representation-invariant, order-antitone tail modulus.
The cutoff uses `qCeilNat` on a reciprocal tolerance rather than an
unreduced numerator, so equivalent rational tolerances receive compatible
cutoffs.

## Declarations

| declaration | location | result |
|---|---|---|
| `geometricTailRate` | `lean/YMGap/Continuum/GeometricAntitoneTailControl.lean:31` | Explicit `qCeilNat` cutoff for `H * r^N <= epsilon`, with `H = 1/(1-r)` supplied by the caller. |
| `geometricTailRate_antitone` | same file `:37` | The cutoff is antitone in the positive tolerance. |
| `geometricTailRate_bound` | same file `:52` | The cutoff satisfies `H * r^N <= epsilon`. |
| `geometricPowerTailControl` | same file `:105` | Inhabited `AntitoneTailControl (fun n => r ^ n)`. |

The finite-tail estimate reuses the existing constructive geometric-series
bound `HKConvGen.geoTailBase_series_le`; no analytic summability assumption is
hidden in a proposition.

## Verification

Monitored check of the module succeeded and emitted an importable `.olean`.
All four declarations report only `{propext, Quot.sound}`. No `sorryAx`,
classical input, custom axiom, `native_decide`, or `noncomputable` declaration
is used.

## Boundary

This is a generic scalar tail certificate. It does not identify a physical
exponential or provide raw moving-cube representative variation, a
physical-rate band, a thermodynamic/continuum passage, OS/QFT reconstruction,
physical mass, or the all-group Clay theorem.
