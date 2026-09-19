# Same-operator Wilson range approximation checkpoint

## Scope

This checkpoint records the bidirectional join from the backward requirement
of a same-operator approximate-preimage interface to a forward construction
on the current completed SU(2) Wilson carrier. It is fixed-spacing data only.

## Forward declaration

`lean/YMGap/Continuum/BF4WilsonSpatialUnionRangeApproximation.lean`

- `evenOrbitSum` constructs the finite vector
  `sum_{k<n} T^(2*k) x` using the existing `completedAdd`, `completedTime`,
  and `completedZero`.
- `evenOrbitSum_sub_twoStep` proves
  `(I - T^2) (sum_{k<n} T^(2*k) x) = x - T^(2*n) x`
  on the same `UnionCompletion` carrier.
- `evenOrbitSum_error_bound` identifies the actual approximation error with
  `T^(2*n)x` and bounds its squared norm for an existing vacuum-complement
  vector by the existing `norm_decay` at exponent `2*n`.

The rate is explicit: `q = twoStepRate w hd`. No inverse, spectral theorem,
choice, auxiliary transfer, or continuum/spacing hypothesis is introduced.

## Verification boundary

Command:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/BF4WilsonSpatialUnionRangeApproximation.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonSpatialUnionRangeApproximation.olean \
  --log-file /tmp/ym-range-approx-20260918e.log
```

Result: passed. The three public declarations printed only
`{propext, Quot.sound}`. No `sorryAx`, `Classical.*`, `native_decide`, or
new axiom appears. Log SHA-256:

`5d334959cde2e4518261353659d82dfcdc9137c6e1c13cd648049602d73498f0`.

The full root, full-tree build, axiom audit, guard and progress runs were not
performed. The result does not supply strict density of strictly-past
observables, a completed spectral gap beyond existing fixed-spacing decay,
changing-spacing control, physical mass calibration, continuum survival, or
the Clay theorem.
