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
- `evenOrbitSum_modulus` packages the explicit cutoff
  `geometricCutoff (q*q) (normCap X) epsilon`, and
  `evenOrbitSum_error_small` proves the resulting late-tail estimate for
  every `n` above that cutoff.
- `evenOrbitSumCauchy` and `evenOrbitSumCauchy_pin` retain the preimage as
  supplied Cauchy data and identify its quotient with the finite sum.
- `evenOrbitSum_range_data` returns the same-completion approximate-preimage
  witness, with vacuum-complement orthogonality retained as an input.
- `evenOrbitResidual` names the actual `(I-T^2)` defect, and
  `evenOrbitResidual_kernel` proves its kernel is trivial on the completed
  vacuum complement.
- `evenOrbitSumStage` and `evenOrbitSumStage_pin` retain the finite geometric
  preimage as a strict `Stage`, and `evenOrbitStage_error_small` transfers the
  explicit modulus to that finite-stage carrier.
- `evenOrbitStage_range_data` packages the cutoff, strict stage preimage, and
  error proof as one dependent witness.
- `evenOrbitResidual_center` proves that the defect commutes with the existing
  same-carrier vacuum-centering projection.
- `evenOrbitCentered_range_data` applies the range certificate to the existing
  center of any supplied representative, retaining the same carrier and no
  uncentered-decay claim.

The rate is explicit: `q = twoStepRate w hd`. No inverse, spectral theorem,
choice, auxiliary transfer, or continuum/spacing hypothesis is introduced.
The modulus is representative-dependent through the existing `normCap X`;
it is a fixed-spacing consumer contract, not a uniform-in-observable or
continuum modulus.

## Verification boundary

Command:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/BF4WilsonSpatialUnionRangeApproximation.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonSpatialUnionRangeApproximation.olean \
  --log-file /tmp/ym-range-approx-20260918aa.log
```

Result: passed. The seventeen public declarations printed only
`{propext, Quot.sound}`. No `sorryAx`, `Classical.*`, `native_decide`, or
new axiom appears. Log SHA-256:

`d1bcad0d3974bed87e55ae1b35205fc22ec545c2144a55ee7d9314b1bfd456aa`.

The full root, full-tree build, axiom audit, guard and progress runs were not
performed. The result does not supply strict density of strictly-past
observables, a completed spectral gap beyond existing fixed-spacing decay,
changing-spacing control, physical mass calibration, continuum survival, or
the Clay theorem.
