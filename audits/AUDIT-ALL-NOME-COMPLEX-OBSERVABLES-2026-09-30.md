# Equal-time observables on the existing all-nome complex carrier

Date: 2026-09-30 UTC. Parent baseline: `0987eef`.

## Mathematical scope

The real time-zero Wilson multipliers commute on the SAME literal-width
all-nome reflected completion. Their componentwise action on the existing
complexification is complex-linear, symmetric for its sesquilinear inner
product, and obeys the original spin-only squared-norm bound. The original
unit creates the original fundamental loop state; its complex time
correlation is the original real lag moment with zero imaginary part.

The complex carrier is exactly `Completion x Completion`, already defined
by `ComplexCarrier` in
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexification.lean:285`.
The inner product's diagonal real part is the sum of the two real squared
norms (`inner_diagonal`, same module, line 324). Adding their multiplier
bounds therefore keeps `characterBound(spin)` unchanged. This is a
squared-norm cap, not that number asserted as a sharp operator norm.
The bound is independent of nome, width and state; the underlying objects
still depend on nome and width. It is not a coupling-uniform spectral gap.

The real commutation argument uses source-polynomial multiplication and
the preceding literal-width `embedWindow_eq_of_source_identity`, not a
small-nome spatial-union identity. The complex argument then uses the
actual real operations componentwise. Supplied constructive-real scalar
moduli remain arguments to complex scalar multiplication. No quotient
representative or scalar modulus is selected.

## Actual consumers and boundaries

`BF4WilsonAllNomeComplexObservables.complexMultiply` is an actual map on
the existing carrier. Its `complexMultiply_smul`,
`inner_multiplier_balance`, `inner_multiplier_bound` and
`complexMultiply_comm` establish its linear, symmetric, bounded and
equal-time commuting laws. `complexMultiply_unit_lag` pins it to the
original action's correlation, via
`BF4WilsonAllNomeTimeZeroVacuum.completedMultiply_unitState_lag`.

| Declaration | Source |
| --- | --- |
| `completedMultiply_comm` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeZeroCommutation.lean:91` |
| `completedInner_multiplier_product_balance` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeZeroCommutation.lean:100` |
| `complexMultiply` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexObservables.lean:48` |
| `complexMultiply_smul` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexObservables.lean:72` |
| `inner_multiplier_balance` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexObservables.lean:79` |
| `inner_multiplier_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexObservables.lean:84` |
| `complexMultiply_comm` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexObservables.lean:96` |
| `inner_multiplier_product_balance` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexObservables.lean:100` |
| `complexMultiply_unit`, `complexMultiply_unit_lag` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexObservables.lean:106`, `:112` |

This supplies further fixed-width J02 observable structure. It does NOT
assert commutation with time evolution, a full observable net, continuum
spacelike locality, continuous physical time, or full QFT reconstruction.
It does not close A03, full J02, scaling or any same-theory Clay endpoint.
The canonical chart block is unchanged.

## Analytic review: no signed-bound closure

The parallel review found no new useful premise-free signed lower bound.
`residual_pair_decomposition` in
`lean/YMGap/Continuum/BF4ExactSlabBlockPredictionCovariance.lean:168`
retains the positive prediction-defect square minus the actual prediction
covariance. Its original-generator consumer remains
`conditionalGenerator_square` in
`lean/YMGap/Continuum/BF4ExactSlabSignedNeighborEnergy.lean:68`.
A collective covariance estimate relative to those defects and the same
energy is still missing. An exact-zero mixed-feature premise merely gives
a conditional consequence and was not added as another wrapper.

Scalar square-root polynomials likewise do not provide an all-nome
continuous-time construction. `rootAction_square` in
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicSquareRootAction.lean:101`
belongs to the distinct fixed-nome thermodynamic completion; its header
explicitly leaves geometric one-step identification and time injectivity
open. It was not transferred to the present carrier by name alone.

## Verification

Both modules passed focused serialized checks via
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20`, with
their individual `--check` sources and `--check-output` paths. All 16
printed gates reported only `{propext, Quot.sound}`. The first checks
found namespace/notation issues in commutation and a final reflexivity
step in the complex correlation pin; these were repaired. Final checks
took approximately 4.9 and 2.9 seconds. No job survived its initial call,
so no manual status poll was needed; automatic safety monitoring remained
active. No new sorry, axiom or analytic premise was added. No broad build,
full audit or guard ran.

Luna implemented real commutation; root implemented the complex consumer
and ran all verification. Sol reviewed the actual carrier, norm convention
and original-correlation pin, and separately reviewed the signed frontier.
