# Positive-source low-heat-mode scaling obstruction

2026-10-01 UTC. Kernel-checked generic finite-chain route pruning, NOT a
Wilson terminal-source or Yang--Mills counterexample. No Clay-facing field
has been discharged, changed or weakened.

## Proposition tested

Does positive symmetric Markov heat, contraction, positive quadratic form,
a strictly positive source and an exact low bare eigenmode imply a bound
`normalizedEnergy <= C*h*OWNVariance`, with C independent of the source and h?
The computed two-state family refutes this inference for every nonnegative
rational C. This is distinct from the earlier fixed-nome SU(2) diagnostic in
`audits/AUDIT-POSITIVE-SOURCE-VARIANCE-FENCE-2026-09-24.md`: it rules out a
source-uniform O(h) coefficient, not just one proposed bare-loss coefficient.

## Actual finite objects and normalization

All declarations below are in
`lean/YMGap/Continuum/PositiveSourceHeatModeScalingObstruction.lean`, namespace
`YMGap.Continuum.PositiveSourceHeatModeScalingObstruction`.

The SAME counting pairing on two states is used throughout. For `0<h<=1/4`,

    P_h = [[1-h, h], [h, 1-h]], q_h = (1,h^2), f = (1,-1).
    W = q_h * P_h(q_h), Z = sum W.
    mean = sum(W*f)/Z, OWNVariance = sum(W*f^2)/Z - mean^2.
    rawEnergy = sum(W*f^2) - pair(q_h*f, P_h(q_h*f)).
    normalizedEnergy = rawEnergy/Z.

The original bridge weight is `q*P(q)`, not `q^2` or an independently
supplied variance proxy. Definitions: `pair` at line 36, `source` at line 40,
`heat` at line 41, `weight` at line 177, `mass` at line 178, `energy` at
line 181, `varianceNumerator` at line 183, `normalizedMean` at line 285,
`normalizedVariance` at line 288 and `normalizedEnergy` at line 292.
Replacing counting measure by uniform probability scales rawEnergy and Z
equally and leaves both normalized quantities unchanged.

| Checked declaration | Module:line | Exact role |
| --- | --- | --- |
| `heat_markov`, `heat_unit` | `lean/YMGap/Continuum/PositiveSourceHeatModeScalingObstruction.lean:71`, `:77` | Nonnegative heat coefficients, row sum one and fixed unit. |
| `heat_selfAdjoint` | `lean/YMGap/Continuum/PositiveSourceHeatModeScalingObstruction.lean:83` | Symmetry for the SAME counting pairing. |
| `heat_contraction` | `lean/YMGap/Continuum/PositiveSourceHeatModeScalingObstruction.lean:99` | Norm contraction for EVERY two-state vector when 0<=h<=1. |
| `heat_positive` | `lean/YMGap/Continuum/PositiveSourceHeatModeScalingObstruction.lean:125` | Positive quadratic form for EVERY vector when 0<=h<=1/2. |
| `heat_probe`, `source_positive` | `lean/YMGap/Continuum/PositiveSourceHeatModeScalingObstruction.lean:156`, `:170` | Exact P_h f=(1-2h)f and strict pointwise source positivity. |
| `energy_pin`, `varianceNumerator_pin` | `lean/YMGap/Continuum/PositiveSourceHeatModeScalingObstruction.lean:226`, `:247` | Exact rawEnergy=4h^3 and varianceNumerator=4AB. |
| `mass_positive`, `varianceNumerator_positive` | `lean/YMGap/Continuum/PositiveSourceHeatModeScalingObstruction.lean:276`, `:280` | Positive actual mass and variance numerator on 0<h<=1/4. |
| `normalizedVariance_cleared`, `normalizedVariance_positive` | `lean/YMGap/Continuum/PositiveSourceHeatModeScalingObstruction.lean:297`, `:324` | Z^2*OWNVariance equals the actual numerator; OWNVariance is positive. |
| `half_variance_energy_floor` | `lean/YMGap/Continuum/PositiveSourceHeatModeScalingObstruction.lean:340` | (1/2)*varianceNumerator <= Z*rawEnergy, i.e. normalizedEnergy >= OWNVariance/2. |
| `counterStep_bounds` | `lean/YMGap/Continuum/PositiveSourceHeatModeScalingObstruction.lean:404` | Computed h=1/[4(C+1)] satisfies 0<h<=1/4 and C*h<=1/4. |
| `counterStep_bound_false` | `lean/YMGap/Continuum/PositiveSourceHeatModeScalingObstruction.lean:417` | Refutes the cleared proposed bound. |
| `counterStep_normalized_bound_false` | `lean/YMGap/Continuum/PositiveSourceHeatModeScalingObstruction.lean:468` | Refutes the bound on ACTUAL normalized energy and OWN variance. |
| `counterexample` | `lean/YMGap/Continuum/PositiveSourceHeatModeScalingObstruction.lean:480` | Returns the computed h and its positive-variance/refutation laws as Type-level sigma data. |

Here `A=1-h+h^3`, `R=1+h-h^2` and `B=h^3*R` are the private factors.
The bridge components are A,B; Z=A+B and the mean is (A-B)/Z. The lower
ratio bound follows by R<=2 and A*R<=2(A+B). The computed heat step then
contradicts the proposed upper bound because OWNVariance is strictly positive
and C*h<=1/4<1/2. No limit theorem is claimed or needed.

## Causal consequence for the original route

The actual source is defined by
`BF4ExactSlabFixedSpatialProjectedSourceEnergy.projectedEndpointSource`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedSourceEnergy.lean:77`):
the fringe projection of the original spatial weight times its terminal
iterate. `energy_projected_source` at line 102 and
`oddMoment_projected_source` at line 117 preserve original energy and moments
on their supported/fringe-independent tests. The example above is NOT
identified with that terminal source or a gauge-theory measure.

The open estimate's existing recipient is
`BF4ExactSlabFixedSpatialFamilyVarianceTaylor.padded_family_energy_variance`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceTaylor.lean:67`):

    E = 12*(1-w)*OWNVariance + varianceRemainder.

The complete signed centered-square recipient is
`BF4ExactSlabFixedSpatialCenteredRemainderSquare.padded_family_energy_centered_square`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredRemainderSquare.lean:292`).
The pruned shortcut is to control this interacting ratio uniformly over
positive sources using only the observable's bare heat eigenpin. That pin
does not give an eigenpin or heat-band bound for `q*(f-ownmean)`. The next
mathematical task remains original terminal-source control of the JOINT
signed energy/correction versus its OWN variance on a justified changing
family. A source-specific proof is not refuted. Uniform source contrast is
not asserted to be a necessary condition for every possible proof.

Changing-scale original bond-pairing compatibility, physical spacing/rate
calibration, a spacing-matched lower generator bound, nonzero continuum
survival, full same-theory QFT, every compact simple group and Clay stay OPEN.
The supporting obstruction leaves every exact canonical chart claim unchanged.

## Verification boundary

Final source SHA-256:
`0de7b2949bd0035df8d6ffc4df574bd30f598d02b7425e0f7a169c2e9bc2da37`.

Focused command from the repository root:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/PositiveSourceHeatModeScalingObstruction.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/PositiveSourceHeatModeScalingObstruction.olean --log-file /tmp/ym-positive-source-heat-mode-verified-20261001.log
```

Exit 0. Final log SHA-256:
`011e8368635177787db07e7d10afc0ebf9af6ac525b03d5370308474177ba89f`.
Eighteen printed gates: seventeen `{propext, Quot.sound}`, and
`source_positive` only `{propext}`. No error, warning or `sorryAx` in the
final log. No new sorry, axiom, classical shortcut, native checker, erased
witness, analytic premise or frontier change. Sol independently checked the
mathematics and actual-vs-model boundary; Luna checked source/log/hash/gates.

Earlier first/second/final/accepted-named draft logs failed and are NOT
verification evidence. The third-named log passed an earlier source, not this
final frozen source. Missing imports, scalar expression typing and a shadowed
heat-step variable were repaired; compiler limits were not raised. Only the
`verified` log above certifies the final file.

One capped compiler, 20-GiB worker ceiling, 12-GiB OS reserve and continuous
safety telemetry. A semantic root import was added, but the full root/tree
build, axiom audit and guard were NOT run. CI and canonical chart unchanged.
