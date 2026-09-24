# Endpoint coefficient limitation and sharp original-energy bound — 2026-09-24

## Scope

Baseline: `53aadee`. This milestone proves a limitation of the computed
original-channel energy certificate and a sharper, independent upper bound
for the ORIGINAL finite energy. Its existing approximation consumer improves
without changing its modulus. No continuum or canonical goal node closes.

The coefficient limitation is NOT an energy lower bound, a Yang--Mills
counterexample, an optimality claim, or a refutation of source-specific
cancellation. It is finite rational algebra for every `0 < w < 1`.

## Computed coefficient, not actual energy

The previous checkpoint proved `2*rho(w)*E_original <= kappa(w)*Z`, with Z
the ORIGINAL marginal partition. Its scalar definitions are:

- `BF4ExactSlabFixedSpatialEndpointEnergyPartitionBound.endpointEnergyPartitionCoefficient`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointEnergyPartitionBound.lean:54`:
  `kappa(w)=32*(1-w)+960*(1-w)^2`.
- `BF4ExactSlabFixedSpatialEndpointChannelHeatFloor.endpointChannelFloorExponent`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointChannelHeatFloor.lean:56`:
  a computed positive integer M dominating `48*C(w)^2`.
- `BF4ExactSlabFixedSpatialEndpointChannelHeatFloor.endpointChannelHeatFloor`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointChannelHeatFloor.lean:59`:
  `rho(w)=(1/2)*w^M`.

`BF4ExactSlabFixedSpatialEndpointEnergyCoefficientFence.endpointFloorPower_le_gap`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointEnergyCoefficientFence.lean:136`)
proves `w^M<=1-w` for this ACTUAL computed exponent. Below w=1/2, use M>=1.
Above w=1/2, its relative-cap definition gives `M*(1-w)^2>=1`; combine this
with the existing reciprocal Bernoulli bound `(1+M*(1-w))*w^M<=1`.
The proof uses neither logarithms nor a floating-point asymptotic calculation.

`BF4ExactSlabFixedSpatialEndpointEnergyCoefficientFence.sixtyFour_endpointHeatFloor_le_coefficient`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointEnergyCoefficientFence.lean:190`)
then proves `64*rho<=kappa`.
`BF4ExactSlabFixedSpatialEndpointEnergyCoefficientFence.normalizedCoefficient_ge_thirtyTwo`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointEnergyCoefficientFence.lean:213`)
states the division-free consequence:

```
0 < w < 1,   kappa(w) <= 2*rho(w)*delta   ==>   32 <= delta.
```

Thus the small numerator kappa does not supply a small normalized coefficient.
The valid partition floor is unchanged. No conclusion about the size of
ACTUAL energy follows from a lower bound on one chosen upper-bound coefficient.
The finer signed/geometric estimates remain available.

## Stronger original-energy upper bound

`BF4ExactSlabFixedSpatialEnergyNormBound.energy_le_norm`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEnergyNormBound.lean:85`) proves

```
energy w K width (terminalMessage w K width n) f
  <= marginalPair w K width n f f.
```

It assumes only `0<=w` and support of f in the actual quaternion blocks.
There is no `w<1`, late-cutoff, centering or stationary-source premise.
Energy is the original diagonal term minus the original transfer quadratic;
the diagonal is identified with the SAME marginal by private `norm_pin`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEnergyNormBound.lean:55`).
The subtracted quadratic is nonnegative by
`BF4ExactSlabFixedSpatialTransferPositive.transferStep_quadratic_nonnegative`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferPositive.lean:67`).
The diagonal pin uses iterate recursion, not a stationary vacuum equation.
The old factor-two theorem remains unchanged for compatibility.

## Existing approximation consumer

`BF4ExactSlabFixedSpatialCenteredFringeExtraction.centered_error_energy_le_same_tolerance`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFringeExtraction.lean:153`)
uses the sharper bound on the explicitly constructed error
`f-(fringePart+centeredActivePart)`. The existing
`centered_error_norm_le_tolerance`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFringeExtraction.lean:121`)
then gives `E(error)<=epsilon*marginalPair(f,f)` rather than twice this value.
The original `relativeApproximationCutoff`, positive epsilon, actual mean-zero
condition, `0<w<1` and head-cutoff guards are retained. No replacement
approximation or new analytic field is introduced. This is upper error
control, not coercivity of the centered active piece.

## Verification boundary

Three final narrow checks passed through `scripts/safe_lean_build.py --jobs 1`,
with a 2 GiB worker cap, unchanged 12 GiB OS reserve, default elaboration
limits, and serialized execution. The first two checks were completed before
the chart-discussion interruption; their sources were unchanged afterward.

| File under `lean/YMGap/Continuum/` | Final log in `/tmp/` | Printed gates |
|---|---|---|
| `BF4ExactSlabFixedSpatialEnergyNormBound.lean` | `ym-gap-original-energy-sharp-norm-check-1.log` | 3 |
| `BF4ExactSlabFixedSpatialCenteredFringeExtraction.lean` | `ym-gap-centered-fringe-sharp-energy-check-1.log` | 11 |
| `BF4ExactSlabFixedSpatialEndpointEnergyCoefficientFence.lean` | `ym-gap-endpoint-energy-coefficient-fence-check-4.log` | 3 |

All 17 printed axiom dependencies are subsets of `{propext, Quot.sound}`.
Development failures were finite-sum expansion, rational equivalence direction,
addition orientation, a parser parenthesis, and explicit scalar normalization
errors. They were repaired without raising limits. Final passing checks
replace failed development output; no proof hole was added to source.

No safety stop, new `sorry`, axiom, analytic premise, canonical-field change,
full-root build/audit/guard, or progress-metric run. The new semantic import in
`lean/YMGap.lean` is recorded; this is not a fresh root-build claim.

## Causal consequence and remaining input

Do not treat another fixed-nome wrapper around this coarse coefficient as
useful scaling control. The existing survival consumer is
`BF4ExactSlabFixedSpatialJointEnergySurvival.response_floor_of_relative_energy`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointEnergySurvival.lean:112`):
it requires a SAME-state relative energy bound with `n*delta+theta<=1` and
a SAME norm floor. Neither a large certificate coefficient nor the universal
upper bound E<=norm constructs the needed changing-scale excitation.

The next analytic input remains useful control of the COMPLETE actual signed
cost against SAME centered variance on ONE justified scaling family, or a
direct response lower bound on that family. The source-increment correction
in `4E+D=2J` has not been bounded sharply enough for this join. A separate
EVERY-state scaling estimate is still needed for the gap branch.

All SAME thermodynamic/continuum, full Hilbert/OS/QFT/YM/UV, physical time/
Hamiltonian/mass and every-compact-simple-group obligations remain OPEN.
Canonical chart schema 1, snapshot 8 changes evidence only: all labels,
layout, status symbols and proof markers are unchanged; A03 remains `[ ]`.
