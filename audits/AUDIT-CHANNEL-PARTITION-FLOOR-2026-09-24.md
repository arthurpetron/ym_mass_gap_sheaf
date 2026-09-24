# Original-channel partition floor — 2026-09-24

## Scope

Baseline: `1708203`. This checkpoint proves a positive, computed comparison
between the actual conditional channel norm of the COMPLETE original endpoint
source and the ORIGINAL odd-marginal partition. Its constants depend on nome,
not spatial width, terminal depth, or cutoff past the computed threshold.
It does not prove a centered-variance comparison or a changing-spacing bound.

For fixed `0 < w < 1`, write

```
q = projectedEndpointSource w K width (terminalMessage w K width depth)
F = spectatorBlocks width face
b_c = familyProject F (q*c)
A = sum_c lambda_c H[b_c^2] = familyChannelQuadratic N w K F q
Z = H[marginalWeight w K width depth]
C = endpointRelativeCap w
M = endpointChannelFloorExponent w >= 48*C^2
rho = endpointChannelHeatFloor w = (1/2)*w^M > 0.
```

The proved comparison is `rho*A <= Z`. The coefficients `lambda_c` are
nonnegative; the channel polynomials `b_c` can be signed. All spatial action
and terminal factors remain in `q`. No stationary-source, degree-cutoff,
channel-positivity, or new analytic premise is introduced.

## Checked mathematical chain

1. **Scalar first moment.**
   `SU2HeatProductFirstMomentFloor.productAttenuation_firstMoment_floor`
   (`lean/YMGap/Continuum/SU2HeatProductFirstMomentFloor.lean:114`) proves
   `w^M*(M-totalCasimir ds) <= M*productAttenuation w K ds` for `M <= K`.
   If total Casimir is at most M, each label survives the cutoff and the
   product is the corresponding power of w. Otherwise the left side is
   nonpositive. `totalCasimirNat` at line 25 returns the integer exponent;
   `totalCasimir_eq_ofNat` at line 30 checks its rational identification.

2. **Existing signed-source paths.**
   `SU2QuaternionFirstMomentHeatFloor.fullProductPairing_firstMoment_floor`
   (`lean/YMGap/Continuum/SU2QuaternionFirstMomentHeatFloor.lean:205`) sums
   that inequality against the existing nonnegative FULL diagonal path
   pairings. The zeroth moment is `H[p*p]`; the first is the unattenuated
   `pairCasimir`; the attenuated sum is the actual full `productMap` pairing.
   No joint projector or source positivity is assumed. The scalar extraction
   `firstMoment_half_floor` at line 224 uses `E <= D*A` and `2*D <= M` to
   retain half the unattenuated mass, without division.

3. **Exactly four actual links.**
   `SU2QuaternionChannelAngularContraction.pairCasimir_channel_eq_active`
   (`lean/YMGap/Continuum/SU2QuaternionChannelAngularContraction.lean:336`)
   exposes the exact complementary-block identity previously internal to
   the contraction proof; the old inequality retains its statement.
   `BF4ExactSlabFixedSpatialEndpointChannelFirstMoment.projectedEndpoint_plaquetteChannel_firstMoment_le`
   (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointChannelFirstMoment.lean:83`)
   combines it with the actual conditional angular bound to prove
   `E_channel <= 24*C^2*A`. Four distinct face links each contribute six
   angular planes. `padded_plaquetteChannel_firstMoment_le` at line 136
   discharges activity from strict lattice padding.

4. **ORIGINAL partition, not replacement normalization.**
   `BF4ExactSlabFixedSpatialEndpointChannelHeatFloor.projectedEndpoint_channelNorm_le_originalPartition`
   (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointChannelHeatFloor.lean:142`)
   uses `oddMoment_eq_plaquette_channels`
   (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPassiveChannels.lean:78`)
   with insertion one to identify `Z` with the SAME channel-summed full heat
   pairing. It then applies the first-moment floor and actual energy cap.
   `padded_channelNorm_le_originalPartition` at line 203 constructs the
   activity guard for a face in any strictly smaller base box.

The public data `endpointChannelFloorExponent`, `endpointChannelHeatFloor`,
and `endpointChannelHeatCutoff` are defined at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointChannelHeatFloor.lean:56`,
`:59`, and `:62`. The cutoff is `max (endpointRelativeCutoff w) M`.
`endpointChannelFloorExponent_sufficient` at line 68 proves the required
integer cap; `endpointChannelHeatFloor_positive` at line 82 proves positivity.
These are computable definitions, not existentially hidden constants.

## Actual original-energy consumer

`BF4ExactSlabFixedSpatialEndpointEnergyPartitionBound.endpointEnergyPartitionCoefficient`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointEnergyPartitionBound.lean:54`)
computes `kappa(w)=32*(1-w)+960*(1-w)^2`.
`geometricSourceCost_le_four_rawSourceMass` at line 107 subtracts the
nonnegative square `H[(q*f)^2]`, hence bounds the geometric source cost by
four times its mass for every supported signed source.
`passiveGeometricBudget_le_channelQuadratic` at line 146 sums this bound with
the positive Gram coefficients: `B_channel <= kappa(w)*A`.

`padded_endpoint_energy_le_originalPartition` at line 179 composes the
EXISTING original-energy bound `2*E_original <= B_channel` with this estimate
and the new floor, giving

```
2*rho(w)*E_original <= kappa(w)*Z.
```

Its guards explicitly include `2 <= K`, `headCutoff w <= K`,
`endpointChannelHeatCutoff w <= K`, `base < width`, and
`face in spatialFaces base`, in addition to `0 < w < 1`. Both sides retain
the same original terminal message and marginal. No division or replacement
normalization occurs. The original sharper geometric/signed budgets remain
available; this coarser corollary does not replace them for scaling analysis.

## Verification boundary

All six final checks passed through `scripts/safe_lean_build.py --jobs 1`
with `--check-worker-limit-gib 2`, the unchanged 12 GiB reserve, default
elaboration limits, and serialized execution. The first listed check was
completed in the preceding proof turn; its source was unchanged afterward.

| File (under `lean/YMGap/Continuum/`) | Final log in `/tmp/` | Printed gates |
|---|---|---|
| `SU2QuaternionChannelAngularContraction.lean` | `ym-gap-channel-casimir-active-identity-check-1.log` | 12 |
| `SU2HeatProductFirstMomentFloor.lean` | `ym-gap-product-first-moment-floor-check-3.log` | 5 |
| `BF4ExactSlabFixedSpatialEndpointChannelFirstMoment.lean` | `ym-gap-endpoint-channel-first-moment-check-2.log` | 3 |
| `SU2QuaternionFirstMomentHeatFloor.lean` | `ym-gap-quaternion-first-moment-floor-check-3.log` | 2 |
| `BF4ExactSlabFixedSpatialEndpointChannelHeatFloor.lean` | `ym-gap-endpoint-channel-heat-floor-check-2.log` | 8 |
| `BF4ExactSlabFixedSpatialEndpointEnergyPartitionBound.lean` | `ym-gap-endpoint-energy-partition-check-3.log` | 4 |

These 34 printed dependencies are empty or subsets of `{propext, Quot.sound}`.
Failed development checks exposed namespace, equality-transport, a parenthesis,
definitional-unfolding, multiline-parser, and zero-exponent reduction errors;
the final checks replace those failures.
No safety stop, raised limit, new `sorry`, axiom, or analytic input. No full-root
build, full-tree audit, guard, or progress-metric run was performed.

## Remaining causal obstruction

This is a norm-to-ORIGINAL-partition estimate, not a norm-to-centered-variance
estimate. Centering uses the SAME global first and second moments; signed
channels cannot be treated as individually positive probability measures.
Useful control of the complete signed energy against that centered variance
on a justified changing-scale observable family remains unproved.

There is already a finite positive centered-variance floor:
`BF4ExactSlabFixedSpatialOddLocalVariance.odd_variance_floor` and
`.odd_marginal_variance_floor`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOddLocalVariance.lean:161`,
`:174`) use the nome-only `starRatio w` for the SAME original marginal.
The missing input is therefore not an arbitrary positive finite variance
bound. A coarse fixed-nome energy/variance bound obtained by combining these
estimates would not by itself supply the small loss needed for survival on a
justified physical scaling family.

Source review also retains the actual dependence of the new floor:
`JacobiShiftedRelativeSlope.budget`
(`lean/YMGap/Continuum/JacobiShiftedRelativeSlope.lean:33`) uses
`HKConvGen.geoTailBase (HKConv.Cstar w) (w*w) 0`;
`geoTailBase` (`lean/YMGap/Continuum/HeatKernelConvGen.lean:335`) includes
the reciprocal of `1-w*w`. `JacobiHeatRelativeAngularBound.relativeCost`
(`lean/YMGap/Continuum/JacobiHeatRelativeAngularBound.lean:46`) multiplies
that budget by the local coefficient, before the cap is squared in the new
first-moment estimate. This checkpoint proves no useful changing-nome bound
on that chain. The sharper averaged source estimate is not supplied by
merely renaming the existing local cap or reusing an unrelated kernel-score
variance bound.

The explicit nome dependence of `C`, `M`, and `rho` is retained. No lower
bound surviving changing nome, spacing, or physical time is claimed. ONE-state
continuum survival, EVERY-state scaling control, SAME thermodynamic/continuum
limits, full QFT/Yang--Mills/UV identification, Hamiltonian/mass calibration,
and every compact simple group remain OPEN. Canonical node A03 stays `[ ]`;
the chart's labels, geometry, and all status markers are unchanged.
