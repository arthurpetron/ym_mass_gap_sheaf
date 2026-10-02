# Full retained-product signed quartic bound

The original one-link signed Schur bound now extends to the complete selected
product on the original doubled Haar carrier. The entire endpoint/source may
depend on every retained lower coordinate, including spectators and inactive
links. Its coefficient is independent of width, source degree and every later
guarded cutoff. Its cost is still RAW Haar source square, not OWN interacting
variance; no filtered-slope or continuum bound follows from this result alone.

## Literal kernel and computed marginals

`quarticProduct`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatQuarticSchur.lean:90`, is

    P = defect(scalarAt i (n+i))^2 * productHeat n q K (i::ids).

All selected factors are retained exactly once. The support declaration is
`quarticProduct_supported` at line 94. `quarticProduct_certificate` at line
102 constructs the actual original square certificate, for `0<q<1` and
`headCutoff q<=K`.

`quarticProduct_upper_marginal` at line 280 and
`quarticProduct_lower_marginal` at line 295 compute BOTH actual marginals:

    H_(2n)[P * f(upper)] = d(q)*H_n[f],
    H_(2n)[P * f(lower)] = d(q)*H_n[f],
    d(q) = 5 - 8*q^3 + 3*q^8.

Their explicit guards are `ids.Nodup`, `i notin ids`, `i<n`, every selected
index less than n, `2<=K`, and actual n-link support of f. The proof peels
other distinct heat factors only at their independent INTEGRATED endpoints.
Generic pair-character vacuum transports the entire remaining insertion
through proved carrier exchanges. No source coordinate is removed, and no
source independence or orthogonal source resolution is assumed.

## Signed bound and precise cost

`quarticProduct_signed_schur`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatQuarticSchur.lean:351`, proves

    H_(2n)[P*a(lower)*a(upper)] <= d(q)*H_n[a^2]

for EVERY supported n-link signed polynomial a. Kernel-certificate positivity
on the actual endpoint-difference square and both computed marginals prove
the inequality without division or an operator-PSD assumption.

`quarticProduct_signed_budget` at line 364 gives

    H_(2n)[P*a(lower)*a(upper)] <= 60*(1-q)^2*H_n[a^2],

using `zeroCoeff_le_sixty`,
`lean/YMGap/Continuum/SU2HeatQuarticLowCoefficients.lean:216`.
`source_quarticProduct_signed_budget` at line 375 substitutes the whole
actual product `source*f` and pays exactly

    60*(1-q)^2 * rawSourceMoment n source (f^2).

The coefficient has explicit nome dependence. It is independent of n, the
number of selected factors, source degree, and K on the stated guarded tail.
This is NOT uniformity of the interacting variance or of a physical gap.

## Backward identification and the missing analytic join

The original odd marginal uses
`endpointSource`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean:47`,
with `terminalMessage n` and the actual `activeBlocks` kinetic list.
`oddMoment_projected_source`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedSourceEnergy.lean:117`,
pins inactive-independent insertions to the original selected sourceMoment
and its full-product fringe projection. The actual odd pair is `(n+1,n)`;
`oddVariance`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceWard.lean:87`,
retains its own first/second moments and the SAME original partition.

The square-specific alternatives are the actual passive-channel sources.
`oddMoment_eq_active_square_channels` and
`oddMass_eq_active_square_channels`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquarePassiveChannels.lean:173` and
`:190`, aggregate their moments and partition. Center after aggregation;
no channelwise OWN-centering law is supplied.

`rawMoment_difference_pin`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatMomentDefect.lean:123`,
retains the explicit signed heat-loss difference between RAW cost and the
interacting sourceMoment. The new bound does not estimate that difference
relative to OWN variance. Nor does it identify its one-step quartic kernel
with the literal radius-two signed filtered observable
`filteredExpression`,
`lean/YMGap/Continuum/BF4WilsonAllNomeFilteredIncrement.lean:37`.
The exact three-slice noise-minus-drift fold and a useful same-partition
reserve/filtered budget remain the next mathematical work, not assumptions
to be hidden in another interface.

## Verification and boundary

The final SECOND focused monitored check exited zero with eight public gates.
Kernel data is axiom-free; the other seven use only `{propext,Quot.sound}`.
No final warning/error occurs. Independent mathematical review passed.
The first check rejected missing namespace opens and a nested tactic; local
repairs changed neither statements nor resource limits.

| Artifact | SHA256 |
| --- | --- |
| `SU2QuaternionProductHeatQuarticSchur.lean` | `f0d9e44d9e77992cf5ef76815f5755ac1697e3e812926ce2faf3a3b59ae16527` |
| `/tmp/ym-product-quartic-signed-schur-20261002-second.log` | `12bbae45bded9cadc3dbe9880c9d6010d6bb2c85ed56fda60fa1cf023666c428` |

One worker, explicit 20-GiB ceiling and 12-GiB OS reserve. Fresh preflight
showed 85 percent pressure-free memory and zero swap. Root import registered,
NOT aggregate-checked. No new sorry, axiom, classical shortcut, weakened field,
surrogate source, broad audit, CI change or exact displayed chart change.
Useful scaling-family costs, spatial/spacing control, continuum survival,
physical calibration, full SAME QFT, every compact simple group and Clay
remain OPEN.
