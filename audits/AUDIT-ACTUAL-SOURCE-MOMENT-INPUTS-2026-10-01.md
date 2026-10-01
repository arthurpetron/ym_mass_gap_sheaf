# Actual source moments and the surviving analytic input

Date: 2026-10-01 UTC. This is a source review, not a new proof of
concentration or physical scaling. The two retained-square energy estimates
do not remove the need to control the actual interacting variance. In
particular, neither terminal positivity nor a free boundary-face identity
supplies concentration for the active plaquette used by the energy bound.

## What the existing declarations supply

`BF4ExactSlabFixedSpatialTerminalBracket.terminalMessage`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalBracket.lean:118`)
and `BF4ExactSlabFixedSpatialDirichletWindow.terminalMessage_next`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:57`)
give the actual finite recursion. The former module also supplies support,
a positive polynomial certificate and positive mass. This is not a stationary
equation for the complete projected source q.

`BF4ExactSlabFixedSpatialFringeFaceTransfer.spatial_fringe_face_moment`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeFaceTransfer.lean:133`)
requires an exclusive `FringeFaceLeaf` and independence of the remaining
source from its link. It does not apply to an arbitrary active face.
`BF4ExactSlabFixedSpatialPlaquetteKinetic.plaquette_active_after_padding`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteKinetic.lean:54`)
makes the energy estimate's padded face fully active. No source-independence
premise for that face is supplied by the terminal recursion.

`BF4ExactSlabFixedSpatialEndpointRelativeBound.projectedEndpointRelativeBound`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointRelativeBound.lean:96`)
controls angular derivatives of the complete projected source. It is not an
estimate that its normalized radial defect tends to zero.
`BF4ExactSlabFixedSpatialChannelGeometricContraction.channelGeometricCost_le_raw`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChannelGeometricContraction.lean:225`)
bounds the channel defect by the raw defect; it does not bound the latter
by a small multiple of raw source mass.

## The two measures and the variance scale

`BF4ExactSlabFixedSpatialPlaquetteSourceGeometry.rawSourceMass`,
`rawSourceSquare` and `geometricSourceCost`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteSourceGeometry.lean:45`,
`:49`, `:54`) define A=H[q^2], F=H[q^2*f^2] and G=4*A-F.
They use the raw q^2 density.
`BF4ExactSlabFixedSpatialProjectedSourceEnergy.oddMoment_projected_source`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedSourceEnergy.lean:117`)
instead pins the original odd marginal to q*Pq for independent insertions.
These densities cannot be interchanged.

The actual odd-law variance floor is supplied by
`BF4ExactSlabFixedSpatialOddLocalVariance.odd_marginal_variance_floor`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOddLocalVariance.lean:174`).
Its certificate number is `starRatio w`.
`BF4ExactSlabStarVarianceLossObstruction.starRatio_le_defect_power`
(`lean/YMGap/Continuum/BF4ExactSlabStarVarianceLossObstruction.lean:38`)
proves that this number is at most (1-w)^12. This is a ceiling on the
available lower-bound certificate, NOT a ceiling on the actual variance.

`QuaternionHaarDensityVariance.normalized_variance_le_shifted`
(`lean/YMGap/Continuum/QuaternionHaarDensityVariance.lean:189`)
proves that variance in any certified positive density is at most its
second moment about any supplied rational center. Center 2 therefore gives
Var(f)<=E[(f-2)^2] in that SAME density. It supplies no estimate for that
second moment.

A proposed requirement Var_odd(f)>=c*(1-w)*A/Z was rejected during this
review: no declaration supplies it. The following is only a scaling
diagnostic, not a Yang--Mills asymptotic theorem. If a microscopic trace
deficit is of order h=1-w in second moment, its variance can be of order
h^2. An energy ceiling of order h^2 then need not produce a vanishing
energy/variance ratio. Furthermore, raw radial concentration does not even
select the identity branch: at f=-2 the polynomial 4-f^2 vanishes while
(2-f)^2=16. A useful identity-localization argument must control this branch
and the actual odd density separately.

## Consequence for the next proof choice

Do not replace the missing estimate by a new variance lower bound chosen
only to make the existing energy ceiling work. Seek a direct upper estimate
for the complete signed energy relative to the SAME centered variance,
with the observable family and physical time scale specified together.
Raw concentration alone is not that comparison.

Spatially smeared or blocked observables remain candidates, not a proved
necessity or a supplied low-energy family. Signed plaquette combinations
retain the linear Casimir eigenvalue, but their squares contain cross terms;
they cannot inherit the single-plaquette square heat formula without a new
calculation. The existing combined signed Ward/Taylor remainder remains
available and must not be replaced by separate absolute-value budgets.

This review changes the next analytic action, not a canonical proof status.
No Lean file was changed for this review, and no new variance/concentration
theorem or continuum claim is made.
