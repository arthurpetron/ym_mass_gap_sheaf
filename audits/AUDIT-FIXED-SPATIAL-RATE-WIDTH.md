# Width dependence of the existing all-nome covariance estimate

Date: 2026-09-17 UTC. Base revision: `8d6a89f`.
Scope: constructive proof following the parallel direction audit; not a
repository-wide axiom audit or a physical no-gap theorem.

## Existing estimate and new result

`BF4ExactSlabFixedSpatialInputCovariance.inputCovariance_bracket_bound`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialInputCovariance.lean:121`)
retains the original partition squared. The same partition cancels in
`BF4ExactSlabFixedSpatialSeparatedCovariance.windowRatio_covariance_bound`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeparatedCovariance.lean:95`).
The resulting envelope is `4*cp*cq*mixRate(w,width)^separation`, independent
of the late heat cutoff and boundary lengths, but not of spatial width.

`kineticFloor` and `kineticCap`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSandwich.lean:57`, `:61`)
raise `headFloor` and `prefixCap` to the number of actual temporal faces.
`mixFraction` is their ratio and `mixRate` is one minus that ratio
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferMixingRate.lean:81`, `:110`).
The already proved `headFloor_le_oneThirtySecond`
(`lean/YMGap/Continuum/BF4ExactSlabSharedWindowFloorBound.lean:46`) and
`prefixCap_ge_one`
(`lean/YMGap/Continuum/BF4ExactSlabStarRateObstruction.lean:32`) therefore
imply a geometric upper bound on this computed margin.

New declarations, all in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRateWidthObstruction.lean`:

- `width_le_temporalFaces_length:37`: the injection
  `i -> ((i,0,0,0),p03)` supplies at least width distinct temporal faces.
- `mixFraction_le_face_power:59`: margin at most `32^(-faceCount)`.
- `mixFraction_le_width_power:74`: margin at most `32^(-width)`.
- `widthModulus:82` and `mixFraction_le_epsilon:84`: a tolerance-dependent
  threshold valid for every rational nome `0<w<1`.
- `one_sub_epsilon_le_mixRate:97`: this computed rate approaches one.
- `violatingWidth:106` and `rate_not_le_at_violatingWidth:108`: return
  a positive width where any proposed common q<1 fails to bound the rate.
- `no_width_uniform_computed_rate:132`: no such common strict rate bounds
  this formula at every positive width, even at a fixed nome.

## Consequence for the plan

Direct spatially uniform promotion USING THIS COMPUTED RATE is excluded.
The theorem supplies no lower bound on actual correlations or the optimal
spectral radius. It does not refute a better all-nome estimate. In particular,
the distinct small-nome bound
`BF4WilsonSpatialUnionCompletedGap.completed_twoStep_form_gap`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionCompletedGap.lean:153`) is unchanged.

The live plan now keeps both limitations visible: the small-nome estimate
does not enter the existing AF chart, while this all-nome estimate does not
give a common strict width-uniform rate. A stronger original-action estimate,
with the required spatial and changing-scale control, remains unproved.
Algebraic cancellation is already available; a proposed two-copy difference
identity is deferred until a concrete analytic argument needs it.

Full gauge-observable coverage, canonical reflected OS/scalar compatibility,
continuous time and generator, same-theory QFT axioms, finite positive physical
mass, continuum nontriviality and all compact simple groups remain open.
No canonical frontier statement was changed in this increment.

## Verification

- Process preflight: no competing Lean/Lake/test/runner process; swap
  6797.19 MiB, unchanged from the preceding recorded baseline.
- One monitored focused check with one worker and a 20 GiB worker ceiling
  passed on its first attempt, with no warnings or errors.
- All 10 public gates passed within `{propext, Quot.sound}`. `marginBase`,
  `widthModulus` and `violatingWidth` have empty axiom sets.
- Log: `/tmp/ym-rate-width-obstruction-20260917.log`.
- Log SHA-256:
  `2d5d9beeb7dc77b48742edd60bd621b8e0407bed69ebcc1b6acca4a717352fc8`.
- Independent read-only source review checked the inequality directions,
  constructive violating width and restricted interpretation; no defect found.
- Root import added; root/full-tree/full audit/guard not run. CI remains
  manual-only. No sorry, axiom, existing analytic guard or safety limit changed.
