# A uniform loop norm cap and its actual response consumer

Date: 2026-09-30 UTC. Parent baseline: `37bf591`.

## Mathematical argument

Let B be the existing all-nome, literal-width completed reflected form, U its
normalized unit, M the existing fundamental Wilson-loop multiplier, and P
the constructed orthogonal vacuum projection. The existing results give

    B(M U, M U) <= 4 B(U,U) = 4,
    B((I-P)x,(I-P)x) = B(x,x) - B(Px,Px) <= B(x,x).

The multiplier-created state is exactly the existing loop state; projection
centering is exactly the existing rational-centered stream. Consequently
EVERY fundamental source loop has centered squared norm at most 4, including
changing-size square loops. The ceiling is independent of nome, width, loop
length and position; no identification of different carriers is asserted.

The actual plaquette consumer retains its original active-link hypothesis.
Write u=`uniformFloor(hw0,width)`, N=B(v,v), and F=B(v,T(2)v) for the existing
plaquette excitation. The original response-square result gives u^2<=N F,
and F>=0. The new N<=4 yields

    F >= u^2/4,
    F >= (u^2/16) N,
    u^2/16 <= twoStepRate(hw0,hw1,width).

The last line also uses the existing SAME-vector strict form upper bound
and positive norm floor. Thus the norm denominator is now a fixed number,
not the generic Cauchy-stream ceiling. This does NOT assert that 4 is smaller
than every previous expression-specific ceiling. The response floor u and
the transfer rate still depend on nome and width. A uniform upper norm bound
is neither a uniform positive response nor a uniform spectral gap.

## Input declarations

- `completedInner_multiplier_bound`:
  `lean/YMGap/Continuum/BF4WilsonAllNomeTimeZeroOperator.lean:159`.
- `completedMultiply_unitState`:
  `lean/YMGap/Continuum/BF4WilsonAllNomeTimeZeroVacuum.lean:109`.
- `centeredPart_pairing_both`, `unitProjection_inner`:
  `lean/YMGap/Continuum/BF4WilsonAllNomeUnitProjection.lean:208`, `:145`.
- `centeredPart_embed`:
  `lean/YMGap/Continuum/BF4WilsonAllNomeCenteringPin.lean:75`.
- `plaquetteExcitation_response_square`:
  `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteTwoStepResponseCore.lean:52`.

## New declarations

| Declaration | Source |
| --- | --- |
| `centeredPart_norm_le` | `lean/YMGap/Continuum/BF4WilsonAllNomeLoopNormBound.lean:51` |
| `loop_norm_le_four` | `lean/YMGap/Continuum/BF4WilsonAllNomeLoopNormBound.lean:59` |
| `centered_loop_norm_le_four` | `lean/YMGap/Continuum/BF4WilsonAllNomeLoopNormBound.lean:74` |
| `plaquette_norm_le_four` | `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteUniformCapResponse.lean:50` |
| `absoluteFloor`, `absoluteFloor_positive` | `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteUniformCapResponse.lean:58`, `:61` |
| `plaquette_twoStep_floor_four` | `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteUniformCapResponse.lean:85` |
| `relativeFloor`, `relativeFloor_positive` | `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteUniformCapResponse.lean:112`, `:115` |
| `plaquette_relative_floor_four` | `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteUniformCapResponse.lean:133` |
| `relativeFloor_le_twoStepRate` | `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteUniformCapResponse.lean:159` |

## Parallel analytic review and remaining frontier

The strict transfer bound supplies a LOWER deficit bound `(1-q)N<=N-F`;
survival instead needs an UPPER relative deficit bound. See
`complex_twoStep_relative_loss` in
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexRelativeLoss.lean:53` and
`dyadic_response_ge_fraction_of_relative_energy` in
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRelativeSurvival.lean:110`.
The already checked `no_starRatio_rational_loss_budget` in
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRationalBudgetObstruction.lean:117`
excludes the current coarse cubic-loss/starRatio certificate, not actual
Yang--Mills survival. The new upper norm cap does not repair that certificate.

The older thermodynamic branch has `rangeApproximationData` and
`transfer_injective` in
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicFullSpaceZeroContinuity.lean:86`
and `:130`, using `completed_bound` in
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicTransferTestBound.lean:132`.
These act on a DIFFERENT fixed-nome plaquette completion. Its inward
plaquette geometry is not an all-nome Wilson boundary-loop identification.
An exact bounded inverse dual test for every boundary generator is one
sufficient route, not a necessary condition for dense range. Constructive
approximate preimages are enough; bare finite heat inversion alone is not
an original OS-to-weighted-Haar realization.

The existing `completedTransfer` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCompletedHaarTransfer.lean:62`
acts on ordinary Haar completion at each finite cutoff; its header explicitly
excludes cutoff convergence and reflected OS identification. The required
same-carrier realization/intertwining or direct joint-limit approximation
remains open. No new analytic premise or conditional interface is added here.

There is useful finite input for that separate realization problem:
`centralDensity_normalizedFloor` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCentralDensityFloor.lean:119`
retains the original central potential and both terminal messages. Its
positive `centralFraction` (`:90`) is independent of the late cutoff K
and terminal depth t, while depending on nome and width. This finite
normalized density comparison is not itself an OS carrier isometry or
time intertwiner. The review does not assert that boundary normalization
must diverge or that every exact boundary test has a bounded inverse.
Moreover, `fringeSum_transfer_pair_zero` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeKernel.lean:100` gives
an actual inactive-link kernel identity for the finite weighted transfer. A full-Haar injectivity
claim is therefore unsafe; the relevant projection/OS quotient must be
identified rather than suppressed. This audit does not infer a nonzero
kernel vector for the all-nome OS transfer from that separate Haar result.

Useful signed collective control, scaling survival, continuous physical
time, full QFT, and every-group continuum Clay closure remain open. The
canonical chart block is unchanged.

## Verification

Both new modules passed focused checks using
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20`, their
individual `--check` sources and corresponding `--check-output` olean paths.
All 11 printed gates report only `{propext, Quot.sound}`. The response
module's first check exposed an omitted implicit face-membership parameter
in the scalar calibration theorem; an explicit `include hf` repaired it.
The final response check completed in approximately 2.1 seconds. No new
sorry, axiom, or analytic premise was added. Root imports were added but
no full-root/full-tree build, full audit or guard ran.

Root implemented the norm argument; Luna implemented the actual plaquette
consumer; Sol reviewed the separate physical-time path and scope. Compilation
is serialized, with one worker and a 20 GiB worker ceiling. Automatic safety
telemetry remains continuous; manual live-job polls are spaced about five
minutes apart. No routine literature rescan was performed.
