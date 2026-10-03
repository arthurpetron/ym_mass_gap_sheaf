# Fixed coupling macroscopic response obstruction

The ORIGINAL Wilson thermodynamic completion now has a checked relative
response bound. At fixed small nome, no choice of centered state or its
scalar normalization can preserve a nonzero positive macroscopic response
ratio beyond the computed onset. This prunes normalization-only rescue in
that regime; it does not exclude the intended changing-coupling route.
The continuum Yang--Mills and Clay targets remain OPEN.

## Actual carrier and checked statements

All paths below are relative to the repository root. The new module uses
`UnionCompletion hw0 hw1 hsmall hd hs` and its original `completedInner`,
`completedTime` and `completedUnit`. Its premises explicitly include
0<w<1, heatRatio(w)<=1/2, heatRemainderBound(w)<1 and
entropyRate(625,adjustedCoreRate(w))<1
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionMacroscopicRatioObstruction.lean:89`).
The rate theta is the nome-dependent squared time rate, not a calibrated
physical mass (`twoStepRate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialDenseGap.lean:65`).

For centered x, define R_x(lag)=B(x,T(lag)x), exactly as
`response`, `lean/YMGap/Continuum/BF4WilsonSpatialUnionMacroscopicRatioObstruction.lean:101`.

- `relative_even_response_bound`, same path:105, proves
  R_x(2*(start+n))<=theta^n*R_x(2*start).
  It applies existing `norm_decay` to the actual vector T(start)x
  (`lean/YMGap/Continuum/BF4WilsonSpatialUnionRelaxation.lean:64`),
  using time composition, preserved orthogonality and the even-time
  squared-norm identity. No initial positive norm floor is assumed.
- `ratioCutoff`, new module:115, computes
  geometricCutoff(theta,1,kappa/2).
  `rate_at_ratioCutoff`, new module:118, proves theta^n<=kappa/2
  at every later n when kappa>0. The threshold depends on theta and kappa,
  not the state, support or normalization.
- `macroscopic_ratio_image_zero`, new module:127, proves that
  kappa*R_x(2*n)<=R_x(4*n) beyond that onset forces T(n)x=0.
  `scalar_ratio_zero`, new module:56, cancels only the strictly positive
  rational margin kappa-theta^n, not the possibly zero response.
  Actual positive definiteness gives vector equality
  (`completedInner_posdef`,
  `lean/YMGap/Continuum/BF4WilsonSpatialUnionPosdef.lean:93`).
- `macroscopic_ratio_response_zero`, new module:144, then proves
  R_x(2*n)=0. Neither theorem asserts that the original x is zero.
- `unit_bounded_response_small`, new module:158, proves
  R_x(2*n)<=epsilon for EVERY centered x with B(x,x)<=1,
  at n>=geometricCutoff(theta,1,epsilon). A single cutoff controls all
  such vectors on this carrier, including arbitrarily normalized ones.

These statements quantify over all x at each n; x need not remain fixed
as n grows. The carrier and its nome nevertheless remain fixed.
No identification with the all-nome finite-width carrier is asserted.

## Forward backward consequence

The older spectator estimate only bounded a sufficient certificate, not
the actual response (`squareResponseFraction_le_half_side`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareSpectatorResponseObstruction.lean:108`).
The new theorem instead bounds the original interacting thermodynamic
response itself under the displayed small-nome guards. Thus state
normalization alone cannot supply nonzero macroscopic survival in this
already constructed fixed-coupling regime.

The backward consumer still requires a positive family-wide estimate
kappa*R(side)<=R(2*side) on the SAME original all-nome family
(`normalizedAnchorResponse_block_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132`).
Producing it on a justified changing family remains OPEN, as does effective
BOTH-order normalized cross-scale comparison. The new theorem does not
assert a uniform rate over varying nomes and does not refute either input.

The forward route must retain the separate actual finite time-horizon
partitions: `window_pairing` and `window_partition_pairing`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowPairing.lean:96` and
`:124`. The new result supplies no lower estimate on the signed interacting
gain and no continuum physical-time or local-field identification.

## Verification boundary

Root ran only this new source with `scripts/safe_lean_build.py`, jobs=1,
reserve=12 GiB and worker cap=20 GiB. Preflight reported 85 percent
system-wide free memory, zero swap and no competing Lean/Lake/pytest/runner
process. The check exited zero. All seven printed gates are exactly
{propext, Quot.sound}, with no `sorryAx` or classical input. One cosmetic
unused-section-variable warning for hw1 remains at line 118.
Independent read-only source/log review confirmed the scope and equations.

- Source SHA256: `32827a10e3adb561c178a93eaa5c54d5c55831905b5a3283fc3138c9fc8348f6`.
- Accepted log: `/tmp/ym-original-fixed-gap-macro-obstruction-20261003-first.log`.
- Log SHA256: `186869d9802a16d341bf336e24d079e3d7d1a530d0e845d2244779242ba2816b`.

The root import is registered, not aggregate-checked. No full build or
repository-wide axiom audit was run. No new sorry, axiom, classical shortcut,
canonical field weakening or CI change was introduced. The exact canonical
chart claims remain unchanged, so no ASCII chart was reprinted.
