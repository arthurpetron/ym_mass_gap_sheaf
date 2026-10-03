# Scaling limits of the spectator and bare transmission certificates

Two focused proofs limit the existing certificate routes. The explicit
spectator response fraction collapses at growing scale for EVERY choice of
strict nome. Separately, a positive repeated bare-transmission floor forces
a cleared total heat-loss bound. Neither result upper-bounds the actual
interacting response or refutes Yang--Mills continuum survival.

## Spectator certificate collapse

The original `squareResponseFraction`, defined in
`lean/YMGap/Continuum/BF4DyadicWilsonSquareSpectatorResponse.lean:220`, is

    Gamma = w^(12*s) * localLower(w,4*s)^2 / localUpper(w,4*s)^2,
    s = side(scale) = 2^scale.

`squareResponseFraction_positive` in that file at line 226 proves strict
positivity at each finite scale. The local factors are the unchanged
`localLower` and `localUpper`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialUniformLocalBand.lean:44`
and line 47. The existing `headFloor_le_oneThirtySecond`,
`lean/YMGap/Continuum/BF4ExactSlabSharedWindowFloorBound.lean:46`, and
`prefixCap_ge_one`,
`lean/YMGap/Continuum/BF4ExactSlabStarRateObstruction.lean:32`, give the
following new bounds in
`lean/YMGap/Continuum/BF4DyadicWilsonSquareSpectatorResponseObstruction.lean`:

- `squareResponseFraction_le_localLower:69`: Gamma<=localLower(w,4*s).
- `squareResponseFraction_le_half_side:108`: Gamma<=(1/2)^s, for ALL 0<w<1.
- `squareResponseFraction_small:121`: scale>=epsilon.den implies
  Gamma<=epsilon, for any positive rational epsilon, simultaneously for all
  strict nomes. The cutoff is explicit and independent of nome.
- `no_uniform_positive_fraction:133`: no arbitrary strict-nome family can
  give this Gamma a fixed positive lower bound at all dyadic scales.

The deliberately coarse geometric ceiling suffices to exclude this route;
no sharp asymptotic claim is needed. The pointwise certificate remains valid
for the existing `anchorNormFloor` and constructive normalizer,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedBondAnchor.lean:67`.
This theorem does NOT show that the actual anchor norm or interacting
doubling ratio collapses.

## Bare transmission necessities

`lean/YMGap/Continuum/BF4DyadicWilsonSquareBareTransmissionNecessary.lean`
uses the existing cleared `oneSub_pow_mul_bernDen_le`,
`lean/YMGap/Continuum/ReciprocalBernoulliUpper.lean:103`, and power
monotonicity. For kappa>0 and 0<w<1, it proves:

- `bare_transmission_floor_necessary:74`: kappa<=w^(12*s) implies
  kappa*(1+12*s*(1-w))<=1.
- `repeated_bare_transmission_floor_necessary:84`: 0<=rho<=w^(12*s)
  and kappa<=rho^s imply kappa*(1+12*s*s*(1-w))<=1.

These are necessities for the displayed reference coefficients, not
sufficient interacting estimates. There is no hypothesis identifying an
actual response with the bare power, no coupling schedule, and no physical
AF identification. The bounds are not claimed sharp.

## Forward and backward meeting point

The backward consumer remains the actual SAME-theory ratio
kappa*R(s)<=R(2*s), uniformly with kappa>0 on a justified changing family.
`normalizedAnchorResponse_block_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132`,
and `normalizedBond_geometric_real_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRealSurvival.lean:148`,
already consume that ratio. Do not try to produce it by promoting the
collapsing Gamma or by assuming the interacting response is a free heat mode.

The comparison producer must also control the normalized samples with
BOTH-order estimates and explicit moduli. The existing fixed-geometry
`dyadicUnitResponse_nome_difference_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNomeComparison.lean:315`, already
compares actual unit responses at two nomes; its cost still names scale,
width and lag. It is not a constructed normalized cross-scale comparison.
Do not duplicate that fixed-geometry producer or assume that a raw additive
comparison controls a quotient with a collapsing normalization.

Physical-time/local-field identification, a justified scaling family,
nontrivial continuum survival, full same-theory QFT and every-group physical
mass gap remain OPEN. A one-probe limit is not the full observable-algebra
object `CanonicalSchwingerLimit`,
`lean/YMGap/Continuum/CanonicalOSRoot.lean:121`.

## Focused verification

The corrected spectator target passed its second focused check; all four
printed gates have exactly {propext, Quot.sound}. The bare-transmission
target passed its first focused check; both printed gates have exactly that
set. Independent source/log review confirmed the statements, scopes and
hashes. No new sorry, axiom, classical shortcut or weakened frontier field.
Root imports are registered, NOT aggregate-checked; no full audit is claimed.
CI and the canonical ASCII fence are unchanged.

Both checks were serialized through the safe launcher with one worker,
20-GiB worker ceiling and 12-GiB system reserve. Fresh preflight before each
found no competing compiler, 84--85% memory-pressure-free and zero swap.

Accepted spectator log:
`/tmp/ym-spectator-response-obstruction-20261003-second.log`.
SHA256 source/log pair:

    a90b955fa217fc46f68bf1e2fcc8ba62fbcc7f19b5549af8b24ff220dbbc52a3
    469d71057bc1c4128f445c74a766f2b4c577db174915a8f5164bab8edab12017

The rejected first spectator draft had a rational power multiplication-order
error and downstream sorryAx output. It is not accepted evidence.

Accepted bare-transmission log:
`/tmp/ym-bare-transmission-necessary-20261003-first.log`.
SHA256 source/log pair:

    6c53b56a20cd7bf521ac25d3bb18b264b956331a036deb14c646366fb746f95c
    d980d30f67cf255cbd12034e7c5aa19c892c09f5bfe76487c04f7076a00458ab
