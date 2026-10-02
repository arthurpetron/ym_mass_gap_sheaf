# Collapse of the certified growing square response floor

## Result and scope

The existing explicit response certificate cannot provide a positive
scale-uniform floor, even with an arbitrary changing coupling schedule.
This is a theorem about the computed lower bound, NOT an upper bound on the
actual completed Wilson response and NOT a refutation of continuum survival.
The original state, action, mean, partition and time operator are unchanged.

For every rational nome 0<w<1 and scale k, let side(k)=2^k and let r(w,k)
be the actual `squareResponseFraction` used by the completed response theorem.
The new module proves

    0 < r(w,k) <= 1/1024 <= 1/2,
    r(w,k)^side(k) <= (1/2)^k = spacing(k).

The positivity was already proved in the response module. The new upper
bounds need no width, cutoff, terminal-depth or physical-calibration input.
For ANY schedule w(k) strictly between zero and one, the explicit modulus
N(epsilon)=epsilon.den ensures, for every k>=N(epsilon),

    r(w(k),k)^side(k) <= epsilon,
    r(w(k),k)^side(k)*starRatio(w(k)) <= epsilon.

No positive fixed rational delta lies below all scales of either certificate.
The second expression is exactly the printed rational lower floor of
`dyadicExcitation_time_geometric_floor` at lag side(k). An actual response
can remain larger than a lower certificate that tends to zero. The existing
positive response theorem at each fixed parameter and finite lag remains valid.

## Mathematical argument

The actual constants are a=w^(12*side), l=headFloor(w)^(28*side),
u=prefixCap(w)^(28*side), and r=a*l^2/u^2. Existing declarations give
headFloor<=1/32 and prefixCap>=1. Since side>=1 and 0<w<1,
a<=1, l<=1/32 and u>=1. Thus r<=1/1024. Monotonicity of rational
powers and side(k)>=k give r^side<=half^side<=half^k. The existing
dyadic spacing modulus completes the uniform estimate. The existing
starRatio<=1/64<=1 bounds the full printed floor by the fraction alone.

For a hypothetical delta>0 below every certified fraction, take
epsilon=half*delta and the concrete scale epsilon.den. The modulus then
forces delta<=half*delta, contradicting positivity. No witness selection,
classical argument or new analytic premise is used.

## Declaration evidence

All paths are relative to the repository root.

| Declaration | Source | Content |
| --- | --- | --- |
| `squareResponseFraction` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSpectatorResponse.lean:220` | Actual coefficient of the existing response theorem |
| `squareResponseFraction_positive` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSpectatorResponse.lean:226` | Existing positivity at each strict nome and scale |
| `headFloor_le_oneThirtySecond` | `lean/YMGap/Continuum/BF4ExactSlabSharedWindowFloorBound.lean:46` | Uniform upper ceiling on the constructed head floor |
| `prefixCap_ge_one` | `lean/YMGap/Continuum/BF4ExactSlabStarRateObstruction.lean:32` | Constant Haar mode retained in the cap |
| `starRatio_le_oneSixtyFourth` | `lean/YMGap/Continuum/BF4ExactSlabStarRateObstruction.lean:40` | Full printed floor cannot exceed its fraction |
| `localLower`, `localUpper` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialUniformLocalBand.lean:44`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialUniformLocalBand.lean:47` | Actual collar powers, unchanged |
| `spacingModulus`, `spacing_small` | `lean/YMGap/Continuum/BF4DyadicWilsonSquare.lean:51`, `lean/YMGap/Continuum/BF4DyadicWilsonSquare.lean:53` | Existing computable epsilon.den modulus |
| `dyadicExcitation_time_geometric_floor` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSpectatorResponse.lean:178` | SAME completed response bounded below by r^lag*starRatio |
| `squareResponseFraction_le_one1024` | `lean/YMGap/Continuum/BF4DyadicSpectatorFloorCollapse.lean:58` | Actual r<=1/1024 for every strict nome |
| `squareResponseFraction_le_half` | `lean/YMGap/Continuum/BF4DyadicSpectatorFloorCollapse.lean:103` | Rational half ceiling |
| `squareResponseFraction_side_le_spacing` | `lean/YMGap/Continuum/BF4DyadicSpectatorFloorCollapse.lean:110` | Certified lag-side fraction<=assigned spacing |
| `squareResponseFraction_side_small` | `lean/YMGap/Continuum/BF4DyadicSpectatorFloorCollapse.lean:122` | Explicit uniform modulus |
| `scheduled_squareResponseFraction_side_small` | `lean/YMGap/Continuum/BF4DyadicSpectatorFloorCollapse.lean:130` | Arbitrary strict coupling schedules admitted |
| `not_uniform_certified_floor` | `lean/YMGap/Continuum/BF4DyadicSpectatorFloorCollapse.lean:139` | No positive all-scale rational floor for the fraction |
| `scheduled_responseFloor_side_small` | `lean/YMGap/Continuum/BF4DyadicSpectatorFloorCollapse.lean:176` | FULL printed certificate has the same modulus |
| `not_uniform_response_floor` | `lean/YMGap/Continuum/BF4DyadicSpectatorFloorCollapse.lean:188` | No positive all-scale floor for the full certificate |

## Next finite estimate remains open

Selecting a different nome schedule cannot repair THIS certificate. The
next mathematical task is an improved estimate on the actual complete signed
energy relative to OWN interacting variance, on a justified changing family.
No additional completion wrapper or separate limits for the signed pieces
are required: `energyLimit_completed_pin` at
`lean/YMGap/Continuum/BF4WilsonAllNomeTemporalEnergyLimit.lean:218` and
`varianceLimit_completed_pin` at
`lean/YMGap/Continuum/BF4WilsonAllNomeMarginalVarianceLimit.lean:236` already
pin the entire original energy and variance to the existing completed state.

The exact `paddedSquare_energy_centered_loss_identity` at
`lean/YMGap/Continuum/BF4DyadicWilsonSquareCenteredEnergyLoss.lean:144`
retains E=s*(A+mu*J)+T-D, with s=1-a. Its actual
`squareCenteredMomentDefect` at
`lean/YMGap/Continuum/BF4DyadicWilsonSquareCenteredEnergyLoss.lean:131`
is D=A-Z*OWNVar. A sufficient next finite proposition is joint control of
the signed remainder s*mu*J+T-a*D against Z*OWNVar, with useful
coupling/perimeter dependence. This estimate is NOT supplied here; the
signed terms are not asserted nonnegative. Small total heat loss is not
imposed as necessary. Physical calibration, nonzero continuum survival,
full SAME-theory QFT and realization for every compact simple group remain OPEN.

## Verification boundary

The final source passed one focused, monitored check with one worker and an
explicit 20-GiB ceiling after a fresh process, pressure and swap inspection.
The accepted third log contains eight axiom outputs, all exactly
{propext, Quot.sound}, and no errors or warnings. An earlier six-theorem
version also passed. The first draft failed because a private power helper's
Nat binder was not annotated; its elaboration placeholders and log are
rejected evidence. The repair changed no mathematical statement or guard.

Independent Sol mathematical review of the coefficient and full printed
certificate and Luna source, log and documentation evidence review passed.
Root imports the module. No new sorry, axiom, classical
shortcut, compiler-trusted decision or weakened frontier is introduced.
Root/tree builds, broad audit/guard and progress metrics were NOT run.
CI remains off. No displayed canonical chart claim changes, so its exact
block is preserved and not reprinted. Literature caches are reused; no scan.

| Final source or accepted log | SHA-256 |
| --- | --- |
| `lean/YMGap/Continuum/BF4DyadicSpectatorFloorCollapse.lean` | `43b43a3d1026daad15972bd29404f72a9bf8f0a169fe2e8401a26230cd550103` |
| `/tmp/ym-dyadic-spectator-floor-collapse-20261002-third.log` | `7be0d82aabbde0610cd7fda3ea09bac77588291279069c98e081c5126965b706` |
