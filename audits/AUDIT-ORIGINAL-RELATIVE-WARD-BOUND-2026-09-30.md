# Original relative signed Ward bound

Date: 2026-09-30 UTC. Whole-project Clay target OPEN.
Classification: PROGRESS on a supplied original finite estimate. The
canonical chart is unchanged; no continuum or physical gap field closes.

## Mathematical change of viewpoint

The preceding literal source y=(I-T)v was proved to vanish unnormalized
as the nome approaches one. The older positive floor used starRatio, whose
global heat-minimum factor can be very small. This increment instead uses
already constructed relative derivative certificates for the full weight.

For a direction D, write d=DW. The two certificates CW+d and CW-d give

    (CW+d)*(Ca-b)^2 + (CW-d)*(Ca+b)^2
      = 2C*(C^2*W*a^2 + W*b^2 - 2*d*a*b).

Positive rational cancellation after ORIGINAL Haar integration gives both
signs of 2H[dab] <= C^2 H[Wa^2]+H[Wb^2]. No division by W or independence
of a,b is used. Let a=f-E_W[f], b=Df and sum the six directions. If E is
the unnormalized angular energy and R the actual signed Ward residual,

    -2R <= 6C^2*Z*Var_W(f)+E,
    E+R = 3Z*Var_W(f),
    E <= 6*(1+C^2)*Z*Var_W(f).

The second equality uses the SU(2) head-linear Casimir. The proof does not
drop R, assert positivity of R, or confuse angular energy with physical time.

## Checked declaration path

- `QuaternionHaarRelativeAngularYoung.scaled_young_certificate`,
  `lean/YMGap/Continuum/QuaternionHaarRelativeAngularYoung.lean:56`,
  supplies the positive-cone identity. `relative_young_upper` at line 159
  and `relative_young_lower` at line 171 are its two signed Haar consumers.
- `QuaternionHaarRelativeCenteredWard.residual_lower`,
  `lean/YMGap/Continuum/QuaternionHaarRelativeCenteredWard.lean:60`,
  retains the complete signed correction. `energy_le_variance` at line 137
  proves the same-weight variance estimate for supported head-linear f.
- `BF4ExactSlabFixedSpatialMarginalRelativeBound.marginalRelativeBound`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMarginalRelativeBound.lean:165`,
  constructs the bound for literal W=(V*g_n)*g_(n+1).
  `frameRelativeBound` at line 193 transports both cone endpoints through
  a selected-to-head block involution, using supported prefix and
  arbitrary-insertion Haar-carrier equalities, not false raw coefficient
  equalities between differently padded polynomials.
- `BF4ExactSlabFixedSpatialRelativeWardBound.marginalScoreCap`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRelativeWardBound.lean:54`,
  is exactly 6*relativeCap(w,4096)+2*relativeCap(w,32).
  `angularVarianceFactor` at line 57 is 6*(1+C(w)^2).
  `frame_energy_le_originalVariance` at line 74 identifies the variance
  with the original middleRatio. `plaquette_energy_le_originalVariance`
  at line 121 supplies physical incidence/linearity as well: no missing
  residual-size, density-comparison or successful analytic input is assumed.
- `QuaternionHaarLinearMeanWard.weighted_linear_mean_ward`,
  `lean/YMGap/Continuum/QuaternionHaarLinearMeanWard.lean:66`,
  separately proves sum_D H[(DW)(Df)]=3H[Wf]. It is an exact forward input
  for a subsequent variance/prediction lower-bound argument, not itself
  such a lower bound and not used in the centered estimate above.

## Exact parameter boundary

The original instance quantifies rational 0<w<1, width, depth n, character
cutoff K, a spatial plaquette and one incident ACTIVE link. K must exceed
the explicit endpointRelativeCutoff(w). No boundary-inactive link is
silently included. The action and both adjacent terminal messages remain.

| Quantity | Explicit dependence | Not asserted |
| --- | --- | --- |
| C(w), 6*(1+C(w)^2) | Nome w; fixed numerical derivative caps 4096 and 32 | Nome-independent or physical-spacing-uniform bound |
| endpointRelativeCutoff(w) | Nome; inherited positive heat floor and deficit moduli | Uniform late cutoff as w approaches one |
| W and its partition Z | Nome, cutoff, width, depth | Alternative reference density or normalization |
| Result | All widths/depths/late cutoffs satisfying the stated active-link guards | All-state transfer coercivity or scaling survival |

`QuaternionHaarHeatRelativeAngularBound.relativeCap`,
`lean/YMGap/Continuum/QuaternionHaarHeatRelativeAngularBound.lean:41`,
contains relativeCost+1, not a reciprocal heat minimum.
`relativeCutoff` at line 46 still uses the heat minimum through its error
tolerance. This report does not assert a proved asymptotic comparison of
the new coefficient with the previous starRatio bound.

## Remaining mathematical join

The already proved exposed four-word kinematics is
`QuaternionHaarExposedFundamentalEnergy.exposedFundamental_angularSquare`,
`lean/YMGap/Continuum/QuaternionHaarExposedFundamentalEnergy.lean:235`.
It identifies angularSquare(f) with 4-f^2 under every insertion. A generic
physical-plaquette/selected-edge recoding still has to join it to this
original odd marginal at arbitrary width. The fixed 116-block face chart
is not that generic pin.

More importantly, a lower bound on global Var_W(f) alone does not replace
the needed floor against EVERY exterior predictor. The next target is
that actual prediction/temporal-loss estimate with the improved coefficient,
followed by the existing literal transfer and normalized-source consumers.
No conditional projector may be iterated as if its idempotent update were
an independent loss step. No new analytic assumption bundle was added.

### Reviewed next argument, NOT a kernel-checked result

For a supported head-independent polynomial q, write g=f-q,
A=H[Wg^2], F=H[Wf^2], E=H[W*angularSquare(f)] and Z=H[W].
Generalized weighted Ward would supply
E+R_f=3F and E+R_g=3H[Wgf]. This generalization must be proved for the
actual g, using Dq=0; it is not the scalar-centered theorem above.

For C>0, apply signed relative Young with a=f, b=2C^2*Df and sum:
R_f <= (3/2)F+C^2 E, so 3F <= 2(1+C^2)E. With the actual kinematic
pin F+E=4Z this gives 12Z <= (5+2C^2)E. The second Ward identity gives
E <= 6H[Wgf]+6C^2 A. The positive square (t*g-f)^2 with
t=4(1+C^2) then gives E <= (24+36C^2)A. Consequently,

    Z <= (5+2C^2)*(2+3C^2)*A.

Root and Sol checked this rational algebra; these are planned proof steps,
not declarations supplied by this commit. No square roots or fiberwise
normalizer inverses are needed. A temporal predictor requires the actual
joint time-window density and its relative cap: the current one-slice
marginal is not automatically that joint density. Conditional-predictor
limits also need the appropriate supported head-independent approximants.

The changing-coupling normalized source estimate, matched physical-time
survival, cross-width/scaling comparison, EVERY-state decay, physical mass,
full same-theory QFT structure and every compact simple group remain OPEN.

## Verification

Five final focused checks passed 13 printed axiom gates, all within
{propext, Quot.sound}: Young (4), centered Ward (2), marginal/frame (2),
original plaquette consumer (4), exact mean Ward (1). Root imports were
registered but no full root build/audit/guard was run.

Final logs:

- `/tmp/ym-relative-angular-young-20260930.log`
- `/tmp/ym-relative-centered-ward-20260930.log`
- `/tmp/ym-marginal-relative-20260930.log`
- `/tmp/ym-original-relative-ward-20260930.log`
- `/tmp/ym-linear-mean-ward-20260930.log`

All checks used the monitored launcher, one worker, 20 GiB hard ceiling,
12 GiB OS reserve and dynamic host telemetry. No new sorry/custom axiom,
old sorry discharge, CI change, surrogate carrier or weakened frontier.
Sol supplied/reviewed the Young and mean identities; Luna supplied and
reviewed the actual marginal/frame certificate construction.
