# Mixed relative heat derivative without an inverse heat minimum

Date: 2026-09-30 UTC. Classification: PROGRESS. Clay target OPEN.

## Concrete producer

`JacobiHeatMixedRelativeAngularBound.weightedHeatBound`,
`lean/YMGap/Continuum/JacobiHeatMixedRelativeAngularBound.lean:264`,
constructs mixed relative certificates for the ACTUAL finite positive Jacobi
weighted character polynomial, on the original supported quaternion carrier.
It retains the coefficient-level Jacobi identity and inverse-nome/half
normalization. This is not an assumed analytic input.

Let the two scalar first-derivative caps be d,e and the ordered mixed scalar
cap be m. For R equal to the existing summed relative-slope budget,

    |X H| <= d R H,  |Y H| <= e R H,
    |X Y H| <= (m R + d e R^2) H.

These inequalities mean explicit positive-Haar polynomial certificates for
both signs, not pointwise assumptions. R depends explicitly on the nome and
does not depend on the finite Jacobi cutoff, carrier size, or coordinate
indices. No uniformity as the nome tends to one is claimed. In particular,
no reciprocal of the whole heat minimum enters the displayed costs.

## Short argument

The affine Jacobi factor has positive constant and slope coefficients.
`factorBound` (:130) clears the known relative slope inequality and obtains
the two first caps d*r,e*r and mixed cap m*r for that actual factor.

Under multiplication, mixed costs gain both cross terms. Summing the factor
rates into R gives m*R+d*e*R^2; the extra diagonal term d*e*r^2 is nonnegative.
`productDerivativeBounds` (:201) proves this simultaneously for the positive
product AND the positive Leibniz derivative defining the heat. This second
component is essential: a bound on the product alone would be the wrong heat
object. `heatBound` (:247) preserves the normalization and uses the existing
uniform finite-prefix slope budget. `weightedHeatBound` transports through
the exact already-proved weighted-character identity.

Supporting finite certificate algebra:

- `QuaternionHaarRelativeIntervalProduct.lean` extends the EXISTING
  `QuaternionHaarRelativePolynomialInterval.RelativeInterval` with base
  transport, signed product, sum-of-bases, simultaneous scaling, cap widening
  and the exact self bound. No new analytic frontier structure is introduced.
- `QuaternionHaarMixedRelativeAngularBound.MixedBound.mul` implements the
  ordered Leibniz rule with explicit first/mixed certificates. Other methods
  preserve coefficients, sums, positive scales and widened caps. This finite
  certificate data is actually inhabited by the Jacobi construction above.

## Follow-on: original unweighted heat prefix

The finite-weight removal is now supplied, not assumed.
`QuaternionHaarHeatMixedAngularDeficit.finite_shifted_tail_le`,
`lean/YMGap/Continuum/QuaternionHaarHeatMixedAngularDeficit.lean:119`,
constructs a degree-m heat-tail cutoff; `mixedAngularDeficitInterval` (:302)
applies it to the degree-six/four majorants of the actual ordered second
derivative. It splits the requested error between a finite Jacobi band and
its tail. Existing `heatSecondTermInterval` is exposed without proof changes.

`QuaternionHaarHeatMixedRelativeAngularBound.heatPrefixMixedRelativeBoundAt`,
`lean/YMGap/Continuum/QuaternionHaarHeatMixedRelativeAngularBound.lean:136`,
constructs all three relative bounds on the SAME original `heatPrefix`:

    |X H_K| <= (d R+1) H_K,  |Y H_K| <= (e R+1) H_K,
    |X Y H_K| <= (m R+d e R^2+1) H_K.

Here K is at least the explicit `mixedRelativeCutoff w d e m` (:98). The
floor sets epsilon=headFloor/(mixedRelativeCost+1); the signed value and
derivative errors consume exactly the floor. It is not divided into the
final cost. Scalar first/mixed intervals and the supported unit quaternion
remain explicit inputs. Cost depends on nome, not K or ambient carrier size.

## Physical follow-on: original four-link scalar and two-link collar

`BF4ExactSlabPlaquetteMixedAngularInterval.plaquetteMixedAngularJet`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteMixedAngularInterval.lean:209`,
constructs value/inner/outer/mixed intervals with caps 256/2048/2048/16384
for the actual four-link quaternion scalar. Both rotations are physical
within-block planes; they may overlap. Identity fallback links are retained.
It reuses the exposed existing `MixedJet` calculus, not the older one-plane
head lemma.

`QuaternionHaarMixedRelativeProduct.productBoundAtLength`,
`lean/YMGap/Continuum/QuaternionHaarMixedRelativeProduct.lean:132`,
retains the ordered product and all mixed cross terms. N factors each with
first cost c and mixed cost m have costs N*c and N*m+(N*c)^2.

`BF4ExactSlabMixedRelativeHeatCollar.faceMixedRelativeBound`,
`lean/YMGap/Continuum/BF4ExactSlabMixedRelativeHeatCollar.lean:50`,
uses the literal original `faceHeatPolynomial`, its proved physical Haar-unit
word, and those actual scalar intervals. `twoLinkCollarMixedRelativeBound`
(:72) composes the original `collarHeat` and `collarCount_le` to N=12.
No action factor is discarded, and no conditional independent-face model
is substituted. The explicit nome costs are independent of extent and late K.

## Remaining consumer and scope boundary

The possible next local consumer is the original-collar relative numerator
C(w)*A +/- Y X(A*g), g=X Y f_p, needed by
`QuaternionHaarRelativeReciprocalDualNorm.reciprocal_dual_weighted_norm_le`.

The collar estimate controls A, not yet Y X(A*g). The full numerator,
new-test residual and signed Gram assembly, improved family estimate,
scaling survival, every-state decay, and all continuum/Clay fields remain OPEN.
The canonical chart has not changed and is not reprinted.

## Quantitative step back before further dual assembly

Source: `JacobiShiftedRelativeSlope.budget`,
`lean/YMGap/Continuum/JacobiShiftedRelativeSlope.lean:33`;
`HKConv.Cstar`, `lean/YMGap/Continuum/HeatKernelConv.lean:461`;
`HKPos.factorLB`, `lean/YMGap/Continuum/HeatKernelPos.lean:150`;
`HKConvGen.geoTailBase`, `lean/YMGap/Continuum/HeatKernelConvGen.lean:335`.
Their rational definitions give R=2w/((1-w)^2*(1-w^2)) for strict nome.
Hence the displayed mixed/collar costs have near-one order (1-w)^-6.

PAPER-LEVEL diagnostic, NOT a new Lean theorem: if a Gram construction
produced only a floor proportional to the inverse square of this cost, its
order would be (1-w)^12. That alone would not pay the available absolute
single-plaquette loss budget 192*(1-w) by direct subtraction near w=1.
The checked obstruction `computedLossRatio_ge`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteAffineCalibrationObstruction.lean:102`,
concerns the OLD floor, not this as-yet-unconstructed proposed floor. Neither
comparison is an upper bound on actual variance or a lower bound on actual
loss. No physical theory is refuted.

Execution priority: seek temporal cost relative to the SAME signed centered
variance, retaining signed cancellations/controlled support, before spending
the remaining effort on a floor-only dual/Gram route. Existing
`response_ge_fraction_of_relative_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointEnergySurvival.lean:97`,
is a precise conditional consumer; its hypothesis still needs an actual
same-object producer and a justified scaling family. Polynomial dependence
alone is not evidence that the required physical comparison closes.

## Verification

Three new modules passed final focused serialized monitored checks. All 20
printed public gates are within {propext, Quot.sound}; the explicit mixed-cost
definitions are axiom-free. No sorry, new axiom, classical input, raised
heartbeat/memory limit, or canonical frontier change. Two local certificate
syntax/normal-form issues were corrected during checks.

Logs: `/tmp/ym-relative-interval-product-20260930.log`,
`/tmp/ym-mixed-relative-angular-bound-20260930.log`,
`/tmp/ym-jacobi-mixed-relative-angular-20260930.log`.
One worker, 20 GiB hard cap, 12 GiB OS reserve, dynamic telemetry. No broad
build/audit/guard or CI change. Sol agents supplied the two finite algebra
modules; root supplied the actual Jacobi producer and all checks. Luna
reviewed the missing weight-removal modulus against existing source.

Follow-on verification: the exposed term module and both original-prefix
weight-removal modules passed three focused serialized checks, 15 printed
gates total. Only {propext, Quot.sound}; all five new printed cutoff/cost
definitions are axiom-free. Two missing namespace openings were fixed during
the checks. No new analytic hypothesis bundle, sorry, classical input,
limit increase, broad run, or canonical status change.

Follow-on logs: `/tmp/ym-heat-second-term-20260930.log`,
`/tmp/ym-heat-mixed-angular-deficit-20260930.log`,
`/tmp/ym-heat-mixed-relative-angular-20260930.log`.
Sol supplied the mixed deficit module; root proved the original-prefix join
and ran all checks. A separate Sol source review identified the one-plane
versus two-plane distinction before any physical claim was made.

Physical follow-on: four final focused checks passed 19 printed gates, all
within {propext, Quot.sound}. Six printed costs/cutoffs are axiom-free.
Logs: `/tmp/ym-relative-heat-mixed-jet-20260930.log`,
`/tmp/ym-plaquette-mixed-angular-20260930.log`,
`/tmp/ym-mixed-relative-product-20260930.log`,
`/tmp/ym-original-mixed-relative-collar-20260930.log`.
Namespace openings, explicit rational equivalence composition, literal
Leibniz cross-term ordering and a transparent block-count abbreviation were
corrected during checks; no resource limits were raised. Sol supplied the
physical jet/product modules; root supplied the original face/collar join.
Luna reviewed the quantitative calibration direction against source.
