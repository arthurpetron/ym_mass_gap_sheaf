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

## Remaining consumer and scope boundary

The immediate consumer is the original-collar relative numerator
C(w)*A +/- Y X(A*g), g=X Y f_p, needed by
`QuaternionHaarRelativeReciprocalDualNorm.reciprocal_dual_weighted_norm_le`.

The finite Jacobi polynomial is WEIGHTED. It is not definitionally the
original unweighted `heatPrefix`. The existing first-derivative weight-removal
modulus does not control a mixed second derivative. Next: construct that
literal mixed deficit interval, using sixth- and fourth-power heat-term
majorants and explicit finite-band/tail cutoffs; absorb its error against
the known positive floor. The floor may set approximation precision, but
must not become an inverse factor in the final relative cost.

The physical four-link mixed scalar caps, original collar product/numerator,
new-test residual and signed Gram assembly, improved family estimate,
scaling survival, every-state decay, and all continuum/Clay fields remain OPEN.
The canonical chart has not changed and is not reprinted.

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
