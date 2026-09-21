# Terminating harmonic recurrence on the actual relative scalar

Date: 2026-09-21 UTC. WHOLE-PROJECT GOAL remains OPEN: constructive,
nontrivial continuum Yang--Mills on R^4 for every compact simple group,
with same-theory QFT axioms, isolated vacuum and finite positive physical
mass gap. This increment concerns the concrete SU(2) polynomial kernel.

## Exact mathematical increment

For a polynomial p homogeneous and harmonic of degree n in the head
quaternion x, with arbitrary retained-variable coefficients, define

    D_y p = sum_(i=0..3) y_i * partial_(x_i) p.

The implementation `lower` deletes only terms whose differentiated
exponent is zero, making the degree decrease syntactically valid without
changing coefficients. The actual quaternion relative scalar is x.y;
its four derivative identities are independently kernel checked.

Gaussian Euler/integration by parts and the polynomial power rule give

    E_x[p * (x.y)^(n+1)] = E_x[(D_y p) * (x.y)^n]

when p has degree n+1 and is harmonic. The integer n+1 is cancelled by
its constructive positivity, not by an unproved division or analytic
bound. Commutation of partial derivatives and head independence of y
prove that D_y p stays harmonic. Its positive degree drops by one.
The recurrence therefore iterates exactly n times, including a checked
degree-zero base case. With D_n the explicit sphere radial denominator:

    D_n * partialHaarHead[p * (x.y)^n]
      = dropHeadPolynomial(lowerIter n p).

This is coefficient equality, before any remaining Haar integration.
`lowerIter` is explicit finite recursion and its final head degree is zero.
There is no hidden normalization, loss of signed coefficients or fixed
retained link. D_n is `sphereFourDenominator n`, defined by
`D_0=1`, `D_(n+1)=(4+2*n)*D_n` in
`lean/YMGap/Continuum/SU2QuaternionPolynomialHaarCarrier.lean:179`.

## Declaration map

| Declaration | Source | Content |
| --- | --- | --- |
| `ratDerivative_comm` | `lean/YMGap/Continuum/SU2QuaternionDerivativeCommutation.lean:77` | Arbitrary coordinate derivatives commute coefficientwise. |
| `headLaplacian_derivative` | `lean/YMGap/Continuum/SU2QuaternionDerivativeCommutation.lean:99` | A derivative commutes with the four-coordinate Laplacian. |
| `activeDerivative_harmonic` | `lean/YMGap/Continuum/SU2QuaternionDerivativeCommutation.lean:121` | The degree-sensitive derivative preserves harmonicity. |
| `harmonic_mul_independent` | `lean/YMGap/Continuum/SU2QuaternionDerivativeCommutation.lean:135` | Head-independent coefficients preserve harmonicity. |
| `headGradientDot_power` | `lean/YMGap/Continuum/SU2QuaternionGaussianHarmonicPowerRecursion.lean:44` | Exact gradient power rule. |
| `harmonic_power_step` | `lean/YMGap/Continuum/SU2QuaternionGaussianHarmonicPowerRecursion.lean:72` | Positive-degree Gaussian lowering; no linearity premise on the power base. |
| `harmonic_haar_power_step` | `lean/YMGap/Continuum/SU2QuaternionGaussianHarmonicPowerRecursion.lean:93` | Original Haar version for a head-linear base, with radial factor. |
| `relativeScalar_derivative` | `lean/YMGap/Continuum/SU2QuaternionRelativeHarmonicLowering.lean:43` | Actual relative scalar differentiated in each head coordinate. |
| `lower`, `lower_coeff` | `lean/YMGap/Continuum/SU2QuaternionRelativeHarmonicLowering.lean:61`, `lean/YMGap/Continuum/SU2QuaternionRelativeHarmonicLowering.lean:67` | Explicit lowering and its equality to the actual gradient pairing. |
| `lower_degree`, `lower_harmonic` | `lean/YMGap/Continuum/SU2QuaternionRelativeHarmonicLowering.lean:77`, `lean/YMGap/Continuum/SU2QuaternionRelativeHarmonicLowering.lean:93` | The iteration's two preserved requirements. |
| `gaussian_lowering_step` | `lean/YMGap/Continuum/SU2QuaternionRelativeHarmonicLowering.lean:104` | Concrete consumer of the generic recurrence. |
| `lowerIter`, `lowerIter_degree_zero` | `lean/YMGap/Continuum/SU2QuaternionRelativeHarmonicLowering.lean:114`, `lean/YMGap/Continuum/SU2QuaternionRelativeHarmonicLowering.lean:118` | Explicit terminating iteration and head-independent output. |
| `gaussian_pairing_lowerIter` | `lean/YMGap/Continuum/SU2QuaternionRelativeHarmonicLowering.lean:126` | All-degree Gaussian pairing evaluation. |
| `haar_pairing_lowerIter` | `lean/YMGap/Continuum/SU2QuaternionRelativeHarmonicLowering.lean:145` | Original Haar evaluation with explicit radial normalization. |

## Actual consumer and remaining join

The intended consumer is the remaining diagonal character pairing in
`heat_harmonic_diagonal`,
`lean/YMGap/Continuum/SU2QuaternionRelativeHarmonicSelection.lean:156`.
The new calculation is not yet its final reproducing formula. Missing:

1. Identify the computed degree-zero output with factorial times the
   actual substitution `translatedHeadPolynomial` by the retained link.
   Respect zero padding through an explicit padded target or the proved
   prefix/Haar carrier; raw unpadded coefficient equality is not assumed.
2. Supply exact radial/factorial and character leading-term normalization,
   using the already proved lower-degree harmonic annihilation.

Sol's bounded inventory found no existing repeated directional-derivative
substitution theorem or public radial/factorial identity in the searched
quaternion differential, Gaussian, translation and substitution modules.
The public substitution is `translatedHeadPolynomial`,
`lean/YMGap/Continuum/SU2QuaternionPolynomialHaarTranslation.lean:387`,
and coordinate semantics are supplied by
`translatedHeadPolynomial_head_coordinate`,
`lean/YMGap/Continuum/SU2QuaternionHeadSubstitutionPrefix.lean:139`.
This inventory is a source review, not an analytic result.

The actual all-block product map, changing-source cutoff control and
original-weight finite-time comparison still need to be joined. In
particular V_K*g_K*f varies with K; this calculation for a given p does
not supply a uniform bound for that family. The existing concrete fringe
reduction `energy_active`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveEnergy.lean:129`,
remains the source reduction to reuse. No identity-at-nome-one,
SAME-variance small rate, spatial/scaling control, continuum survival,
physical mass calibration, full QFT or other-group construction is proved.

## Verification and division of work

Three final focused checks passed 17 printed gates, all within
`{propext, Quot.sound}`. The two derivative commutation gates use only
`propext`. The dependency-complete concrete consumer target
`+YMGap.Continuum.SU2QuaternionRelativeHarmonicLowering:olean` passed.
Final logs contain no errors, warnings, classical dependencies or
`sorryAx`. No new hole, named analytic premise or canonical field change.

Checks were serialized through the safe launcher with one capped 20 GiB
worker. No full-root build, full-tree audit or guard was run. Automatic CI
remains disabled. Logs:

- `/tmp/ym-gap-derivative-commutation-check.log`
- `/tmp/ym-gap-gaussian-harmonic-power-recursion-check.log`
- `/tmp/ym-gap-relative-harmonic-lowering-check.log`
- `/tmp/ym-gap-harmonic-recursion-producers-build.log`
- `/tmp/ym-gap-relative-harmonic-lowering-build.log`

Sol supplied the bounded derivative-commutation draft and source inventory.
Main supplied the Gaussian recurrence, concrete lowering iteration,
integration fixes and serialized verification.
