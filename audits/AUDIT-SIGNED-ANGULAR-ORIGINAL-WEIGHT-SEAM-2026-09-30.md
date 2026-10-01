# Audit: signed angular estimate versus original Wilson family weight

Date: 2026-09-30 UTC. Classification: source review and proof-plan boundary,
not a Lean result, obstruction theorem, or new estimate.

CORRECTION AND FOLLOW-ON (2026-09-30): this review overlooked existing
`BF4ExactSlabFixedSpatialProjectedSourceEnergy.energy_projected_source` and
`BF4ExactSlabFixedSpatialSourceTaylor.energy_taylor_angular`. They already
pin the Taylor formula to original energy for fringe-independent sources.
The actual distinction was q^2 versus the odd marginal q*Pq, not the energy
identity itself. The subsequent checked
`BF4ExactSlabFixedSpatialMarginalTaylor.finite_family_increment_taylor`
now retains that signed weight correction and the whole padded signed
family's SAME partition. Exact evidence is in
`AUDIT-SIGNED-ORIGINAL-MARGINAL-TAYLOR-2026-09-30.md`.
The original next-producer diagnosis below is superseded; the quantitative
SAME-variance/scaling estimate remains open.

## Exact original family objects

`BF4WilsonPlaquetteFamilySourcePin.familyExpression`,
`lean/YMGap/Continuum/BF4WilsonPlaquetteFamilySourcePin.lean:49-71`, is the
literal radius-zero signed sum of physical plaquette Wilson expressions.
`source_family_span` and `mixedProduct_square` at lines 92-117 and 154-178 pin
its finite source polynomial and diagonal square coefficientwise.

`BF4WilsonPlaquetteFamilyIncrement.source_difference_family` and
`source_square_family`,
`lean/YMGap/Continuum/BF4WilsonPlaquetteFamilyIncrement.lean:96-113`, show
that shifting the whole signed source gives the existing spatial jump and
that its square retains all signed cross terms. The finite pin
`finite_family_increment_pin` at lines 121-133 identifies its finite original
window ratio with twice the existing normalized temporal energy.

The original finite measure is not an independently selected marginal:
`BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.originalWindowScalar`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.lean:117-131`,
pins it to `windowRatio`. `windowRatio` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowPairing.lean:132-137`
uses the actual observed/terminal-message numerator and the same positive
terminal-pair denominator. The finite-value definition is numerator times
the original reciprocal in `lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetExpectation.lean:47-62`;
the finite partition is the original `heatProductHaar` in
`lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetReciprocal.lean:46-63`.

`BF4WilsonAllNomePlaquetteFamilyVariance.centered_norm_pin`,
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyVariance.lean:111-136`,
pins the original mean and diagonal square moments, hence the centered scalar
moment, through that same original ratio. It does not identify completed
carriers or provide an off-diagonal carrier map. The resulting floor is
`centered_norm_floor` at lines 140-144; it is a lower bound, not a relative
upper estimate.

## Angular Taylor weight and missing comparison

`SU2QuaternionProductHeatAngularTaylor.weightedAngularEnergy`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularTaylor.lean:43-47`, is
the auxiliary quantity

    sum_i quaternionHaar(tail+1, (a*a) * blockAngularSquare(i,f)).

`sourceEnergy_taylor_angular` at lines 107-117 gives an exact first-order
coefficient for an abstract full product-heat source energy, but retains both
signed remainders. `sourceEnergy_le_angular_add_quadratic` at lines 121-132
retains a source-dependent quadratic budget. The `a^2` weight is not the
original odd marginal without a correction. The existing original-energy
pins were missed in this review; the follow-on above retains the correction,
shared partition and terminal factors explicitly.
Generic `SU2QuaternionHaarAngularIBPAt.quaternionHaar_weighted_angular_at`,
`lean/YMGap/Continuum/SU2QuaternionHaarAngularIBPAt.lean:99-110`, retains both
product-rule terms for arbitrary polynomials, but is not by itself an
action-derivative identity for this original signed family.

The original proposed next producer was a coefficient-exact same-cutoff comparison
for the specific family/jump source: identify the complete weighted angular
Taylor integral and its signed remainder terms against the original finite
numerator, with the original partition and terminal factors unchanged. This
was a proposed missing comparison, not an asserted impossibility or estimate.
The correction and checked follow-on above supersede that diagnosis.

The existing downstream consumer is
`BF4WilsonAllNomeSectorSourceTransfer.relative_derivative_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomeSectorSourceTransfer.lean:114-126`.
It accepts a same-source original energy upper bound
`E x <= c * B(x,x)` and transfers it to the actual original derivative/core
form. The angular Taylor identities above do not yet supply that input for
the signed plaquette family. No carrier identification, physical scaling
estimate, OS conclusion, or continuum mass-gap claim is made here.
