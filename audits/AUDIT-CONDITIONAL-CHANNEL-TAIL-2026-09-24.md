# Conditional channel tail audit — 2026-09-24

## Scope and baseline

This audit records the six narrow serialized checks that establish a
conditional-channel, one-link harmonic-tail result for the actual fixed-spatial
endpoint source.  The repository baseline for the work was `78ffbf9`.

This is a finite-cutoff result.  It is not a full-root audit, a joint four-link
tail estimate, a retained-heat floor, a comparison with the SAME centered
variance, a scaling theorem, or a continuum conclusion.

## Checked chain

### 1. Partial spectator swap

`SU2QuaternionPartialSliceSwap.swap` exchanges lower block `i` with upper
block `n+i` exactly when `i` belongs to the selected list; other blocks remain
fixed (`lean/YMGap/Continuum/SU2QuaternionPartialSliceSwap.lean:39`).
The carrier lemmas `reindex_fixed_of_selected_independent`,
`reindex_familyProject`, and `reindex_familyProject_fixed` show that the swap
fixes a supported polynomial independent of the selected blocks and that
reindexing commutes with the selected family projection
(`lean/YMGap/Continuum/SU2QuaternionPartialSliceSwap.lean:258`,
`lean/YMGap/Continuum/SU2QuaternionPartialSliceSwap.lean:285`,
`lean/YMGap/Continuum/SU2QuaternionPartialSliceSwap.lean:303`).

This supports the exact shared-active conditional Fubini identity
`partialSwap_familyProject_pairing`: in the doubled Haar integral, only the
selected spectator coordinates of the second factor are swapped into the
auxiliary slice, while the unselected active coordinates remain shared.  The
result is the original Haar pairing of the two family projections
(`lean/YMGap/Continuum/SU2QuaternionPartialSwapPairing.lean:62`).  Its proof
integrates the selected upper blocks and transports the projected polynomial
back through the partial swap.  It does not identify this construction with a
partial `productMap`.

### 2. Original-kernel positivity and cone domination

The bilinear family-channel pairing is identified with the actual conditional
product-heat kernel on the doubled carrier, with all unselected variables
shared by `familyChannelPair_eq_conditionalKernel`
(`lean/YMGap/Continuum/SU2QuaternionFamilyChannelCone.lean:131`).
Consequently, `familyChannelPair_nonnegative` obtains mixed positivity from a
certificate for that original positive kernel
(`lean/YMGap/Continuum/SU2QuaternionFamilyChannelCone.lean:147`).

The channel polynomials themselves can be signed; no termwise positivity of
those polynomials is assumed.  Applying mixed positivity to the two certified
cone elements `c*p-d` and `c*p+d` gives the SAME-form estimate

`familyChannelQuadratic n w K ids d ≤ (c*c) * familyChannelQuadratic n w K ids p`

under the explicit cone certificates in `familyChannelQuadratic_le_of_cone`
(`lean/YMGap/Continuum/SU2QuaternionFamilyChannelCone.lean:241`).

### 3. Actual endpoint regularity

For the complete projected endpoint source
`q = projectedEndpointSource w K width (terminalMessage w K width n)`, the
already proved positive-cone certificate is instantiated at an actual active
physical link.  Each angular plane satisfies

`Q_F(D_ij q) ≤ endpointRelativeCap(w)^2 * Q_F(q)`

for every bounded Nodup spectator list in
`projectedEndpoint_familyChannelDerivative_le`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointChannelRegularity.lean:61`).
Summing the six angular planes gives the literal factor-six bound

`sixValue (Q_F(D_ij q)) ≤ 6 * endpointRelativeCap(w)^2 * Q_F(q)`

with no width- or cutoff-dependent factor added at this step by
`projectedEndpoint_familyChannelAngular_le`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointChannelRegularity.lean:91`).

The exact channel angular identity needed for the tail argument is
`channelSource_blockAngularSquare_eq`.  For a block outside `ids`, it rewrites
the Gram-weighted sum of channel-source angular squares as the six family
channel quadratics of the corresponding derivatives of the original source
(`lean/YMGap/Continuum/SU2QuaternionChannelAngularContraction.lean:166`).

### 4. Summed channel high tail

`projectedEndpoint_familyChannel_highTail_small` applies the existing
selected-block Casimir threshold separately to every actual channel source,
sums with the nonnegative Gram weights, uses the exact angular identity, and
then applies endpoint channel regularity.  The explicit degree modulus cancels
the positive threshold and yields

`channelSum channels (H[(selected high part of channelSource)^2])`

`≤ epsilon * familyChannelQuadratic ... q`.

The statement and proof are `projectedEndpoint_familyChannel_highTail_small`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointChannelTail.lean:122`).
Only the Gram coefficients are used as nonnegative weights in this summation;
the signed channel polynomials are not asserted positive.

The actual plaquette specialization replaces the arbitrary family by
`spectatorBlocks width face`.  Observable-block membership of the selected
link proves that it lies outside this complementary spectator family, while
the filtered range supplies Nodup and boundedness in
`projectedEndpoint_plaquetteChannel_highTail_small`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointChannelTail.lean:192`).

## Explicit guards and uniformity

The terminal tail theorem retains the following hypotheses:

- fixed nome `w` with `0 < w < 1`;
- `K ≥ endpointRelativeCutoff w`;
- arbitrary spatial `width` and terminal depth `n`;
- an actual selected base link whose block belongs to `activeBlocks width`;
- a Nodup list `ids`, every entry of which is below the complete carrier size;
- the selected active block is outside `ids`;
- `epsilon > 0`; and
- `L ≥ endpointTailDegree w epsilon he`.

The plaquette specialization replaces the last family-side conditions with
membership of the selected block in `observableBlocks width face`; the
existing complementary-filter geometry discharges the spectator guards.
Constants are independent of width, depth, and every cutoff past the stated
threshold, but may depend strongly on the fixed nome through
`endpointRelativeCap w` and `endpointTailDegree w epsilon he`.

## Verification record

All checks used the repository's serialized safe-check path at default Lean
elaboration limits, with one worker, a 2 GiB worker limit, and a 12 GiB reserve.
No safety stop occurred in this turn.  Earlier namespace and arithmetic-rewrite
failures were repaired before the final checks.

| Log | Checked declarations / gates | Result |
| --- | ---: | --- |
| `/tmp/ym-gap-partial-slice-swap-check-4.log` | 10 | pass |
| `/tmp/ym-gap-partial-swap-pairing-check-2.log` | 1 | pass |
| `/tmp/ym-gap-channel-angular-identity-check-1.log` | 11 | pass |
| `/tmp/ym-gap-family-channel-cone-check-2.log` | 5 | pass |
| `/tmp/ym-gap-endpoint-channel-regularity-check-1.log` | 2 | pass |
| `/tmp/ym-gap-endpoint-channel-tail-check-1.log` | 2 | pass |

The total is 31 printed axiom gates.  Every printed declaration depends only
on the permitted kernel axioms `{propext, Quot.sound}`.  The checked sources
contain no admitted holes (`sorry` or new axioms) in this chain.  These narrow
checks do not imply that the entire repository was rebuilt or audited.

## Remaining boundary

The result controls one selected link after conditional spectator-channel
decomposition.  It does not itself give a simultaneous four-link truncation,
a joint retained-heat floor, or a bound by the SAME centered variance.  The
planned joint-comparison route remains unproved; an alternative direct-response
route remains possible.  Scaling control and continuum closure also remain
open.  The present theorem therefore does not establish, or require us to
claim, that a new projector is the necessary route beyond this point.

## Reviewed next argument, not a checked result

After this milestone, a shorter candidate uses the already constructed full
degree-path expansion of each signed channel source. The unattenuated path
pairings are nonnegative by `full_path_pairing_nonnegative`
(`lean/YMGap/Continuum/SU2QuaternionCyclicDiagonalRemainder.lean:70`).
The actual attenuation exponent is d*(d+2), and `productAttenuation` and
`totalCasimir` are its product and rational sum
(`lean/YMGap/Continuum/SU2HeatProductTaylorRemainder.lean:23`,
`lean/YMGap/Continuum/SU2HeatProductTaylorRemainder.lean:28`).

For a positive integer M and K>=M, the candidate scalar inequality is

    M * productAttenuation(w,K,ds) >= w^M * (M-totalCasimir(ds)).

Below total Casimir M every label lies below K and exponent monotonicity
applies; above M the right side is nonpositive. Summing the existing positive
path masses would bound the heat pairing from the zeroth and first moments.
The intended original-channel aggregation has A=Q_F(q), angular cost
E<=24*C(w)^2*A from four active links, and a computed M>=48*C(w)^2,
giving a proposed positive floor (w^M/2)*A at fixed nome. The new scalar
inequality and its actual aggregate consumer are NOT proved by this audit or
the six checks above. Neither would furnish a centered-variance lower bound.
This is the next proof candidate, not a new assumed interface or closed node.
