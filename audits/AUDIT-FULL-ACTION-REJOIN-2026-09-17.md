# Full-action rejoin: source dependence and finite-test feasibility

Date: 2026-09-17 UTC. Source revision: `806bf5d`.
Scope: read-only mathematical/source review, followed by a work-plan update.
No new Lean theorem, compiler verification, or frontier closure is claimed.

## Unchanged whole-project goal

For every compact simple gauge group, construct nontrivial continuum
Yang--Mills on R^4 with the required same-theory QFT structure and a strictly
positive physical Hamiltonian mass gap. Retain the constructive, Mathlib-free
Lean substrate and its {propext, Quot.sound} axiom gate. This remains OPEN.

## 1. The next missing estimate, and algebra already available

The actual spatial potential is `spatialWeight`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSliceHeat.lean:70`.
The original transfer is `transferStep`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferStep.lean:51`;
its iterate is `terminalMessage`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalBracket.lean:118`.
The endpoint weight is V*T^n1, not T^n1 alone.

`adjacent_shared_defect`,
`lean/YMGap/Continuum/SU2QuaternionAdjacentPlaquetteHeat.lean:326`,
retains the two signed shared-link SU(2) channels, but its test enters as
`liftHead r`. It cannot absorb other factors depending on the source link.
`weightedResidual_pairing`,
`lean/YMGap/Continuum/SU2QuaternionWeightedBlockCentering.lean:77`, already
expresses an arbitrary weighted residual pairing as its conditional covariance
numerator, retaining the weight in every moment. Re-proving this identity
would not remove an analytic obligation.

The exact source-dependent covariance-response algebra also exists:
`connected_response_identity`,
`lean/YMGap/Continuum/RationalConnectedResponse.lean:26`.
Its specialization to a normalized positive reference functional mu is

    Z = mu(b) > 0;  p0 = P-mu(P);  q0 = Q-mu(Q);
    R_b = Z^2 * (Cov_(b*mu/Z)(P,Q) - Cov_mu(P,Q))
        = Z*mu((b-Z)*p0*q0) - mu((b-Z)*p0)*mu((b-Z)*q0).

This displayed specialization is mathematical bookkeeping for the next task,
not a newly checked declaration identifying a physical conditional measure.
The reference functional, full source-dependent b, normalization and probes
must first be pinned to the actual action. In particular, neither b nor the
combined temporal transfer test may be replaced by an independent spectator.
The identification of this shared-heat comparison with the relevant original
temporal-form term must also be supplied; the generic identity alone is not
that bridge.

The immediate objective is a quantitative signed bound on this full-source
remainder, sufficient for the diagonal energy budget of the original cleared
temporal covariance defect. The existing global consumers remain
`terminal_energy_variance_floor` and
`terminal_normalized_energy_variance_floor`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletCoercivity.lean:242`
and `:284`; their supplied fraction is still width-dependent.
The weighted decomposition and a width-independent cross-term summation budget
are also still required. Bounding one selected plaquette pair does not supply
the all-observable inequality.

## 2. What the available estimates do not supply

| Existing declaration | Actual scope and planning consequence |
|---|---|
| `conditionalMessage_lowerCertificate`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialConditionalMessage.lean:103`; `conditionalMessage_capCertificate`, same file:117 | Windows for the produced message; not windows for its product with V, and not small cross influence. |
| `no_universal_terminal_singleFactor_gap`, `lean/YMGap/Continuum/RationalWeightedProductGapObstruction.lean:316` | Refutes the generic preservation of the stated one-factor rate, even for a produced finite-model message. Does not refute the actual SU(2) theory or all smaller rates. |
| `atMostSix_bounds`, `lean/YMGap/Continuum/BF4ExactSlabLocalStarComparison.lean:96` | Full local-action floor/cap comparison; not a supplied small signed-response estimate. |
| `not_two_mul_inverseRate_lt_one`, `lean/YMGap/Continuum/BF4ExactSlabStarRateObstruction.lean:65` | The displayed coarse inverse-rate smallness condition is false. Do not reopen that numerical criterion unchanged. |
| `relativeTail_weighted_bound`, `lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:141` | Small later-minus-retained cutoff tail against a positive retained background; not smallness of that background's entire covariance response. |
| `response_activity`, `lean/YMGap/Continuum/BF4ExactSlabResponseInsertionActivity.lean:157` | Exact w^3 activity with a signed cofactor, not a bound on that cofactor. |
| `left_pair_response_zero`, `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:220`; `right_pair_response_zero`, same file:227; `response_ne_zero`, same file:278 | Pairwise vanishing does not justify dropping the third connected contribution. |

A quantitative full-source remainder bound sufficient for the temporal cross
budget was **NOT FOUND** in the reviewed `BF4ExactSlabFixedSpatial*.lean`,
`SU2QuaternionProductHeat*.lean`, `SU2QuaternionWeightedBlockCentering.lean`,
`RationalConnectedResponse*.lean`, `BF4ExactSlabResponseInsertionActivity.lean`,
`BF4ExactSlabLocalStarComparison.lean`,
`BF4ExactSlabStarNonneighborCommutation.lean`,
`BF4ExactSlabStarLocalInfluence.lean`, and
`BF4ExactSlabRetainedHeatHeadComparison.lean`.
This is a scoped source-search finding, not a theorem of nonexistence.

Decision: investigate the signed remainder itself. A small relative weight
variance would be a sufficient possible route, not a newly required field or
a proved property of V*T^n1. Do not add its generic Cauchy--Schwarz consumer
before identifying a usable physical producer. Similarly, the sharp unweighted
matrix estimate is deferred unless a genuinely weighted estimate consumes it.

## 3. The smallest box is not a fully propagated plaquette test

The following are deductions from existing membership characterizations, not
newly kernel-checked cardinality or transfer theorems.

`SliceLink`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLayerBoundary.lean:50`,
allows all three spatial directions at bases with coordinates <= width.
`baseLinks_mem_iff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSliceCarrier.lean:47`,
identifies the carrier with exactly those links, including its unused fringe.
By contrast `spatialFaces_mem_iff` and `temporalFaces_mem_iff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFacePlacement.lean:98` and `:104`,
require all three spatial base coordinates < width.
`activeBlocks`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialKineticMarginals.lean:83`,
uses exactly the lower spatial links of the temporal faces;
`kineticWeight_eq_indexedProduct`, same file:118, pins these to the actual
kinetic product.

Thus at width one only the three origin spatial links are kinetically paired.
Each of the three origin spatial plaquettes has two shifted links outside
that active set. At width two the origin plaquette in the x0-x1 plane has all
four boundary links active. Width two is the first width with such a plaquette.
The review does NOT establish T1=1, a zero plaquette response, or an operator
degeneracy theorem at width one; those would require their own proof.

Decision: do not use width one as evidence for a fully propagated bulk
plaquette estimate. Prefer a factorized symbolic calculation keeping the full
incident action. Any finite numerical test must first check that its chosen
geometry exercises the proposed implication.

## 4. Harmonic inclusion is not positivity of a finite prefix

The new shared-link identity accepts K>=2. The all-nome positivity certificate
`faceHead_floorCertificate`,
`lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:71`,
instead requires `headCutoff w <= K`; `headCutoff`, same file:55, is an explicit
deficit modulus, not a smallest positive cutoff. Its background extension
`headProduct_certificate`, same file:101, retains that guard.
The general geometric modulus `powBaseCutoff`,
`lean/YMGap/Continuum/HeatKernelConvGen.lean:266`, uses the numerator of an
explicit rational reciprocal, not a logarithmic search for the minimum K.

Decision: do not assume K=2 satisfies an all-nome positivity guard or launch
a raw expansion using its conservative cutoff. A smaller finite positive
prefix requires a separate checked positivity certificate. An exact signed
polynomial identity can instead be tested without invoking positivity, but
must be reported at that weaker scope. Neither option changes existing guards
or establishes the late-cutoff/depth/spatially uniform gap.

Existing finite positivity need not be rebuilt: `faceCertificate` and
`faceProductCertificate`,
`lean/YMGap/Continuum/BF4ExactSlabSmallNomeHaarComparison.lean:62` and `:70`,
apply at every cutoff under their stated small-nome guards. This enables
tests in that regime, not a replacement for the missing scaling estimate.
`partialFactors_boundary_haar`,
`lean/YMGap/Continuum/SU2QuaternionPartialFactorizedHaar.lean:65`, and
`quaternionHaar_eq_compactBivalentFactorizedHaar`,
`lean/YMGap/Continuum/SU2QuaternionBivalentHaarContraction.lean:219`, provide
existing exact factor-list contraction. A residual-pairing test must keep
the extra weight factors in `weightedResidual`,
`lean/YMGap/Continuum/SU2QuaternionWeightedBlockCentering.lean:33`, specialized
by `terminalResidual`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalDirichletCoercivity.lean:104`.
Removing a fringe factor as if it occurred only once in a vacuum integral
does not establish an identity for that residual pairing.

## 5. Execution boundary

Two parallel read-only reviews covered source dependence and finite-test
geometry. The work plan now prioritizes the full-source signed estimate and
reuses existing response algebra; no additional assumption bundle is planned.
Independent review of the resulting report and plan checked the centered
algebra, geometry, declaration citations and explicit proof-status boundaries.
No `.lean` file, `sorry`, axiom, frontier statement, analytic guard or resource
limit changed. No build, full audit, guard run or literature scan was performed.
The small-nome fixed-spacing results are preserved. Spatial/scaling control,
physical mass calibration, full same-theory QFT and every-group realization
remain open; this planning checkpoint closes none of them.
