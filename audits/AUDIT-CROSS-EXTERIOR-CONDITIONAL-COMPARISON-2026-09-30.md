# Original shared-link conditional comparison with both normalizers

## Whole-project goal and exact scope

The goal remains OPEN: constructive continuum Yang--Mills on R^4 for
every compact simple group, with SAME-theory QFT axioms, nontriviality
and a finite positive physical Hamiltonian gap.

This increment constructs a finite approximate conditional-kernel comparison
for the ORIGINAL shared-link SU(2) slab action, not a new action or an
independent-face surrogate. Its assumptions are rational nome 0<w<1,
K>=headCutoff(w), and membership of the updated link in the original slab.
No open analytic estimate is assumed.

Let A be the original product of incident face weights at link j, let S
exchange every exterior coordinate between two copies while fixing j in
both, and put A'=S A. Let D=project_j A and E=S D=project_j A'. With
d=incidentIds.length, ell=headFloor(w)^d, and U=prefixCap(w)^d, the constructed
certificate is

    U^2 A E - ell^2 A' D >= 0.

The inequality is certificate order on the original doubled Haar carrier,
under every certified nonnegative joint-copy insertion. Both actual
normalizers remain polynomials; neither is replaced by a scalar marginal.

## Actual-object pins and raw comparison

Paths in this table start at `lean/YMGap/Continuum/`.

| Declaration | File:line | Checked content |
| --- | --- | --- |
| `exteriorSwap_lower_fixed`, `exteriorSwap_lower_moves` | `SU2QuaternionSharedBlockExteriorSwap.lean:41`, `:51` | The updated original coordinate stays fixed; other lower coordinates move to the upper copy |
| `reindex_project_commutes` | `SU2QuaternionSharedBlockExteriorSwap.lean:63` | Selected-coordinate Haar integration commutes with that exterior exchange |
| `incidentHeatLowerCertificate`, `incidentHeatUpperCertificate` | `BF4ExactSlabStarBandCertificate.lean:118`, `:129` | Actual incident product has floor ell and cap U despite shared face variables |
| `otherNormalizer_project_pin` | `BF4ExactSlabCrossExteriorStar.lean:88` | E is the actual projection of A' at the SAME updated link |
| `otherNormalizer_lift_pin` | `BF4ExactSlabCrossExteriorStar.lean:96` | E equals the lifted original D under arbitrary Haar insertions |
| `inPlaceNormalizer_head_pin` | `BF4ExactSlabCrossExteriorStar.lean:106` | D agrees with the existing original head normalizer, restored to original coordinates |
| `full_marginal_pin` | `BF4ExactSlabCrossExteriorStar.lean:115` | The actual full-action marginal is D times the entire unchanged complementary action |
| `crossStarComparison` | `BF4ExactSlabCrossExteriorStar.lean:194` | Constructed U^2 A E - ell^2 A' D certificate |

Multiplication uses the existing sum-of-squares certificate product
construction. It does not assume independence of overlapping plaquettes.
The independent source review confirmed the comparison orientation: after
justified normalization, it bounds the other-exterior conditional kernel
by (U/ell)^2 times the first-exterior kernel.

## Finite reciprocal argument

For each actual denominator D,E, let G_D(k),G_E(k) be the existing finite
positive geometric reciprocal polynomials, using the SAME U. Their exact
identities are D G_D+e_D=1 and E G_E+e_E=1. Put rho=1-ell/U, so 0<=rho<1.
The key identity is

    U^2 A G_D - ell^2 (1-rho^k) A' G_E
      = (U^2 A E - ell^2 A' D) G_D G_E
        + U^2 A G_D e_E
        + ell^2 A' G_E (rho^k-e_D).

Every term on the right has a constructed nonnegative certificate.
In particular, positivity of G_D and G_E is proved from the signed geometric
remainder, not inferred from a symmetric error interval. No configurationwise
division, limiting inverse or pointwise positivity oracle is used.

| Declaration | File:line | Checked content |
| --- | --- | --- |
| `correctorCertificate`, `reciprocalCertificate` | `QuaternionHaarReciprocalCrossComparison.lean:36`, `:45` | Positivity of the actual finite reciprocal polynomials |
| `reciprocalCrossComparisonOfCross` | `QuaternionHaarReciprocalCrossComparison.lean:108` | The exact identity above consumes the raw cross comparison |
| `starUpper_positive`, `starLower_le_starUpper` | `BF4ExactSlabStarReciprocalParameters.lean:40`, `:50` | Actual star parameters form a positive ordered window |
| `starRadius`, `starRadius_nonnegative`, `starRadius_lt_one` | `BF4ExactSlabStarReciprocalParameters.lean:61`, `:66`, `:73` | Explicit reciprocal error ratio in [0,1) |
| `starApproximationCutoff` | `BF4ExactSlabStarReciprocalParameters.lean:81` | Computable common tolerance cutoff |
| `firstKernel`, `otherKernel` | `BF4ExactSlabConditionalStarComparison.lean:57`, `:62` | Actual A G_D and A' G_E on the original doubled carrier |
| `bothNormalizerErrors` | `BF4ExactSlabConditionalStarComparison.lean:100` | One supplied tolerance and computed cutoff control BOTH actual normalization defects |
| `kernelComparisonCertificate` | `BF4ExactSlabConditionalStarComparison.lean:117` | Concrete original-slab instance of the positive comparison |
| `weighted_kernel_comparison` | `BF4ExactSlabConditionalStarComparison.lean:163` | ell^2(1-rho^k) H[A'G_E r] <= U^2 H[A G_D r], for every certified nonnegative joint insertion r |

The constants ell,U,rho and the tolerance cutoff depend explicitly on nome
w and the actual incident count d, not on the late heat cutoff K. The
existing `BF4ExactSlabLinkStarGeometry.incidentIds_length_le_six` at
`lean/YMGap/Continuum/BF4ExactSlabLinkStarGeometry.lean:89` bounds d by six.
The comparison theorem retains d; it does not yet rewrite its loss to a
literal exponent twelve. No beta/spacing-uniform estimate is asserted.

## Parallel exact variance identity

`SU2QuaternionGlobalVarianceReplica.global_variance_identity` at
`lean/YMGap/Continuum/SU2QuaternionGlobalVarianceReplica.lean:131` proves

    H_2n[W(x)W(y)(f(x)-f(y))^2]
      = 2 * (H_n[W] H_n[W f^2] - H_n[W f]^2).

Both W and f are arbitrary supported original polynomials; the identity
requires no positivity or inverse hypothesis. Its proof expands the square,
retains the SAME weight in all three moments, and uses exact two-copy Haar
factorization. `replicaDifference_supported` at the same file's line 50
supplies support of the actual difference. This establishes the algebraic
starting identity for the path calculation, not its ordered-coordinate
telescope, normalization or energy inequality.

## Remaining mathematical join

This closes the raw two-normalizer and finite-reciprocal comparison, not
the limiting conditional-kernel/path-energy comparison. The next consumer
must identify these actual reciprocal approximants, with joint insertions,
with the EXISTING conditional inverse pairings; then compose with the
original replica-cut comparison and the ordered-coordinate variance path.
Neither a new assumed-kernel bundle nor a generic completion theorem
supplies that identification.

Existing consumers are `BF4ExactSlabStarCompletedInverse.inverseState`
at `lean/YMGap/Continuum/BF4ExactSlabStarCompletedInverse.lean:107`,
`normalizerCompletion_injective` at `:169`, `normalizer_inverseState`
at `:196`, and `conditionalState` at `:215`. They act in the original
complementary-action weighted exterior completion and use an existing
approximation sequence. This increment does NOT yet prove that the new
doubled finite reciprocal pairings converge to those same objects.
Independent source review confirmed both this residue and the finite
comparison's orientation and common-cutoff scope.

The preceding candidate N*(prefixCap/headFloor)^(2C+12) remains a reviewed
paper budget, not a Lean Poincare theorem. Its cut-area dependence would
still not supply the useful signed spatial/scaling estimate. No improved
conditional-generator gap, OS-transfer gap or physical mass is claimed.
Continuum survival, same-theory reconstruction, physical-time calibration,
full QFT and every-group construction remain open. Canonical chart states
are unchanged, so no chart is reprinted.

## Verification and parallel work

Eight final focused module checks passed all 59 printed gates within
{propext, Quot.sound}: SharedBlockExteriorSwap 9, CrossNormalizedComparison 3,
StarBandCertificate 7, CrossExteriorStar 19, StarReciprocalParameters 6,
ReciprocalCrossComparison 4, ConditionalStarComparison 8,
GlobalVarianceReplica 3.
No sorry or custom axiom was introduced, and no existing sorry discharged.

All checks were serialized through the monitored launcher, one worker,
20 GiB cap, 12 GiB OS reserve and continuous safety telemetry. Short checks
completed in the initial call; the one yielded check was inspected after
independent mathematical work, not polled every ten seconds. No full-root
build, global audit or frontier guard was run. Root imports are registered
without claiming root compilation. Routine literature scanning was not
repeated within its twelve-hour cache interval.

Final logs under `/tmp/`: `ym-shared-exterior-swap-20260930.log`,
`ym-cross-normalized-comparison-20260930.log`,
`ym-star-band-certificate-20260930.log`, `ym-cross-exterior-star-20260930.log`,
`ym-star-reciprocal-parameters-20260930.log`,
`ym-reciprocal-cross-comparison-20260930.log`, and
`ym-conditional-star-comparison-20260930.log`, and
`ym-global-variance-replica-20260930.log`.

Luna constructed the original star window and scalar reciprocal parameters;
Sol supplied exterior exchange, cross-product algebra, the finite reciprocal
identity, exact global variance identity and independent scope review. Root
proved the actual original-action pins and instantiated the normalized
comparison. Lean verification remained
serialized while mathematical source work ran in parallel.
