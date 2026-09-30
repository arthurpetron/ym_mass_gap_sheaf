# Original signed feature cancellation

Date: 2026-09-30 UTC. This is finite polynomial algebra on the original
SU(2) law, not a new spectral-gap or continuum theorem.

## Exact mathematical increment

For shared-feature positions t, write
`A_t = leftMoment(L,1,t)`, `Af_t = leftMoment(L,f,t)`,
`B_t = rightMoment(R,1,t)` and `Bg_t = rightMoment(R,g,t)`.
The signed numerator is exactly, coefficientwise,

```
(sum A_t B_t)(sum Af_t Bg_t) - (sum Af_t B_t)(sum A_t Bg_t)
  = sum_{s<t} (A_s Af_t - A_t Af_s)(B_s Bg_t - B_t Bg_s).
```

There is no factor of one half: each unordered pair of LIST POSITIONS
appears once. No distinct-label hypothesis is needed. The generic proof is
`RatPolyTwoByTwoCauchyBinet.determinant_eq_pairSum`,
`lean/YMGap/Continuum/RatPolyTwoByTwoCauchyBinet.lean:113`.
`productSum`, `minor`, and `pairSum` are at lines 23, 28, and 32.

The original shared-term coefficient occurs in `leftMoment` through
`outsideFeature`, not again in `rightMoment`; a pair therefore carries
exactly the product of its two original coefficients. The one-sided action
factors stay inside the moments. Definitions: `leftMoment` and `rightMoment`,
`lean/YMGap/Continuum/SU2QuaternionSeparableConditionalMoments.lean:30`
and `:33`. Its `weighted_moment` at `:84` supplies the existing exact
factorization used by the original-law pin.

## Same-law connection and certificate consumer

All declarations in this paragraph are in
`lean/YMGap/Continuum/BF4ExactSlabTwoLinkFeatureWedge.lean`:

- `signedFeatureNumerator_wedge_pin:71` rewrites the existing moment
  determinant as the minor sum.
- `covarianceVector_wedge_pin:89` connects it to the ORIGINAL covariance
  vector, for tests independent of the opposite integrated block. It uses
  `BF4ExactSlabTwoLinkFeatureMoments.covarianceVector_feature_pin`,
  `lean/YMGap/Continuum/BF4ExactSlabTwoLinkFeatureMoments.lean:129`.
- `wedgeBudget:98` replaces only the mixed term in
  `rho*(N_pp+N_qq)-2*N_pq`. It does not apply opposite-block independence
  incorrectly to the diagonal pairs p,p or q,q.
- `covarianceBudget_wedge_pin:103` and `certificate_of_wedgeBudget:119`
  transport a SUPPLIED certificate to the literal original budget.
- `covarianceVector_symm:129`, `covarianceBudget_symm:138`, and
  `certificate_of_reversed_wedgeBudget:148` swap tests, not the link list.
  The original ordered union [left,right] and its normalizer are unchanged.

The last point matters for actual predictions: integrating left makes
the left prediction independent of LEFT, whereas the feature formula's
first test must be independent of RIGHT. This independence is already
proved by `predictionRep_independent`,
`lean/YMGap/Continuum/BF4ExactSlabBlockPredictionCovariance.lean:72`.
The reversed certificate transport handles these exact hypotheses; it
does not assume a permutation of integrations or select a quotient
representative.

The certificate's output type is the input of `inverse_covariance_bound`,
`lean/YMGap/Continuum/BF4ExactSlabBlockCovarianceCertificate.lean:58`.
That existing checker retains the constructed inverse of the ACTUAL
normalizer, with no change in rho. The existing completed consumer is
`residual_pair_lower_of_certificates` in the same file at `:83`; it still
requires certificates for every actual prediction approximant and a
coefficient in [0,1]. No such family is produced here. The detached action
is still counted once through the original background carrier.

## What has not been proved

Neither positivity of the individual minor products, a useful strict rho,
uniformity in cutoff/extent/coupling/spacing, nor a bounded feature rank is
asserted. The finite pair sum can grow with the shared heat expansion.
No scalar lower bound replaces the actual normalizer. The result does not
evade the checked shared-heat degree obstruction or the conservative patch
coefficient obstruction.

The remaining mathematical task is a useful estimate of this signed sum
against the SAME original diagonal covariance on justified scaling, or
collective/actual-auxiliary control that bypasses a universal pairwise
bound. No new analytic input structure is introduced. Ordinary full-action
conditional covariance is not an OS-transfer or physical-Hamiltonian gap.
A03 and all same-theory continuum/Clay requirements remain open.

## Verification and parallel work

Sol implemented the finite algebra while the main agent integrated the
original covariance/certificate connection. Luna and Sol independently
reviewed signs, coefficient multiplicity, original action/normalizer and
the prediction-order issue. Lean compilation was serialized, not parallel.

Final focused checks via `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check <file> --check-output <matching olean>`:

- `RatPolyTwoByTwoCauchyBinet.lean`: exit 0, approximately 0.79 s;
  its three computational definitions are axiom-free and its determinant
  theorem uses only {propext, Quot.sound}.
- `BF4ExactSlabTwoLinkFeatureWedge.lean`: exit 0, approximately 6.50 s;
  all nine printed gates use only {propext, Quot.sound}.

These short checks completed in their initial calls; no live long job was
polled. A missing namespace and an elaboration-order issue were corrected
before these final passing checks. No new sorry/axiom, weakened field or
broad build/audit/guard. Root imports were added; the root file was not
compiled. The canonical displayed claims are unchanged, so no chart was
reprinted.

## Quantitative follow-up: stop before rebuilding the absolute-window route

Reviewed after commit `56bff05`, 2026-09-30 UTC. This section is source
review and mathematical analysis, NOT an additional kernel-checked result.
The earlier verification record applies only to the two modules above.

The feature list is a monomial expansion, not a positive orthogonal-channel
decomposition. The two antisymmetric minors can have different signs.
Thus the checked identity does not itself yield a positive certificate or
an operator-norm improvement. Sol independently reviewed this issue.

One tempting next estimate charges only the shared face. The geometry
already proves that distinct physical links share at most one plaquette:
`BF4ExactSlabSharedFaceUniqueness.sharedIds_length_le_one`,
`lean/YMGap/Continuum/BF4ExactSlabSharedFaceUniqueness.lean:24`.
The actual one-face form comparison is also already available:
`BF4ExactSlabSharedFaceComparison.shared_weighted_bounds:88` and
`shared_signed_pair:127` in
`lean/YMGap/Continuum/BF4ExactSlabSharedFaceComparison.lean`.
Luna checked these declarations; they do not construct the retained
reference's conditional projections or a completed residual-angle bound.

**Quantitative rejection before implementation.** Put L=headFloor(w),
U=prefixCap(w). Bounding both products in the crossed determinant by
[L^2,U^2] suggests the coefficient

```
rho_window = (U^2-L^2)/(U^2+L^2).
```

This is only a proposed sufficient bound, not an identified actual
conditional correlation. The existing theorem
`thirtyTwo_mul_headFloor_le_prefixCap`,
`lean/YMGap/Continuum/BF4ExactSlabSharedWindowFloorBound.lean:57`,
gives U>=32L, with L>0 by `headFloor_positive`,
`lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:52`.
Consequently U^2>=1024L^2, and the exact scalar calculation

```
1025*(U^2-L^2) - 1023*(U^2+L^2) = 2*(U^2-1024L^2) >= 0
```

gives rho_window>=1023/1025. Even degree two cannot satisfy
degree*rho_window<1. This proposed compiler therefore has no sufficient
producer for the intended neighbor-budget consumer. Both agents stopped
before creating its proposed certificate and four-copy-variance modules.
No Lean file was edited and no compiler was run in this follow-up.

This revisits an already known failure class, not a new Yang--Mills
obstruction: `not_absolute_window_half_norm_inference`,
`lean/YMGap/Continuum/BF4ExactSlabSharedWindowInfluenceObstruction.lean:112`,
already refutes a strong universal inference from this window. A sharper
original-action estimate is not refuted. Do not restart this branch merely
because the twelve-face exponent has been reduced to one.

### The existing consumer does not require pointwise SOS

For the actual prediction representatives, write
`C_n(p,q)=inverseCovarianceSequence(...,p,q,n)`; its definition keeps
the actual inverse normalizer and detached background:
`lean/YMGap/Continuum/BF4ExactSlabBlockPredictionCovariance.lean:87`.
The already-proved sufficient input is the integrated inequality
`2*C_n(p,q) <= rho*(C_n(p,p)+C_n(q,q))`, with 0<=rho<=1.
Its direct consumer is `residual_pair_lower_of_dense_covariance_bound`,
`lean/YMGap/Continuum/BF4ExactSlabBlockPredictionAngle.lean:116`.
The completed-state version is `residual_pair_lower_of_prediction_bound`
in the same file at `:53`. A polynomial SOS certificate is one sufficient
way to supply this bound, not a necessary intermediate theorem. Requiring
positivity separately at every exterior configuration is stronger than
this integrated consumer and can discard the needed signed cancellations.

The narrower alternative is still the reverse-energy inequality only on
the actual second coupled auxiliary, consumed by `finiteCovariance_sq_bound`,
`lean/YMGap/Continuum/BF4ExactSlabChebyshevCovarianceBound.lean:102`.
Neither route requires first proving a universal pairwise bound for all
independent tests. A new analytic estimate is still required; no replacement
hypothesis bundle is warranted.

### Targeted literature check, not a routine listing rescan

Shen--Zhu--Zhu, [A stochastic analysis approach to lattice Yang--Mills at
strong coupling](https://arxiv.org/pdf/2204.12737), equations (1.1)--(1.3)
and section 1.2, uses the Wilson exponential action and Langevin dynamics.
For SU(N) its stated smallness condition is |beta|<1/[16(d-1)], hence
|beta|<1/48 in d=4. Its curvature-based functional inequalities and
exponential clustering therefore do not supply the missing weak-coupling
estimate for this repository's original truncated heat action. No action
identification or constructive import of that paper was performed. This
is a scope comparison, not an independent verification of its proof.
The cached math-ph listing was reused; no new listing scan was made.
