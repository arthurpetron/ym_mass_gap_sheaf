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
