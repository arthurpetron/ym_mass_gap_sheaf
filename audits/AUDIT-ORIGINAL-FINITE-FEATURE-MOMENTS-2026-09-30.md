# Original weighted moments through finitely many interaction features

## Mathematical result and consumer

For distinct selected blocks a,b, write the actual collar as L*R*K, with
L independent of b, R independent of a, and K the shared-face heat product.
Let f be independent of b and g of a. Split each raw monomial term t of K
as u_t*v_t, where u_t retains its coefficient and every non-b coordinate,
and v_t retains only the b coordinates with coefficient one. Then

    M(f,g) = sum_(t in K) P_a(L*f*u_t) * P_b(R*g*v_t)
           = P_[a,b](L*R*K*f*g).

The index list is K, not the expansion of f, g, L or R. Thus its length
does not depend on the test degree. Both one-sided weights remain inside
the exact moments. Every exterior coordinate remains symbolic.

- Monomial splitting: `term_factorization`,
  `lean/YMGap/Continuum/SU2QuaternionBlockMonomialFeatures.lean:85`.
- Explicit moment functions and indexed sum: `leftMoment`, `rightMoment`,
  `featureMoment`, respectively
  `lean/YMGap/Continuum/SU2QuaternionSeparableConditionalMoments.lean:30`,
  `:33`, `:37`.
- Weighted identity: `weighted_moment`,
  `lean/YMGap/Continuum/SU2QuaternionSeparableConditionalMoments.lean:84`.
- Independence of both selected slots: `featureMoment_independent`,
  `lean/YMGap/Continuum/SU2QuaternionSeparableConditionalMoments.lean:134`.

The actual slab instance uses the original link indices and the literal
`leftOnlyHeat`, `rightOnlyHeat`, `sharedHeat`. It identifies

    D    = M(1,1)       N_f  = M(f,1)
    N_g  = M(1,g)       N_fg = M(f,g)
    N    = D*N_fg - N_f*N_g.

Sources in `lean/YMGap/Continuum/BF4ExactSlabTwoLinkFeatureMoments.lean`:
`moments` at line 51; `normalizer_feature_pin` at 75;
`inserted_left_feature_pin` at 85; `inserted_right_feature_pin` at 93;
`inserted_product_feature_pin` at 68; `signedFeatureNumerator` at 120;
`covarianceVector_feature_pin` at 129.

`full_marginal_feature_pin`, same module line 102, retains the detached
`neitherHeat` exactly once. `covarianceVector_feature_pin` is coefficient
equivalence of the EXISTING numerator representative, not a newly assumed
vector or a literal equality of completed states. The existing inverse
continues to act on that original vector. Any separate feature-vector
implementation must prove support and use the coefficient-equivalence
bridge; it cannot assume literal equality.

The existing consumer is `covariance_normalizer_projection`,
`lean/YMGap/Continuum/BF4ExactSlabBlockCovarianceNormalizer.lean:151`:
the completed pairing uses the actual inverse of D on the detached
background, representing E*N/D, not E*N or N divided by a global floor.
`prediction_covariance_limit`,
`lean/YMGap/Continuum/BF4ExactSlabBlockPredictionCovariance.lean:182`,
and `residual_pair_decomposition` in that module at line 168 connect those
numerators to the actual prediction covariance and signed residual pair.
For predictions of the selected links, use f=P_b x and g=P_a x (in this
opposite order) at the proved independent dense approximants.

## What this reduction does not prove

K.length counts summands, with repetitions and possible zero coefficients.
It is not a minimal rank or a dimension of the full Hilbert space. The
moment entries remain exterior-valued polynomials; their complexity and
values may depend on test degree. There is no exterior discretization,
finite numerical matrix certificate, or effective cost bound here.

The identities are polynomial equalities for arbitrary rational nome and
cutoff. They assert no uniform analytic bound in nome/beta, cutoff, volume,
spacing or exterior configuration. The typed covariance-vector pin uses
the existing strict nome and late-cutoff guards. No gap follows merely
from finite rank at a fixed cutoff; the feature length is not bounded
uniformly in cutoff by these declarations.

The positive Gram channels of
`productChannels_familyProject_square_le`,
`lean/YMGap/Continuum/SU2QuaternionFamilyHeatGramBessel.lean:147`,
are for the specified product-heat family. That theorem does not identify
these signed monomial features, original one-sided weights or actual
interacting marginal norms with its channels. Its coefficient-one bound
has not been imported into the current estimate.

The focused computational lookup found no exported bound on the selected
block's maximum exponent degree for the actual `faceHeatPolynomial` or
`sharedHeat` in the face-heat, locality, shared-face and center-charge
modules searched. `faceHeatPolynomial`,
`lean/YMGap/Continuum/BF4ExactSlabAllExtentObservableHaarForm.lean:140`,
is a finite spin prefix; that definition alone is not a proved compressed
feature-count theorem. `HasCharge`,
`lean/YMGap/Continuum/SU2QuaternionBlockCenterCharge.lean:31`, records
only parity, not a degree ceiling. `faceHeat_coefficientL1_bound`,
`lean/YMGap/Continuum/BF4ExactSlabAllExtentFaceHeatBound.lean:43`,
bounds a different quantity. No tight rank bound or efficient numerical
certificate producer has been claimed from these results.

## Next mathematical target, still open

Use the actual moments to bound the signed expression together with the
positive defect from `residual_pair_decomposition`, relative to the SAME
residual energy on a justified scaling family. The immediate pairwise
consumer is `neighboringCross_lower`,
`lean/YMGap/Continuum/GNSProjectionNeighborLowerBound.lean:142`.
A collective alternative retains the signed sum in
`conditionalGenerator_square`,
`lean/YMGap/Continuum/BF4ExactSlabSignedNeighborEnergy.lean:68`.
Neither estimate is supplied by the feature identities.

The exact conditional second moments can use the same formula with
(f*f,1) or (1,g*g). Their normalizing determinant is still the actual D;
an unweighted Euclidean estimate on the feature coefficient arrays is not
automatically an estimate in these interacting variances. No Gram inverse,
positivity of individual features, useful scalar neighbor coefficient, or
matrix norm bound is assumed. A small absolute pair bound is sufficient,
not a necessary condition for the collective signed estimate.

These remain ordinary full-action conditional dynamics, not OS time
translation. Scaling, nontrivial continuum survival, thermodynamic control,
same-theory QFT/Hamiltonian calibration, and every-group Clay remain open.
The canonical chart's displayed claims therefore do not change.

## Keep the consumer's quantifiers minimal

`state_norm_le`, `lean/YMGap/Continuum/GNSChebyshevEnergy.lean:127`,
needs contraction only at the actual auxiliary recurrence vector.
`finiteCovariance_sq_bound`,
`lean/YMGap/Continuum/BF4ExactSlabChebyshevCovarianceBound.lean:102`,
likewise asks reverse energy at the actual recurrence of its centered
polynomial seed. Uniform coercivity on every centered state is a sufficient
producer, not a necessary input of that covariance consumer. A bound along
the needed recurrence family remains an admissible target. No gauge-sector
invariance of the original conditional projections has been inferred from
the unrelated temporal change-of-variables sweep. No frontier field changes.

## Verification

All three new modules passed focused serialized one-worker/20 GiB checks,
with all 22 printed axiom gates within {propext, Quot.sound}. Four executable
feature definitions have empty axiom sets. An initial helper check exposed
a missing zero tail in a singleton coefficient sum. The slab draft exposed
a local-notation quotation error and missing section-hypothesis inclusion;
the notation was replaced by explicit `List.idxOf` application. These were
fixed without changing the mathematical factorization or raising
resource/heartbeat limits.
The final checks exited 0 with no `sorryAx` dependency.

Independent Luna source review found no orientation/normalization defect
and confirmed the exterior-valued, coefficient-equivalence scope above.
Only the three named files were compiled; the root import additions were
not a root build. No full-tree build/audit, guard, progress metric, CI run,
new sorry, axiom, classical input or frontier weakening. Long-job manual
observations were spaced approximately five minutes apart; mathematical
and source review proceeded between them, with automatic safety monitoring
left running.
