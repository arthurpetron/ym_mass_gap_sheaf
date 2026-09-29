# Original conditional covariance: actual reciprocal normalization

Date: 2026-09-29 UTC. The unchanged continuum/every-group Clay target is OPEN.

## Mathematical increment

Let the original full action be E*W, where E is the detached action and W
is the selected-block collar. Write P for Haar integration of the selected
coordinates, D=P(W), N_p=P(p*W), and

`N(p,q) = D*N_pq - N_p*N_q`.

On the existing background completion weighted by E, I(r) is the already
constructed inverse-normalizer state with dense numerator r. On the existing
full-action completion F, C is the already constructed block conditional
projection. The new theorem proves

`<I(N(p,q)),1>_E = <p,q>_F - <C p,C q>_F`.

In integral notation its left side is H(E*N/D), not H(E*N), and D is the
actual interacting normalizer, not a global lower bound. This statement uses
the unnormalized full-action inner product. Dividing both sides by the common
full partition is not a separate new theorem here.

Evidence:

- `lean/YMGap/Continuum/BF4ExactSlabBlockInverseAlgebra.lean:92`,
  `approximateInverse_mul_right`: each actual inverse approximant commutes
  coefficientwise with right multiplication by a supplied supported polynomial.
- `lean/YMGap/Continuum/BF4ExactSlabBlockInverseAlgebra.lean:183`,
  `approximateInverse_sub`: subtraction is preserved term by term.
- `lean/YMGap/Continuum/BF4ExactSlabBlockCovarianceNormalizer.lean:66`,
  `inverseState_sub`: the actual completed inverse preserves subtraction of
  dense inputs, by a null relation with cutoff zero.
- `lean/YMGap/Continuum/BF4ExactSlabBlockCovarianceNormalizer.lean:76`,
  `inverseState_product_pair`: `<I(r),t>_E = <I(r*t),1>_E` follows by
  termwise equality and the existing explicit Cauchy pairing limits.
- `lean/YMGap/Continuum/BF4ExactSlabBlockCovarianceNormalizer.lean:97`,
  `covarianceVector_pin`: the actual background vector is the previously
  defined family covariance numerator, with only multiplication-order changes.
- `lean/YMGap/Continuum/BF4ExactSlabBlockCovarianceNormalizer.lean:112`,
  `inserted_product_mean`: the original full-action pairing is the background
  mean of its inserted numerator.
- `lean/YMGap/Continuum/BF4ExactSlabBlockCovarianceNormalizer.lean:128`,
  `conditional_pair_background`: both original conditional outputs pair as
  `<I(N_p),N_q>_E`.
- `lean/YMGap/Continuum/BF4ExactSlabBlockCovarianceNormalizer.lean:139`,
  `covariance_normalizer_pair`, and line 151,
  `covariance_normalizer_projection`: these facts compose with the existing
  `BlockCompletedInverse.inverseState_normalizer` into the displayed identity.

No multiplication operation on arbitrary completed vectors is constructed or
assumed. Only dense supported products and the existing inverse Cauchy states
are used. The convergence moduli remain the existing explicit ones; no witness
is selected from an erased existence claim.

## Pin to the actual shared-face determinant

`BF4ExactSlabTwoLinkNormalizerPin` proves the missing literal identification
between the two previously constructed action decompositions:

- `lean/YMGap/Continuum/BF4ExactSlabTwoLinkNormalizerPin.lean:50`,
  `detached_eq_neither`, proves equality of the actual face lists.
- The same file at line 66, `collar_perm`, proves the collar is a permutation
  of the shared, left-only and right-only face lists. The proof cancels a
  common suffix of finite lists, not an exterior polynomial factor.
- At lines 78 and 83, `background_pin` and `collarHeat_pin` identify E and W
  with the actual neither-face heat and four-copy interaction weight.
- At lines 96 and 103, `normalizer_pin` and `insertedNormalizer_pin` identify
  the same family Haar normalizer and inserted moments.
- At line 120, `covarianceVector_interaction_pin` identifies the constructed
  background vector with the literal four-copy interaction numerator.
- At lines 136 and 152, `interactionCovarianceVector` and
  `interaction_covariance_normalizer_pair` construct that literal vector and
  prove its inverse-normalized pairing equals the original completed
  covariance. Both selected links are required to be physical.

These pins do not require distinct links. The previous four-copy formula
still requires distinct selected links and opposite-coordinate independence
of its tests. Those hypotheses have not been removed. The new theorem
normalizes its numerator; it does not yet construct a doubled-carrier
integral with a nonpolynomial reciprocal insertion.

## Scope and next mathematical input

The normalization theorem applies to every supported dense p,q, every finite
list of physical links, rational 0<w<1, and K>=headCutoff(w). It has no
small-nome guard and supplies no new uniform estimate. The inversion constants
still depend on nome and block size; its algorithmic convergence rate is not
a conditional-dynamics gap.

The common-block expression `<p,q>-<C p,C q>` is not automatically the
neighboring residual pairing `<(1-C_A)x,(1-C_B)x>`. In particular, the
four-copy formula's opposite-coordinate independence hypotheses must be
proved for its inputs; arbitrary residual vectors do not acquire these
hypotheses from the normalization identity.

Next: a signed estimate relative to the SAME interacting conditional
variances on a justified scaling family, followed by the completed
prediction-space/two-projection estimate and actual block geometry. The
normalizer must remain inside the exterior average. Finite observable tests
are not an all-polynomial bound. No new assumed-angle structure is added.

This is ordinary full-action weighted L2. No new OS transfer, physical
Hamiltonian, continuum limit, thermodynamic modulus, nontrivial-survival,
physical-mass or every-group theorem is claimed. The prior absolute-window
budget obstruction is not removed by this identity.

## Verification boundary

All three new modules passed focused serialized checks through
`python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20
--check <file> --check-output <matching olean>`:

- `BF4ExactSlabBlockInverseAlgebra.lean`;
- `BF4ExactSlabBlockCovarianceNormalizer.lean`;
- `BF4ExactSlabTwoLinkNormalizerPin.lean`.

All 27 printed axiom gates report only `{propext, Quot.sound}`. No new sorry,
axiom, classical input, analytic assumption bundle or weakened frontier was
introduced. One worker, mandatory 20 GiB ceiling and automatic memory/swap
monitoring remained in force. A longer draft check was observed after
independent source/proof-scope work, not repeatedly polled; it terminated
with elaboration errors. Missing namespace opens and a notation precheck
were corrected without raising limits. Final focused checks terminated
successfully in their initial calls.

The interrupted parallel proof draft was reviewed, repaired and checked
locally after the agents reported their usage limit. This is not a claim of
a new independent review of the final sources. No full-tree/root build,
full axiom audit, guard, progress-metric or CI run was performed. The root
import list was updated; the verification boundary is the three focused
modules, not the whole root. Canonical chart claims are unchanged.
