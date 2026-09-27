# Signed four-copy conditional covariance

Date: 2026-09-27 UTC. Status: finite exact identity checked; analytic bound and
normalized completed-operator join OPEN. The continuum/every-group Clay target
is unchanged and OPEN.

## Mathematical increment

Write P for original Haar integration over disjoint coordinate families A,B,
leaving every other coordinate z shared. For W,f,g define the polynomial

`N(f,g) = P(W)*P(W*f*g) - P(W*f)*P(W*g)`.

The existing partial slice swap R_A replaces just A by its auxiliary copy;
R_B replaces just B. For f independent of B and g independent of A, the
new theorem proves, under every supported (A union B)-independent insertion r,

`H_doubled[r * (W*R_AB(W)-R_A(W)*R_B(W)) * (f-R_AB(f)) * (g-R_AB(g))]`

`= 4 * H_original[r * N(f,g)]`.

The Lean statement writes four as two doublings. No normalization, positivity,
single observable approximation, or assumed integration law enters this identity.
The selected coordinates are copied, not the exterior law.

Evidence:

- `lean/YMGap/Continuum/SU2QuaternionFamilyCovarianceReplica.lean:57`,
  `spectator_pairing`: the insertion remains once-only through exact Fubini.
- `lean/YMGap/Continuum/SU2QuaternionFamilyCovarianceReplica.lean:127`,
  `mixed_identity`: the uncrossed mixed replica gives twice N, including for
  jointly dependent tests.
- `lean/YMGap/Continuum/SU2QuaternionFourCopyCovariance.lean:115`,
  `fourEnergy_as_swap_sum`: under the stated single-block independence, the
  crossed signed term is the selected-swap image of the uncrossed term.
- `lean/YMGap/Continuum/SU2QuaternionFourCopyCovariance.lean:169`,
  `four_copy_identity`: exact factor four with explicit support, disjointness,
  in-range, no-duplicates and exterior-independence hypotheses.
- `lean/YMGap/Continuum/SU2QuaternionFourCopyCovariance.lean:78`,
  `crossDeterminant_zero_of_left_independent`: exact cancellation when W has
  no dependence on the left family.
- `lean/YMGap/Continuum/SU2QuaternionSharedFactorDeterminant.lean:45`,
  `shared_factor_determinant`: for W=L*R*K, L independent of B and R of A,
  its crossed determinant equals
  `(L*R_A(L))*(R*R_B(R))*(K*R_AB(K)-R_A(K)*R_B(K))`
  under EVERY doubled-carrier polynomial insertion. K retains all shared
  interaction factors. This is an equality, not a signed estimate.
- `lean/YMGap/Continuum/SU2QuaternionSharedFactorDeterminant.lean:116`,
  `weighted_four_copy_identity` composes that factorization with the identity.
- `lean/YMGap/Continuum/BF4ExactSlabTwoLinkFourCopy.lean:113`,
  `full_factor_pin` identifies E*W with the complete original slab action;
  at line 151, `interaction_cross_determinant_pin` extracts its actual
  left-only/right-only heat factors while retaining every shared face.
- `lean/YMGap/Continuum/BF4ExactSlabTwoLinkFourCopy.lean:255`,
  `original_shared_four_copy_identity` is the concrete original-action
  consumer. Both physical links are in range and distinct; tests are supported
  and independent only of the opposite selected coordinate, not restricted to
  single-link observables. All exterior variables remain available to the
  tests. The neither-face product occurs once. These algebraic identities need
  no positivity, coupling or late-cutoff guard.

## Remaining normalization join

This paragraph records the mathematical normalization requirement, not a newly
formalized theorem. If the original full action is E(z)*W(a,b,z) and D=P(W),
the conditional covariance is N/D^2. The original exterior marginal has
density E*D divided by H(E*D). Therefore its averaged conditional covariance
requires `H(E*N/D)/H(E*D)`, not `H(E*N)` and not a product of separately
averaged exterior moments. The numerator identity alone does not identify
an original completed residual or prediction-space pairing.

Relevant existing exact machinery, not a proved four-copy join:

- `lean/YMGap/Continuum/BF4ExactSlabBlockNormalizer.lean:64`, `normalizer`;
  at lines 101, 110 and 136, `full_marginal_pin`,
  `full_inserted_marginal_pin`, and `full_test_pin` retain the original action.
- `lean/YMGap/Continuum/BF4ExactSlabBlockCompletedInverse.lean:105`,
  `inverseState` constructs the inverse image of a supplied background
  polynomial; at lines 205 and 210, `normalizer_inverseState` and
  `inverseState_normalizer` prove the actual multiplier identities.
- `lean/YMGap/Continuum/BF4ExactSlabBlockOriginalConditional.lean:142`,
  `conditionalRep`; at lines 154 and 175, `toFull_pair_of_independent` and
  `toFull_test_of_independent` supply original-completion transport identities.

Next: prove the actual inverse-normalizer pairing join for the signed exterior
numerator and a useful conditional-variance-relative estimate. Do not replace
the normalizer by the already-obstructed coarse floor or assume an angle.
Block schedule geometry, justified physical scaling and nontrivial survival,
thermodynamic control and same-theory OS/QFT/mass/every-group construction
remain open. No ordinary conditional dynamics is identified with OS time here.

## Independent review and verification boundary

Parallel Sol review checked the factor four, the shared-exterior dependence,
the necessity of single-block test independence and the missing reciprocal
normalization. Parallel source review checked the existing original-face
decomposition. Compilation was serialized, not parallel.

Focused commands used `python3 scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check <file> --check-output <matching olean>`.
All five new modules passed their final focused checks; printed axiom
dependencies are contained in `{propext, Quot.sound}`. Final checks completed
in their initial calls, with no live heavy job remaining. An earlier
consumer elaboration timeout was traced to the local `blocks` notation
swallowing a sum into its extent argument; explicit parentheses corrected
the drafted doubled-carrier statement. No production frontier was weakened.
Automatic safety
monitoring stayed enabled; no worker/memory/OS-reserve limit was raised.

No new sorry, axiom, classical input, opaque analytic bundle or weakened field.
These are product-Haar algebraic identities, not a load-bearing nonabelian
uniform bound. No full-tree/root build, full axiom audit, guard, progress metric
or CI run. The canonical chart claims have not changed; no chart reprint.
