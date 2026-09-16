# Original connected face response: identity, finite obstruction, open estimate

Date: 2026-09-15 (America/Los_Angeles). Base: `963cbb9`.

PROGRESS: the exact original-action response and its conditional cutoff-limit
consumer are proved. A positive original cutoff-one example rules out
discarding the third connected term merely because the two insertion pair
responses vanish. No spatially summable estimate or canonical frontier atom
is discharged. The continuum/all-group Clay target remains OPEN.

## 1. The same original action and both partitions

For a selected physical face list S, let M(f) be the original unnormalized
Haar moment, Z=M(1), r the full cutoff-K heat polynomial of the appended
face, and R=M(r), the NEW partition. Put

    C(p,q) = M(pq) Z - M(p) M(q)
    T(p,q,r) = M(pqr) Z^2 - M(pq) M(r) Z
               - M(pr) M(q) Z - M(qr) M(p) Z
               + 2 M(p) M(q) M(r).

The checked identity is

    C_new(p,q) Z^2 - C_old(p,q) R^2
      = R T(p,q,r) - C_old(p,r) C_old(q,r).

These are the literal original face-product moments; no replacement
measure or common partition is substituted. Appending adds one heat factor;
the identity permits repeated face indices and does not assert the face
was absent from S.

| Declaration | Source | Content |
|---|---|---|
| `RationalConnectedResponse.connected_response_identity` | `lean/YMGap/Continuum/RationalConnectedResponse.lean:26` | Polynomial identity for eight rational moments. |
| `RationalConnectedResponse.covariance_clear` | `lean/YMGap/Continuum/RationalConnectedResponse.lean:52` | Clear covariance by its own partition square using the supplied reciprocal equality. |
| `RationalConnectedResponse.difference_clear` | `lean/YMGap/Continuum/RationalConnectedResponse.lean:73` | Clear a difference using both endpoint equalities. |
| `BF4ExactSlabConnectedFaceResponse.thirdNumerator` | `lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:60` | T, cleared by the OLD partition cubed. |
| `BF4ExactSlabConnectedFaceResponse.response` | `lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:68` | Signed combination R*T minus the two connected-pair product. |
| `BF4ExactSlabConnectedFaceResponse.responseDenominator` | `lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:73` | Exactly R^2*Z^2. |
| `BF4ExactSlabConnectedFaceResponse.connected_append_face` | `lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:78` | New connected numerator expressed in old moments of the actual inserted heat. |
| `BF4ExactSlabConnectedFaceResponse.response_identity` | `lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:90` | Original-action instance of the identity above, at every cutoff. |
| `BF4ExactSlabConnectedFaceResponse.diagonal_response_le_third` | `lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:104` | For p=q the correction is a negative square; no sign or bound on T is asserted. |
| `BF4ExactSlabConnectedFaceResponse.connected_unit_left` | `lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:111` | Constant PROBE has zero connected numerator. |
| `BF4ExactSlabConnectedFaceResponse.response_unit_left` | `lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:125` | Constant PROBE has zero response, not a claim about constant insertion. |

## 2. What the cutoff-limit consumer proves and assumes

The actual normalized finite covariance is defined by
`BF4ExactSlabConnectedFaceResponse.finiteCovariance`,
`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:152`.
Its CReal counterpart is `covariance` at `:157`; explicit approximation
modulus data are returned by `covarianceCauchy` at `:161`.
`finite_covariance_converges` at `:166` uses the existing face-set
expectations of the FIXED p, q and p*q.

`finite_response_cleared`,
`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:188`, proves
that their finite covariance difference times R^2*Z^2 equals the signed
response. `responseDenominator_positive` at `:199` supplies positivity for
physical faces, 0<w<1 and K>=headCutoff(w). No uniform lower constant is
silently used to replace these partitions.

`finite_response_bound` at `:209` cancels the actual denominator.
`covariance_response_bound_eventually` at `:224` then proves the CReal
covariance change has absolute value at most b GIVEN an explicit K0 and

    for every K >= K0:
      abs(response(w,K,S,f,p,q)) <= b * responseDenominator(w,K,S,f).

This finite quantitative hypothesis remains UNSUPPLIED. The heat insertion
depends on K and stays inside that hypothesis; it is not passed through a
fixed-polynomial limit. No spatial, volume or coupling independence of b
is asserted. The threshold headCutoff itself depends on w.

`full_covariance_pin`,
`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:253`, identifies
the full odd-slab specialization with
`BF4ExactSlabTwoProbeCovariance.covariance`; it uses
`BF4ExactSlabAllNomeFaceSetExpectation.odd_expectation_pin`,
`lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetExpectation.lean:141`.
Thus the consumer refers to the existing original covariance, not a new model.

## 3. A concrete failure of pairwise-only closure

Take one original physical plaquette, p=chi_2, q=chi_3, w=1/8, K=1,
and initially empty selected action. The full inserted heat is
r=1+(1/256)*chi_1. The new module supplies the following exact witness:

| Declaration | Source | Checked content |
|---|---|---|
| `BF4ExactSlabPairwiseResponseObstruction.nome` | `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:55` | w=1/8. |
| `BF4ExactSlabPairwiseResponseObstruction.signal` | `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:56` | 1/256; `signal_positive` at `:58` proves positivity. |
| `BF4ExactSlabPairwiseResponseObstruction.leftProbe` | `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:60` | Original face character chi_2; support at `:64`. |
| `BF4ExactSlabPairwiseResponseObstruction.rightProbe` | `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:61` | Same face character chi_3; support at `:68`. |
| `BF4ExactSlabPairwiseResponseObstruction.insertion` | `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:62` | Literal full heat prefix at K=1. |
| `BF4ExactSlabPairwiseResponseObstruction.insertion_pin` | `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:128` | r=1+(1/256)*chi_1 as polynomial coefficient equivalence. |
| `BF4ExactSlabPairwiseResponseObstruction.insertionCertificate` | `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:137` | Existing constructive positive-square certificate for this actual heat. |
| `BF4ExactSlabPairwiseResponseObstruction.empty_partition` (private) | `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:216` | Old partition is one. |
| `BF4ExactSlabPairwiseResponseObstruction.left_pair_response_zero` | `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:220` | C_old(p,r)=0. |
| `BF4ExactSlabPairwiseResponseObstruction.right_pair_response_zero` | `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:227` | C_old(q,r)=0. |
| `BF4ExactSlabPairwiseResponseObstruction.old_connected_zero` | `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:234` | C_old(p,q)=0. |
| `BF4ExactSlabPairwiseResponseObstruction.singleton_partition` | `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:241` | New partition is one. |
| `BF4ExactSlabPairwiseResponseObstruction.singleton_connected` | `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:245` | C_new(p,q)=1/256. |
| `BF4ExactSlabPairwiseResponseObstruction.thirdNumerator_eq` | `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:254` | T(p,q,r)=1/256. |
| `BF4ExactSlabPairwiseResponseObstruction.response_eq` | `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:273` | Signed response=1/256. |
| `BF4ExactSlabPairwiseResponseObstruction.response_ne_zero` | `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:278` | Response is not zero. |
| `BF4ExactSlabPairwiseResponseObstruction.concrete_face_physical` | `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:289` | Literal extent 1, face id 0 is physical. |
| `BF4ExactSlabPairwiseResponseObstruction.concrete_response_ne_zero` | `lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:292` | No uninhabited geometry hypothesis in the concrete example. |

The probes are original character polynomials; the existing vertex-ledger
invariance declaration (using three auxiliary blocks) is
`BF4ExactSlabVertexGaugeAction.character_invariant`,
`lean/YMGap/Continuum/BF4ExactSlabVertexGaugeAction.lean:208`.
The witness uses arbitrary supported polynomial observables and does NOT
claim these labels belong to a cutoff-one boundary-code carrier.

Scope is essential: both probes occupy the SAME face; the old action is
empty and the new one has ONE face. This is not a separated-probe,
full-slab, all-late-cutoff or cutoff-removed example. It excludes a universal
finite-cutoff rule that drops the third term when these two pair responses
vanish. It does not exclude estimates with additional hypotheses, grouped
observables or independent control of the third moment.

## 4. Causal next estimate and rejected detours

For the response route, the missing estimate is a late-cutoff bound

    abs(R*T - C(p,r_K)*C(q,r_K)) <= b_f * R^2 * Z^2,

with an actual spatially summable family b_f, suitable ambient-action and
volume uniformity, and explicit coupling dependence. The finite bound is
the named hypothesis of `covariance_response_bound_eventually` above;
the required spatial summability is NOT constructed there.

An existing original spatial theorem is
`BF4ExactSlabTwoProbeDistanceDecay.connectedNumerator_distance_bound`,
`lean/YMGap/Continuum/BF4ExactSlabTwoProbeDistanceDecay.lean:65`.
It retains the actual partition square and works at every cutoff, but
requires heatRatio<=1/2, heatRemainderBound<1, and
entropyRate 625 (adjustedCoreRate w)<1. The full-action specialization is
`full_connectedNumerator_distance_bound` at `:79`. These guards are not
removed by the new identity.

The old unit-reference expansion has an independently proved limitation:
`BF4ExactSlabHeatHaarGuardObstruction.no_eventual_small_intervals`,
`lean/YMGap/Continuum/BF4ExactSlabHeatHaarGuardObstruction.lean:340`, excludes
even eventual remainder caps <=1 for w>=7/8. Its exact late square-test
moment is `test_remainder_haar_late` at `:285`, namely 4*w^3+3*w^8 for
K>=2. Later cutoffs therefore do not repair that particular expansion.
This does not refute every possible spatial bound.

Normalization is not a missing construction:
`BF4ExactSlabRetainedHeatHeadComparison.faceHead_weighted_floor`,
`lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:132`, already
gives a one-face relative partition floor for a positive background.
Likewise, telescoping the preceding cutoff-stability theorem controls
regulator changes, not separation. Neither supplies spatial cancellation.

NOT FOUND in the bounded source review: an all-nome, spatially summable
bound for this original third response. Searched
`BF4ExactSlabTwoProbeDistanceDecay`, `BF4ExactSlabTwoProbeTailBudget`,
`BF4ExactSlabInnerMarginBoundaryDecay`, `BF4ExactSlabSpacetimeExpectationDecay`,
`BF4ExactSlabAllNomeFaceSetComparison`, and the new response module.
Existing guarded bounds and conditional all-nome consumers are not
classified as a supplied instance.

Varying-coupling thermodynamic/OS compatibility, physical time/spacing
calibration, continuum QFT/nontriviality and the all-compact-simple-group
target remain open. This checkpoint proves no OS/Hamiltonian gap.

## 5. Parallel work and exact verification boundary

Independent work streams supplied rational algebra, the original finite
witness, and read-only physical/limit/consumer review. The parent integrated
the actual original-action identity and normalized limit consumer. No
heterogeneous-cutoff telescope or new frontier bundle was added.

The parent alone ran six focused serialized one-worker/20 GiB safe checks:
one rational check, three response-module checks, and two witness checks.
Two initial attempts failed on syntax/namespace/parameter/elaboration
issues and were corrected; the final logs are error-free. No limit was
raised and no dependency rebuild or parallel compilation was used.

All 49 new public gates pass: 3 rational, 18 original-response, 28 witness.
They use only {propext, Quot.sound}, or no axioms. No sorryAx, classical
choice or compiler-backed native decision is present in the final gates.
New artifacts and their direct imported artifacts are newer than source.

Final local log SHA-256 values:

- `/tmp/ym-rational-connected-response.log`:
  `0e4e46403556f0ab8f19a404faeebdcea6070b3146d096afa521c72112ea6543`.
- `/tmp/ym-original-connected-response.log`:
  `fb226b26e95fab698325b3c1677f219ef3c4a59f7e4666b8e909a583d43b42a7`.
- `/tmp/ym-pairwise-response-obstruction.log`:
  `06e5bad4a56dfa4cdae5ef56cba1cfc680874a87149dde429b1ce2b936723a30`.

Three semantic-root imports added; root/full-tree build and full audit
not run. CI remains manual-only. No old theorem statement, canonical field,
custom axiom or literal hole changed. Goal remains active.
