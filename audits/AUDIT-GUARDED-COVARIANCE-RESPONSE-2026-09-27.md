# Guarded spatial control of the original signed covariance response

Date: 2026-09-27. Base: `c8f7606`.

## Checked result

The original connected covariance changes by at most

    A(w, P, c) * s(w)^(dist(P.root, inserted face) - |P|)

when one original heat factor is appended to a duplicate-free selected
physical action. Subtraction in the exponent is saturated natural subtraction.
Both observables have interval cap c and are local on the SAME supplied
connected probe carrier P. The factor need not be fresh in the old action.

The exact rate is `entropyRate 625 (adjustedCoreRate w hd)`. The hypotheses
retain `0<w<1`, `heatRatio w <= 1/2`, `heatRemainderBound w < 1`, and that
rate is below one. No weak-coupling or changing-spacing assertion follows.
The amplitude retains nome, observable cap, carrier size and link count,
but no ambient face count, extent or representation cutoff. The finite
normalized statement uses cutoffs at least `headCutoff w`.

## Proof and exact consumer

Let Z and R be the old and appended original partition functions. For each
of p, q and pq, the change-of-action determinant is the old-action connected
numerator with the actual cutoff-dependent inserted heat polynomial F.
The proved two-probe bound gives `|det| <= D * Z^2`. The original one-face
comparison gives `(1-delta(w))*Z <= R`, where `delta=heatRemainderBound`.
Canceling the exact positive product R*Z therefore costs only
`inverseFaceFloor(w)*D`.

The existing three-moment covariance inequality recombines these changes.
The endpoint marginal caps also come from the actual normalized laws.
Multiplication by the exact response denominator `(R*R)*(Z*Z)` and the
existing cleared identity bounds the COMPLETE signed response. Its original
rooted expansion inherits that bound by equality; there is no termwise
absolute-value estimate on the three-mark core sum.

This pays one relative face floor after two-probe clustering, not the
core-dependent `collarCost` from the earlier response majorant. It does not
remove the earlier two-probe theorem's own strong-coupling restrictions.

All following declarations are in
`lean/YMGap/Continuum/BF4ExactSlabGuardedCovarianceResponse.lean`:

| Declaration | Line | Content |
|---|---:|---|
| `momentBudget` | 114 | One relative floor times the explicit two-probe budget. |
| `covarianceBudget` | 118 | Joint-moment error plus the two capped marginal errors. |
| `covarianceAmplitude` | 122 | Position-, cutoff- and ambient-volume-independent amplitude. |
| `covarianceBudget_geometric` | 127 | Exact amplitude-times-rate identity with the saturated distance exponent. |
| `finite_moment_insertion_bound` | 152 | Actual new-minus-old normalized moment. |
| `finite_covariance_insertion_bound` | 190 | Actual connected covariance change; pq stays on P. |
| `signed_response_bound` | 208 | Full response bounded with its exact endpoint denominator. |
| `rooted_signed_response_bound` | 227 | The EXISTING signed rooted sum satisfies the bound. |
| `covariance_insertion_bound` | 241 | The EXISTING fixed-volume cutoff-limit covariance inherits it. |

The key pre-existing inputs are
`BF4ExactSlabTwoProbeDistanceDecay.connectedNumerator_distance_bound`
(`lean/YMGap/Continuum/BF4ExactSlabTwoProbeDistanceDecay.lean:65`),
`BF4ExactSlabSmallNomeHaarComparison.insertFace_lower`
(`lean/YMGap/Continuum/BF4ExactSlabSmallNomeHaarComparison.lean:147`), and
`BF4ExactSlabAllNomeFiniteMomentBounds.covariance_difference_bound`
(`lean/YMGap/Continuum/BF4ExactSlabAllNomeFiniteMomentBounds.lean:80`).
The limit uses `covariance_response_bound_eventually` in
`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:224`, with the
quantitative finite hypothesis now supplied in this guarded local scope.

## Boundary and next causal requirement

This is insertion-to-common-carrier decay. It is not decay in the full
three-mark diameter when the two probes themselves separate. Enlarging P
to connect distant probes changes both amplitude and the saturated exponent;
no uniform estimate for that enlargement is asserted.

The result removes the need to estimate the signed rooted cofactor termwise
in this already guarded regime. It does NOT improve the allowed coupling
range. Further strong-coupling rewrapping cannot supply the physical-spacing
family. The remaining analytic work is a spatial estimate on the same
interacting action that remains useful along the required changing-coupling
scaling family. Existing old-guard obstructions remain in force. No canonical
field, continuum time structure, survival input or physical-mass input is
changed or supplied here.

## Parallel primary-source check

Sol searched for a general SU(2) heat-kernel partition deletion inequality;
the two closest screened results do not justify importing one. Chatterjee's
[Lemma 17.3](https://arxiv.org/html/1602.01222#S17) uses the nonnegative shifted
Wilson plaquette energy defined in section 2. Chevyrev--Garban's
[Corollary 1.6](https://link.springer.com/article/10.1007/s10955-025-03420-1)
states Villain loop-expectation monotonicity for U(1); its nearby non-Abelian
convergence theorem is a different assertion. Our conclusion is limited to
these screened sources: neither supplies the desired SU(2) normalized
heat-action partition comparison. No literature claim is used as an axiom
or proof input. This was targeted research, not another math-ph listing scan.

## Verification

The final focused monitored check passed in 1.17 seconds with one worker
capped at 20 GiB. All nine public gates report only `{propext, Quot.sound}`;
no warning, classical dependency or `sorryAx`. Earlier checks exposed an
unused namespace opening and a multiline match indentation error, corrected
without changing statements or resource limits. Sol independently reviewed
the moment normalization, whole-signed-sum transfer and scope. No full-tree
build/audit, new hole, analytic premise, or broad chart-marker change.
