# Exact signed score replica for the original Wilson block

The unchanged goal is nontrivial continuum Yang--Mills on R^4 for every
compact simple group, SAME-theory QFT axioms and a finite positive physical
mass gap. It remains OPEN. This increment is an exact finite SU(2) identity,
not the missing useful relative estimate.

## Exact new producer

For the ORIGINAL transfer and terminal message, put

    H=t*N, t>=1, W=g_n*halfOpenAction(N,K,V,t),
    A=g_(n+t), c_n=middleRatio(n+1,n,f),
    b=T^t(g_n*(f-c_n)), DW=output angular derivative of W.

Two copies of all H integrated heads share ONE unchanged output tail. The
literal signed polynomial is

    J=(copy_H f-lift_H f)
        *(copy_H(DW)*lift_H W-copy_H W*lift_H(DW)).

Its checked head integral, as polynomial coefficient equality, is

    partialHaarHeads(2H,J) = 2*(A*partial b-b*partial A).

This statement retains every original input/intermediate spatial factor.
The final spatial factor remains outside the message, exactly as in the
existing transfer construction; it is not silently dropped from a pairing.
The angular indices shift by 4H through integration. Head support makes the
source test's output derivative zero. No positivity of W is needed for the
identity, and there is no inverse of A or normalized logarithmic score.

The chronological center cancels EXACTLY in the integrated signed score.
The actual specialization still names c_n on the RHS; it is never replaced
by the mean at n+t. The new code does NOT assert coefficientwise centering
invariance of the replica before integration: copy/lift use distinct padded
monomial representatives. No estimate has been taken before this cancellation.

## Source anchors and causal joins

All paths have prefix `lean/YMGap/Continuum/`.

| Declaration | File:line | Role |
|---|---|---|
| `copy_mul` | `SU2QuaternionMultiHeadVarianceReplica.lean:111` | Existing multiplicative copy proof exposed; body unchanged. |
| `conditionalScore` | `SU2QuaternionMultiHeadScoreReplica.lean:37` | Literal A*partial b-b*partial A. |
| `scoreReplica` | `SU2QuaternionMultiHeadScoreReplica.lean:44` | Two copied head slices and common surviving tail. |
| `scoreReplica_identity` | `SU2QuaternionMultiHeadScoreReplica.lean:102` | Exact signed integral and its positive factor two. |
| `conditionalScore_shifted` | `SU2QuaternionMultiHeadScoreReplica.lean:160` | Arbitrary rational center cancels in the integrated score. |
| `scoreReplica_shifted` | `SU2QuaternionMultiHeadScoreReplica.lean:195` | Integrated replica centering invariance. |
| `blockWindowWeight` | `BF4ExactSlabFixedSpatialBlockScoreReplica.lean:45` | W is the complete actual half-open window with g_n. |
| `blockScoreReplica` | `BF4ExactSlabFixedSpatialBlockScoreReplica.lean:50` | Literal original signed source. |
| `original_block_scoreReplica` | `BF4ExactSlabFixedSpatialBlockScoreReplica.lean:97` | A=g_(n+t), b=the actual centered t-step message. |
| `paddedSquare_own_block_scoreReplica` | `BF4ExactSlabFixedSpatialBlockScoreReplica.lean:131` | Original padded-square observable and chronological OWN mean. |

The existing `replica_product` (`SU2QuaternionMultiHeadVarianceReplica.lean:157`)
preserves the common tail; `angularDerivative_partialHaarHeads`
(`SU2QuaternionHaarTailDerivative.lean:171`) preserves both shifted indices.
The existing `windowMessage_iterate` and `windowMessage_one`
(`SU2QuaternionHeadWindowContraction.lean:201,209`) pin both actual messages.
`iterateStep_add` (`BF4ExactSlabFixedSpatialMiddlePairing.lean:47`) supplies
the literal chronological terminal shift. No new conditional bound is assumed.

## Verification boundary

Three serialized focused checks exited zero with the monitored launcher,
one worker, 20 GiB cap and 12 GiB OS reserve. Twelve printed gates are within
{propext, Quot.sound}: six unchanged prerequisite gates, and six for the
exposed product identity and new score producers. Accepted logs have no
error, warning, sorryAx or PANIC. No heartbeat/resource increase occurred.
The initial generic check needed the defining namespace for liftBoundary;
adding that open resolved the cascade without altering the statement.

| Target | Accepted log in /tmp | Gates |
|---|---|---|
| `SU2QuaternionMultiHeadVarianceReplica.lean` | `ym-multihead-copy-product-20261003-a.log` | 6 unchanged |
| `SU2QuaternionMultiHeadScoreReplica.lean` | `ym-multihead-score-replica-20261003-b.log` | 4 |
| `BF4ExactSlabFixedSpatialBlockScoreReplica.lean` | `ym-original-block-score-replica-20261003-a.log` | 2 |

Source SHA256, in table order:

    c2dc496515ffa0e82f1051cf6de360923220b4ceae01ff2a9aeac2975db5f219
    6732a87a9a6326de58f753bfb058e97d30a7781d10d9613f715f0db6600a9f83
    58046969a5c70e966d0565a4f68b7c1893562d9ef426655e09e41f968177005d

Accepted-log SHA256, in table order:

    4881c676912f7e4dbdcf59f635fa7a110859a19e60757cfbe8bbeb08ff9aca09
    4c7541a4a1213afef23e9af089d90ab93cac8c23c0049c4e88b0dfe35531eafe
    040a33d4a581d90f1682eec00ebab970a24d383bb5157504e55a6e373faef473

Independent source-only semantic review confirmed orientation, factor two,
tail sharing, literal message pins and chronological centering. No sorry
added/discharged, new axiom, classical shortcut or frontier weakening.
Root imports registered only; no aggregate build/audit, broad guard or
progress metric ran. CI and exact canonical chart are unchanged.

## Unpaid quantitative join

This exposes an exact signed conditional-score numerator on the SAME finite
original window. It does not identify its angular form with the discrete
transfer cost or the completed physical Hamiltonian, prove a favorable sign,
or bound it relative to ell(b*b). The next producer remains a useful estimate
for the complete original cleared cost

    s*[Z1*ell(b*b)-Z0*ell(b*T b)] <= C*Z1*ell(b*b)

on a JUSTIFIED changing family, retaining both partitions and their boundary
allowances. Total conditional noise is not a substitute: its exact law is
endpoint variance minus filtered norm (`blockNoise_variance_loss`,
`BF4ExactSlabFixedSpatialBlockConditionalNoise.lean:138`). That positivity
provides only the opposite-direction endpoint norm comparison.
Canonical OS, spatial/spacing and physical calibration, nontrivial continuum
survival, full QFT, every group and Clay remain OPEN.
