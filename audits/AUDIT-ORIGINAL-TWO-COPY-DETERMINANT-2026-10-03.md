# Signed two-output polarization of the original determinant

Whole-project goal remains OPEN: nontrivial continuum Yang--Mills on R^4
for every compact simple group, SAME-theory QFT axioms and a finite positive
physical mass gap. This is an exact finite SU(2) producer, not the missing
signed relative estimate, an OS reconstruction or physical uniformity.

## Exact original objects and cancellation

Use the original finite transfer T and ell(p)=H_N[V*p]. On two output
slots, tensor(p,q)=p(x)*q(y) uses an explicit lift of the second slot.
The doubled functional is exactly H_(N+N)[V(x)*V(y)*p(x,y)]. Each output
V occurs once; the input V inside the unchanged transfer is retained.

    Pi = A(x)*b(y)+b(x)*A(y),
    Lambda = A(x)*b(y)-b(x)*A(y),
    firstDifference = (T A)(x)*b(y)-(T b)(x)*A(y),
    secondDifference = A(x)*(T b)(y)-b(x)*(T A)(y),
    D = ell(A*T A)*ell(b*b)-ell(A*A)*ell(b*T b).

The checked pairings with Pi are D and -D. The mixed terms cancel exactly
using ell(b*T A)=ell(A*T b) and ell(b*A)=ell(A*b). Their difference pairing
is D+D. No inverse of A, positivity, stationarity, eigenpin, centering or
relative-norm premise is used. No ambient tensor operator or completion
is postulated: both transformed differences are literal finite polynomials.

The actual square specialization has

    f = the padded-square fundamental trace,
    c_n = middleRatio(n+1,n,f),
    A = g_(n+t), b = T^t(g_n*(f-c_n)).

The mean is still at n. Neither the later endpoint mean nor its variance
is substituted into b. The next existing consumer still requires
s*D <= C*Z1*ell(b*b) on a justified changing family. This identity gives
an alternative complete signed expression for D, not its useful bound.

## Source anchors

All paths start with `lean/YMGap/Continuum/`.

| Declaration | File:line | Role |
|---|---|---|
| `tensor` | `BF4ExactSlabFixedSpatialTwoCopyRayleighDeterminant.lean:48` | Explicit placement of two output slots. |
| `twoCopyMass` | `BF4ExactSlabFixedSpatialTwoCopyRayleighDeterminant.lean:52` | Original V once in each functional slot. |
| `tensor_pair` | `BF4ExactSlabFixedSpatialTwoCopyRayleighDeterminant.lean:68` | Signed original product-weighted Haar factorization. |
| `firstDifference` | `BF4ExactSlabFixedSpatialTwoCopyRayleighDeterminant.lean:134` | Original transfer in the first tensor factor. |
| `secondDifference` | `BF4ExactSlabFixedSpatialTwoCopyRayleighDeterminant.lean:140` | Original transfer in the second tensor factor. |
| `first_pairing_determinant` | `BF4ExactSlabFixedSpatialTwoCopyRayleighDeterminant.lean:145` | Actual pairing is D. |
| `second_pairing_determinant` | `BF4ExactSlabFixedSpatialTwoCopyRayleighDeterminant.lean:182` | Actual pairing is -D. |
| `antisymmetric_pairing_determinant` | `BF4ExactSlabFixedSpatialTwoCopyRayleighDeterminant.lean:220` | Difference pairing is D+D. |
| `paddedSquare_own_twoCopy_determinant` | `BF4DyadicWilsonSquareTwoCopyRayleighDeterminant.lean:49` | Literal chronological square/block consumer. |
| `haar_split_pairing` | `SU2QuaternionHaarMarkovContraction.lean:51` | Existing exact supported two-slot factorization. |
| `transferStep_weighted_symmetric` | `BF4ExactSlabFixedSpatialTransferSymmetry.lean:97` | Existing SAME-action mixed-term cancellation. |
| `clearedRayleighCost` | `BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:131` | Exact unchanged cost targeted by this producer. |

## Verification boundary

Two serialized focused checks exited zero with one worker, 20 GiB ceiling,
12 GiB OS reserve and the monitored launcher. Five printed gates are within
{propext, Quot.sound}; accepted logs contain no error, warning or sorryAx.
No resource/heartbeat increase. Initial generic retries fixed only a
defining namespace, match-branch layout and explicit weightedMass unfolding.
Those failed logs are not accepted proof evidence.

| Target | Accepted log in /tmp | Gates |
|---|---|---|
| `BF4ExactSlabFixedSpatialTwoCopyRayleighDeterminant.lean` | `ym-original-two-copy-determinant-20261003-c.log` | 4 |
| `BF4DyadicWilsonSquareTwoCopyRayleighDeterminant.lean` | `ym-original-square-two-copy-determinant-20261003-a.log` | 1 |

Source SHA256, in table order:

    add43868deb8a338a39a4c36b4cde7b4d86d0c26b0850fab7cec729aa8c73afd
    7874004148ae75310e57c0bae00249991ba8d677c827ba0c16fe858e42adad04

Accepted-log SHA256, in table order:

    9940483c1a019008dc3efcc67fb89c3046a0938ff9e2be6436989b98c75184b9
    ddd36a8754798068bf5020bce8d9350c23c8ffc3a90e4222521e0bb981daab7b

Independent source review checked signs, original weights/transfer and
chronological source pins; a separate evidence review checked accepted
logs and source hashes. No sorry added/discharged, axiom, surrogate,
classical shortcut, hidden reserve or frontier weakening. Root imports
registered only; no aggregate build, full audit or broad guard. Exact
canonical chart and CI unchanged. Signed relative control, canonical OS,
spatial/spacing control, continuum survival, physical calibration, full QFT,
every compact simple group and Clay remain OPEN.
