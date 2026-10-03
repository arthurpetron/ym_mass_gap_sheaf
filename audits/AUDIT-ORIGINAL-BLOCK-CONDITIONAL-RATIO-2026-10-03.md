# Original conditional ratio and its cleared angular reconstruction

The whole-project goal remains OPEN: nontrivial continuum Yang--Mills on
R^4 for every compact simple group, SAME-theory QFT axioms and a finite
positive physical mass gap. This checkpoint constructs finite polynomial
conditional ratios and an explicit cleared-angular reconstruction modulus.
It does not bound the complete interacting signed cost along a scaling family.

## Checked mathematical increment

Use the ORIGINAL interacting transfer T, spatial action V and functional
ell(p)=H[V*p]. For a supported source psi, set

    A = g_(n+t),  b = T^t(g_n*psi),  n+t >= 1.

The actual last transfer step constructs the denominator window

    L = kineticFloor(w,width)*ell(g_(n+t-1)),
    U = kineticCap(w,width)*ell(g_(n+t-1)),
    0 < L <= A <= U.

These inequalities are Type-valued original-carrier certificates. A
constructed source interval with cap C propagates through the full original
positive transfer to the two relative certificates C*A plus/minus b.
There is no bare-heat substitution or independent-variable factorization.

With sigma=1/U, R=sigma*A-1, E_k=(-R)^k and the existing finite reciprocal
G_k, the coefficient identity A*G_k+E_k=1 is exact. The actual output
phi_k=G_k*b has a constructed square certificate phi_k^2<=C^2. The cap
does NOT divide by the terminal lower floor. Its SAME-weight reconstruction is

    ell[(b-A*phi_k)^2] <= mixRate(w,width)^(2*k)*ell[b^2].

The previous terminal mass cancels from the denominator floor/cap ratio:
rho=1-L/U is coefficient-pinned to the existing mixRate(w,width). The
reconstruction rate and its relative tolerance onset are independent of
cutoff, terminal depth and message amplitude within the stated guards.
Nome and width remain explicit; no uniformity in them is proved.

For any valid angular derivation D, put S=A*Db-b*DA. Differentiating the
existing cancellation, rather than exchanging a derivative with a limit,
proves both signed errors:

    A^2*D(b*G_k)-S = -E_k*S - A*b*DE_k,
    DE_(k+1) = -(k+1)*E_k*DR.

For ANY constructed positive weight W on the SAME finite carrier, the
parallelogram estimate and residual-square certificates then give

    H[W*(A^2*D(b*G_(k+1))-S)^2]
      <= 2*rho^(2*k+2)*H[W*S^2]
         + 2*(k+1)^2*rho^(2*k)*H[W*(A*b*DR)^2].

The statement uses sumBound for the two doubled budgets. Neither actual
square cost is replaced by a source coefficient cap, a different norm or
an assumed analytic ceiling. Positivity of their SAME-weight squares is
constructed from W's certificate and their literal support.

An explicit all-later onset is

    max(geometricCutoff(rho,C0,epsilon/4),
        polynomialCutoff(rho,C1,2,epsilon/4)),
    C0 = H[W*S^2],  C1 = H[W*(A*b*DR)^2].

The proof weakens squared geometric powers to rho^k; no inverse of rho
appears, so zero radius and zero costs are covered. The actual original-block
consumer constructs every input at W=V and reconciles G*b with b*G by explicit
coefficient commutation. Its cutoff uses the literal finite costs and window.

For the literal padded Wilson square, psi is shifted by the ORIGINAL
depth-n ownMean. Its source interval is constructed from the existing
centered square cap16, giving interval cap17 and ratio square cap17^2.
The actual angular reconstruction theorem discharges the support input from
that constructed interval. It does not assume a new source bound.
The mean is the existing `ownMean`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredOwnYoung.lean:93`);
the existing `mean_pin`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonMeanRadial.lean:104`)
provides rational equivalence to the chronological middleRatio at (n+1,n).
No equality of means at different depths is asserted.

## Exact declarations and downstream boundary

| Declaration | Source | Checked role |
|---|---|---|
| `blockWindowCertificates` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:103` | Constructed actual terminal floor and cap. |
| `blockRelativeCertificates` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:172` | Both source signs propagated through original T. |
| `blockConditionalRatio_squareCertificate` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:233` | Ratio square cap without terminal-floor loss. |
| `blockWindow_radius_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:250` | Actual rate is the existing coupling/width mixRate. |
| `blockConditionalRatio_reconstruction` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:281` | Relative error in original V-weighted norm. |
| `blockConditionalRatio_reconstruction_tolerance` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:326` | Computed relative norm-error onset. |
| `ownPaddedSquareInterval` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:350` | Actual chronological OWN-source bound constructed. |
| `ownPaddedSquareRatio_squareCertificate` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:368` | Literal ratio cap17^2. |
| `reciprocal_ratio_score_error` | `lean/YMGap/Continuum/QuaternionHaarReciprocalAngularScore.lean:71` | Exact two signed angular residuals. |
| `residual_angularDerivative_succ` | `lean/YMGap/Continuum/QuaternionHaarGeometricResidualAngularDerivative.lean:42` | Exact differentiated-geometric factor. |
| `residualAngularInterval` | `lean/YMGap/Continuum/QuaternionHaarGeometricResidualAngularDerivative.lean:86` | Constructed finite derivative interval. |
| `reciprocal_ratio_score_error_square_le` | `lean/YMGap/Continuum/QuaternionHaarReciprocalAngularScoreBound.lean:77` | Same-weight two-cost square estimate. |
| `scoreErrorModulus` | `lean/YMGap/Continuum/QuaternionHaarReciprocalAngularScoreModulus.lean:38` | Computed fixed-window onset. |
| `reciprocal_ratio_score_error_tolerance` | `lean/YMGap/Continuum/QuaternionHaarReciprocalAngularScoreModulus.lean:122` | All-later tolerance with constructed cost signs. |
| `blockConditionalRatio_angular_reconstruction` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalScore.lean:75` | Actual original block and action instantiate the modulus. |
| `ownPaddedSquareRatio_angular_reconstruction` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalScore.lean:115` | Literal chronological OWN-square consumer. |

CORRECTION (2026-10-03): the prior version of this audit incorrectly said
`clearedRayleighCost_split`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:214`)
requires an exact multiplication identity. It requires only support of b
and A*f, so the finite ratio can be inserted directly, with its signed
multiplication cost retained. This ratio checkpoint did not bound that cost;
the subsequent checked finite energy/error join is recorded in
`audits/AUDIT-ORIGINAL-BLOCK-CONDITIONAL-ENERGY-2026-10-03.md`.
The angular estimate remains cleared by A^2, not an unweighted
inverse-derivative estimate.

The existing `paddedSquare_exact_block_heatDefect`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareExactBlockHeatDefect.lean:65`)
retains the complete signed heat defect, boundary drift and signed
multiplication cost. Their combined quantitative size relative to the SAME
filtered norm remains OPEN. The existing backward consumer
`normalizedAnchorResponse_block_floor`
(`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132`)
still requires a positive family-wide macroscopic response ratio. No new
necessary frontier field or conditional survival wrapper was introduced.

## Source-reviewed route selection, not new proofs

The bare tested overlap ell(b*f) is not automatically the completed centered
two-point correlation. `observedMessage_endpoints`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockWindowPin.lean:54`) and
`window_pairing` / `window_partition_pairing`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowPairing.lean:96` and
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowPairing.lean:124`)
retain the right terminal message g_n and its partition. The bare
overlap has right distance zero. The existing `centeredPair`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMovingCenterLagDifference.lean:57`)
has both terminal distances n. `windowRatio_right_commonTail`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowBracket.lean:140`)
requires s<=both right distances; comparison against zero cannot give a
growing common-tail onset. No bare-overlap-to-completed-correlation theorem
was added or claimed.

The fixed-carrier signed unitary branch already supplies `signedAction`
(`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime.lean:125`),
`signedContinuityCertificate`
(`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleySignedTimeContinuity.lean:111`),
`productLimitCertificate`
(`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit.lean:224`),
`ofPointRealTangent` / `ofRealTangent`
(`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyRealTangentData.lean:120`
and `lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyRealTangentData.lean:161`)
and `domainLogarithmCertificate`
(`lean/YMGap/Continuum/BF4WilsonAllNomeDomainLogarithm.lean:193`). These existing
declarations were inspected, not recompiled here. No duplicate continuity,
Cayley or ordinary-log wrapper was added. Physical clock calibration,
canonical reflected OS identification and the scaling join remain OPEN.

## Verification boundary

Accepted serialized focused checks, completed 2026-10-03 UTC:

| Target (under `lean/YMGap/Continuum/`) | Accepted log | Public gates |
|---|---|---|
| `QuaternionHaarReciprocalAngularScore.lean` | `/tmp/ym-reciprocal-angular-score-20261003-c.log` | 4 |
| `QuaternionHaarGeometricResidualAngularDerivative.lean` | `/tmp/ym-geometric-residual-angular-20261003-a.log` | 2 |
| `QuaternionHaarReciprocalAngularScoreBound.lean` | `/tmp/ym-reciprocal-score-bound-20261003-b.log` | 1 |
| `QuaternionHaarReciprocalAngularScoreModulus.lean` | `/tmp/ym-reciprocal-score-modulus-20261003-b.log` | 3 |
| `BF4ExactSlabFixedSpatialBlockConditionalRatio.lean` | `/tmp/ym-original-block-ratio-20261003-b.log` | 17 |
| `BF4ExactSlabFixedSpatialBlockConditionalScore.lean` | `/tmp/ym-original-block-conditional-score-20261003-d.log` | 4 |

All six accepted runs exited zero. The 31 public gates use only
{propext, Quot.sound}; scoreErrorModulus is axiom-free. No accepted error,
warning or sorryAx. Independent read-only review checked all six complete
sources, accepted logs, actual variables, guards and hashes.

Checks used one worker, a 20 GiB hard worker ceiling, a 12 GiB OS reserve
and automatic safety telemetry. Dynamic preflights before every launch found
no competing compiler/runner, 82--84% pressure-free percentage and zero swap.
The safety thresholds and heartbeat ceiling were not raised.

Earlier rejected attempts are not proof evidence: generic score attempts
a/b needed its defining carrier namespace and coefficient-zero transport;
bound attempt a needed a parenthesis and explicit coefficient-negation
transport; modulus attempt a needed rational quarter algebra and natural
one-multiplication reduction; ratio attempt a had a nested-comment token;
concrete score attempts a/b/c needed the actual defining namespaces.
The first concrete score attempt also exhausted its ordinary heartbeat
ceiling while identifiers were unresolved. No statement or mathematical
assumption was weakened to obtain the accepted checks.

Source SHA256, in the table's order:

    48edcaf34fe700c36d51804a7e1693659388d2b6563b97aca5f9ca6a29ea84b3
    1e6402db6825960b4d10c911462d4c865fffefcde3b7480974c61342036b58d5
    cd3f9ecf385a95a60037cc76b6db89cc1560c63705e11ede46a9afef2f86eb42
    275fa9000917db5eb0748e8e8edd49839c6051903b3f4d744ca0cd0a63fc80cd
    82a601ad971dd71e9721ddb541ee86cb9fed993f84ed55e5bd8cced064bc42f6
    523c53b5af0134d8d49f3e5234e5a8b1c9d767b25536d83a024d9d3cc5634a73

Accepted-log SHA256, in the same order:

    0a706c323a2f141f0252f0abae1b686f125bfb4a864dd7923a0dd4f9fb8fc62e
    6658f310793601d285b08a54ebcd0ee73588a75931935a85e21852baded6fada
    1fef20045e51e1e932179ae7eb763842ab5440f19b1945da259b7dbb12230181
    8e9967e13d476e6a57a36c06710ec9982f9ed610675baef2a902dc8f4282e41e
    0edbae6d57dfe315109608b287858244695e225ced1c7629907906be36fe7fa4
    11efe92e7c25ad6372c2cd75b2f6b6cd41e8b138e3008b857df5e0fcc47e9715

Root import registration only; no aggregate build, full axiom audit or broad
guard was run. No sorry, axiom, classical shortcut, surrogate or frontier
weakening. Continuum survival, physical mass calibration, full canonical
OS/QFT and every-group closure remain OPEN. CI and the exact canonical ASCII
block are unchanged; no displayed claim closes and no chart is reprinted.
