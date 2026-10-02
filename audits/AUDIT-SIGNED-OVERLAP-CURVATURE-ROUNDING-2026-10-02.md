# Signed overlap and exact response curvature

Three checked results advance the existing forward and backward fronts:
an estimate retaining the original source overlap, an exact response identity
retaining positive curvature, and an explicit bounded time-rounding modulus.
None supplies uniform survival or a continuum Yang--Mills theory. The unchanged
Clay goal and every continuum endpoint remain OPEN.

## Original source overlap gives a signed gain estimate

Use the original active product heat P, positive partition Z, literal padded
dyadic Wilson square f and its OWN mean mu at terminal depth n+1. Write
q=V*terminalMessage(n+1), psi=f-mu, a=w^(12*side) and S=Z*OWNVar.
The previous computed defect is C=P(q*f)-a*(Pq)*f and G=H[q*psi*C].
The current construction retains the actual predecessor spectator R at depth n:

    U = H[q*(P R)*psi^2],
    D = H[R*(P R)*f^2] + a*mu^2*H[R*(P R)].

These are actual original-source moments, not coarse upper/lower local-band
constants. The affine dual test is t=R*(f-a*mu), not R*psi or a bare centered
eigenvector. Existing spectator transmission gives Pt=a*(P R)*psi. Its
cross kinetic moment with x=q*psi is a*U and its diagonal is a*D; the zero
first spectator moment removes the cross term but retains a*mu^2.

The original kinetic diagonal is G+a*S. Sharp kinetic Cauchy--Schwarz gives
a^2*U^2<=(G+a*S)*a*D. Cancelling only the proved positive a yields

    a*U^2 <= (G+a*S)*D,
    G*D >= a*(U^2-S*D).

Guards are 0<w<1, headCutoff(w)<=K, 1<=K and side<width. The extra 1<=K
belongs to the spectator word transmission, not to the previous defect
identity. No source independence, favorable sign of G, replacement by local
bands, angular-generator identity, or inverse of D/source/variance is used.
No usable uniform overlap or positive dual-moment floor is proved here.

| Declaration | Source | Checked content |
| --- | --- | --- |
| `squareSpectatorOverlap` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedOverlapGain.lean:73` | Actual U at OWN center |
| `squareSpectatorDualMoment` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedOverlapGain.lean:85` | Actual D with affine mean correction |
| `paddedSquare_kinetic_signedHeatDefect_pin` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedOverlapGain.lean:97` | Actual kinetic diagonal G+a*S |
| `paddedSquare_signed_overlap_cleared` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedOverlapGain.lean:139` | Cleared sharp overlap bound |
| `paddedSquare_signed_overlap_gain` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedOverlapGain.lean:230` | Signed G*D lower bound |

## The exact backward criterion retains positive curvature

On the EXISTING all-nome completed carrier let T be its actual time action,
D_time=I-T and B its inner form. This D_time is distinct from the finite
dual moment D above. Define e(x)=B(x,D_time*x). Existing actual mixed moments
M(x,k,l)=B(x,T(k)*D_time^l*x) are nonnegative and satisfy their exact split.
The new head-recursive triangular sum computes

    C_m(x) = sum(j=0,...,m-2) (m-1-j)*M(x,j,2),
    M(x,j,2) = B(D_time*x,T(j)*(D_time*x)).

The sums are empty at m=0,1. Telescoping the split proves

    B(x,T(m)*x) = B(x,x)-m*e(x)+C_m(x),  C_m(x)>=0.

For the previously constructed SAME dyadic unit excitation u, B(u,u)=1.
Its actual response therefore obeys

    R(m)=1-m*e(u)+C_m(u),
    m*e(u)-C_m(u)<=1-gamma  iff  gamma<=R(m).

The equivalence holds for every rational gamma; a positive gamma common to
the changing family is an OPEN analytic requirement, not an input proved
here. The computed curvature avoids discarding positive terms. The stronger
linear criterion m*e<1 and the previous geometric floor remain sufficient
options, not necessary obligations. This milestone constructs neither a
uniform gain estimate nor a spectral measure or logarithm identification.

| Declaration | Source | Checked content |
| --- | --- | --- |
| `responseOneStepLoss`, `responseOneStepLoss_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeResponseCurvatureGain.lean:113`, `lean/YMGap/Continuum/BF4WilsonAllNomeResponseCurvatureGain.lean:115` | SAME actual loss e |
| `responseCurvatureRow`, `responseCurvatureGain` | `lean/YMGap/Continuum/BF4WilsonAllNomeResponseCurvatureGain.lean:120`, `lean/YMGap/Continuum/BF4WilsonAllNomeResponseCurvatureGain.lean:127` | Computed triangular sum |
| `responseCurvature_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeResponseCurvatureGain.lean:130` | Actual defect response |
| `responseCurvatureRow_nonnegative`, `responseCurvatureGain_nonnegative` | `lean/YMGap/Continuum/BF4WilsonAllNomeResponseCurvatureGain.lean:135`, `lean/YMGap/Continuum/BF4WilsonAllNomeResponseCurvatureGain.lean:146` | Nonnegative gain |
| `response_curvature_identity` | `lean/YMGap/Continuum/BF4WilsonAllNomeResponseCurvatureGain.lean:173` | Exact actual response |
| `dyadicUnit_response_curvature_identity` | `lean/YMGap/Continuum/BF4WilsonAllNomeResponseCurvatureGain.lean:201` | SAME unit instance |
| `dyadicUnit_response_lower_iff` | `lean/YMGap/Continuum/BF4WilsonAllNomeResponseCurvatureGain.lean:210` | Exact scalar floor equivalence |

## Bounded integer rounding has an explicit uniform modulus

For ANY state x of the SAME completion, the actual mixed-moment column bound
and telescoping give

    0 <= B(x,T(n)*x)-B(x,T(n+j)*x) <= j/(n+1)*B(x,x).

The original bound is `mixedMoment_column_bound` at
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectTail.lean:87`.
The constructed unit norm makes the right side j/(n+1), without any energy
or curvature hypothesis. For a bounded shift j<=J and tolerance epsilon>0,
the computed modulus is

    roundingModulus(J,epsilon) = denominator(epsilon/(J+1)).

At scale k>=this modulus and lag n>=side(k), the actual unit responses
satisfy R(n+j)<=R(n)<=R(n+j)+epsilon. The proof uses side(k)>=k,
1/(n+1)<=epsilon/(J+1) and j<=J.

This error modulus is independent of every strict nome and width, named in
the theorem. It compares bounded forward offsets within each SAME state
at n>=side(k), not different states or dyadic neighboring lags with j growing
like n. It does not cover all assigned positive times, zero-time continuity,
cross-scale Cauchy convergence, or physical Yang--Mills time calibration.

| Declaration | Source | Checked content |
| --- | --- | --- |
| `response_shift_decreasing` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicResponseRounding.lean:79` | Actual shift monotonicity |
| `response_shift_upper` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicResponseRounding.lean:89` | j/(n+1) norm-relative ceiling |
| `dyadicUnitResponse_shift_bounds` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicResponseRounding.lean:121` | SAME original normalized response |
| `roundingModulus` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicResponseRounding.lean:143` | Computed tolerance cutoff |
| `dyadicUnitResponse_rounding_small` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicResponseRounding.lean:170` | Nome/width-uniform bounded rounding |

## Remaining forward backward join

Useful control of the actual overlap/dual moment and completed curvature on
a justified changing family remains OPEN. The cleared gain bound does not
give G>=0, a lower floor for D, or any common physical-scale response floor.
The exact backward target retains C_m; it does not postulate its estimate in
a new certificate bundle. A useful joint estimate must still be proved from
the original action and connected to the SAME response.

The ENTIRE original energy and variance already have SAME completed-state
pins: `energyLimit_completed_pin` at
`lean/YMGap/Continuum/BF4WilsonAllNomeTemporalEnergyLimit.lean:218` and
`varianceLimit_completed_pin` at
`lean/YMGap/Continuum/BF4WilsonAllNomeMarginalVarianceLimit.lean:236`.
Separate limits of the signed defect and another completion wrapper are not
required for a bound on that entire energy.

The bounded rounding estimate removes only that within-state sampling
error. Common-carrier or joint-functional cross-scale convergence with
explicit moduli, admissible renormalized YM field identification, nontrivial
continuum survival, physical mass calibration, full SAME QFT axioms and
every compact simple group remain OPEN. No displayed canonical chart claim
is closed by these supporting results.

## Verification boundary

Three final focused checks passed with one monitored worker, explicit
20-GiB ceiling and fresh process/memory/swap inspections before each launch.
The 5+10+5 printed gates use only allowed axioms propext and Quot.sound;
roundingModulus is axiom-free. Accepted logs have no errors or warnings.
Independent Sol mathematical reviews and Luna evidence review passed.
No new sorry, axiom, classical shortcut, analytic premise, erased witness
or weakened frontier is introduced. Root imports the three consumers, but
root/tree, broad audit/guard and progress metric were NOT run.

All first logs are REJECTED: overlap had a non-closed decide goal and
elaboration timeouts, curvature omitted time-zero simplification, and
rounding used unqualified identifiers. Closed-goal typing, bounded local
opacity/explicit transports, controlled simplification and correct namespaces
repaired these without statement, guard or resource-limit changes.
CI and the canonical chart remain unchanged; no paper-list/chart reprint.

Accepted SHA256 evidence:

| Artifact | SHA256 |
| --- | --- |
| `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedOverlapGain.lean` | `9271a2c9a86942bcff5ef449e61d4daac59293c728805e681cde56868aff6417` |
| `/tmp/ym-dyadic-signed-overlap-gain-20261002-second.log` | `f7447a0e6c23a1940e174e3aa1cb2938d7d6434c4f58cd19aee008accfe68855` |
| `lean/YMGap/Continuum/BF4WilsonAllNomeResponseCurvatureGain.lean` | `ab0240cded73ebb78c74c2bb27c8d9831c2688f8a8f42d6e43dc54c782e5619d` |
| `/tmp/ym-response-curvature-gain-20261002-second.log` | `d9e14f63974bc3a6e903b0b88d9c977cd1323da4ca1dc0bab5e14b231f6e17ad` |
| `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicResponseRounding.lean` | `127c7e72776b8a151bbee1b143380a6d043b1beaede27ae49d3cd4d97c9fc2b3` |
| `/tmp/ym-dyadic-response-rounding-20261002-second.log` | `d6e784e77c808c7431c1d53e52bac834acf6fc98045eccfe1b8590faf9fdcb75` |
