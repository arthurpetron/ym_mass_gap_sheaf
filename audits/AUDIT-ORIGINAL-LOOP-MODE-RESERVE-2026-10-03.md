# Actual Wilson-loop mode in the original signed-cost reserve

The whole-project goal remains OPEN: nontrivial continuum Yang--Mills on
R^4 for every compact simple group, SAME-theory QFT axioms and a finite
positive physical mass gap. This checkpoint proves a finite original-source
reserve, not a uniform changing-family estimate or continuum survival.

## Checked mathematical increment

Let H be the actual product Haar functional and P the actual selected-link
product heat. Suppose the supported polynomial f satisfies H(f)=0,
H(f*f)=1 and the tested identity P f=a*f. For ANY supported signed p, put
m=H(p), z=H(p*f) and r=p-m*1-z*f. Symmetry, the two tested pins and
positivity of the SAME kinetic quadratic give

    0 <= H(r*P r) = H(p*P p)-m^2-a*z^2.

There is no division, positive-source assumption, new normalizer or spectral
theorem. The generic statement names its mode identities explicitly.

For the literal padded dyadic square f, s=side(scale), the source constructs
H(f)=0 and H(f*f)=1 using its unique selected edge, independent unit tail
and Haar word moments. Distinct active edges give a=w^(12*s). This is an
identity for the actual ACTIVE product heat P, NOT an eigenpin for the
interacting transfer T. Substituting p=V*h, with the ORIGINAL spatial
action V retained, and using the original quadratic pin proves

    ell(h)^2 + w^(12*s)*ell(h*f)^2 <= ell(h*T h),

where ell(h)=H(V*h) and T is the original interacting transfer. The source h
may be signed and contain every action/message factor. This theorem assumes
w>=0, K>=1 and s<width; it does not need a strict spatial-density guard.

Its actual chronological OWN-block specialization uses

    c = middleRatio(...,(n+1),n,f),
    A = g_(n+t),  b = T^t(g_n*(f-c)),
    Z0 = ell(A*A),  Z1 = ell(A*T A),
    S = ell(b*b),   J = ell(b*T b),
    D = Z1*S-Z0*J.

Under the explicit strict-nome and original head-cutoff guards, the actual
square certificate proves Z0>=0. Consequently

    D + Z0*(ell(b)^2+w^(12*s)*ell(b*f)^2) <= Z1*S.

Both distinct partitions, the complete signed cost, the full action and
the depth-n center remain unchanged. The extra tested-loop contribution
has a nonnegative explicit coefficient; no positive lower bound for its
overlap with b is asserted.

## Exact declarations and existing consumers

| Declaration | Source | Role |
|---|---|---|
| `kineticPair_two_mode_floor` | `lean/YMGap/Continuum/SU2QuaternionProductHeatTwoModeFloor.lean:36` | Division-free two-mode kinetic residual bound. |
| `paddedSquare_transfer_loop_mode_floor` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareLoopModeReserve.lean:159` | Actual square-loop reserve in the ORIGINAL transfer quadratic. |
| `paddedSquare_own_block_cost_loop_reserve` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareLoopModeReserve.lean:217` | Reserve retained in the complete cleared chronological OWN-block cost. |
| `original_quadratic_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferPositive.lean:56` | Existing original transfer-to-kinetic-form identity, with V*h. |
| `clearedRayleighCost` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:131` | Existing complete D=Z1*S-Z0*J. |
| `originalOwnBlockVariance_converges` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:136` | Existing SAME filtered denominator reaches Norm*R(2*t). |
| `originalOwnBlockCost_converges` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:157` | Existing normalized complete cost reaches Norm*(R(2*t)-R(2*t+1)). |
| `normalizedAnchorResponse_block_floor` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132` | Existing backward survival consumer of kappa*R(s)<=R(2*s). |

The existing consumer declarations were source-reviewed, not recompiled in
this checkpoint. No new frontier bundle, hypothesis field or survival wrapper
was added. The generic mode assumptions are discharged for the literal loop.

## Unpaid causal edge

The reserve now retains a literal nonconstant Haar mode, rather than only
the constant projection. Its magnitude relative to the SAME filtered norm
on a justified changing family is NOT bounded here. The coefficient
w^(12*s) explicitly depends on nome and side; it is not a proved uniform
physical mass floor. Neither bare Haar normalization nor P f=a*f supplies
the missing interacting overlap estimate.

The next analytic task is quantitative control of the complete original
signed cost/response, or the existing macroscopic response ratio directly.
Passing that estimate uniformly through spatial growth and spacing,
nontrivial survival, physical mass calibration, canonical reflected OS
realization, full QFT and every compact simple group remain OPEN.

## Verification boundary

Accepted focused targets and logs, completed 2026-10-03 UTC:

| Target | Accepted log | Printed gates |
|---|---|---|
| `SU2QuaternionProductHeatTwoModeFloor.lean` | `/tmp/ym-heat-two-mode-floor-20261003-a.log` | 1 |
| `BF4DyadicWilsonSquareLoopModeReserve.lean` | `/tmp/ym-original-loop-mode-reserve-20261003-b.log` | 2 |

Both monitored runs exited zero, serialized with one worker, a 20 GiB worker
cap and 12 GiB OS reserve. Separate dynamic preflights found no competing
compiler/runner, 83--84% memory-pressure free percentage and zero swap.
All three accepted printed gates use only {propext, Quot.sound}; no accepted
error, warning or sorryAx. Independent read-only review confirmed the hashes,
literal source/center, guard scope and axiom outputs.

The first concrete attempt (`/tmp/ym-original-loop-mode-reserve-20261003-a.log`)
was rejected for a reflexivity/unfolding mismatch in the private Haar-moment
pin. Explicitly unfolding the locally irreducible source fixed it; no theorem
statement, mathematical assumption, heartbeat or resource limit changed.
Only the accepted second log is proof evidence.

Source SHA256, generic then concrete:

    8c27a8011f45503897e6735eb41ae0c9452bf470a8844064975368f9c30fa072
    bcb1eaaf29ff9bdc7af23b9db9e843397750c523cc21d694c4ca8a6a2129791a

Accepted-log SHA256, in the same order:

    fd491cf8ab9ff402c5f4a9cdf1cdfb71ca22983843dd552b18c7d8d13f0f4c22
    2351b91dc1e9bf6bb042fa685b781ce8e0f878f378070eeb0bb6b28a589f0cb5

Root import registration only; no aggregate build, full audit or broad guard
was run. No sorry, axiom, classical shortcut, surrogate or frontier weakening.
The exact canonical ASCII block and CI are unchanged; this supporting result
closes no displayed continuum box and requires no chart reprint.
