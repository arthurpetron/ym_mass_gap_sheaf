# ORIGINAL quadratic cost damping — 2026-10-04 UTC

PROGRESS: this report records the checked mathematical increment after
`2d7812e`, not an aggregate survival estimate or continuum/Clay closure.

## Constructed quantitative payment

Keep ORIGINAL ell=weightedMass (one V) and T=P M_V, with

    A=T a, b=T c, z=ell(a²), p=ell(a*A), v=ell(A²),
    C=ell(c²), B=ell(b²),
    Di=clearedRayleighCost(a,c), Do=clearedRayleighCost(A,b),
    y=p*c-z*b, R=p*ell(y²)+z*ell(y*T y).

`costTransportResidual_pair_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRayleighCostCoercivity.lean:70`,
identifies the literal ell(c*y) with the COMPLETE Di. Actual V-weighted
Cauchy--Schwarz and original quadratic positivity therefore yield

    p*Di² <= C*R.

`costTransportRemainder_cost_square_le` in the same file:107 has arbitrary
supported a,c and the actual positive-density cutoff K>=headCutoff(w),
0<w<1. It does not require positive a,c, Di>=0 or C>0. There is NO division
by source norm, and C=0 remains covered. This is a quantitative lower
payment, stronger than discarding R by nonnegativity.

The actual terminal transport then gives

    C*z³*Do + p*v*Di²
        <= v*p²*C*Di + eta*z²*p*v*C*B,

where a=g_(s+1) and eta=comparisonEta(w,width,s).
`terminal_clearedRayleighCost_quadratic_damping`, same file:141, retains the
favorable quadratic term on the LEFT. The incoming cost on the RIGHT is
still SIGNED. Every mass refers to its original chronological source.

Inputs are the existing `weighted_cauchySchwarz`,
`lean/YMGap/Continuum/QuaternionHaarWeightedCauchySchwarz.lean:87`, with
W=actual spatialWeight and constructed spatialCertificate; the original
`transferStep_quadratic_nonnegative`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferPositive.lean:67`; and
`terminal_clearedRayleighCost_transport_le`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRayleighCostTransport.lean:334`.
No auxiliary product reference law, guessed cancellation or new analytic
hypothesis is inserted. Both Taylor terms stay inside the complete cost.

## Consumer and remaining mathematical demand

`original_block_clearedRayleighCost_quadratic_damping`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRayleighCostCoercivity.lean:202`,
pins the inequality to consecutive ACTUAL block sources:

    a=g_(n+t), c=T^t(g_n*psi),
    A=g_(n+t+1), b=T^(t+1)(g_n*psi), eta=comparisonEta(w,width,n+t-1).

Only 1<=n+t and source support are required beyond the original cutoff
conditions. The exact same input psi is used at both endpoints; signed
psi, t=0 (n>=1), and zero source norm are included. The filtered norm C
and all original action factors remain.

The intended original source is c=T^t(g_stage*psi_stage), with the SAME
stage OWN center at every lag. `originalOwnBlockCost`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:98`,
normalizes the incoming cost by z*p and the next by v*q, where
q=ell(A*T A). These factors cannot be identified or replaced by one.
`original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`, still
requires the actual aggregate estimate versus SAME surviving variance.

This new damping permits persistent relative attenuation; it does NOT
supply an O(1/side) relative loss or macro retention by itself. Neither
the actual filtered-variance UPPER comparison nor a fixed-nome eta modulus
provides the missing changing-family lower survival/relative estimate.
C is the actual incoming filtered square, not the initial or odd-law OWN
variance. No vanishing C is canceled.

Parallel source reviews found no existing producer of the needed residual
cancellation magnitude. OWN centering gives orthogonality only against
its original odd marginal; after filtering the ground test changes to
T^(2t+1)g_stage. No later mean is silently identified with the stage mean.
Likewise fixed-carrier smoothing is already provided by
`mixedMoment_column_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectTail.lean:87`, and
`smoothing_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicDefectDecay.lean:259`;
neither is a source-relative survival producer. No duplicate smoothing
wrapper is added.

## Verification boundary

Final focused check: exit 0, no errors/warnings, all five public printed
gates use only {propext, Quot.sound}. Independent Sol semantic/source review
passed, including the original block specialization. Safe launcher: one
worker, 20 GiB ceiling, 12 GiB OS reserve, 300-second status interval. Fresh
process/swap/pressure checks before each launch found no competing Lean/
Lake/pytest/runner process, zero used swap, and 77 percent memory free.

Accepted source SHA-256:
`ee18dc54314647fe4e3bdbb93cac0587e43f3389bf679ed4616c120e7e843da5`.
Final log: `/private/tmp/ym-rayleigh-cost-coercivity-20261004-3.log`, SHA-256
`813e75ef18369abc6f178f758a42368295338ff73f3c5a402b7a07d1599f9c00`.
An earlier core-only check also passed. The rejected first attempt had
missing namespace opens and a weighted-pair elaboration timeout. Explicit
unfolding repaired it; no heartbeat or memory limit was raised. No rejected
sorryAx output is treated as proof evidence.

Root import registration only; no full/root build, audit, guard or broad
progress metric. No new sorry, axiom, analytic premise, frontier weakening,
resource/CI change or canonical chart closure. Nontrivial continuum survival,
physical mass, canonical OS/full QFT, every compact simple group and Clay
remain OPEN. The independent backward OS scout found no new fixed-carrier
seam with constructed limiting inputs; existing numerical/domain results
cannot replace `PositiveTimeOSRoot`'s canonical continuum pins.
