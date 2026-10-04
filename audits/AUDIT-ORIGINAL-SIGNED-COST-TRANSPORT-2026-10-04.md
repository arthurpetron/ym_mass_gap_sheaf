# ORIGINAL signed cost transport — 2026-10-04 UTC

PROGRESS after `2538a94`: a finite ORIGINAL cost recursion retains a favorable
positive residual and pays only vacuum-partition mismatch. It is not an
aggregate survival estimate, a justified scaling family, or Clay closure.

## Forward construction and exact mathematical statement

In the notation of the checked leaf, ell is ORIGINAL `weightedMass`, containing
one original spatial V, and T is ORIGINAL `transferStep = P M_V`. Set

    A=T a, b=T c,
    z=ell(a²), p=ell(a*A), v=ell(A²), q=ell(A*T A),
    Di=clearedRayleighCost(a,c), Do=clearedRayleighCost(A,b),
    y=p*c-z*b, R=p*ell(y²)+z*ell(y*T y), M=z*q-v*p.

The exact identity is

    z³*Do + v*R = v*p²*Di + z²*M*ell(b²).

`clearedRayleighCost_transport_identity`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRayleighCostTransport.lean:166`,
proves this as a rational setoid equality for every supported signed c. It
uses ORIGINAL weighted transfer symmetry and linearity. Neither a sign of
Di nor a vacuum eigenpin is assumed. The definitions of y and R are
`costTransportResidual` and `costTransportRemainder` in the same file at
lines 115 and 120. The cost is the EXISTING
`clearedRayleighCost`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:131`.

For a=g_(s+1), late original cutoff K>=headCutoff(w), and 0<w<1:

* `costTransportRemainder_terminal_nonnegative`, same transport file:217,
  proves R>=0 from actual weighted square positivity and ORIGINAL T PSD.
  Signed and zero-norm c are included.
* `terminal_vacuum_mismatch_upper`, same file:273, proves
  M<=comparisonEta(w,width,s)*p*v. It propagates the actual terminal bracket
  through T, integrates with positive a and A, and cancels the absolute
  bracket scale. It does not assume M=0 or favorable source cost.
* `terminal_clearedRayleighCost_transport_le`, same file:334, therefore proves

      z³*Do + v*R <= v*p²*Di + eta*z²*p*v*ell(b²).

  The favorable residual is retained on the LEFT. Only the ground mismatch
  term is enlarged; no absolute bound is taken on the complete signed cost.

The explicit eta is `comparisonEta`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalComparison.lean:94`:
comparisonKappa(w,width)*mixRate(w,width)^s. It is cutoff/source independent
at FIXED nome and width, NOT coupling/width/spacing uniform.

## Exact backward consumer join

`original_block_clearedRayleighCost_transport_le`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRayleighCostTransport.lean:360`,
specializes the upper bound to

    a=g_(n+t), c=T^t(g_n*psi),
    A=g_(n+t+1), b=T^(t+1)(g_n*psi), eta=comparisonEta(w,width,n+t-1).

Its only additional guard is 1<=n+t. BOTH endpoints use the SAME input psi;
psi may be the existing stage-OWN-centered Wilson polynomial. It is NOT
recentered at the next lag. All original action factors are retained.

The existing `originalOwnBlockCost`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:98`,
uses exactly c=T^t(g_stage*shifted(f,OWNmean_stage)) and divides Di by z*p.
The next endpoint divides Do by v*q, NOT by the incoming partitions.
`originalOwnBlockCost_converges` in that file:157 supplies fixed-member
convergence to the SAME completed response drop.
The intended consumer is `original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`, which still
requires the ORIGINAL eventual aggregate cost bound against SAME surviving
variance. This increment does NOT produce that hypothesis.

The new information relative to completed defect monotonicity is the exact
finite favorable residual with moving ORIGINAL ground partitions. It is
not a new conditional budget interface. A useful source-specific signed
control of incoming cost MINUS retained residual, or its aggregate, remains
OPEN on a JUSTIFIED changing family. Di need not be nonnegative at finite
cutoff; near-unit coefficients cannot silently be replaced by one. Both
signed Taylor terms remain inside the complete cost; no source/variance
inverse or terminal eigenpin has been supplied.

## Verification and boundaries

Final focused check: exit 0, no errors/warnings, seven printed gates all
within {propext, Quot.sound}. Command used the safe launcher, one worker,
20 GiB ceiling, 12 GiB reserve and 300-second status interval. Fresh process,
swap and pressure preflights preceded every launch: no competing Lean/Lake/
pytest/runner process; swap used zero; memory free 77 percent.

Final source SHA-256:
`865f2e76a8f6dc84e3ba78125131d58f8b0e126778e10150aa9ad0fe73b70cc2`.
Accepted log: `/private/tmp/ym-rayleigh-cost-transport-20261004-3.log`, SHA-256
`3d557c081b823797a0bb99302e1b01aae74a87702ef366cb23f943aff3c19969`.
The earlier core-only check also passed. The rejected first attempt contained
a missing namespace open and a parenthesis error; it is NOT verification
evidence. No accepted sorryAx. Independent Sol semantic review passed.

Root import registration only; no full/root build, audit, guard or broad
progress metric run. No new sorry, axiom, analytic premise, resource increase,
CI change or frontier weakening. Nontrivial continuum survival, physical mass
calibration, full OS/QFT, every compact simple group and the whole Clay target
remain OPEN. No exact canonical chart claim changes; no chart reprint.
