# Normalized response survival throughout bounded real time

The macroscopic ratio now gives a positive response floor throughout each
bounded interval of represented positive real geometric times, not merely at
integer block endpoints. One explicit block of slack avoids an unnecessary
sharp-endpoint continuity argument. The family-wide ratio and cross-scale
limit remain missing inputs; no continuum mass-gap theorem is claimed.

## Proved discrete to real join

All declarations below are in
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRealSurvival.lean`.

`mesh_response_antitone:72` proves that the original completed dyadic
response decreases as mesh time increases. At the finer square-root mesh,
B(x,S(depth,n)x) is exactly a squared norm. The remaining mesh evolution
contracts that norm. The proof uses no source sign or spectral theorem.

`positiveAction_response_integer_slack:96` proves, on ANY state x in the
SAME original completion, for positive integer gap and represented time t<=L,

    B(x,T(L+gap)x) <= B(x,positiveAction(t)x).

The positive slack absorbs the upper-rounded dyadic approximants. The existing
witnessed timeRows and pairing modulus pass this order to their actual limit.
No exact real-time antitonicity, endpoint identity, new limit or selected
quotient representative is assumed.

`normalizedBond_geometric_real_floor:148` specializes the result to the
EXISTING normalized bond excitation z and the supplied SAME ratio
kappa*R(side)<=R(2*side), kappa>0. For every natural j and every represented
positive real time with spacing(scale)*t<=j, it proves

    bondInner(z,action(t)z) >= kappa^(j+1) > 0.

The ONE-block slack is visible. The proof preserves the original transfer,
completion, normalizer, range witness and vacuum complement. It needs no
adjacent budget, uniform raw norm floor, half-anchor estimate or additional
side>=2 premise. The j=0 time hypothesis is not inhabited by positive times;
every j>=1 gives the intended nonempty geometric interval.

## Next forward and backward inputs

With a fixed positive kappa across a justified changing family, this floor
does not collapse at a fixed geometric horizon. Producing that ratio and
BOTH-order effective normalized cross-scale comparisons remains OPEN.
The assigned geometric spacing is not yet calibrated as physical time.

The existing `CReal.ModCauchyEv`,
`lean/YMGap/Constructive/CRealCompleteCauchy.lean:70`, retains the outer
modulus, inner regularity and pairwise approximation thresholds.
`CReal.completeLimitCauchy:246` and
`CReal.convergesTo_completeLimitCauchy:276` in that file already consume
such data. The next missing work is an actual comparison producer, not
another interface assuming scalar convergence.

A one-probe scalar limit would NOT construct `CanonicalSchwingerLimit`,
`lean/YMGap/Continuum/CanonicalOSRoot.lean:121`: its observable algebra,
stage maps, norm/expectation pins and separate volume/cutoff moduli remain
additional requirements. Full QFT, local-field/physical-time identification,
continuum survival and the every-group Clay endpoint remain OPEN.

## Focused verification

Final third focused check passed all three printed gates, each exactly
{propext, Quot.sound}. Independent source/log review confirmed the actual
objects, positive slack and matching hashes. No new sorry, axiom, classical
shortcut or weakened field. Root import registered, NOT aggregate-checked;
no full build/audit claimed. CI and the canonical chart fence are unchanged.

The safe launcher used one worker, a 20-GiB worker cap and a 12-GiB reserve.
Fresh preflight found no competing compiler, 85% memory-pressure-free and
zero swap. Accepted log: `/tmp/ym-normalized-macro-real-survival-20261003-third.log`.
SHA256 source/log pair:

    1b229af4bc111179af00eb4a0b8f459744108f5ca30d6bd2ec2a07255f1ff57d
    eb53a5fc8a8878e9cc70d97b1e69f023ee376e701f626ec9c7c23e5ec276a314

The first two rejected drafts had local notation/rewrite failures and downstream
sorryAx outputs. Only the final corrected source and third log are evidence.
