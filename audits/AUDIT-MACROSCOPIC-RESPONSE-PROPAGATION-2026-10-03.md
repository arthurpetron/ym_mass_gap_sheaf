# Macroscopic response propagation on the original transfer

A single supplied response ratio now propagates across arbitrary integer
blocks of the SAME completed transfer. This removes the need to prove an
adjacent-step estimate merely to obtain later block-response floors. The
ratio itself is still an open analytic input on a changing family.

## Proved statements

Write R(n)=B(x,T(n)x), where x belongs to the original all-nome completion.
The state, nome, width, completed inner product and transfer remain fixed.

`response_block_second_difference`,
`lean/YMGap/Continuum/BF4WilsonAllNomeBlockResponseLower.lean:81`, proves

    R(n+2*s)-rho*R(n+s) >= rho*[R(n+s)-rho*R(n)].

It uses the existing positive time form on the actual vector
T(s)x-rho*x. No sign premise on rho, spectral theorem, new carrier or
block-operator structure is introduced. The statement also permits s=0.

`response_shifted_block_step_lower`,
`lean/YMGap/Continuum/BF4WilsonAllNomeBlockResponseLower.lean:104`, propagates
a supplied rho*R(start)<=R(start+s), for rho>=0, to every full later block.

`response_shifted_block_geometric_lower`,
`lean/YMGap/Continuum/BF4WilsonAllNomeBlockResponseLower.lean:129`, consequently
proves, for every natural j,

    rho^j*R(start) <= R(start+j*s).

These are conditional estimates, not physical instances of a uniform ratio.
Their immediate intended consumer is the existing normalized positive-time
anchor. A ratio kappa*R(s)<=R(2*s) can first propagate to R(3*s), then
control R((j+2)*s) relative to R(2*s), without dividing by a collapsing
raw norm. That actual anchor specialization is a separate proof boundary.

## Remaining mathematical input

Produce a positive rational kappa independent of the family index such that
kappa*R(s)<=R(2*s) on an explicitly justified family, and prove the required
normalized cross-scale comparisons and physical-time calibration. No such
family estimate or limit is supplied by this module. Full QFT structure,
continuum survival and the every-group Clay endpoint remain OPEN.

## Focused verification

The first focused check passed all three printed gates, each with precisely
{propext, Quot.sound}. Independent source/log review confirmed the algebra,
zero-block case and matching hashes. No new sorry, axiom, classical shortcut or weakened
field. Root import registered, NOT aggregate-checked; no full audit claimed.
CI and the canonical chart fence are unchanged.

The safe launcher used one worker, a 20-GiB worker cap and a 12-GiB reserve.
Fresh preflight found no competing compiler, 84% memory-pressure-free and
zero swap. Accepted log: `/tmp/ym-block-response-lower-20261003-first.log`.
SHA256 source/log pair:

    369f25fe02358bbb3543bd8fc66c4f66844d9c532d95785f6426f28322e8ebb7
    a6de4fc322f3df357131154d9f03b835c8450fa509826a21fb8d444842d41cc0
