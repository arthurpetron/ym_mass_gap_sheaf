# Exact spectator channel cost and retained source responses

Date: 2026-10-01 UTC. For ONE literal SU(2) spatial plaquette, integrating
the computed spectator channels cannot increase the exact single-ended
Young cost. The original terminal energy has an exact channel identity and
a retained response-square bound. This is a supplied-input finite estimate,
not a comparison with interacting variance or a physical scaling theorem.

## Sign preserving cost comparison

For an arbitrary supported source q and fundamental face character f, write

    A=H[q^2], F=H[q^2*f^2], G=4*A-F,
    alpha=1+w^32-2*w^12, beta=1-w^32,
    gamma=5-8*w^12+3*w^32=beta+4*alpha.

The original exact cost is C=beta*A+alpha*F. For each computed spectator
Gram channel c with nonnegative weight rho_c, first form
b_c=familyProject_spectators(q*c), then form its cost. Let A_ch, F_ch,
G_ch and C_ch be the unnormalized weighted sums of those quantities.
The signed b_c are not declared probability densities.

The existing coefficient-one mass and geometric contractions are
`channelSourceMass_le_raw` and `channelGeometricCost_le_raw`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChannelGeometricContraction.lean:261`
and `:225`). The new square comparison is `channelSourceSquare_le_raw`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChannelYoungCostComparison.lean:103`),
using weighted Bessel and the face's spectator independence.

If alpha>=0, compare beta*A_ch+alpha*F_ch with beta*A+alpha*F.
If alpha<0, rewrite the same cost as gamma*A+(-alpha)*G and use the
mass and geometric contractions. Both coefficients in that branch are
nonnegative: the curvature certificate is `fundamental_curvature_bounds`
(`lean/YMGap/Continuum/SU2HeatFundamentalIncrementBudget.lean:119`).
No absolute value replaces the original signed coefficient.

`channelYoungCost`, `channelYoungCost_le_raw`, `channelYoungCost_pin`
and `channelSingleEndedCost_le_original` are respectively at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChannelYoungCostComparison.lean:94`,
`:211`, `:271` and `:293`. They define the literal C_ch, prove C_ch<=C,
pin it to the actual single-ended heat costs at K>=2, and give their
coefficient-one contraction. Nome, cutoff, width, face and source remain
explicit; no terminal-stationarity or normalized-norm premise is introduced.

## Same original terminal energy

Now supply q=P_fringe(V*g_depth), the complete original terminal source.
Use the existing `passiveChannelIncrement` for D_ch, not the unsplit D.
The new declarations below are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPassiveSourceCancellation.lean`.

`padded_terminal_channel_young_identity` (line 115) proves

    4*E_original+D_ch=2*C_ch.

It uses the existing exact energy decomposition and Young identity within
each integrated channel. `passiveResponseSquares` (line 109) is
R_ch=sum_c rho_c*J_c^2, with the computed
J_c=2*(1-w^12)*H[b_c*f]. `passive_responses_le_increment` (line 151)
proves R_ch<=D_ch by positive product-heat Cauchy--Schwarz in each channel.
The pairing is formed AFTER spectator integration, not under an individual
sign-changing spectator rank-one pair factor.

`padded_terminal_passive_retained_square` (line 169) therefore proves

    4*E_original+R_ch<=2*C_ch,

and `padded_terminal_passive_retained_raw_cost` (line 186) supplies
the no-larger original-cost ceiling. No source or denominator is inverted.
The retained R_ch is not identified with the old global response square,
the original interacting mean, or centered variance.

`padded_terminal_increment_difference` (line 210) identifies exactly

    D_original-D_ch=2*(C_original-C_ch).

`padded_terminal_channel_increment_le_original` (line 245) proves D_ch<=D.
Cost and increment shrink together; the energy itself is unchanged. A
strict cost decrease or nonzero response for the actual source is not
proved. No channelwise centering replaces the original global mean.

## Remaining estimate and scope

The next analytic producer must compare the complete channel cost and
retained corrections, or the existing whole-family signed Ward/Taylor
remainder, with SAME interacting variance on a justified physical family.
No quantitative response fraction or spacing-uniform estimate follows
from the new contraction. The existing partition and variance floor
certificates do not supply that missing comparison.

The sign decomposition above uses ONE face's identity G=4*A-F. It does
not authorize applying the one-face result termwise to a signed family:
shared-link and all other cross terms would still require their own
common-active-set estimate. No new union-family estimate is claimed.
Physical calibration, nontrivial continuum survival, uniform every-state
physical decay, canonical limiting OS/observable identification, full QFT,
every compact simple group and the Clay target remain OPEN.
The canonical displayed nodes and chart remain unchanged.

## Verification boundary

Two final focused serialized checks passed 11 printed gates, all exactly
{propext, Quot.sound}. Earlier elaboration timeouts were repaired by local
opacity and explicitly typed channel-sum steps, not by raising limits or
changing statements. Error-recovery axiom output from failed draft checks
is not accepted evidence. The accepted logs have no warnings or errors.

The safe-build skill kept one worker, a 20 GiB worker ceiling, a 12 GiB OS
reserve and dynamic pressure monitoring. Preflight found no competing
compiler/test/runner and 91 percent memory free. Sol supplied and reviewed
the sign-preserving cost argument; main supplied the actual terminal-energy
consumer and serialized all compilation. No new sorry, axiom, Classical,
native_decide, noncomputable declaration or canonical field change.
No full root/tree build, audit or guard was run. Root imports are registered
only, not an aggregate root verification. The documentation skill keeps
the checked finite result distinct from its open scaling consumer.

Final log SHA-256 values, under `/tmp/`:

- `ym-channel-young-cost-comparison-accepted-20261001.log`:
  `5c7618ec77aa4e525c060f7e352a75a30c5ebfe9f08e84b7f60b7c25cb0974a9`.
- `ym-passive-source-cancellation-final-accepted-20261001.log`:
  `16daa542e7f9f747728bea4d1be6782bf8b07b20da3b70e8beda7aeb657c00ff`.
