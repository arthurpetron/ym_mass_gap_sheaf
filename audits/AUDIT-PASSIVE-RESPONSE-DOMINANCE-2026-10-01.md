# Spectator response dominance in the original energy ceiling

Date: 2026-10-01 UTC. The computed spectator response squares now dominate
the original single response square. Together with exact one-face cost
contraction, they give two nonnegative gains in the SAME original terminal
energy ceiling. Neither a strict gain nor a variance-relative scaling
estimate is proved.

## Exact channel mean Gram identity

For supported p on n quaternion blocks, selected list S and its literal
product channels (rho_c,c), define R(p)=sum_c rho_c*H[p*c]^2.
`channelMeanSquares` is defined in
`lean/YMGap/Continuum/SU2QuaternionProductHeatChannelMeanGram.lean:58`.
`channelMeanSquares_pin`, same file, line 78, identifies R(p) exactly with
the original selected-product kinetic pairing B_S(p,p). The proof uses
the existing passive-channel moment identity with EMPTY active heat list,
and `productMap_nil`. It does not mistake selected product heat for
conditional heat: unselected coordinates are Haar-averaged on both sides.

`channelMeanSquares_ge_haar_square`, same file, line 108, applies the
existing kinetic Cauchy--Schwarz inequality against the unit polynomial.
The normalized unit has B_S(1,1)=1 and B_S(p,1)=H[p], so

    H[p]^2 <= R(p).

This needs only nonnegative nome, distinct in-range selected blocks and
supported p. No late-cutoff, pointwise kernel floor or positive source
premise is required. `channel_mean_projected` and
`channelMeanSquares_projected_pin`, same file, lines 133 and 153, give
H[q*f*c]=H[b_c*f] when f is S-independent and b_c=P_S(q*c).
The generic identity retains any signed cross terms already in f.

## Complete original terminal source

The concrete consumer is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPassiveResponseDominance.lean`.
For the literal face f, set a=2*(1-w^12) and q=P_fringe(V*g_depth).
The original response is J=a*H[q*f]; computed channel responses are
J_c=a*H[b_c*f]. They are not interacting means.

`channel_response_squares_pin` (line 98) proves
sum_c rho_c*J_c^2=a^2*R(q*f). `channel_response_squares_ge_original`
(line 123) then proves J^2<=sum_c rho_c*J_c^2 for any supported q.
`passive_responses_ge_original` (line 146) supplies the COMPLETE actual
terminal source and the existing `passiveResponseSquares` R_ch.

Let C be the original exact plaquette Young cost and C_ch its checked
spectator-integrated cost. `passiveGain` (line 163) defines

    G=2*(C-C_ch)+(R_ch-J^2).

`passiveGain_nonnegative` (line 169) proves G>=0 for 0<=w<=1, every
cutoff, width and depth. At the actual late-cutoff regime and strict
padding, `padded_terminal_energy_with_passive_gain` (line 185) proves

    4*E_original+J^2+G <= 2*C_original.

The response correction cannot decrease and the exact cost cannot
increase. Neither contribution is declared nonzero; a quantitative useful
gain relative to Z*Var_odd is still missing. The concrete COST comparison
uses ONE face, not a facewise composition for a signed family.

## Verification and open input

Two focused serialized checks passed all nine printed gates, exactly
{propext, Quot.sound}, with no warnings or errors in the accepted logs.
No new sorry, axiom, Classical dependency, native_decide, noncomputable
declaration or canonical field change. Root imports are registered only;
no full root/tree build, audit or guard was run. The canonical displayed
nodes remain unchanged, so no ASCII chart is reprinted.

Accepted checks used one worker, an explicit 20 GiB ceiling, 12 GiB OS
reserve and dynamic memory telemetry. Preflight found no competing
compiler/test/runner and 91 percent memory free. One failed namespace-only
draft used the checkout's 32 GiB launcher default before the explicit
20 GiB cap was restored; no launcher or configuration limit was changed.
Its error-recovery axiom output is not accepted evidence. Sol supplied the
generic Gram proof; main supplied the actual source and energy consumer.
The documentation skill preserves this finite gain separately from its
open analytic consumer.

The remaining input is complete signed cost/remainder control against
SAME interacting variance on a justified physical source family. The
whole-family positive-weight cost extension is under source review, not
proved by this milestone. Physical calibration, nontrivial continuum
survival, uniform every-state physical decay, canonical limiting OS/QFT
identification, every compact simple group and Clay remain OPEN.

Final log SHA-256 values, under `/tmp/`:

- `ym-channel-mean-gram-accepted-20261001.log`:
  `4db5ed556721c28eaab47d298eab0f64957b1a7054f5f8a933588776ced9cabb`.
- `ym-passive-response-dominance-draft-20261001.log` (accepted first consumer check):
  `4aa40953b24185ccb1378cb453995beb1dadcc24cce5ffcd3accd8c383e42d2f`.
