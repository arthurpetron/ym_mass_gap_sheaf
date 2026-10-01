# Whole signed family spectator cost contraction

Date: 2026-10-01 UTC. Exact spectator cost contraction now applies to
the WHOLE signed spatial plaquette family, rather than one face at a time.
The original terminal source and all cross terms are retained. The original
energy ceiling has a proved nonnegative gain. Its same-channel globally
centered moment sum equals the original Z*Var. No quantitative
variance-relative gain or physical scaling estimate is proved.

The positive cost comparison assumes 0<w<1 and K>=headCutoff(w).
The original energy consumer also assumes strict spatial padding and faces
inside the smaller slice; its heat eigenpin requires K>=1. Width, cutoff,
terminal depth, coefficients and family remain explicit parameters. These
are finite rational statements, not uniform thermodynamic or continuum bounds.

## Common footprint and original source

`familySlots`, `familyObservableBlocks` and `familySpectatorBlocks` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelPartition.lean:40`,
`:45` and `:49` use the union of every literal face support and its complement
on the complete slice. `familySpectator_observable_cover`, line 82, proves
the partition, and `spatialSpan_familySpectator_independent`, line 128,
proves independence of the COMPLETE signed family. Coefficients can have
either sign and faces can repeat; no facewise cost addition is used.

The source is q=P_fringe(V*g). The final consumer supplies the actual
g=terminalMessage(w,K,width,depth). Choosing only fringe spectators would
not advance the cost comparison because q is already projected there.
The common observable footprint can also retain spectators inside the
original action's active slice; strict improvement is not asserted.

## Constructed positive weight

Let H_n be the original product Haar functional and K_A the actual product
heat on the common active list A. Define

    e_f = partialHaarHeads_n(K_A*(f_lower-f_upper)^2).

`jumpDensity`, `jumpDensity_certificate`, `jumpDensity_independent` and
`singleEndedCost_eq_jumpDensity` are respectively
`lean/YMGap/Continuum/SU2QuaternionProductHeatJumpDensity.lean:48`,
`:64`, `:99` and `:118`. The certificate is Type-level data constructed
from the actual late-cutoff heat certificate and the square of the WHOLE
jump. Spectator independence follows from that of f and the active kernel,
transported through head integration. It is not a new analytic premise.

`singleEndedCost_drop_independent` and `singleEndedCost_full_eq_jumpDensity`
in `lean/YMGap/Continuum/SU2QuaternionProductHeatPassiveYoungContraction.lean:56`
and `:99` prove the exact full-kernel cost pin C_full(b,f)=H_n[b^2*e_f].
The cost-drop step uses the existing three-moment identity and supported
Haar equalities, not coefficientwise heat normalization.

`productHeat_partialSwap` in
`lean/YMGap/Continuum/SU2QuaternionPartialSwapHeat.lean:87` preserves the
actual kernel under exchange of selected endpoint blocks. The weighted
Bessel theorem `productChannels_familyProject_positiveWeighted_square_le`
in `lean/YMGap/Continuum/SU2QuaternionFamilyHeatGramPositiveWeight.lean:131`
proves, for actual channels (rho_c,c) and b_c=P_S(q*c),

    sum_c rho_c H_n[b_c^2*e_f] <= H_n[q^2*e_f].

It certifies K_S*(q-swap_S(q))^2*e_f on the doubled carrier. It does NOT
infer independence of individual square generators of a certificate for e_f.
The complete positive weight is sufficient. Consequently
`singleEndedCost_projected_channels_le`, PassiveYoungContraction line 114,
gives C_ch<=C_original for the whole f, with coefficient one.

## Actual energy and retained responses

All declarations in this paragraph are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyPassiveCancellation.lean`.
`family_cost_le_original`, line 140, supplies the common geometry and complete
original q. `padded_family_energy_eq_channels`, line 152, preserves the
ORIGINAL temporal energy before any estimate.

The existing `spatialSpan_fullRange` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyHeatEigen.lean:42`
supplies lambda=w^12 for the actual family. `eigen_jump_mean` and
`sourceIncrement_ge_eigenResponse_square` in
`lean/YMGap/Continuum/SU2QuaternionProductHeatEigenResponse.lean:44` and
`:67` retain J(b)=2*(1-lambda)*H_n[b*f]. These are ordinary Haar source
responses, NOT interacting means.

`padded_family_energy_channel_responses`, FamilyPassiveCancellation line 173,
proves 4*E_original+R_ch<=2*C_ch, with R_ch=sum_c rho_c J(b_c)^2.
`family_responses_ge_original`, line 224, proves R_ch>=J(q)^2 using the
previously checked channel mean Gram identity. `familyGain` and
`familyGain_nonnegative`, lines 262 and 270, give

    G = 2*(C_original-C_ch)+(R_ch-J(q)^2) >= 0.

`padded_terminal_family_energy_with_gain`, line 281, supplies the actual
terminal message and proves 4*E_original+J(q)^2+G<=2*C_original.

## Same interacting variance and remaining estimate

`padded_family_centered_channel_variance`, FamilyPassiveCancellation line 324,
uses psi=f minus its ACTUAL original odd-marginal mean and proves

    sum_c rho_c sourceMoment_full(b_c,psi^2) = Z*Var_odd(f).

The SAME terminal source, partition, global center and channel family are
retained. Individual sourceMoment(b_c,psi^2)=H[b_c*psi^2*P(b_c)] terms are
not asserted nonnegative or interpreted as separate probability measures
or channel-centered variances. Positive Gram coefficients alone do not
justify discarding their signed contributions.

NEXT: obtain a useful complete signed cost/remainder estimate against THIS
interacting variance on one justified physical source family. G can vanish.
Neither a lower fraction of Z*Var nor an appropriate scaling rate is supplied.
Physical mass calibration, nontrivial continuum survival, every-state uniform
physical decay, full same-theory OS/QFT structure, every compact simple group
and the Clay target remain open. No canonical field or chart node changes.

## Verification

Seven final focused checks passed all 19 printed gates exactly in
{propext, Quot.sound}. No new sorry, axiom, Classical dependency,
native_decide, noncomputable declaration or frontier weakening. Sol agents
supplied independent density/eigenresponse and footprint arguments; read-only
Sol and Luna reviews found no sign, parameter, cross-term or source mismatch.

Only main compiled, serially through the monitored launcher with one worker,
explicit 20 GiB ceiling and 12 GiB OS reserve. Preflight found no competing
compiler/runner and 91 percent free memory; no safety limit changed.
Namespace-only draft errors and dependent elaboration timeouts were fixed
before acceptance, without increasing resource limits. No full root build,
tree audit or guard was run; root imports are registered only. CI remains
manual-only. The unchanged canonical chart was not reprinted.

Final log SHA-256 values under `/tmp/`:

- `ym-partial-swap-heat-final-accepted-20261001.log`:
  `a5b1df262e0841be49e0d9450b50c0cf1c9ab9d882413ec8fa27da5998519ec6`.
- `ym-positive-weight-gram-final-accepted-20261001.log`:
  `ba184a57aa8a3fa6abcdd8dd79aae268892f304b7de53eaaf7d47afd5e83db7c`.
- `ym-whole-jump-density-accepted2-20261001.log`:
  `dd95c3f8f77781900d1892e95b2f2d1552ffa96cbc366720d83aa607c27ff93f`.
- `ym-whole-passive-young-accepted-20261001.log`:
  `a2b13fc3485fa60f463d5b325bca236678a94fc9b868b94f5770cba097e794fb`.
- `ym-family-channel-partition-accepted-20261001.log`:
  `a6cee3fdb6b97969fd41156d4c576817cc706070e0c6563bcc011f560080f15f`.
- `ym-eigen-response-accepted-20261001.log`:
  `dc990191152356a8ac2cd477d48aea2cdbcffa82c471a23d29ae4699ed860306`.
- `ym-whole-family-cancellation-accepted-20261001.log`:
  `88ec769cfb7da855a87279d05b4cc7fd9cf576f8fab1bf3d97b1e26bc664e664`.
