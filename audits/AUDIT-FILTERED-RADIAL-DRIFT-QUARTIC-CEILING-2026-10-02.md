# Original signed radial drift ceiling with the quartic correction paid

The COMPLETE original filtered source now has a signed upper ceiling whose
word quartic correction is bounded against its SAME even partition. Its
upper radial term and drift square share the actual middle marginal.
The useful comparison to OWN interacting variance on a justified changing
family remains OPEN. No survival or continuum endpoint is closed.

## Exact original source and measure

Put g=terminalMessage_n, A=Tg, B=T(g*f), C=T(g*f^2), and
ell(p)=H[spatialWeight*p], with T the ORIGINAL transferStep. The literal
symmetric radius-two numerator is S=N-D, where N=ell(AC-B^2) and
D=ell((B-A*f)^2). The new exact fold is

    S = J - 2*D,
    J = H[W*(f(lower)-f(upper))^2],
    W = kineticWeight * (spatialWeight*g_n)
          * lift(spatialWeight*g_(n+1)).

`mixedDensity`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredRadialDrift.lean:82`,
retains ALL original factors. Its actual Type-valued positivity certificate
is `mixedDensity_certificate` at line 103. `mixedJumpSquare_noise_drift`
at line 306 proves J=N+D; `filtered_loop_jump_drift` at line 365 proves
the displayed identity for the literal original fundamental-loop source.
This is not the old matched-terminal selected insertion.

`mixedDensity_mass` at line 268 identifies ONLY the total mass with the
SAME evenPartition, whose middle pin is ell(A^2).
`mixedDensity_upper_marginal` at line 209 identifies the upper marginal,
with arbitrary insertion p, as ell(A^2*p). The lower marginal with p
inserted is not identified with it. `mixedRadialMoment_upper_pin` at
line 459 recodes the upper word's trace using padded original-Haar
coefficient equality, not a pointwise-to-coefficient inference.

## Signed radial ceiling

Let chord be the squared quaternion distance between the actual lower
and upper ordered words. Define R=H[W*chord*(4-f(upper)^2)] and
Q=H[W*chord^2]. The actual quaternion radial square certificate gives

    S <= 2*R + 2*Q - 2*D.

This is `filtered_loop_radial_drift_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredRadialDrift.lean:540`.
`filtered_loop_radial_drift_normalized` at line 551 bounds the EXISTING
windowRatio(n,2,n) using the reciprocal of its SAME positive evenPartition.
Neither the negative square nor a spatial/terminal factor is discarded.

## Actual mixed quartic producer

The selected squared-chord probe is independent of K, and its cap 16 is
constructed as an actual interval certificate:
`selectedQuarticProbe_interval`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMixedDepthQuarticInsertion.lean:86`.
The original prefix profile bounds its matched window(n,1,n). The existing
right common-tail theorem transports the COMPLETE probe to window(n,1,n+1),
giving, with c(w)=40*24576^2*(1-w)^2,

    H[W*selectedChord^2]
      <= (c(w)+epsilon+32*mixRate(w,width)^n)*evenPartition.

This is `mixed_quartic_mass_bound` at line 251. The computed depth onset
`mixedQuarticDepthCutoff` at line 171 is geometricCutoff(mixRate,32,epsilon).
`mixed_quartic_mass_tolerance_bound` at line 264 therefore gives

    H[W*selectedChord^2] <= (c(w)+2*epsilon)*evenPartition.

Both statements retain the computed original inclusive cutoff
quarticCutoff(w,epsilon)<=K, headCutoff(w)<=K, 16/17<=w<1,
epsilon>0 and an actual active selected link. The physical oriented-link
version is `oriented_link_fourth_tolerance_bound` at line 329.

The coefficient after the depth onset is independent of width/depth/link.
The depth onset depends on nome, width and tolerance; it is independent
of K and selected link. No uniformly bounded onset along a changing
family is asserted. The heat cutoff depends on nome/tolerance. No nome
identification with beta or physical spacing is supplied.

## Complete word correction paid in the signed source

`mixedWordQuarticRate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredQuarticCeiling.lean:43`,
is the EXPLICIT rate b=16*length^4*(c(w)+2*epsilon).
`mixed_word_quartic_tolerance_bound` at line 48 uses the existing ordered
quaternion word telescope under the SAME mixedDensity certificate to give
Q<=b*evenPartition. Repeated links/shared variables require no independence.

`filtered_loop_quartic_paid` at line 70 and its normalized version at
line 88 give the actual full-source ceiling

    S <= 2*R + 2*b*evenPartition - 2*D,
    windowRatio(n,2,n) <= [2*R+2*b*evenPartition-2*D]/evenPartition.

`paddedSquare_filtered_quartic_paid` at line 112 consumes the literal
existing padded square and constructs its active-link hypotheses from
strict spatial padding. No new source, center, norm or scaling hypothesis
is supplied. The length^4 cost is NOT uniform in square size.

NEXT is a useful estimate on the COMPLETE signed radial-minus-drift term
and this length-dependent correction relative to OWN variance/lag-one
response on a justified changing family. The conditional consumer remains
`dyadicUnitResponse_filtered_block_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicFilteredGeometricSurvival.lean:154`.
No declaration here produces its uniform C and positive reserve.

## Verification and boundary

The final focused THIRD radial/drift, SECOND mixed-quartic and SECOND
complete-word checks all exited zero. Their 14, 9 and 5 public gates
(28 total) use only {propext,Quot.sound}, or no axioms. All accepted logs
are free of errors, warnings and sorryAx. Independent source/math/log/hash
review passed for each. Rejected preliminary checks were elaboration,
namespace/support or explicit lift/parenthesization issues, not evidence;
no mathematical statement or guard was weakened.

| Artifact | SHA256 |
| --- | --- |
| `BF4ExactSlabFixedSpatialFilteredRadialDrift.lean` | `d16508bdae34ff5902205d5abdd581c001f8f3ee82f21f89c8f66e58f9ce3416` |
| `/tmp/ym-filtered-radial-drift-20261002-third.log` | `eee109f7debd7f03922ef1c8b5d02a3a48296f8af7b5c117f4d24720eac35a56` |
| `BF4ExactSlabFixedSpatialMixedDepthQuarticInsertion.lean` | `a65909f9b1f1b916988d93f91279e5d19a41b0633f7b5755256b5591a44c8b71` |
| `/tmp/ym-mixed-depth-quartic-20261002-second.log` | `9e2c9a9e3b084c86a73d76d5e949fda36583a77c160ab93b8d267f4e0500f051` |
| `BF4ExactSlabFixedSpatialFilteredQuarticCeiling.lean` | `7b0d8da20940325b0044d62878677f68624ab61216902f51eb074b3d9af6fd83` |
| `/tmp/ym-filtered-quartic-ceiling-20261002-second.log` | `09ea6a74de9288528c0fbb6c5338e7456d3e471d38a1cdb47adee16476b44bd9` |

Checks were serialized with one worker, explicit 20-GiB ceiling and 12-GiB
OS reserve. Every fresh launch preflight showed 85 percent pressure-free
memory and zero swap. Root imports registered, NOT aggregate-checked;
root/tree, broad audit/guard and progress metric were NOT run. No new
sorry, axiom, classical shortcut, weakened field, surrogate source or CI
change. The documentation skill kept coefficient uniformity distinct from
the width-dependent onset and the open physical scaling estimate. Exact
canonical chart unchanged; no ASCII reprint. Spatial/spacing control,
continuum survival, physical mass calibration, full SAME QFT, every compact
simple group and the Clay target remain OPEN.
