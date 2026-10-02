# Completed growing Wilson square response with retained exterior

## Result and scope

The EXISTING completed dyadic Wilson excitation now has a strictly positive
response floor at EVERY integer lag, without a small-total-heat-loss premise. The finite
proof compares the original endpoint with its constructed exterior spectator,
and the completed proof uses the SAME original variance and transfer limits.
No original source, state, center, partition or time operator is substituted.

For 0<w<1 and the literal square perimeter P=4*side(scale), set

    a = w^(3P), l = headFloor(w)^(7P), u = prefixCap(w)^(7P),
    r = a*l^2/u^2 > 0.

At every positive terminal depth n+1, headCutoff(w)<=K, the SEPARATE guard
1<=K, and side(scale)<width, the COMPLETE original energy satisfies

    u^2*E + a*l^2*Z*OWNVar <= u^2*Z*OWNVar,
    E/Z <= (1-r)*OWNVar.

Here Z and OWNVar are the original odd marginal mass and variance. Only the
explicit positive band cap and original positive partition are inverted;
interacting variance is never inverted. The label-two guard is unnecessary.

For v=dyadicExcitation.val, B=completedInner and T=completedTime on the SAME
original completion, the existing regulator limits then give

    B(v,T(1)v) >= r*B(v,v) >= r*starRatio(w) > 0.

The already proved positive-form propagation on this SAME completion gives,
for EVERY integer m, including m=side(scale),

    B(v,T(m)v) >= r^m*B(v,v) >= r^m*starRatio(w) > 0.

The coefficient has no width, cutoff or terminal-depth argument, but DOES
depend on nome and perimeter; its propagated power additionally depends on
lag. This is not a uniform changing-family floor, fixed-physical-time scaling
survival estimate, positive physical mass or continuum QFT result.

## Mathematical argument

The generic word induction carries a lower spectator independent ONLY of
the distinct word links. Every remaining kinetic factor is retained, yielding

    P_active(R*f) = a*(P_active R)*f

as supported-Haar equality. It does not assert that the original interacting
endpoint q=V*u_(n+1) is independent of those links. The actual R contains the
full predecessor source V*u_n and the spatial collar complement.

An erased selected edge supplies an independent proof representative of
P_active R. Its exact fundamental first moment proves H[R*(P_active R)*f]=0,
with the full active heat unchanged in the statement. The existing constructed
certificates lR<=q<=uR and `response_band_cleared` then give a*l^2*A<=u^2*C
for A=sourceMoment(q,psi^2) and C=kineticPair(q*psi,q*psi).
The dual test is shifted by a times the mean; psi=f-OWNmean is NOT treated
as a heat eigenvector. Exact existing pins A=Z*OWNVar and E=A-C give the
finite bound above.

The completed consumer uses diagonal regulators k=depth=s>=1. Taking
n=s-1 preserves the positive-depth premise; K=headCutoff(w)+s supplies both
cutoff guards. Existing finiteVariance=finiteEnergy+finiteScalar converts the
energy bound to r*finiteVariance<=finiteScalar. The already constructed
variance and transfer Cauchy streams and their completed pins give the SAME
one-step pairing. The existing excitation norm floor supplies r*starRatio.
No reference-depth propagation, width map or new convergence hypothesis is used.

`response_geometric_lower` then propagates the constructed one-step fraction.
Its positivity argument uses actual time powers on the existing completion,
not a supplied positivity or spectral hypothesis. Thus fixed-parameter
lag-side response no longer needs a supplied relative-energy budget. The
explicit r^side floor still gives no positive uniform scaling limit.

## Declaration evidence

Paths below are relative to the repository root.

| Declaration | Source | Content |
| --- | --- | --- |
| `pairing_with_prefix_spectator` | `lean/YMGap/Continuum/SU2QuaternionProductHeatSpectatorWilsonWord.lean:141` | Word induction retains exterior and full remaining heat |
| `productMap_fundamental_word_spectator` | `lean/YMGap/Continuum/SU2QuaternionProductHeatSpectatorWilsonWord.lean:287` | Fundamental transmission with SAME transformed spectator |
| `fundamental_word_first_moment` | `lean/YMGap/Continuum/SU2QuaternionProductHeatSpectatorWilsonWord.lean:326` | One forward exposed edge kills the independent insertion moment |
| `squareSpectator` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSpectatorResponse.lean:113` | Actual exterior constructed from original predecessor |
| `paddedSquare_spectator_kinetic` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSpectatorResponse.lean:138` | Literal growing square under ORIGINAL active heat |
| `paddedSquare_spectator_zero` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSpectatorResponse.lean:162` | Actual kinetic-weighted zero moment |
| `squareResponseFraction` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSpectatorResponse.lean:220` | Explicit r with complete parameter dependence |
| `squareResponseFraction_positive` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSpectatorResponse.lean:226` | Strictly positive r at fixed nome and scale |
| `paddedSquare_energy_band_cleared` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSpectatorResponse.lean:237` | COMPLETE energy versus OWN variance, cleared |
| `paddedSquare_energy_band` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSpectatorResponse.lean:337` | SAME original normalized energy ceiling |
| `finite_dyadic_transfer_fraction` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSpectatorResponse.lean:104` | Original finite reserve versus OWN variance |
| `dyadicExcitation_oneStep_fraction` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSpectatorResponse.lean:111` | SAME completed one-step response versus its norm |
| `dyadicExcitation_oneStep_floor` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSpectatorResponse.lean:134` | Existing norm floor gives r*starRatio |
| `dyadicExcitation_oneStep_ne_zero` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSpectatorResponse.lean:142` | Actual one-step response is nonzero |
| `response_geometric_lower` (existing) | `lean/YMGap/Continuum/BF4WilsonAllNomeResponseLower.lean:117` | Actual positive time powers propagate an initial fraction |
| `dyadicExcitation_time_geometric_fraction` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSpectatorResponse.lean:170` | SAME excitation retains r^m of its norm at every integer lag |
| `dyadicExcitation_time_geometric_floor` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSpectatorResponse.lean:178` | Positive r^m*starRatio floor, including lag side(scale) |
| `dyadicExcitation_time_response_ne_zero` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSpectatorResponse.lean:189` | Actual response never vanishes at a finite integer lag |

## Remaining frontier

This supplies a response producer for the original growing loop, extending
the earlier plaquette linear-span band. It does not merely consume an
unavailable relative-energy hypothesis and does not reprove the existing
norm floor or construct a replacement excitation.

The next required estimate is useful control at assigned fixed physical time
on an explicitly justified changing family. The lag-side instance is now
proved at each fixed parameter, but r^side need not stay positive uniformly
when perimeter or nome changes. No independent all-state lower bound, nontrivial
continuum survival, cross-scale carrier comparison, physical Hamiltonian
calibration, full SAME-theory QFT or every-group construction follows.
The older exact signed-energy and optional loss-only routes remain available.
No canonical frontier field or displayed chart claim is changed.

## Verification boundary

Three final serialized focused target checks passed, each with one worker and an explicit
20-GiB ceiling after a fresh process, pressure and swap check. The accepted
logs contain 4+9+8 printed axiom outputs, each exactly {propext, Quot.sound},
and no errors or warnings. The first generic draft and first finite draft
failed elaboration and were repaired; their logs are NOT accepted evidence.
Earlier completed-consumer checks also passed before the integer-lag append
and scope-docstring correction; final source evidence uses the third check.
No limits, guards or theorem statements were weakened to repair those drafts.
Independent Sol mathematical review and Luna source, log and documentation
evidence review passed. Root imports the final consumer;
root/tree builds, broad audit/guard and progress metric were NOT run. No
sorry, new axiom, classical shortcut or compiler-trusted decision was added.
CI remains unchanged and off; the canonical ASCII block is unchanged.

| Source or accepted log | SHA-256 |
| --- | --- |
| `lean/YMGap/Continuum/SU2QuaternionProductHeatSpectatorWilsonWord.lean` | `24624a5fb16acb95096c6c2541b45dfdbad2450299658bfa7dcaa2202bd15679` |
| `lean/YMGap/Continuum/BF4DyadicWilsonSquareSpectatorResponse.lean` | `490fd735d162dc0f57cb1cc3a183a54f4465054dbefe7f1ae72725f4f23768bc` |
| `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSpectatorResponse.lean` | `1317a798451f270b6fd1f180b579f8d2d55f7343a66225d9f344bc36b0ad29ac` |
| `/tmp/ym-spectator-wilson-word-20261002-second.log` | `22b2da6c71c2c8726344efc43199c9530be5aa82f4b451dfe60d697ae5dac65b` |
| `/tmp/ym-dyadic-spectator-response-20261002-second.log` | `438dcbbf4cb5eecca78a78e08ae9a3e752544ec43117b0a329c3d43f146ce948` |
| `/tmp/ym-completed-dyadic-spectator-response-20261002-third.log` | `7e0eb3c54d375b233c478556b62831e96a6265dd7cd900333cc56b5a2db82633` |
