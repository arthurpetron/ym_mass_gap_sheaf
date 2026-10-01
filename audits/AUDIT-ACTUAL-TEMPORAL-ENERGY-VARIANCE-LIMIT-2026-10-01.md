# Actual temporal energy, marginal variance and original completed norms

Date: 2026-10-01 UTC. PROVED for supplied radius-zero signed Wilson sources
at fixed nome and literal spatial width. This continues `cb41d35` without
identifying single-slice variance with physical bond norm alone.

## Weaker finite angular consumer

All declarations in this section are in
`lean/YMGap/Continuum/BF4WilsonAllNomeCenteredAngularBondBound.lean`.
`normalizedAngularReserve` at :45 retains g=terminalMessage(t), the ACTUAL
odd-marginal center psi, full transfer output T(g*psi), and SAME positive
oddMass. Its value is (1-w)*Angular(T(g*psi))/oddMass.

`normalizedAngularReserve_le_finiteScalar` at :58 derives support from
Within(0,e), applies original full-output smoothing to g*psi and multiplies
by the original positive reciprocal. `normalizedAngularReserve_completed_approx`
at :89 bounds this finite value by transferLimit.approx(p)+epsilon with
separate cutoff, exterior-time and representative guards. The preceding
`BF4WilsonAllNomeCenteredTransferBondLimit.transferLimit_completed_pin`
identifies this representative's class with the existing connected bond norm.
No raw-output Cauchy witness, angular limit or positive angular fraction is
assumed or constructed. This is a finite one-sided asymptotic upper bound.

## One fixed signed insertion constructs the actual energy limit

All declarations in this section are in
`lean/YMGap/Continuum/BF4WilsonAllNomeTemporalEnergyLimit.lean`.
`source_square_jump` at :67 uses `source_difference` and padded `source_shift`
to identify source(squareAt(e,1)) with jump(source(e)) squared. Padded negation
and multiplication keep unit terms and ALL signed cross terms.

`finiteEnergy` at :90 is the ACTUAL normalizedEnergy at K=headCutoff(w)+k
and terminal depth t, not a substitute sequence. `finite_increment_pin`
at :102 uses originalWindowScalar_pin, supported windowRatio_padded_congr
and normalizedEnergy_window to prove

    W_(k,t,t)[(e-shift(1,e))^2] = 2*finiteEnergy(k,t).

The original one-step action and odd partition are unchanged.
`finiteEnergy_half_pin` at :124 halves this exact identity.
`energyCutoffThreshold` and `energyTimeThreshold` at :141 and :144 use
the existing SINGLE squared-increment source thresholds at 2*epsilon.
`finiteEnergy_rectangle` at :149 controls every independent late (k,t),(j,s).
`energyCauchy` at :165 computes a Type-valued max-of-thresholds modulus;
`energyLimit` at :173 constructs the actual sequence's CReal.
`energyLimit_approx` at :176 retains all three explicit guards.

`energyLimit_increment_pin` at :199 identifies that limit as half the existing
increment CReal. `energyLimit_reflected_pin` at :209 and
`energyLimit_completed_pin` at :218 then identify it with

    B_V(v,v) - B_V(v,T_1 v), v=original centeredVector(state(e)),

using increment_reflected_pin and centeredVector_loss_pin. This is temporal
time loss, NOT B_V(v-T_1 v,v-T_1 v). No moving mean limit is needed here.

## Exact variance decomposition and the two distinct completed norms

All declarations in this section are in
`lean/YMGap/Continuum/BF4WilsonAllNomeMarginalVarianceLimit.lean`.
`bond_connected_time_pairing` at :75 uses crossOdd_pin, original time balance
and BOTH unit-stationarity laws to prove, for every intrinsic source x,

    connected_bond(0,ofSource(x),ofSource(x)) = B_V(v_x,T_1 v_x).

`finiteVariance` at :96 retains the ACTUAL original oddVariance, source and
finite mean. `finiteVariance_budget_pin` at :119 applies generic scalar
normalization to centered_transfer_quadratic_pin, dividing ONLY by SAME
proved-positive oddMass. At EVERY original finite regulator pair,

    finiteVariance(k,t) = finiteEnergy(k,t) + finiteScalar(k,t).

`varianceCutoffThreshold` and `varianceTimeThreshold` at :145 and :149 max
the energy and bond thresholds at epsilon/2, separately for the two raw
regulators. `finiteVariance_rectangle` at :154 and `varianceCauchy` at :181
give the actual variance's independent rectangle and Type-valued modulus.
`varianceLimit` at :189 constructs its CReal; `varianceLimit_approx` at :191
controls late raw regulators against an explicitly indexed representative.

`varianceLimit_budget_pin` identifies it with energyLimit+transferLimit.
`varianceLimit_completed_pin` uses both completed pins and the above bond
time pairing, then exact subtraction/addition cancellation. Thus

    Var_limit = Energy_limit + connected_bond_norm = B_V(v,v).

The ambient diagonal norm and adjacent-time physical bond norm remain
distinct. No new carrier, mean, action, time, partition or analytic premise
was supplied to make this join.

## Causal consumer and residue

This removes separate generic finite temporal-energy and marginal-variance
convergence obligations at fixed nome/width for radius-zero sources. Finite
signed energy/variance estimates now have constructed original completed
consumers. It does NOT estimate their complete signed remainder usefully
along a changing-coupling/spatial/spacing family. Fixed-source moduli are not
uniform changing-source or continuum moduli.

OPEN: the primary useful complete signed original-energy/SAME-variance
scaling estimate; spatial/spacing control; nontrivial continuum survival;
physical time and positive physical mass; canonical continuum OS/QFT and
every compact simple group. A limiting/lower-semicontinuous angular form
still needs construction if that stronger form is used; it is not needed
for the finite one-sided angular bound proved here. No canonical field or
displayed chart marker changes; the unchanged ASCII chart was not reprinted.

## Verification and independent review

All THREE final focused checks exited zero. Their 3+14+11=28 printed gates
depend exactly on {propext, Quot.sound}. No sorry, new axiom, Classical,
native_decide, noncomputable declaration or weakened frontier was introduced.
Initial explicit-support/doc-comment and whnf/type-inference errors were
repaired before acceptance. Generic scalar normalization, opaque original
objects and explicit scalar-convergence types resolved elaboration without
raising heartbeat, worker or memory limits. Intermediate failed logs are
not accepted proof evidence.

Independent Sol mathematical review checked the source-square, support,
normalization, time-loss and distinct-norm joins. Luna independently checked
the final sources, explicit witness/modulus flow and all accepted gate names
and dependencies. Neither reviewer ran a compiler. Main alone compiled,
serialized through the safe-build skill/monitored launcher with one worker,
20 GiB ceiling, 12 GiB OS reserve and dynamic telemetry. Preflight found
83 percent pressure-free memory and zero swap. A separate user-owned test
process initially deferred compilation; it was not killed or competed with.

No full root/tree build, broad audit or guard ran. Root import registration
does not assert aggregate-root checking. CI remains manual-only.

Accepted logs and SHA-256:

- `/tmp/ym-centered-angular-bond-first-20261001.log`:
  `024ac81f688ae7a98186e6986dfb8e666fcf99721b94a2fa5b2fcbf54f673e68`.
- `/tmp/ym-temporal-energy-limit-accepted-20261001.log`:
  `b825b78aede6b99a7888697e6afada5c23e7108227899e34330432e16dd2a4f6`.
- `/tmp/ym-marginal-variance-limit-accepted-20261001.log`:
  `b02e39a1d9aded9124915f17199bf70d426ecc1c22098b86af8911dd6bc0ad44`.
