# Second derivative witnesses on the original physical carrier

Date: 2026-10-01 UTC. PROGRESS after `627d529`: supplied original Cauchy
representatives now construct TWO consecutive physical derivative-domain
points, not merely a first-order Taylor statement. The second output has an
explicit squared-norm ceiling. This is fixed-nome/fixed-width regularity,
not density, continuous unitary time or a continuum Hamiltonian.

## Constructed witnesses

All new declarations are in
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSSecondCore.lean`.
Let T be the EXISTING original one-step completed time and L the EXISTING
bounded `BF4WilsonAllNomeDyadicDerivative.derivativeAction`. L is not silently
identified with an everywhere-defined physical generator or with a logarithm.
The existing `BF4WilsonAllNomeSectorDerivative.corePoint`
(`lean/YMGap/Continuum/BF4WilsonAllNomeSectorDerivative.lean:139`)
constructs a physical derivative pair `(T y,L y)`.

`timeSeed` (:50) applies the actual nonexpansive T map to a supplied Cauchy
representative Y; `timeSeed_pin` (:53) identifies its class with T y.
`derivativeSeed` (:58) extracts the explicitly supplied range representative
from `corePoint(Y).output.range`; `derivativeSeed_pin` (:62) identifies its
class with L y. The extraction uses the existing constructive
`BF4WilsonAllNomeTimeRangeClosed.representative` and `representative_pin`
(`lean/YMGap/Continuum/BF4WilsonAllNomeTimeRangeClosed.lean:128` and `:132`).
No representative of a bare quotient value is selected.

For a supplied pair of original Cauchy representatives `(Y1,Y2)`,
`firstPoint` (:69) and `secondPoint` (:75) apply the actual `corePoint` to
these two computed seeds componentwise. `first` (:79) and `second` (:82)
map them to the EXISTING complex physical derivative domain.

`first_input_value` (:85), `first_output_value` (:95),
`second_input_value` (:105) and `second_output_value` (:115) prove the
original completed-value identities

    first  = (input T^2 y, output T L y),
    second = (input T L y, output L^2 y).

The first output uses the proved original commutation law
`BF4WilsonAllNomeDerivativeCore.derivativeAction_commutes_time`
(`lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeCore.lean:55`).
`first_output_eq_second_input` (:127) uses the actual physical value map's
injectivity to join them on the SAME completed bond carrier.

## Quantitative regularity

`second_output_norm_le` (:135) proves

    physicalNormSquared(output(second(Y1,Y2)))
      <= originalAmbientNormSquared(y1)+originalAmbientNormSquared(y2).

It applies the existing `derivativeAction_norm_bound` TWICE per component
(`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicDerivativeLaws.lean:108`) and
the physical `inner_value` pin. The right side is the ORIGINAL PREIMAGE
norm, not the norm of T^2 y. This does not bound the physical
derivative on every state, prove full-domain invariance, or supply a mass gap.

Both domain points and their source/range witnesses are returned as data.
There is no new analytic field and no erased existential supplying a source.
The represented range witness retains its existing explicit moduli; no
new approximation limit is claimed in this module.

## Causal consumer and open work

This provides an actual second derivative for these twice-time-smoothed
inputs, a regularity input for a quantitative scaled-Cayley local-error
argument. The scaled imaginary-shift inverses, local-error estimate and
product-Cauchy modulus are not constructed here. With the existing
plus=input+i*output and minus=input-i*output convention, a future phase
calibration must retain the factor two; it must not conflate one Cayley
step with one unit of physical time.

The existing original inverse-sum estimate approximates T y by T^2-images
with explicit relative squared error
(`BF4WilsonAllNomePositiveTimeRange.inverseSum_error_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomePositiveTimeRange.lean:75`).
An assembled Type-valued density certificate for these NEW physical second
points on supplied Rows is not built in this checkpoint. No arbitrary
derivative-domain output is asserted to lie in the derivative domain again.

The PRIMARY open producer remains useful complete signed error versus SAME
interacting variance on a justified coupling/spatial/spacing family.
Nontrivial continuum survival, physical time and positive physical mass,
full same-theory continuum OS/QFT, Yang--Mills field/UV identification,
every compact simple group and the Clay target remain OPEN. No canonical
field or displayed chart claim changes; no ASCII reprint.

## Verification

The final focused check exited zero, emitted the target olean and passed all
14 printed gates, exactly {propext,Quot.sound}. Independent Sol mathematical
review and Luna source/log/hash review passed. No sorry, new axiom, Classical,
native_decide, noncomputable declaration, analytic premise or weakened frontier
was introduced. The first draft's namespace/unfolding errors were repaired
before acceptance; its log is not proof evidence.

Only main compiled, serialized through the safe-build skill and monitored
launcher: one worker, 20 GiB ceiling, unchanged 12 GiB OS reserve and dynamic
telemetry. No memory, heartbeat or worker limit was raised. Final telemetry
found 84 percent pressure-free memory and zero swap; user-owned reliability
jobs were left untouched. No full-root/tree build, broad audit, guard,
progress-metric script or CI change ran. Root import registration is not
aggregate checking. The documentation skill preserves the distinction
between the second-domain witness and the missing density/time/scaling data.

Accepted log: `/tmp/ym-complex-bond-second-core-second-20261001.log`.
SHA-256: `518d74de14f25074f5cec302289f2bd8657f6e471610489e0594ed4801786de4`.
