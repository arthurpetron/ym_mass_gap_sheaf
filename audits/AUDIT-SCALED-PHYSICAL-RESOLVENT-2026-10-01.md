# Parameterized resolvents on the original physical carrier

Date: 2026-10-01 UTC. PROGRESS after `7f3886d`: for every positive rational
t, the existing physical derivative graph now has a constructed
R_t=(I+t*A)^(-1) and a two-sided inverse of D_t=R_t^2+(I-R_t)^2.
The carrier, derivative domain and source witnesses are unchanged. This
removes the denominator construction needed for scaled imaginary shifts;
it does not construct those shifts or a continuous unitary time group.

## Constructed operators and rates

Module paths in this table are relative to `lean/YMGap/Continuum/`.

| Declaration | Module and line | Checked claim |
| --- | --- | --- |
| `resolventDomain`, `graph_sum` | `BF4WilsonAllNomeBondOSScaledResolvent.lean:108,144` | With lambda=1/t, scale the original (lambda*I+A) inverse domain point by lambda. Its input plus t times its output is x. |
| `inverse_right`, `inverse_left` | `BF4WilsonAllNomeBondOSScaledResolvent.lean:233,240` | Both inverse laws hold on the actual quotient graph domain for input+t*output. |
| `norm_bound` | `BF4WilsonAllNomeBondOSScaledResolvent.lean:272` | The original squared norm of R_t x is at most that of x. |
| `reflection_norm_bound`, `neumannStep_norm_bound` | `BF4WilsonAllNomeBondOSScaledReflection.lean:191,252` | S_t=2R_t-I is contractive; N_t=(I-S_t^2)/2=2R_t(I-R_t) has squared-norm factor 1/4. |
| `modulus`, `rows`, `fixed_point` | `BF4WilsonAllNomeScaledResolventNeumannLimit.lean:218,244,272` | Witness-preserving iteration b_(n+1)=x/2+N_t b_n returns a geometric modulus and actual completed limit y=x/2+N_t y. |
| `denominator_resolvent_square_pin` | `BF4WilsonAllNomeBondOSScaledDenominator.lean:58` | The constructed I-N_t equals R_t^2+(I-R_t)^2 on the same carrier. |
| `inverse_right`, `inverse_left` | `BF4WilsonAllNomeBondOSScaledDenominator.lean:134,230` | The actual inverse is 2y; the form floor 1/2 gives injectivity and the second inverse law. |
| `inverse_approximation_bound`, `inverseCertificate` | `BF4WilsonAllNomeBondOSScaledDenominator.lean:243,277` | Supplied Rows return the inverse and a Type-valued all-tail rate. Accuracy epsilon/4 pays the squared-distance factor four. |

The Neumann cutoff uses the supplied source's rational norm ceiling. The
completed approximation rate also retains its represented range moduli.
Descent to all bond classes uses congruence and quotient lift, not selection
of a representative. No new analytic premise is added.

The constants 1/4, 1/2 and 4 are uniform in t, nome, width and state for
these operator/denominator estimates. In particular, the squared inverse
norm ceiling 4 is not a physical generator spectral-gap estimate. The
parameter t is mathematical; no lattice-spacing or physical-time calibration
is inferred from it.

## Remaining causal work

Next on this operator branch are scaled imaginary-shift inverses, scaled
Cayley operators, local consistency on the existing second core, and a
product-Cauchy modulus with the factor-two phase convention checked.
The primary scaling estimate remains useful JOINT complete signed error
versus the SAME interacting variance on a justified changing family.
Survival, physical mass/time, continuum QFT, field/UV identification and
every compact simple group remain OPEN. No canonical frontier field or
displayed chart claim changes.

## Verification

Four focused checks returned terminal exit zero and emitted their target
oleans. All 71 gates use exactly {propext,Quot.sound}: 20 resolvent, 12
reflection, 22 Neumann limit, 17 denominator. Sol reviewed the mathematical
chain independently; Luna checked the final denominator source/log/hash.
No new sorry, axiom, Classical dependency, native_decide, analytic field or
frontier weakening. Earlier failed draft logs are not accepted evidence.

Main alone compiled with one monitored 20 GiB worker, unchanged 12 GiB OS
reserve and dynamic telemetry. No broad build/audit/guard, progress-metric
script, raised limit or CI change. Root imports are registration only, not
aggregate verification. The documentation skill keeps operator uniformity
separate from physical mass uniformity.

| Accepted log under `/tmp/` | SHA-256 |
| --- | --- |
| `ym-scaled-physical-resolvent-two-sided-final-20261001.log` | `595b85de8b2010dd91a832413c457ac0e97ac834dc972682c903c234258f407d` |
| `ym-scaled-physical-reflection-first-20261001.log` | `cd9e7c411efd2d1081aa13b425df035907e4c8ef015e537f2c20879c938bf62e` |
| `ym-scaled-resolvent-neumann-first-20261001.log` | `f0e3f634083914db94b783773d0c307394634eb00b7bf4b4f4badcc295e90e01` |
| `ym-scaled-physical-denominator-second-20261001.log` | `da54460994fbed4fbed02288bf14e62617b1d76582ede4d05a4dc7cfe7f4f4ab` |
