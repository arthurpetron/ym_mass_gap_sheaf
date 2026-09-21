# Inverse-heat remainder: coefficient obstruction, 2026-09-21

## Result and exact scope

The tested spin-uniform bound on the separated inverse-heat remainder is
false at EVERY fixed rational nome `0<w<1`. This remains true when the
proposed finite rational cap depends on w. It is not a refutation of the
full double commutator, the interacting energy estimate, or Yang--Mills.
The whole-project continuum R4 Yang--Mills/QFT/positive physical mass-gap
goal, for every compact simple gauge group, remains open.

## Coefficients actually checked

`physLinkWeight`, `lean/YMGap/Continuum/PeterWeylRealWeight.lean:126`, is
`lambda_j=w^(j*(j+2))`. It is the dimension-divided coefficient:
`coeffW_eq_dim_mul_phys` in the same file at line 132 states the exact
dimension factorization. This audit does not substitute `coeffW` itself
for lambda or use the legacy single-channel `RGTransport.charAlg`.

For physical label j>=1, define

```text
u = lambda_j/lambda_(j+1)     d = lambda_j/lambda_(j-1)
v = lambda_(j+1)/lambda_j     e = lambda_(j-1)/lambda_j
R_j = u+d-v-e
    = (1-w^2)*(w^(-(2*j+3)) + w^(2*j+1)).
```

The literal four-ratio definition is `rawAdjacentRemainder`,
`lean/YMGap/Continuum/SU2InverseHeatRemainderObstruction.lean:109`.
Its natural argument is j-1, so all three labels are valid, including the
vacuum when j=1. `rawAdjacentRemainder_eq_factorized`, same file at line 118,
proves the displayed equality using `physLinkWeight_succ_factor` at line 63
and positive rational reciprocals. The auxiliary factorized expression is
also defined at zero; no two-neighbor interpretation is asserted there.

At w=1/2, `six_four_pow_le_inverseHeatRemainder`, same file at line 206,
proves `6*4^j <= R_j`. The general result does not extrapolate from this
special case: `escapeIndex`,
`lean/YMGap/Continuum/SU2InverseHeatRemainderUnbounded.lean:42`, computes a
spin using the rational geometric cutoff. `raw_escapeIndex_bound` at
line 104 proves the raw value there is at least `1+abs C`.
`no_raw_spin_uniform_cap` at line 114 refutes every proposed cap at every
fixed strict nome. The index is witnessing data, not an erased existence.

## Why this is only the separated-remainder test

The algebraic motivation was inverse-heat conjugation of character
multiplication. In finite character coordinates, put
`A=P^(-1/2) M P^(1/2)` and `A*=P^(1/2) M P^(-1/2)`. The proposed split is

```text
P^(-1/2) (M^2 P - 2 M P M + P M^2) P^(-1/2)
  = -(A-A*)* (A-A*) + [A*,A].
```

This display explains the attempted route; it is NOT an implemented
operator identity on the actual joint completion. The scalar bookkeeping
that prevents misusing the obstruction IS checked:
`full_diagonal_cancellation`,
`lean/YMGap/Continuum/SU2InverseHeatRemainderObstruction.lean:226`, states

```text
[4-(u+d+v+e)] + [u+d-(v+e)] = 4-2*(v+e).
```

Thus the lower bound for R_j does not survive adding the discarded term.
The genuine adjacent character recurrence is available as
`character_step_pin`,
`lean/YMGap/Continuum/QuaternionHaarChebyshevEnergy.lean:41`.
The packaged diagonal `charTransfer`,
`lean/YMGap/Continuum/WilsonSchurIdentities.lean:288`, is a character-model
operator, not the interacting fixed-spatial transfer. No arbitrary-spin
interacting eigenvector identification is claimed by these new modules.

## Original-action consumer and repointing

`edgeDensity`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:55`, retains
`K(x,y)*(V*g)(x)*(V*g)(y)`. `energy_identity` in that file at line 253 gives
twice the whole signed energy as the integral of this density times the
squared jump. `normalizedEnergy_window`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:109`,
uses the actual terminal message and original partition. A signed high-spin
character is not an identified replacement for that positive endpoint source.

`centered_relative_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointTemporalEnergy.lean:128`,
still requires a supplied sufficiently useful SAME-variance one-step bound.
The coefficient obstruction supplies no such bound. Stop the attempted
branch that drops the negative square and independently caps its remainder
uniformly in spin. Keep the whole signed energy and original endpoint weights
in the next comparison. Do not replace the missing estimate by a static Ward
cost, a bare heat eigenrelation, or a degree-dependent cap without the required
regulator control. This does not add an all-observables requirement: the
intended spatial/nome/spacing family remains to be justified.

## Verification

The dependency-complete
`+YMGap.Continuum.SU2InverseHeatRemainderUnbounded:olean` target and both direct
checks passed all 15 printed gates (9 coefficient, 6 escaping-witness), within
`{propext, Quot.sound}`, without warnings or `sorryAx`. The index and its
positivity are axiom-free. One monitored 20 GiB worker was used; no full-root
build/audit was run. No hole, analytic assumption or canonical field changed.
Sol supplied the coefficient draft, ratio-factorization proof and independent
review; main supplied the general escaping witness, its raw-ratio consequence,
elaboration fixes and serialized verification. Logs:

- `/tmp/ym-gap-inverse-heat-obstruction-check2.log`
- `/tmp/ym-gap-inverse-heat-unbounded-check.log`
- `/tmp/ym-gap-inverse-heat-final-build.log`
