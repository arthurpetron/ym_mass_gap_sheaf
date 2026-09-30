# Literal plaquette time-defect orbit and its scaling boundary

Date: 2026-09-30 UTC. Whole-project Clay target OPEN.
Classification: PROGRESS on a supplied original observable, not closure of
the primary normalized scaling-family estimate. Canonical chart unchanged.

## Step back and exact consumer

The previous prediction floor concerned an initial fundamental plaquette,
not all its conditional transforms. The actual conditional family is
idempotent (`BF4ExactSlabConditionalSweep.projections`,
`lean/YMGap/Continuum/BF4ExactSlabConditionalSweep.lean:56`). Repeating the
same conditional update is not an independent prediction-loss step.

This increment instead joins the existing finite physical-time energy
floor to a concrete observable on the literal Wilson completion. It does
not iterate the initial-source covariance bound or substitute a conditional
heat-bath operator for physical time.

## Short argument, on the same carrier

Write T for the existing one-step completed physical time and D=I-T.
The already proved mixed moments m(k,l)=<x,T^k D^l x> are nonnegative and
satisfy m(k,l)=m(k+1,l)+m(k,l+1):
`BF4WilsonAllNomeTimeDefectMoments.mixedMoment_nonnegative`,
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectMoments.lean:343`, and
`mixedMoment_split` at line 349.

Time-direction telescoping gives

    (n+1) m(k+n,l+1) <= m(k,l).
    (n+1)^2 m(2n,2) <= m(0,0).
    ||T^n D x||^2 <= ||x||^2/(n+1)^2.

The finite plaquette energy floor supplies <v,Dv> >= s(w)/2 for the
existing centered literal plaquette v, with s=starRatio. Cauchy--Schwarz
and the already proved ||v||^2<=4 give

    ||Dv||^2 >= s(w)^2/16 > 0,
    ||T^n Dv||^2 <= 4/(n+1)^2.

This supplies a nonzero actual observable, not just an implication with a
missing analytic hypothesis. The time-defect state stays in the existing
vacuum complement. No identification between different widths is asserted.

## Checked declaration path

- `BF4WilsonAllNomeTimeDefectTail.mixedMoment_time_budget`,
  `lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectTail.lean:71`;
  `mixedMoment_column_bound` at line 87 and `mixedMoment_two_defect_bound`
  at line 100 prove the two telescoping steps. `timeDefect_norm_pin` at
  line 112 pins the actual orbit, `timeDefect_bound` at line 122 bounds it,
  and `timeDefect_small` at line 129 supplies the explicit relative modulus.
- `BF4ExactSlabFixedSpatialPlaquetteEnergyFloor.plaquette_energy_floor`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteEnergyFloor.lean:257`,
  is the existing original finite odd-window input.
- `BF4WilsonAllNomePlaquetteEnergyFloor.finite_plaquette_increment_floor`,
  `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteEnergyFloor.lean:120`,
  pins that input to the original Wilson window. `plaquette_timeIncrement_floor`
  at line 139 passes through its actual joint diagonal limit.
  `plaquette_timeIncrement_defect_pin` at line 152 identifies the increment
  with twice the literal completed defect form, canceling the same centering
  terms. `plaquette_defect_form_floor` at line 173 proves the supplied floor.
- `BF4WilsonAllNomePlaquetteDefectOrbit.plaquette_defect_norm_floor`,
  `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteDefectOrbit.lean:92`,
  proves the nome-only positive norm bound. `plaquette_defect_orthogonal`
  at line 124 and `plaquette_defect_ne_zero` at line 149 certify its domain
  and nonvanishing. `plaquette_defect_orbit_bound` at line 156 proves the
  absolute polynomial tail; `orbitModulus` at line 165 and
  `plaquette_defect_orbit_small` at line 168 supply its rational-tolerance
  cutoff. `decayingExcitation` at line 231 constructs the source at every
  positive width without a face-existence input.

The previous `BF4WilsonAllNomePositiveTimeTail.positiveTimeTail_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomePositiveTimeTail.lean:126`, bounds the
opposite orbit D^n T x. The new estimate counts actual time steps in T^n D x.
The algebra is a positive-contraction smoothing argument, not a novel
non-abelian spectral-gap mechanism.

## Crucial limit test and next frontier

`BF4WilsonAllNomePlaquetteDefectOrbit.plaquette_defect_nome_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteDefectOrbit.lean:193`, proves

    ||Dv||^2 <= 192*(1-w)

for an ACTIVE four-link plaquette. It uses m(0,2)<=m(0,1) and the existing
`BF4WilsonAllNomeTimeIncrement.timeIncrement_nome_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeIncrement.lean:120`.
The active-link hypothesis is retained; arbitrary boundary faces are not
covered by this nome upper bound. The lower floor and polynomial tail do
not require that guard.

Thus the unnormalized source vanishes as w approaches one. An absolute
tail estimate for this source is not nontrivial continuum survival. The
generic tail uses the PREIMAGE norm ||x||, not the norm ||Dx||. There is no
uniform bounded inverse for D supplied here, no exponential EVERY-state
bound, no cross-width carrier map, and no physical-spacing calibration.

NEXT remains a supplied estimate for a controlled normalized original
source on a justified changing-coupling family at matched physical time.
No new analytic input bundle is introduced. A03, A05, B04/B05, the full QFT
obligations and the every-compact-simple-group Clay goal remain OPEN.

## Verification boundary

Three final focused checks: TimeDefectTail (7 gates), PlaquetteEnergyFloor
(4 gates), and PlaquetteDefectOrbit (11 gates). All 22 printed dependencies
are within {propext, Quot.sound}. The monitored launcher used one worker,
a hard 20 GiB worker ceiling, a 12 GiB OS reserve and dynamic safety telemetry.
No bare Lean invocation, broad root build/audit/guard, or CI change.

Final logs: `/tmp/ym-time-defect-tail-20260930-final.log`,
`/tmp/ym-plaquette-energy-floor-20260930-final2.log`, and
`/tmp/ym-plaquette-defect-orbit-20260930-final.log`.
No new sorry, custom axiom, assumed analytic producer, surrogate carrier,
or weakened frontier. No existing sorry discharged. Sol reviewed the
mathematics/source joins; Luna reviewed the unchanged canonical chart scope.
