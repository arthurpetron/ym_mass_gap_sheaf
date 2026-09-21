# Original temporal family upper bound — source inventory, 2026-09-21

This is a source review, not a new upper-bound theorem or a counterexample.
It accompanies the independent construction of finite signed time sums on
the actual all-nome joint completion. The continuum Yang--Mills goal is open.

## Actual identity and missing estimate

`energy_identity`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:253`,
states `2*energy(g,f) = H[edgeDensity(g)*(jump f)^2]` up to rational
equivalence, for arbitrary supported signed f. `edgeDensity` in the same
file at line 55 is `K(x,y)*(V*g)(x)*(V*g)(y)`: the endpoint factors are not
removed. `normalizedEnergy_window`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:109`,
uses the actual `terminalMessage` and positive `oddMass` to identify this
energy with the original one-step window increment.

**NOT FOUND in the modules below:** a theorem bounding that whole signed
spatial plaquette increment by a nome-dependent multiple of `sum_p c_p^2`
without an extra family-cardinality factor, while retaining the same edge
density and partition. Such an upper estimate alone would still need a
quantitatively sufficient comparison with actual variance along the chosen
scaling family; its existence would not by itself settle calibration.

## Available estimates and their actual direction

- `energy_le_two_norm`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEnergyNormBound.lean:83`,
  bounds energy by twice the SAME unnormalized marginal squared norm.
  It does not give a coefficient-square upper bound for that norm.
- `wilson_energy_normalized`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonKineticIncrement.lean:283`,
  supplies a single-loop upper bound with active-edge guard.
  `joint_increment_nome_bound`,
  `lean/YMGap/Continuum/BF4WilsonAllNomeKineticIncrement.lean:168`,
  passes its cutoff/time limits to give `24*length^2*(1-w)`.
- `mixedTimeIncrement_cauchySchwarz`,
  `lean/YMGap/Continuum/BF4WilsonAllNomeMixedTimeIncrement.lean:56`,
  bounds each mixed increment without assigning a sign or setting it to zero.
- `family_energy_floor`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy.lean:174`,
  is a whole-signed-family theorem with no additional cardinality factor,
  but says `lower(w)*sum c_p^2 <= 600*upper(w)*normalizedEnergy(F)`.
  It is a LOWER bound and cannot be used as the sought upper estimate.

## Factorized and Ward results are different forms

`productMap_conditional_pair_bound`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatContraction.lean:171`,
requires literal conditional centering of its input under the bare product
map/Haar form. `productMap_plaquette_of_perm`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatPlaquette.lean:186`,
proves the `w^12` eigenrelation for a bare plaquette under that product map.
Neither statement diagonalizes the endpoint-weighted `productMap(a*f)`
for the actual `a=V*terminalMessage`.

`totalScore_cost_le`,
`lean/YMGap/Continuum/BF4ExactSlabWardFamilyCost.lean:115`, and
`diagonal_cost_le`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteGradientCost.lean:190`,
give bounded-overlap and coefficient-square control for static angular
Ward scores under the full action. **NOT FOUND in these modules:** a
comparison identifying their score cost with the temporal normalized
energy. No temporal cross-term cancellation is claimed by this audit.

## Independent same-carrier construction

`orbitSum_pairing`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointBilinearTime.lean:163`,
retains the full signed double correlator sum for finite time smearing.
This removes the missing vector-construction step on the all-nome carrier,
not the missing analytic estimate. Its orthogonality and two-step-bound
consumers cover empty and cancelling filters as well: no nonzero or
near-one filtered response follows from their statements.

The searched scope is the modules named above, the fixed-spatial kinetic
alignment/marginal/Dirichlet modules, and the all-nome Wilson time- and
mixed-increment modules. Absence in this inventory is not a proof that the
desired estimate is false.

## Later SAME-carrier consumer (2026-09-21)

`completedInner_oneStep_nonnegative`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointTimePositive.lean:116`,
now passes the original odd-window positive quadratic through the actual
padding, cutoff and representative limits to the existing all-nome
fixed-width `JointCompletion`. It is not a bare-product-map surrogate.

`temporalEnergy_linear`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointTemporalEnergy.lean:102`,
applies positivity to x-Tx and proves
`B(x,x)-B(x,T^n x) <= n*(B(x,x)-B(x,T x))` for every actual completed state.
The constructed signed orbit sums are included. This strengthens the
available consumer beyond time-zero presentations, not the missing
relative one-step producer. `centered_relative_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointTemporalEnergy.lean:128`,
keeps an explicitly SUPPLIED one-step bound relative to the SAME centered
variance; it does not produce a scaling family or prove survival.

## Tested inverse-heat shortcut

The later [coefficient audit](AUDIT-INVERSE-HEAT-REMAINDER-2026-09-21.md)
records a checked obstruction to bounding the separated inverse-heat
remainder uniformly in spin at any fixed strict nome. Its negative-square
partner cancels the growing inverse terms. This prunes that separate-remainder
estimate, not the full double commutator or the original weighted energy
bound sought here. The latter remains open.

## Later actual-source regularity

`terminalMessage_angular_bounds`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalAngularBound.lean:89`,
now constructs `C(w)g +/- h(w)Dg >= 0` for the actual `g=T^(n+1)1`.
`terminalMessage_angular_weighted_square` in that file at line 166 gives
the relative quadratic bound against every certified positive background.
Width/depth/cutoff do not enter the constants; nome does. This supplies a
source-specific derivative estimate, not a gradient-to-original-energy
comparison or a sufficiently small SAME-variance energy rate. See
`AUDIT-TERMINAL-ANGULAR-BOUND-2026-09-21.md` for the exact uniformity scope.

## Later relative Jacobi refinement

`terminalMessageRelativeWeightedSquare`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalJacobiAngularBound.lean:123`,
now gives `H[R(Dg)^2] <= B(w)^2 H[Rg^2]` for the same original source,
with `B(w)=32*JacobiShiftedRelativeSlope.budget w+1`. Differentiated
weight removal reaches the original unweighted heat prefix; the global
heat floor pays only approximation precision, not the relative constant.
The guard is `relativeCutoff w 32 <= K`; active links and positive depth
are explicit. The new bound still does not identify this derivative-square
quantity with the temporal energy or produce a useful SAME-variance rate.
See `AUDIT-JACOBI-RELATIVE-ANGULAR-BOUND-2026-09-21.md` for the checked path.
