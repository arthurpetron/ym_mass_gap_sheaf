# Actual auxiliary loss and finite rational certificate consumer

## Result and open boundary

On the original finite full-action completion, let S be the eight-color
conditional sweep, B=S* S, and u the actual second coupled Chebyshev
component. The required analytic inequality has the exact reformulation

    c ||B u||^2 <= 2 ||S u||^2
      iff (c-2)||S u||^2 <= c loss(reverse schedule, S u).

This is `reverse_energy_iff_loss`,
`lean/YMGap/Continuum/BF4ExactSlabChebyshevRescale.lean:134`.
For c>2, a positive fraction of the original squared norm of S u must be lost.
Neither the equivalence nor the results below produce that fraction.

## Operational cone and signed mixed cost

- `coneSchedule`, `lean/YMGap/Continuum/BF4ExactSlabConeSchedule.lean:31`,
  computes the retained physical-link word. `runLayers_eq_coneSchedule`
  (`:62`) and `reverse_loss_eq_coneSchedule` (`:110`) prove equality of
  completed outputs and TOTAL Pythagorean losses for localized inputs.
  No summandwise identification of the different trajectories is claimed.
- `coupled_second_succ_localized`,
  `lean/YMGap/Continuum/BF4ExactSlabChebyshevAuxiliaryCone.lean:67`,
  places the auxiliary at step n+1 inside 16*n star expansions. Applying
  the forward sweep adds eight expansions. The exact reverse-loss target
  is on that computed cone word in `auxiliary_reverse_energy_iff_cone_loss`
  (`:154`). Localization is operational, not literal polynomial support.
- `mixedNumerator`,
  `lean/YMGap/Continuum/BF4ExactSlabStarMixedPolynomialCost.lean:60`,
  retains D_i*N_i(p*q)-N_i(p)*N_i(q). `exterior_mixed_pair` (`:75`)
  identifies its original-exterior integral with the actual signed form
  pairing. `cross_link_kernel_test` (`:130`) specializes p to t_j(p).
  Its first vector is J_i(r)*t_j(p): arbitrary exterior multiplication
  need not preserve the j-kernel. No sign, small angle, or coercivity is
  inferred from this identity.

## Constructed evaluator, not an assumed real inequality

1. `sweepRep`,
   `lean/YMGap/Continuum/BF4ExactSlabChebyshevRepresentative.lean:61`,
   applies the existing dense conditional representative maps. `sweepRep_pin`
   (`:69`) identifies its quotient with the actual completed sweep for any
   supplied word. `coupledRep` (`:146`) constructs the literal recurrence;
   `coupledRep_pin` (`:177`) pins BOTH components to the completed recurrence.
   All Cauchy moduli are inherited explicitly. No representative is chosen
   from an arbitrary quotient.
2. `innerRegularity`,
   `lean/YMGap/Continuum/GNSInnerRationalBracket.lean:24`, supplies Type-level
   regularity for the existing completed pairing representative. Its outer
   rate epsilon.den is valid because `cinnerRep` already uses the computed
   QMhat diagonal; it is not a claim about the raw inner-product sequence.
   `inner_bracket` (`:85`) proves both eventual-order rational bounds.
3. `margin`,
   `lean/YMGap/Continuum/BF4ExactSlabChebyshevFiniteTest.lean:64`, constructs
   a CReal representative of 2||S u||^2-c||B u||^2. `marginRegularity`
   (`:71`) computes its modulus, `marginValue` (`:79`) reads the rational
   approximation at that index, and `margin_pin` (`:83`) proves the exact
   original-object identity. `reverse_energy_of_finite_test` (`:115`)
   proves that epsilon>0 and epsilon<=marginValue imply the required
   completed reverse-energy inequality. It uses the auxiliary at step n;
   the n+1 indexing in the separate cone theorem is not silently reused.
4. `finiteCovariance_sq_bound_of_finite_test`,
   `lean/YMGap/Continuum/BF4ExactSlabChebyshevFiniteCovariance.lean:53`,
   starts with the constant Cauchy representative of the actual centered
   polynomial. It consumes the rational test and concludes

       Cov(p,q)^2 <= T_n(c-1)^(-2) Var(p) Var(q)

   under the existing 16*n separation, c>=0 and positive T_n(c-1).
   Covariance, partition reciprocal and BOTH variances are the originals.

The evaluator currently uses full schedule representatives. The checked
cone identities do not mean it has already been optimized to evaluate only
cone words. No numerical test was run and no successful instance, useful
c>2 bound, runtime bound or parameter-uniform producer is claimed. The
finite rational premise is still unsupplied. The result is soundness of
an explicit finite test, not a proof that it succeeds.

## Verification

Nine modules passed focused, serialized checks through
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check ...`:
BalancedCone (8 printed gates), ChebyshevRescale (5), StarMixedPolynomialCost
(4), ConeSchedule (7), ChebyshevAuxiliaryCone (6), GNSInnerRationalBracket
(6), ChebyshevRepresentative (6), ChebyshevFiniteTest (5), and
ChebyshevFiniteCovariance (1). These are 48 printed gates, including existing
ones in the two extended modules; all report a subset of {propext, Quot.sound}.
Failed drafting checks were repaired before the final passing checks.
Subsequent edits in the checked mixed-cost and auxiliary-cone files changed
comments only. Independent Sol reviews checked the loss/evaluator scope
and caught the exterior-kernel wording and n/n+1 distinction recorded above.

No new sorry, axiom, classical input, canonical frontier field or chart
marker changed. Root imports are recorded; no root/full-tree build, audit
or guard was run. One compiler at a time, one worker and a 20 GiB ceiling
were used. No confirmed live job was polled at short intervals.

NEXT is a useful lower estimate on this actual signed reverse loss (or a
uniform family of successful finite tests), with explicit cutoff, volume,
coupling and physical-spacing control. More existence wrappers are not
the missing input. This remains conditional-update spatial covariance,
not an OS-transfer identification. Same-theory continuum/QFT, nontrivial
survival, positive physical mass, every compact simple group and Clay remain
open. No unchanged ASCII chart is reprinted.
