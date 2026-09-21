# Original terminal-message relative angular estimate

Date: 2026-09-21 UTC. Status: PROVED finite original-action source estimate;
the continuum/Clay target remains OPEN.

The whole-project goal is unchanged: constructive continuum Yang--Mills on
R^4 for every compact simple group, with same-theory QFT structure, nontrivial
observables, an isolated vacuum and a finite positive physical mass gap.

## Actual conclusion

For the original terminal message `g = T^(n+1)1`, every active link rotation
`D`, every strict nome `0<w<1`, and every `K >= relativeCutoff w 32`, the
constructed positive Haar certificates give

    B(w)*g - Dg >= 0,    B(w)*g + Dg >= 0,
    H[R*(Dg)^2] <= B(w)^2 * H[R*g^2],
    B(w) = 32 * JacobiShiftedRelativeSlope.budget w + 1.

Here `R` is ANY certified positive polynomial on the same original carrier.
It may share all variables with `g`; no independence, normalization, erased
action or replacement heat kernel is assumed.

Declarations: `terminalMessageRelativeBound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalJacobiAngularBound.lean:66`;
`terminalMessageRelativeSquare`, same file at line 83;
`terminalMessageRelativeWeightedSquare`, same file at line 123.

The earlier bound used `C(w)*g +/- h(w)*Dg`. The new bound has no global
heat-floor reciprocal in its relative constant. The old theorem and cutoff
remain unchanged; this new theorem has a separately computed later cutoff.
No comparison asserting the new numerical constant is smaller at EVERY nome
is claimed.

## Causal proof and original-object pins

1. `slope_le_rate_mul_base` and `prefix_le_budget`,
   `lean/YMGap/Continuum/JacobiShiftedRelativeSlope.lean:78` and `:110`,
   bound each actual shifted affine factor's slope by its positive base
   times `rate w k`, and sum those rates with the explicit geometric budget.
   `rate` is `geoIncrBase (Cstar w) (w*w)`; `budget` is
   `geoTailBase (Cstar w) (w*w) 0` (definitions at lines 29 and 33).
2. `RelativeBound.affine`,
   `lean/YMGap/Continuum/QuaternionHaarRelativeAngularBound.lean:166`,
   constructs the affine relative derivative certificate. `mul` at line 131
   adds costs; `add` at line 108 preserves a common cost. The simultaneous
   positive Leibniz induction is `productDerivativeBounds`,
   `lean/YMGap/Continuum/JacobiHeatRelativeAngularBound.lean:71`.
3. `heatBound` and `weightedHeatBound`, same Jacobi file at lines 96 and
   107, retain the existing inverse-nome/half normalization and use
   `shiftedHeat_subst_coeffEqv_weightedPolynomial` to identify the actual
   weighted character polynomial coefficient-sensitively. This alone is
   NOT the original unweighted cutoff.
4. `finite_shifted_tail_le`,
   `lean/YMGap/Continuum/SU2HeatQuarticTailCutoff.lean:104`, supplies a
   computable quartic-tail modulus. `angularDeficitInterval`,
   `lean/YMGap/Continuum/QuaternionHaarHeatAngularDeficit.lean:142`, splits
   the literal differentiated Jacobi deficit into a finite band and that
   tail, producing a two-sided original Haar certificate of size epsilon.
5. `RelativeBound.ofApproximation`,
   `lean/YMGap/Continuum/QuaternionHaarRelativeAngularBound.lean:222`,
   absorbs value and derivative errors with budget `c*a+b`. In
   `heatPrefixRelativeBoundAt`,
   `lean/YMGap/Continuum/QuaternionHaarHeatRelativeAngularBound.lean:77`,
   both errors use `epsilon=headFloor/(relativeCost+1)`. `error_budget`
   at line 62 proves `c*epsilon+epsilon=headFloor`. The SAME unweighted
   heat prefix therefore has relative cost `relativeCost+1`.
6. `heatRelativeBound`, `integrateRelative`, and `productMapRelativeBound`,
   `lean/YMGap/Continuum/SU2QuaternionProductHeatRelativeAngularMessage.lean:48`,
   `:73`, and `:91`, keep the matching kinetic factor, every other factor,
   and the full positive input inside the original partial Haar integral.
   Exact upper-block independence removes derivatives of the other factors
   and input. The terminal consumer inserts the actual
   `spatialWeight * terminalMessage n`; its square keeps the negative
   derivative square rather than discarding it.

## Parameter and boundary audit

- The final constant is independent of width, terminal depth, active link
  and admissible cutoff. Nome dependence is explicit, not uniformly bounded
  as `w` approaches one. General heat bounds also name the scalar derivative
  cap `d`; the kinetic/terminal consumer supplies the constructed cap 32.
- `relativeCutoff w d`,
  `lean/YMGap/Continuum/QuaternionHaarHeatRelativeAngularBound.lean:46`,
  is the sum of the existing heat-positivity cutoff and explicit value and
  derivative deficit cutoffs. It depends on the nome, derivative cap and
  the original heat floor through the error tolerance, but not the carrier.
- Positive depth means exactly `n+1`. Only active output links are covered.
  The estimate is for a finite polynomial source; no completed angular
  operator or convergence of such operators is asserted.
- There is no lattice-spacing parameter or physical time calibration in
  this theorem. It is not a temporal Dirichlet-energy estimate, a variance
  floor, a nontrivial scaling limit, or a mass-gap theorem.

## Remaining mathematical join

`centered_relative_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointTemporalEnergy.lean:128`,
still requires a supplied one-step energy bound relative to the SAME
centered variance. The new source-derivative estimate does not supply that
bound. A quantitatively useful original-weight gradient/energy comparison
and justified spatial/nome/spacing observable family remain open. No new
analytic hypothesis bundle, canonical field, hole or axiom was introduced.

## Verification and delegation

The dependency-complete target
`+YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalJacobiAngularBound:olean`
passed, followed by eight serialized direct checks. All 54 printed gates
are within `{propext, Quot.sound}`; no warning, error, `sorryAx`, classical
axiom or compiler-trusting reduction occurred in the final logs. All checks
used one capped 20 GiB worker. No full-root build, full-tree audit or guard
was run. Root imports were added; CI remains off.

Build log: `/tmp/ym-gap-terminal-jacobi-angular-build.log`.
Direct logs: `/tmp/ym-gap-jacobi-final-<Module>.log`, for the eight new
modules named above. Gate counts in dependency order are 12, 6, 6, 8, 8,
8, 3 and 3.

Sol supplied the scalar slope, quartic-tail and differentiated deficit
drafts and an independent read-only mathematical/scope review (PASS).
Main supplied the relative certificate algebra, positive-product proof,
original-kernel weight-removal consumer, full-message consequences, final
elaboration fixes and all serialized checks.
