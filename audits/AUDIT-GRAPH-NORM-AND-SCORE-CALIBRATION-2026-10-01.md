# Physical derivative graph limits and score envelope obstruction

Date: 2026-10-01 UTC. Two results continue the original SU(2) route after
`888c639`. The actual physical derivative graph now has a constructed
represented limit controlling both input and output with one explicit rate.
Separately, the current score-based energy coefficient cannot meet the
required smallness threshold near nome one. Neither result supplies the
missing signed scaling estimate or a continuum mass gap.

## Exact graph pairing and distance

All declarations in this section are in
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSGraphNorm.lean`.
The domain and input/output maps are those of the EXISTING
`BF4WilsonAllNomeComplexBondOSDerivative`; the carrier and Hermitian pairing
are the EXISTING `BF4WilsonAllNomeComplexBondOSCompletion`. Write u(d) for
input, v(d) for output, P(d)=u(d)+i*v(d), and I for that physical pairing.

`plus_graph_pairing` (:105) proves the full complex identity

    I(P(d),P(e)) = I(u(d),u(e)) + I(v(d),v(e)).

Both real and imaginary mixed terms cancel by the original real derivative's
`symmetric` theorem, not by a new self-adjointness assumption.
`plusDomain_graph_pairing` (:135) applies the existing constructed inverse of P;
`plus_graphQuadratic` (:143) and `plusDomain_graphQuadratic` (:147) pin its squared norm.

`distance_pairing` (:205) polarizes the ACTUAL completed squared distance.
`plus_graph_distance` (:225) then proves

    dist(P(d),P(e)) = dist(u(d),u(e)) + dist(v(d),v(e)).

Each summand is nonnegative. `input_distance_le_graph` (:267) and
`output_distance_le_graph` (:276) therefore bound each original component by the
same graph distance, with no factor-two loss or unproved square root.

`graphRows` (:287) applies the original `plusDomain` to each supplied physical Rows
witness. `graphRowsLimit` (:291) applies it to the existing constructed `limitRows`.
`graphRows_bound` (:298), `graphRows_input_bound` (:310) and `graphRows_output_bound` (:322)
preserve the SAME `limitRate`, epsilon and all-tail guard. No quotient
representative is selected; this does not assert completion for an arbitrary
unrepresented sequence of quotient classes.

This is fixed-nome, fixed-width graph convergence on the SAME physical bond
carrier. It does not construct continuous unitary time, spatial/spacing maps,
a continuum Hamiltonian, or physical mass calibration.

## Quantitative obstruction for the existing score ceiling

All declarations in this section are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialScoreCalibrationObstruction.lean`.
Put h=1-w, b=JacobiShiftedRelativeSlope.budget(w), and
C=BF4ExactSlabFixedSpatialRelativeWardBound.marginalScoreCap(w).
For 1/2<=w<1, `squared_gap_budget_ge_one` (:38) uses the FIRST geometric increment
and the exact positive-denominator cancellation to prove h^2*b>=1.

`marginalScoreCap_formula` (:63) gives C=24640*b+8. Nonnegativity gives b<=C;
since 0<=h<=1, `gap_score_square_ge_one` (:83) proves h*C^2>=1.
For every nonempty listed face family qs,
`family_energy_coefficient_ge_twentyFour` (:113) proves

    24 <= h * familyLengthAngularVarianceFactor(w,qs).

`not_family_energy_coefficient_lt_half` (:140) excludes a coefficient below 1/2,
the positive retained-fraction threshold in the existing
`BF4WilsonAllNomeSectorSourceTransfer.relative_derivative_bound`
(`lean/YMGap/Continuum/BF4WilsonAllNomeSectorSourceTransfer.lean:116`).
Width, terminal depth and cutoff do not enter this coefficient.

This lower-bounds a COMPUTED UPPER-BOUND COEFFICIENT, not the true energy or
energy/variance ratio. It does not give a Yang--Mills counterexample. Signed
corrections could improve a complete joint estimate; the theorem excludes
calibrating THIS score ceiling alone. Nonempty lists may have zero or
cancelling coefficients, without changing that precise scope.

## Consequences for the next frontier

Do not keep tuning the isolated score coefficient near w=1. The primary
producer still needed is useful JOINT control of completeCenteredError
relative to SAME interacting variance along a justified coupling, spatial
and spacing family. The checked square-completion argument remains the
relevant route; no sign or smallness of its complete error is inferred here.

The independent operator branch can use represented graph convergence
without a separate input/output limit-selection obligation. A parameterized
scaled Cayley construction and its quantitative product limit are not built
in this checkpoint. Existing first-order Taylor control does not itself
assert that every derivative-domain output has a second derivative.

Nontrivial continuum survival, physical time and positive physical mass,
full same-theory continuum OS/QFT, Yang--Mills field/UV identification,
every compact simple group and the Clay target remain OPEN. No canonical
frontier field or displayed chart claim changes; no ASCII reprint.

## Focused verification

Both accepted focused checks exited zero and emitted their target oleans.
All 5+13=18 printed gates depend exactly on {propext, Quot.sound}.
Independent Sol mathematical review and Luna source/log/hash review passed.
No sorry, new axiom, Classical dependency, native_decide, noncomputable
declaration, analytic premise or weakened frontier was introduced.

Failed drafts are not proof evidence. The repairs corrected the finite-sum
orientation, opened the defining pairing namespace and made physical
distance arguments explicit. No heartbeat, memory or worker limit was raised.
Only main compiled, using the safe-build skill and monitored launcher with
one 20 GiB worker, unchanged 12 GiB OS reserve and dynamic telemetry.
Preflight found 84 percent pressure-free memory and zero swap. User-owned
reliability-study processes were left untouched.

No full root/tree build, broad audit, guard, progress-metric script or CI
change ran. Root imports are registered only, not aggregate-checked. The
documentation skill preserves the distinction between a coefficient
obstruction, fixed-parameter graph limits and the open continuum target.

Accepted logs and SHA-256:

- `/tmp/ym-original-score-calibration-third-20261001.log`:
  `d3afb403af43fc1a1b69f018d9cfd3468086e71830728d1f451e3ecdb539fe27`.
- `/tmp/ym-complex-bond-graph-norm-second-20261001.log`:
  `020b8589092b0a205d81b332de3241af7166a853bc140ae0cc971b2327168fdc`.
