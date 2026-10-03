# Original local radial cost and its remaining relative estimate

The original OWN-centered Wilson-square covariance cost now exposes its
exact heat-loss cancellation. A second-order scalar term and a first-order
term multiplying the actual weighted trace defect replace the earlier
unsplit expression. This is a proved finite estimate, not the missing
relative budget or a continuum mass-gap theorem.

## Literal weighted trace defect

The module is
`lean/YMGap/Continuum/BF4DyadicWilsonSquareFilteredGainRadialCost.lean`.
Let f be the ORIGINAL padded-square fundamental trace, c its finite center,
b=T(g_n*(f-c)), V the original spatial action and ell=H[V*].

`centeredMessageTraceGap` at line 60 defines Gap=ell[b^2*(4-f^2)].
`centeredMessageTraceGap_pin` at line 94 proves Gap=4*Q2-Q2f2, where
Q2=ell(b^2) and Q2f2=ell(b^2*f^2).
`centeredMessageTraceGap_nonnegative` at line 108 constructs Gap>=0
from the ORIGINAL cap-four certificate, multiplied by V and b^2.
It permits any rational c and retains 0<w<1,K>=headCutoff(w),side<width.
The gap is not OWN variance, nor is its smallness asserted.

## Exact second order cancellation in the actual cost

`radialSecondRate` at line 121 and `radialFirstRate` at line 124 define

    nu(x)=(1-x)^2*(1+2*x+3*x^2), h(x)=x^3*(1-x).

`radial_rates_nonnegative` at line 126 and `radial_rates_upper` at line
138 prove 0<=nu<=6*(1-x)^2 and 0<=h<=1-x for 0<=x<=1, including
both endpoints. `paddedSquare_radial_rates_bounds` at line 165 supplies
those guards for the actual x=w^(8*side).

`retained_cost_decomposition` at line 227 proves the exact identity

    (1-d)*Q2-(a^2-d)*Q2f2 = nu(x)*Q2+h(x)*Gap,
    a=w^(12*side), d=w^(32*side), x=w^(8*side).

Thus a^2=x^3 and d=x^4. The scalar coefficient is second-order in
1-x; the TOTAL cost is not asserted second-order because Gap is an
actual, as-yet-unestimated weighted moment.

`paddedSquare_own_commutatorGain_local_radial_bound` at line 258 consumes
the checked local covariance theorem at its SAME actual OWN odd mean:

    [G2-(a-1)*c*ell(A*b)]^2
      <= originalLocalSourceHeatLoss * [nu(x)*Q2+h(x)*Gap].

The original full kinetic kernel, word-only lower sweep, source V*g_n,
upper action V, transfer, center and literal mean residue all remain.
Guards include K>=headCutoff(w),K>=2 and side<width. No signed gain
alignment or interacting-variance comparison is inferred.

## Existing test norm join and the next producer

No new norm-limit wrapper is needed. `gainLimit_completed_pin`,
`lean/YMGap/Continuum/BF4WilsonAllNomeFilteredGainLimit.lean:131`,
at a=0 identifies the existing gain with the SAME completed T^2 pairing.
`dyadicUnit_gain_pin` at line 144 applies the existing unit normalizer
twice and identifies it with R(2). `normalizedFiniteGain_approx`,
`lean/YMGap/Continuum/BF4WilsonAllNomeFilteredFiniteGainLimit.lean:111`,
already supplies both approximation directions at computed cutoff/time/
representative thresholds for 0<=a<=1, at FIXED nome/width/observable.

`time_defect_nonnegative`,
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectMoments.lean:171`,
gives the nonnegative T(I-T) form on the SAME completion. Together with
`centeredVector_time_pairing`,
`lean/YMGap/Continuum/BF4WilsonAllNomeCenteredVector.lean:159`,
it yields C2<=C1 for the same centered vector. This is not a positive
response floor or changing-family convergence theorem.

The next forward estimate concerns the COMPLETE product
localSourceHeatLoss*[nu(x)*Q2+h(x)*Gap] relative to the SAME completed
lag-one response squared, or its actual signed pairing directly.
Neither factor is required here to converge or become small separately.
The quadratic coefficient is in the WORD-SCALE loss 1-w^(8*side),
which is not automatically small on growing words merely because w->1.
Replacing Gap by 4*Q2 loses the exposed cancellation. The family-wide
estimate, justified trajectory, cross-scale and physical-time joins,
full QFT and every-group continuum endpoint remain OPEN.

## Focused verification

Final second focused check passed all ten printed gates, contained in
{propext, Quot.sound}; both rate definitions are axiom-free. Independent
mathematical review checked weights, powers, center and residue. No new
sorry, axiom, classical input, weakened field or resource-limit increase.
Root import registered, NOT aggregate-checked; no full build/audit claimed.
CI and the canonical chart fence are unchanged.

The safe launcher used one worker, a 20-GiB worker cap and a 12-GiB reserve.
Fresh preflight found no competing compiler, 85% memory-pressure-free,
zero swap. Accepted log: `/tmp/ym-square-local-radial-cost-20261003-second.log`.
SHA256 source/log pair:

    9b1e07c1da5e025439148798860c633343ef22b63c056168342fa83edb6831fe
    be73bc95cb3d5d0fd552bf1ee6d6d3cb16db24b6c830b9808c0d91e978a51316

The rejected first draft and its downstream sorryAx output are not evidence.
