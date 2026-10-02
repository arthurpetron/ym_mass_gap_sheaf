# Filtered survival with any finite relative budget

The SAME original dyadic unit response now has a stronger sufficient
survival theorem. A bounded relative filtered slope, with any fixed finite
integer budget C, suffices; its total decrement need not fit inside a
small linear reserve. The useful Yang--Mills reserve and budget remain
unproved on a justified changing family. The continuum Clay target is OPEN.

## The precise proved implication

Write R(j) for the existing `dyadicUnitResponse`, retaining its constructed
unit state, completed original transfer, action and OWN normalization.
For C>=1 and m>=4*C, the two explicit hypotheses

    gamma0 <= R(1),
    m*(R(1)-R(2)) <= C*R(1)

give

    gamma0*(1/4)^(2*C) <= R(m).

`dyadicUnitResponse_filtered_block_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicFilteredGeometricSurvival.lean:154`,
proves this implication. `dyadicUnitResponse_filtered_block_ne_zero` at
line 184 excludes a zero response when gamma0>0. No CReal response or
variance is inverted. Across a changing family, the resulting floor is
uniform only when the SAME C and positive gamma0 work throughout that
family; the theorem does not construct either input.

## Mathematical argument

`response_shifted_step_lower` and `response_shifted_geometric_lower`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicFilteredGeometricSurvival.lean:78`
and `:93`, propagate a ratio bound from any supplied integer starting lag.
They use the actual positive-time second difference
`response_second_difference`,
`lean/YMGap/Continuum/BF4WilsonAllNomeResponseLower.lean:79`.
There is no fractional-time state, state replacement or spectral measure.
The existing lag-zero geometric consumer does not supply this shifted
lag-one statement.

Set rho=1-C/m. The relative budget gives rho*R(1)<=R(2), so positivity
propagates R(m)>=rho^(m-1)*R(1). The exact unit-state specialization is
`dyadicUnitResponse_shifted_geometric_lower` in the new module at line 141.

`blocked_rate_floor`,
`lean/YMGap/Continuum/RationalBlockedSurvival.lean:137`, proves the rational
estimate rho^(m-1)>=(1/4)^(2*C). Its computed block length is
b=floor((m-1)/(2*C))+1. The integer inequalities m-1<=2*C*b and
4*C*b<=3*m give a per-block loss at most 3/4. The existing constructive
`prod_floor_weierstrass`, `lean/YMGap/Continuum/ProductFloor.lean:204`,
then gives rho^b>=1/4. Raising to 2*C and using decreasing powers on
[0,1] proves the floor. All reciprocals are explicit rational inverses of
positive integer lags, not inverses of a heat floor or interacting norm.

## Revised analytic target and unchanged source boundary

The earlier `dyadicUnitResponse_filtered_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicFilteredSurvival.lean:165`,
requires (m-1)*(R1-R2)<=reserve-gamma with gamma>0. The new sufficient
criterion permits ANY fixed finite C in m*(R1-R2)<=C*R1. It removes an
unnecessary small-total-budget requirement; it does not discharge the
actual relative-budget producer.

`dyadicUnit_filtered_source_pin`,
`lean/YMGap/Continuum/BF4WilsonAllNomeFilteredIncrement.lean:102`, already
pins the literal signed radius-two source times the EXISTING normalizer
squared to 2*(R1-R2). The finite original decomposition
`filtered_loop_numerator`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredNoiseDrift.lean:217`,
is noise MINUS drift square at symmetric external depths, with its SAME
even partition. It is not a finite odd-partition variance identity.
An actual quantitative source estimate and the original regulator-limit
transport must supply the new budget; neither is proved here.

## Verification

Two final focused monitored checks exited zero: the THIRD scalar check
and SECOND same-state consumer check. All eleven public gates stay within
{propext,Quot.sound}; final logs have no warning or error. Independent
mathematical review passed. Initial checks rejected one namespace, one
integer regrouping and one dependent rational-denominator rewrite; local
repairs did not change statements or suppress linters.

| Artifact | SHA256 |
| --- | --- |
| `RationalBlockedSurvival.lean` | `3785cc42119636fdc937c749dcfcca48a6757be952dd9583b98ee9470e1ec8fe` |
| `/tmp/ym-rational-blocked-survival-20261002-third.log` | `bcdcfe3a6349a5ff7f42f5f5bc2cd804759fe02774b71c414407f15d16b7d5de` |
| `BF4WilsonAllNomeDyadicFilteredGeometricSurvival.lean` | `977a14f795d8aa22b4a207344c78d72d646b4d2e47794d6bbb386b639b8c9430` |
| `/tmp/ym-filtered-geometric-survival-20261002-second.log` | `120ed57dc77a552475c5ca036778ae89ff99d64c2daccac85ff2fc3750b4b157` |

Checks used one worker, an explicit 20-GiB ceiling and a 12-GiB OS reserve,
with fresh dynamic preflights before every launch: 85 percent pressure-free
memory and zero swap. Root imports are registered, NOT aggregate-checked.
No new sorry, axiom, classical shortcut, frontier structure, weakened field,
broad audit, progress-metric run or CI change. The canonical chart is unchanged.

The documentation skill kept the implication and its unavailable inputs
separate. Useful signed source control, spatial and spacing control,
continuum survival, physical calibration, full SAME QFT and every compact
simple group remain OPEN.
