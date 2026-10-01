# Local Cayley consistency and commutation

The actual scaled Cayley maps on the ORIGINAL complex physical bond carrier
now have a checked linked-domain local error, an explicit squared ceiling,
constructed graph-preserving witnesses and parameter commutation. These are
fixed-nome, fixed-width inputs to time-product construction, not a physical-time
group, calibrated Hamiltonian or continuum mass gap.

## Exact error and quantitative consumer

Write `x=input d`, `y=output d=input e`, `z=output e` for actual original
graph points, and `J_t z=input(plusDomain_t z)`. For positive rational `t`,
the complete identity is

`C_t x - x + 2*i*t*y = -t^2*(z+C_t z) = -2*t^2*J_t z`.

The declarations in
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency.lean`
are `linked_error_cayley_sum:315`, `cayley_average_input:384` and
`cayley_linked_error:443`. Both rational scalar Cauchy witnesses are retained.
No arbitrary graph output is assumed to belong to the domain.

In `lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound.lean`,
`linked_error_norm_le_four:245` proves

`||C_t x-x+2*i*t*y||^2 <= 4*t^4*||z||^2`.

`secondCore_error_norm_le_four:299` consumes the EXISTING linked second core
and bounds this error by `4*t^4*preimageNorm Y`, where `preimageNorm:259`
is the sum of the squared norms of the two supplied ORIGINAL Cauchy preimages.
It is not the norm of the twice-time-smoothed input. The link and source ceiling
are `first_output_eq_second_input:127` and `second_output_norm_le:135` in
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSSecondCore.lean`.

The proof uses the original squared-distance triangle and Cayley unitarity:
`||z+C_t z||^2 <= 2*||z||^2+2*||C_t z||^2 = 4*||z||^2`.
No square root, spectral theorem or additional analytic premise is used.

## Constructed graph preservation and commutation

`resolvent_graph_output:81` and `resolvent_commute:103` in
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSScaledResolventCommutation.lean`
show that the actual real resolvent transports graph inputs and outputs
together, and that `R_s R_t=R_t R_s` for every positive rational pair,
including `s=t`. Only positive `s` is canceled; there is no `s-t` division.

In `lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyCommutation.lean`,
`cayley_pairResolvent_commute:175` transports the original plus/minus shift
through the componentwise real resolvent. `graphMap:240` constructs an actual
domain point using the unit resolvent, with BOTH pins
`graphMap_input:243` and `graphMap_output:274`. They imply
`cayley_commute:315`: `C_t C_s=C_s C_t` on the same carrier.

This is not the group law `C_(s+t)=C_s C_t`. It proves preservation of the
witnessed graph by Cayley maps, not that arbitrary graph outputs lie in the
domain.

## Verification boundary

All four focused monitored checks succeeded and emitted their target `.olean`s.
All 38 source-site gates report exactly `{propext, Quot.sound}`. Independent
mathematical and source/log reviews passed. The accepted logs and SHA256s are:

| Module suffix | Gates | Accepted log in `/tmp` | SHA256 |
| --- | ---: | --- | --- |
| `ScaledCayleyConsistency` | 12 | `ym-scaled-cayley-consistency-second-20261001.log` | `4e1a60b36ad462d5c7ad72bbb5f6b65ba92db0b138641a71aaa5243b2f0d4efa` |
| `ScaledCayleyErrorBound` | 13 | `ym-scaled-cayley-error-bound-first-20261001.log` | `57dcd092a32e5870f9a4a2dd5457784d600eb47864cc7b3e00a6b70da76c1da9` |
| `ScaledResolventCommutation` | 2 | `ym-scaled-resolvent-commutation-first-20261001.log` | `2755e1a1630d7b44c26ea09f4f10a2ae4b786478319b6dcb328d079337b5555c` |
| `ScaledCayleyCommutation` | 11 | `ym-scaled-cayley-commutation-second-20261001.log` | `ba57046a9df13bd56edf44a9399bdbba3c54233557ad9009c474b557a8e8cb0f` |

One serialized worker, 20-GiB ceiling and 12-GiB OS reserve were retained.
No full-tree build, audit or guard was run. No new `sorry`, axiom, analytic
field or frontier weakening was introduced.

## Remaining join

No actual Cayley time-product limit declaration is supplied by these modules.
The next construction is a dyadic-product Cauchy modulus on the represented
second core, then extension through its supplied-Rows density. Its phase must
retain the factor two above. Identification with physical time and the original
transfer logarithm remains separate and open.

Useful complete signed error/SAME-variance scaling on a justified changing
family, continuum survival, positive finite physical mass, full same-theory
QFT and every compact simple group remain open. No displayed chart claim changes.

The parallel survival/mass review found no typed same-action/carrier pin from
the legacy cylinder `DynamicVacuumSectorCompletedFamily`, at
`lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorCompletedFamily.lean:53`,
or its `DynamicVacuumSectorSameObjectRCChannel`, at
`lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorSameObjectRCChannel.lean:56`,
to the current original Wilson `ComplexBondCompletion`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSCompletion.lean:44`.
Their rate-band and continuum-join records remain legacy conditional consumers,
not current Wilson survival or physical-Hamiltonian producers. This does not
make a bridge to every legacy scaffold a prerequisite for the direct route.

## Explicit product representatives and first graph differences

The next checked increment supplies finite product representation data and a
first-order graph estimate, not the product Cauchy theorem. In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyRows.lean:128`,
`cayleyState_pin` identifies a constructed pair of original time-sector states
with the existing quotient Cayley action. The denominator's represented limit
supplies its inverse state; no quotient representative is chosen.
`iterateRows_pin`, at the same path `:185`, returns original Rows for every
finite iterate with the exact actual-operator pin. Range witnesses and moduli
are carried by the existing state constructors.

In `lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.lean:252`,
`cayley_domain_difference` proves `x-C_t x=i*t*(y+C_t y)` for an actual graph
point with input x and output y. `cayley_domain_difference_norm_le_four`, at
`:287`, proves `||x-C_t x||^2 <= 4*t^2*||y||^2`. The additive cancellation and
imaginary-scalar norm lemmas are proved on the original physical completion.
No unbounded operator is applied to an arbitrary completed vector.

The missing doubled-step theorem is distinct: linked original graph points
must control `||C_h^2 x-C_(2h) x||^2` at fourth order. It is NOT present in the
new module. Subsequent finite-power amplification, explicit dyadic Cauchy
modulus, supplied-Rows density extension and physical-time/logarithm pin
remain open.

## Literal plaquette moment input

`plaquette_cubic_zero` and `plaquette_quartic_two` in
`lean/YMGap/Continuum/SU2QuaternionPlaquetteQuarticHaar.lean:112` and `:132`
prove bare third and fourth Haar moments 0 and 2 for the same literal four-link
spatial face. The proof decomposes the fundamental powers into SU(2) characters
and integrates an actual selected face link. It does not assume the moments.

These supply inputs to an auxiliary-source Ward-sign diagnostic. The weighted
Haar moments and the source's own centered residual have not been proved here;
no sign, useful SAME-variance bound or terminal-source identification follows
from the bare moments alone.

## Requested parallel continuum review

The survival and physical-mass review located actual conditional consumers:
`marginRate_le_of_sampled_response`, at
`lean/YMGap/Continuum/BF4WilsonSurvivalPhysicalRateCeiling.lean:77`, and
`logRate_le_of_sampled_response`, at the same path `:149`. They require a norm
cap and positive sampled response. The relative-energy consumer
`dyadic_response_floor_of_relative_energy`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRelativeSurvival.lean:124`, still
requires the SAME state's energy budget. This review supplies no such
changing-family budget or cross-scale comparison map.

The QFT review found bare-multiplier commutation on an ambient carrier:
`completedMultiply_comm`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeZeroCommutation.lean:91`, and
`complexMultiply_comm`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexObservables.lean:96`.
In contrast, `act_root_pin`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSInsertion.lean:100`, pins the
physical insertion to the time-buffered sandwich `R_buffer M R_buffer`.
The ambient commutation theorem therefore does not have the physical insertion
as its operator. Existing physical word product, adjoint and source laws are
`wordAct_append`, `wordAct_adjoint` and `wordAct_ofSource`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSSeparatedWords.lean:70`, `:82`
and `:93`; their complex lifts already exist. No new physical locality claim
is made by this review.

The every-group review distinguishes `CartanType`, at
`lean/YMGap/RepTheory/CartanType.lean:58`, and
`CompactSimpleGlobalFormCode`, at
`lean/YMGap/RepTheory/CompactSimpleGlobalForm.lean:318`, from actual compact
groups. `CentralQuotientPresentation.descendRepresentation`, at
`lean/YMGap/RepTheory/ConstructiveRepresentationDescent.lean:230`, has an
algebraic consumer `descendSignRepresentation`, at
`lean/YMGap/RepTheory/RationalQuaternionSignQuotient.lean:165`.
This does not construct compact SO(3). The current heat path remains
quaternion-specific: `productHeat` and `productMap`, at
`lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:53` and `:56`.
Actual compact/global-form realization, normalized Haar, representation/heat
data and the pinned physical Wilson construction beyond SU(2) remain open.

These are source-review findings, not analytic discharges. All four continuum
requirements remain open; parallel work must retain their shared group,
action, carrier and physical-time pins.

## Verification of the new supporting results

Three focused monitored checks succeeded, with independent source/log reviews.
All 23 printed gates report exactly `{propext, Quot.sound}`. Accepted logs:

| Module suffix | Gates | Accepted log in `/tmp` | SHA256 |
| --- | ---: | --- | --- |
| `ScaledCayleyRows` | 12 | `ym-scaled-cayley-rows-second-20261001.log` | `fb733125691a03da9c649c571e77aae289f1bf92b8e7027cf0fcde54c8066529` |
| `ScaledCayleyRefinement` | 9 | `ym-scaled-cayley-refinement-partial-second-20261001.log` | `117290293a003523ce5c395e2b0013e07ea7c71bba6551a7bf812f77ccf30e65` |
| `PlaquetteQuarticHaar` | 2 | `ym-plaquette-quartic-haar-second-20261001.log` | `8d1d812d093a6d3b88a8c0c718053beefb52d91530c025c99ed3b186986526e8` |

Verification used one serialized worker, the unchanged 20-GiB ceiling and
12-GiB OS reserve. No broad build, audit or guard ran. Root imports were added
but no full-root check is claimed. CI is unchanged. The canonical chart's
displayed claims remain unchanged, so it was not reprinted.
