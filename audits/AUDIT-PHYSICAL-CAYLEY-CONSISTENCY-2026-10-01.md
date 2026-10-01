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
