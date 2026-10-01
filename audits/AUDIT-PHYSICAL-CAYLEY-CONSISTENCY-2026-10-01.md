# Local Cayley consistency and commutation

The actual scaled Cayley maps on the ORIGINAL complex physical bond carrier
have checked linked-domain errors, explicit squared ceilings, constructed
graph-preserving witnesses and parameter commutation. The latest addendum
constructs their dyadic-product limit first on the represented second core,
then for EVERY supplied original Rows with a computed modulus. The latest
quotient-map, linearity and inverse addenda construct a complex-linear,
pairing-preserving bijective map on every original physical class, with
an actual two-sided inverse and Type-valued preimage witness.
Nome and width remain fixed; no
physical-time group, calibrated Hamiltonian or continuum gap is claimed.

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

The four local-error/commutation modules alone do not supply a product limit.
The later `ScaledCayleyDyadicLimit.productLimitCertificate` now constructs
that limit on the represented second core, as recorded below. The final
addendum extends it through supplied-Rows density. The quotient-map addendum
also proves descent and FULL pairing preservation. Complex linearity, inverse
and time laws are next. Its phase must retain the factor two above. Identification
with physical time and the original transfer logarithm remains separate and open.

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

At this earlier checkpoint, the doubled-step theorem was missing: linked
original graph points must control `||C_h^2 x-C_(2h) x||^2` at fourth order.
The first-difference module does not prove it. The latest addendum supplies
the doubled estimate, finite-power amplification and explicit core Cauchy
modulus; the final addendum extends to every supplied Rows.
Physical-time/logarithm pin remains open.

## Literal plaquette moment input

`plaquette_cubic_zero` and `plaquette_quartic_two` in
`lean/YMGap/Continuum/SU2QuaternionPlaquetteQuarticHaar.lean:112` and `:132`
prove bare third and fourth Haar moments 0 and 2 for the same literal four-link
spatial face. The proof decomposes the fundamental powers into SU(2) characters
and integrates an actual selected face link. It does not assume the moments.

These supply inputs to an auxiliary-source Ward-sign diagnostic. The bare
moments alone prove no sign or terminal-source identification. The latest
addendum supplies weighted moments and the auxiliary source's own centered
negative residual, not a useful YM SAME-variance scaling estimate.

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

## Constructed second core product limit

For actual linked domain points, `doubled_error_identity`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity.lean:275`,
expands `C_h^2 x-C_(2h) x` into three local consistency errors and one
first-graph-difference term. `doubled_error_norm_le`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledBound.lean:115`,
proves its squared norm is at most `352*h^4*||output e||^2`.
`secondCore_doubled_error_norm_le`, at the same path `:162`, consumes the
actual linked second core and bounds the same quantity by its ORIGINAL
preimage norm. There is no third-derivative assumption.

`cayley_parameter_congr`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyParameter.lean:65`,
identifies actual operators at rationally equivalent parameters.
`dyadic_iterate_comparison`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyPowerComparison.lean:248`,
uses parameter commutation and unitarity to amplify a comparison with base
counts `a,b` by `4^n` in squared norm. The dyadic consumer takes `a=2,b=1`;
equal base counts would not compare two half steps with one full step.

`productRows_pin`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicProducts.lean:114`,
pins original represented Rows to
`P_n Y=C_(t/2^n)^(2^n)(input(first Y))`.
`product_consecutive_norm_le`, at the same path `:232`, proves

`||P_(n+1) Y-P_n Y||^2 <= 22*t^4*(1/4)^n*preimageNorm Y`.

The coefficient is the proved rational equivalence
`352*4^n*(t/2^(n+1))^4 = 22*t^4*(1/4)^n`, not an opaque constant.
`geometric_tail_bound`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSGeometricRowsLimit.lean:111`,
contracts a consecutive squared-distance bound `B*(1/4)^n` into the all-tail
bound `4*B*(1/4)^n`. `cauchyOfConsecutive`, at the same path `:150`, returns
an actual Rows sequence with modulus `geometricCutoff quarter (4*B)`.

`preimageNorm_le_ceiling`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyDyadicLimit.lean:78`,
uses the two supplied ORIGINAL Cauchy streams and the SAME pairing data to
compute a nonnegative rational ceiling `C(Y)`.
`productSequence:127` consumes the proved product estimate with computed
budget `B=22*t^4*C(Y)`. `productLimitCertificate:150` returns original limit
Rows and an explicit rate, with the actual physical-distance bound proved
by `productLimit_bound:139`. No quotient representative, countable choice,
analytic convergence field or changed physical carrier is introduced.

This closes the represented second-core product Cauchy construction. The
final addendum extends to arbitrary supplied Rows using the existing core
density and finite-product isometry. No all-carrier descent, continuous unitary
group, generator/transfer logarithm or physical-time identification is yet
claimed. Nome and width stay fixed, and the original local phase retains its
factor two.

## Own centered auxiliary Ward sign

For the literal spatial plaquette character `f`, the auxiliary weight is
`U=(1+f/4)*(1+lambda*f/4)`. The declarations in
`lean/YMGap/Continuum/SU2QuaternionPlaquetteAuxiliaryWardSign.lean` are
`auxiliary_mass:154`, `auxiliary_first:175`, `auxiliary_second:199` and
`auxiliary_angular:279`. They prove actual bare-Haar pins
`Z=1+lambda/16`, `H(U*f)=(1+lambda)/4`, `H(U*f^2)=1+lambda/8` and
`H(U*Gamma(f,f))=12+lambda/2`.

`auxiliary_mass_positive:313` proves positive TOTAL mass for lambda>=0.
`auxiliaryCenter:325` centers f using U's OWN mean, and
`auxiliary_center_mean_zero:332` verifies it. `auxiliary_ward_residual_pin:349`
proves the complete residual

`12*H(U*(f-ownMean)^2)-H(U*Gamma(f,f))`
`=lambda-(3/4)*(1+lambda)^2/(1+lambda/16)`.

`auxiliary_ward_residual_le_neg_one:531` proves this is <=-1 for
lambda>=1/2. The module supplies no pointwise positivity theorem for U,
terminal heat-image pin or original Yang--Mills source identity. This is a
finite auxiliary-source sign diagnostic, NOT a Yang--Mills counterexample
or useful changing-family error/SAME-variance estimate.

## Parallel survival mass and group findings

The source reviews found no independent unconditional survival/mass producer
beyond the earlier conditional consumers. The current physical carriers fix
nome and width; separate nonzero excitations at every cutoff do not constitute
a common continuum excitation. `nonzeroExcitation`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicExcitation.lean:93`, has the
nome-dependent `starRatio` floor, not a uniform common-limit norm floor.
The absolute original-family loss is already controlled by
`completed_family_time_l1_bound`, at
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyKineticUpper.lean:259`;
it is not a relative bound on a justified changing family. The remaining
inputs are original pairing-compatible scale maps, fixed-physical-time
nonzero survival, and SAME-generator finite upper/positive lower rate
calibration. The product limit does not supply those inputs.

The group review again found no new algebraic theorem filling a physical
all-group consumer. `descendRepresentation`, at
`lean/YMGap/RepTheory/ConstructiveRepresentationDescent.lean:230`, and its
rational unit-quaternion consumer already exist. Finite Cartan/global-form/G2
codes do not construct normalized Haar, representations or heat/action data
for an actual compact group. No duplicate assumption wrapper was added.

## Product and auxiliary sign verification

Eight focused checks succeeded; independent mathematical and source/log reviews
passed. There are 51 source-site gates: two empty, one {propext} and 48
{propext,Quot.sound}. The accepted logs and SHA256s are:

| Module suffix | Gates | Accepted log in `/tmp` | SHA256 |
| --- | ---: | --- | --- |
| `ScaledCayleyDoubledIdentity` | 4 | `ym-scaled-cayley-doubled-identity-second-20261001.log` | `c7e8bc2e755d5024f75ebd04d4d721b36c3d6a1443f6bfa0bb845ec90773d596` |
| `ScaledCayleyDoubledBound` | 2 | `ym-scaled-cayley-doubled-bound-first-20261001.log` | `a8107a510a192fb4edf45ec404bfbfba3185bfac5f958997f84efe76059efba6` |
| `ScaledCayleyParameter` | 5 | `ym-scaled-cayley-parameter-first-20261001.log` | `e20d13d2382bf09577000426bd2ce5468302efe03fc692c48a6e5fdd6ce2274e` |
| `ScaledCayleyPowerComparison` | 7 | `ym-scaled-cayley-power-comparison-second-20261001.log` | `b7217ecc64db62604896098471f2b3c1252017d611906c0d85f8cbbeb4faab4f` |
| `GeometricRowsLimit` | 5 | `ym-complex-bond-geometric-rows-second-20261001.log` | `f56ba414a0cae02224a07cdcdb6cc77f46ed15b723823c1ab1bb90dbab5cc4ca` |
| `ScaledCayleyDyadicProducts` | 6 | `ym-scaled-cayley-dyadic-products-normalized-second-20261001.log` | `2abf135a3f8712889b1261cdc182f5b218822056ccd78189589c048a3dffbc52` |
| `ScaledCayleyDyadicLimit` | 11 | `ym-scaled-cayley-dyadic-limit-third-20261001.log` | `4e30ed04c3e3bc1f40901d15a49b2f9ee45e4eb71e8da7fde0ffc162ee46a4a1` |
| `PlaquetteAuxiliaryWardSign` | 11 | `ym-plaquette-auxiliary-ward-sign-second-20261001.log` | `06e65ed76f0ae40273f5c6b35b1a66465a0cddc64a64952fbac4e657b76f2a7a` |

The focused checks emitted their `.olean`s. Source scans and accepted logs
contain no sorryAx or forbidden axiom; one harmless unused-argument warning
remains in the auxiliary module. The failed draft normalization and projection
notation checks were repaired and are not accepted verification evidence.
One serialized worker, 20-GiB hard ceiling and 12-GiB OS reserve were retained.
Eight semantic-root imports were added; the root itself and full-tree
build/audit/guard were NOT run. CI is unchanged. No canonical displayed
claim changed, so no ASCII chart was reprinted. The Clay target remains OPEN.

## Extension to every supplied original Rows

The parallel Sol construction now removes the second-core restriction for
SUPPLIED original physical Rows. It does not select representatives of
arbitrary quotient classes. The declarations are in
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsLimit.lean`.
`ofRows_eq_ofState_rowState:80` pins the existing computed state to the
original Rows class. `productRows_pin:96` identifies the finite represented
product with `P_n X=C_(t/2^n)^(2^n)(ofRows X)`.
`iterate_distance:104` proves exact finite-power isometry by consuming the
proved additive-difference and norm laws, not a domain invariance assumption.

For epsilon>0, `coreSource:61` computes one source using the existing
`SecondCoreDensity.pairSources X` at index `(epsilon/16).den`.
`coreSource_near:64` proves squared distance to its actual second-core input
is at most delta=epsilon/16. `product_near_core:117` transports that estimate
to every finite product index without changing its constant. The all-tail
core product bound at tolerance delta supplies the middle comparison.
Two squared triangles give

`D(P_m X,P_n X) <= 2*delta+2*(2*delta+2*delta)`
`=10*delta <= epsilon`.

`productModulus:167` computes the SAME chosen source's core modulus at delta.
`productSequence:171` returns the actual Rows Cauchy sequence with that
all-tail modulus. `productLimitCertificate:224` returns original limit Rows
and an explicit rate; `productLimit_bound:213` proves the SAME physical
squared-distance estimate. The norm-dependent core cutoff is read from
constructed source data. It is not claimed uniform over all inputs.

The focused serialized check passed and emitted the target `.olean`:
`/tmp/ym-scaled-cayley-all-rows-limit-second-20261001.log`, SHA256
`a9d88aee4433127f8c93dd8a9dda7ccb3984ea05d13aa1b7b1c4f08930ceac6b`.
All 16 source-site gates passed: two empty, fourteen {propext,Quot.sound}.
Independent mathematical and source/log review passed. The rejected first
draft's rational-equivalence notation and sequence-projection rewrites were
repaired without changing the mathematics or raising limits. No new sorry,
axiom, analytic field, witness erasure or canonical frontier change.
One root import was added, but no full-root/tree/build/audit/guard ran.

At this Rows-only checkpoint, NEXT was a physical quotient operator with
pairing/isometry laws. The following addendum supplies that map and its
full pairing, distance and injectivity laws. Complex linearity, inverse,
group/continuity and actual transfer/physical-time calibration remain open.
None follows from the Rows limit alone. PRIMARY useful complete
signed scaling, a justified changing-scale surviving excitation, finite
positive physical mass, full continuum QFT, all actual compact groups and
Clay remain OPEN. No displayed chart claim changed and no ASCII reprint.

## Physical quotient limit and full pairing

The constructed product limit now acts on EVERY original complex physical
bond class. In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyLimitMap.lean`,
`rows_limit_unique:45` transports the SAME physical distance and supplied
Type-level rate through `sectorSequence` and the existing
`ComplexTimeSector.limit_unique`. `productLimit_unique:61` identifies a
limit of the ACTUAL finite products. Equal input classes give equal finite
products, so `productLimit_congr:74` identifies their output classes.
`limitMap:88` applies Quotient.lift2 to the two EXISTING real row setoids,
with that proved independence. No representative is selected.

`limitMap_ofRows:94` pins the quotient map to the original constructed Rows
limit. `limitMap_bound:100` retains its computed approximation rate whenever
Rows are supplied. `limitMap_parameter_congr:110` identifies equivalent
rational presentations; it does not assert a parameter-addition law.

The FULL Hermitian form is retained by the declarations in
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyLimitPairing.lean`.
`finite_product_pairing:252` iterates the actual Cayley pairing law at the
same step and power for both inputs. `sum_pairing_limits_eq:76` transports a
TWO-TERM pairing equality through original represented limits. Four original
`RowPairingLimit.row_pairing_bound` estimates use epsilon/4, and a common
maximum of their COMPUTED moduli pays exactly epsilon. No new uniform source
cap or analytic field is assumed.

`productLimit_pairing:275` consumes those estimates for the full real SUM and
the imaginary cross-term DIFFERENCE. The latter is transported by the exact
equivalence `a-b=c-d` iff `a+d=c+b`. Individual real component pairings of
the finite Cayley maps are NOT asserted invariant.
`limitMap_pairing_preserved:332` descends this full identity to EVERY physical
quotient class. The public original `GraphNorm.distance_pairing` then gives
`limitMap_distance:354`. `limitMap_injective:366` tests original pairings
against mapped test states; it requires no onto assumption.

The two focused monitored checks succeeded and emitted their `.olean`s;
independent mathematical and source/log reviews passed. All 13 source-site
gates report {propext,Quot.sound}:

| Module suffix | Gates | Accepted log in `/tmp` | SHA256 |
| --- | ---: | --- | --- |
| `ScaledCayleyLimitMap` | 7 | `ym-scaled-cayley-limit-map-first-20261001.log` | `28ad1a3933c7fa7d6953ac035d51442ff811e9655b052582e1f369936b196976` |
| `ScaledCayleyLimitPairing` | 6 | `ym-scaled-cayley-limit-pairing-first-20261001.log` | `10d61ce82a247cafb61b3a310f69256d28c2a3b3f4bacf4c3f11efd265998495` |

Targeted source scans and accepted logs contain no sorryAx or forbidden
construct. One serialized 20-GiB worker and 12-GiB OS reserve were retained;
capacity analysis found no competing build or swap. Two root imports were
added, but no full-root/tree/build/audit/guard ran. CI is unchanged.

At the quotient-map checkpoint, NEXT was complex linearity from full pairing
and positive definiteness; the next addendum proves it. An actual inverse
and group/continuity laws remain open. A pairing-preserving injective
map is not yet declared unitary. The original derivative/transfer relation
is written in `time_stateQuotient:51` and
`derivative_equation_of_quotient_limit:61`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeEquation.lean`, and
`graph_time_pin:97`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraph.lean`.
These are original-transfer/graph identities, not physical spacing
calibration or a declared equality A=-log(T). No new such identification
is supplied here. Nome and width stay fixed. Useful complete signed scaling,
continuum survival, finite positive physical mass, full continuum QFT,
every actual compact group and Clay remain OPEN. No canonical displayed
claim changed, so no ASCII chart was reprinted.

## Complex linearity on the original physical carrier

The actual quotient limit is now complex-linear. In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyLimitLinear.lean`,
`limitMap_add:155` and `limitMap_smul:163` consume the checked full Hermitian
identity and the ORIGINAL physical positive-definiteness law. The proof
compares the mapped sum/scalar multiple with the sum/scalar multiple of the
mapped inputs. Their norm and cross-pairing identities make their physical
squared distance zero. It requires neither surjectivity nor a new
scalar-continuity estimate; both supplied scalar QCauchy witnesses remain.

The first focused monitored check passed and emitted the target `.olean`.
Accepted log: `/tmp/ym-scaled-cayley-limit-linear-first-20261001.log`, SHA256
`4f3415757a7951f2e3878f348a3b57425d48387dd663b0fed72f856a48846f7e`.
Both source-site gates report {propext,Quot.sound}; independent mathematical
and source/log/hash reviews passed. Targeted source scans found no forbidden
construct. One serialized 20-GiB worker and 12-GiB OS reserve were retained;
no competing compiler or swap was found. One semantic-root import was added,
but no full-root/tree/build/audit/guard ran. CI is unchanged.

At this linearity checkpoint, NEXT was an actual inverse of this SAME map;
the constructive-inverse addendum below supplies it. Group/continuity laws
remain open. Physical-time/logarithm identification and the
changing-scale continuum construction are still separate OPEN obligations.
This proof fixes nome and width. Complete signed scaling, continuum survival,
finite positive physical mass, full continuum QFT, every actual compact group
and Clay remain OPEN. No displayed chart claim changed and no ASCII reprint.

## Parallel endpoint input review

These are read-only source findings, not additional proof closures.

Continuum survival already has a small-nome spatial comparison:
`chartScalar_spatial_bound`, at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSpatialComparison.lean:186`,
compares the actual normalized recentered finite actions with their partitions.
`spatialCauchy:62` and `spatialCauchy_modulus:70`, at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSpatialLimit.lean`,
provide computed spatial Cauchy data. Their small-nome, remainder and entropy
guards are essential. In particular, `heatRemainderBound_eq`, at
`lean/YMGap/Continuum/QuaternionHaarCharacterInterval.lean:85`, gives 128*w^3,
so the remainder guard excludes w tending to one. The review found no
corresponding all-nome original centered cross-width comparison. A syntactic
width/time identity is already proved by `denseTime_naturality`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeDenseTimeNaturalTransformation.lean:82`;
its module explicitly supplies no map between different completed carriers.
The existing small-nome result must not be duplicated or advertised as a
changing-spacing survival theorem.

Physical mass has fixed-parameter ingredients: `twoStepRate:45` and
`twoStepRate_lt_one:53`, at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDenseCenteredGap.lean`, and
`coreMargin:52`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean`.
The latter module explicitly excludes scalar-log, generator and physical
mass identification. The original range derivative and its transfer graph
pin are documented above; the Cayley limit does not introduce lattice
spacing or identify a physical Hamiltonian. A justified changing family,
spacing-matched calibration and a surviving nonzero response remain missing.

Every-group algebraic inputs are separate from actual gauge realization.
`ConstructiveGroup`, at `lean/YMGap/RepTheory/ConstructiveGroup.lean:51`,
is a setoid group, and `CompactSimpleGlobalFormCode`, at
`lean/YMGap/RepTheory/CompactSimpleGlobalForm.lean:318`, is finite code data.
`group`, at `lean/YMGap/RepTheory/RationalQuaternionUnitNormGroup.lean:419`,
constructs rational unit quaternions; its header explicitly excludes compact
completion and all of SU(2). The review found no typed construction from
general Cartan/global-form codes into the current SU(2)-specific original
Haar/heat/Wilson carrier. No extra code-level wrapper was added. Actual
compact-group realization with compatible Haar, representations and heat
action, followed by the analytic/scaling construction, remains OPEN.

## Constructive inverse on the original physical carrier

The actual limit map now has a constructive two-sided inverse. In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyConjugation.lean`,
`conjugate:56` negates only the imaginary ORIGINAL bond component.
`conjugate_involutive:69` and `conjugate_distance:75` retain the original
physical quotient and squared distance. `conjugateRows:95` constructs the
negated supplied sector Rows; `conjugateRows_pin:100` keeps its large range
witness opaque. No arbitrary quotient representative is selected.

`conjugateDomain:170`, `conjugateDomain_input:172` and
`conjugateDomain_output:178` use the actual BondOSAdjoint construction to
supply the conjugate graph point, not an ambient replacement domain.
`conjugate_cayley_conjugate:220` proves K*C_t*K=the actual finite inverse
at the SAME positive rational parameter.

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyLimitInverse.lean`,
`iterate_conjugate_inverse_right:61` gives P_n*(K*P_n*K)=identity.
`inverseRows_product_distance:87` identifies

`D(P_n(inverseRows X),ofRows X)`
`=D(P_n(conjugateRows X),F(ofRows(conjugateRows X)))`.

This is an EXACT equality from finite-product and conjugation isometry,
not a new analytic estimate. `inverseMap:73` is K*F*K;
`inverseRows:76` and `inverseRows_pin:80` retain constructed original Rows.
`limitMap_inverse_right:122` applies the original product-limit uniqueness
with the UNCHANGED computed forward rate for conjugateRows.
`limitMap_inverse_left:137` uses already proved injectivity.
`preimage:143` returns a Type-valued witnessing preimage on EVERY class.
With the prior linearity and full-pairing laws, F is a complex-linear
bijective isometry at fixed nome and width.

Both focused monitored checks passed and emitted their `.olean`s;
independent mathematical and source/log/hash reviews passed. All seventeen
source-site gates report {propext,Quot.sound}:

| Module suffix | Gates | Accepted log in `/tmp` | SHA256 |
| --- | ---: | --- | --- |
| `ScaledCayleyConjugation` | 9 | `ym-scaled-cayley-conjugation-third-20261001.log` | `afeef9731d89096ebf348ae68a91c62b761058e50befdc24903c3fb16823153d` |
| `ScaledCayleyLimitInverse` | 8 | `ym-scaled-cayley-limit-inverse-second-20261001.log` | `adea3e6f6680d4607a7cef7050e325929df2bfb129b8110241da2590fc08a184` |

Rejected elaboration logs are not verification evidence. Their opaque-range,
namespace and local-parameter seams were repaired without changing estimates
or increasing limits. Accepted sources/logs contain no sorryAx or forbidden
construct. One serialized 20-GiB worker and 12-GiB OS reserve remained in
force. Two root imports were added, but no full-root/tree/build/audit/guard
ran. CI is unchanged. No canonical displayed claim changed and no ASCII reprint.

At this inverse checkpoint, NEXT was rational composition and continuity.
The next addendum proves exact doubling and finite-product continuity only.
No full rational composition, limit-continuity moduli, physical-time/
logarithm calibration, changing-family continuum survival, finite positive
physical mass, full continuum QFT or every-group realization is asserted.
The primary complete signed scaling estimate and Clay target remain OPEN.

## Exact doubling and finite product continuity

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyLimitComposition.lean`,
`doubled_step_eqv:61` aligns step(2t,n+1) with step(t,n) by rational
equivalence. `product_double_succ:72` combines actual parameter congruence
and `PowerComparison.iterate_add_index` to prove P_(n+1)(2t)=P_n(t)^2.
`doubleRate:86` computes max(rate_X(e/4),rate_limitRowsX(e/4))+1.
`product_double_limit_bound:91` applies finite-product isometry and one
squared triangle; four quarter-error copies pay e. Original limit uniqueness
gives `limitMap_double_ofRows:134` and quotient induction gives
`limitMap_double:155` on EVERY original class. No shifted sequence or
scalar spectral calculus is assumed. This is the doubling case only.

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyProductContinuity.lean`,
`displacementCoefficient_pin:46` proves 4^n*4*step(t,n)^2=4*t^2 modulo
rational equivalence. `product_domain_distance_le_four:86` applies the
actual dyadic power comparison with counts 1 and 0, then the ORIGINAL
graph one-step bound and squared-distance symmetry. Its ceiling is
4*t^2*||output d||^2 for every finite depth and actual graph point d;
there is no third derivative, universal source-norm cap or limit assertion.

The focused monitored checks emitted `.olean`s, and independent source/math/
log/hash reviews passed. All ten source-site gates stay inside the permitted
gate: one empty, one {propext}, eight {propext,Quot.sound}.

| Module suffix | Gates | Accepted log in `/tmp` | SHA256 |
| --- | ---: | --- | --- |
| `ScaledCayleyLimitComposition` | 7 | `ym-scaled-cayley-limit-composition-third-20261001.log` | `1818c2b2c90767d41d7f34ebd23a9e4fd547bb4b9af40755bc35551d0fcd6024` |
| `ScaledCayleyProductContinuity` | 3 | `ym-scaled-cayley-product-continuity-second-20261001.log` | `1a7013c926407865e3183f9d14aa3b75e0250659babd506f4e82c01614077076` |

One rejected doubling draft compiled but reported Classical.choice; replacing
the automated index reasoning by explicit Nat.max/succ order lemmas removed
that dependency. Earlier rejected logs are not accepted evidence. Accepted
sources/logs contain no sorryAx or forbidden construct. One serialized
20-GiB worker and 12-GiB OS reserve were retained. Two root imports were
added; no full-root/tree/build/audit/guard ran, and CI is unchanged.

NEXT: the full rational addition law requires mixed local defect control and
composite-power comparison; t-to-zero limit continuity requires the finite
ceiling, constructed original source caps and existing density. Parallel
drafts are not yet verified. These laws are distinct from physical-time/
logarithm calibration and the changing-family continuum construction.
Signed scaling, survival, physical mass, full continuum QFT, every group and
Clay remain OPEN. No canonical displayed claim changed and no ASCII reprint.

## Computed rational zero-parameter continuity and mixed defects

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyLimitContinuity.lean`,
`first_output_norm_le_preimage:64` combines ORIGINAL time and derivative
contraction; `first_output_norm_le_ceiling:81` retains the computed source
ceiling. For supplied original Rows X and positive tolerance e,
`radius:140` uses the existing rational linear tolerance with budget
4*outputCeiling(X,e)+e/256+1. Its positive radius is thus equivalent to
(e/256)/(4*outputCeiling(X,e)+e/256+2). This is source/nome/width/tolerance
dependent, not a uniform cap over those parameters.

`finite_product_near_identity:242` uses the existing second-core source
approximation and finite isometry; three original squared-distance bridges
cost 10*(e/256). `limitMap_near_identity_ofRows:296` selects the ACTUAL
product-limit rate at e/256; one further squared triangle costs 22*(e/256)
<=e. `continuityCertificate:326` returns the positive rational radius as
Type-level data and its all-positive-rational-t bound. No representative is
selected. This is rational zero-parameter continuity of the original
fixed-carrier limit, not full-real or physically calibrated time.

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyMixedIdentity.lean`,
`mixed_error_identity:239` expresses C_b*C_a-C_(a+b) on an actual graph input
as three ORIGINAL local errors and the positive correction
2*i*b*(output d-C_a(output d)). The identity needs d only. In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyMixedBound.lean`,
`mixedCoefficient:106` retains the nested squared-triangle coefficient,
equal modulo rational equivalence to
32*b^4+32*a^4+16*(a+b)^4+32*a^2*b^2.
`mixed_error_norm_le:127` requires actual linked d,e with output d=input e
and bounds the squared defect against ||output e||^2. No third derivative or
parameter-addition law is assumed.

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyCompositePowerComparison.lean`,
`compositeIterate:37` is the actual pair of original Cayley powers.
`dyadic_composite_comparison:90` uses their proved commutation and isometry
to amplify a one-step squared defect by 4^n at exponent 2^n. It applies to
actual operators, not a substitute composite. Dyadic coefficient cancellation
and the limit-addition consumer remain to be proved.

All four focused monitored checks emitted their `.olean`s; independent
source/math/log/hash review passed. Sixteen source-site gates report one
empty and fifteen {propext,Quot.sound} profiles:

| Module suffix | Gates | Accepted log in `/tmp` | SHA256 |
| --- | ---: | --- | --- |
| `ScaledCayleyMixedIdentity` | 2 | `ym-scaled-cayley-mixed-identity-second-20261001.log` | `d22fcdd84dafce0b1dfaae29b458c7ff129fdfea7fb8dee47bae4d948751cbe8` |
| `ScaledCayleyMixedBound` | 2 | `ym-scaled-cayley-mixed-bound-first-20261001.log` | `9fa7a68b2e9169d6773e6a8e6ecdc238191b36f420293e6355aa9d4480959bb5` |
| `ScaledCayleyCompositePowerComparison` | 5 | `ym-scaled-cayley-composite-power-first-20261001.log` | `e662a8d20526dce6785fed02f0ad2e9e2e813dbedc342c11d1db4259f793fb02` |
| `ScaledCayleyLimitContinuity` | 7 | `ym-scaled-cayley-limit-continuity-third-20261001.log` | `714d72cda005539f15a9f6ffd8bde1d94a19ccb9a5e417d983f2a6866927082e` |

Rejected continuity drafts had elaboration seams, not accepted axiom evidence;
the explicit rational-coefficient `change` repair preserves the proof budget.
Accepted sources/logs contain no sorryAx or forbidden construct. One
serialized 20-GiB worker and 12-GiB OS reserve were retained; preflight found
no competing compiler and zero swap. Four root imports were added, but no
full-root/tree/build/audit/guard ran. CI is unchanged.

The user-requested endpoint parallel review found that fixed-parameter
positive-time/vacuum laws already exist and do not fill the missing canonical
continuum realization pins. No new QFT closure was reported. General Cartan
codes and central representation descent likewise have no supplied physical
Haar/heat/Wilson join. Further proof work is assigned to the actual mixed
dyadic-product estimate and the factor-two infinitesimal action; both are
unverified at this checkpoint. Complete signed scaling, changing-family
survival, SAME-transfer physical-time/logarithm calibration, finite positive
physical mass, full continuum QFT, every actual group and Clay remain OPEN.
No canonical displayed claim changed; no ASCII chart was reprinted.

## Quarter-geometric mixed finite products

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyMixedProducts.lean`,
`step_add_eqv:52` aligns the actual halved parameter sum.
`mixedCoefficient_scale_eqv:82` proves exact quartic homogeneity;
`dyadic_fourth_factor_eqv:93` uses 4*(1/2)^4=1/4, and
`dyadic_mixed_coefficient_eqv:127` combines both identities.
`mixed_products_bound:185` applies the actual mixed defect and commuting
finite-power comparison to the ORIGINAL represented first/second graph
points. Its squared error is <= quarter^n*mixedCoefficient(a,b)*preimageNorm Y.
The second-output ceiling is scaled only after explicit nonnegativity.

The second focused monitored check emitted its `.olean`; independent
source/math/log/hash review passed. All five gates report
{propext,Quot.sound}. Accepted log:
`/tmp/ym-scaled-cayley-mixed-products-second-20261001.log`, SHA256
`c66605b496ca5f2bee3390ed55343bf3de80ccefa1e5587b9c113e54ffe38a3c`.
The rejected draft used unsupported notation-qualified `PD.Cauchy`; writing
the actual Cauchy type repairs elaboration without changing the proposition.
Accepted source/log contains no sorryAx or forbidden construct. One
serialized 20-GiB worker and 12-GiB OS reserve were retained, with zero swap
and no competing compiler at preflight. One root import was added; no
full-root/tree/build/audit/guard ran and CI is unchanged.

This is a finite same-carrier estimate, not the limiting addition law.
Passing it through actual limits is the next mathematical consumer.
The factor-two tangent draft is separate and unverified. Physical calibration,
changing-family survival/mass, full continuum QFT, every actual group and Clay
remain OPEN. No displayed chart claim changed; no ASCII reprint.

## Positive rational limit addition and second-core tangent

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyAllRowsMixedComparison.lean`,
`mixedBudget:88` multiplies the exact mixed coefficient by the ceiling of
the ONE computed original source at requested precision. `mixedRate:101`
returns its quarter-geometric cutoff at e/16. `mixed_allRows_bound:146`
uses actual composite isometry, the checked core estimate and the same-core
endpoint comparison; three squared-distance bridges cost10e/16<=e.

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyLimitAddition.lean`,
`additionRate:96` is max(mixedRate, max(rate_X(a),rate_limitRows_X_a(b)))
at tolerance e/16. `product_addition_limit_bound:105` uses those three
all-larger-index estimates to bound the ACTUAL parameter-(a+b) products
against F_b(F_a x). `limitMap_add_parameter_ofRows:145` identifies their
original limit by `productLimit_unique`; `limitMap_add_parameter:167`
descends by quotient induction to EVERY original physical class.
`limitMap_commute:176` uses rational parameter congruence. These are arbitrary
positive rational parameters, not just the prior doubling case.

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyInfinitesimal.lean`,
`orbit_consecutive:122` pays22*t^4*quarter^n against the actual linked second
output norm. `orbit_tail:196` retains that CReal-valued norm, with coefficient
88*t^4 at index0. `finite_product_tangent:275` combines the tail with the
4*t^4 one-step graph error to pay184*t^4. Its phase is EXACTLY -2i, not -i.

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyLimitInfinitesimal.lean`,
`coreRows:65`, `coreRows_input:70` and `coreRows_product:85` construct and pin
ORIGINAL Rows from the supplied firstPoint, without representative selection.
`limitMap_secondCore_tangent:153` chooses the ACTUAL product-limit rate at
epsilon/2; the squared triangle and `le_of_all_errors` remove epsilon and give

`||F_t(input d)-input d+i*t*(output d+output d)||^2`
`<=368*t^4*||output e||^2`,

for original d=first Y and e=second Y. No third graph point, rational surrogate
norm cap, norm-limit axiom or physical-time premise is introduced.

All four focused checks emitted `.olean`s; independent source/math/log/hash
reviews passed. All seventeen source-site gates report {propext,Quot.sound}:

| Module suffix | Gates | Accepted log in `/tmp` | SHA256 |
| --- | ---: | --- | --- |
| `ScaledCayleyAllRowsMixedComparison` | 4 | `ym-scaled-cayley-all-rows-mixed-first-20261001.log` | `7766245806914d4bafcaf6866ea2022bb35203c8f8904e28a8de32a924a0fa3e` |
| `ScaledCayleyLimitAddition` | 5 | `ym-scaled-cayley-limit-addition-first-20261001.log` | `1c72e2da83a37f92550789f4dfbd5f0bba12ff832cc02ce5fcf389be93f8eb64` |
| `ScaledCayleyInfinitesimal` | 4 | `ym-scaled-cayley-infinitesimal-third-20261001.log` | `13aa15642288f62cf959e6af54f805c3cbacf361db2357ea6655d1975e0cb506` |
| `ScaledCayleyLimitInfinitesimal` | 4 | `ym-scaled-cayley-limit-infinitesimal-second-20261001.log` | `0e989363176acc16dcf446f808ee5e7b040fd1cd8e01acec82aadd8d88ba1ef1` |

Rejected tangent drafts had private-zero, normalization and distance-orientation
seams; direct existing algebra and explicit symmetry repair them without a
changed bound. Nat index equalities use explicit algebra, not automated
classical-dependent reasoning. Accepted sources/logs contain no sorryAx or
forbidden construct. One serialized20-GiB worker and12-GiB OS reserve were
retained; refreshed preflight found zero swap and no competing compiler.
Four root imports were added; no full-root/tree/build/audit/guard ran. CI is
unchanged. No canonical displayed claim changed; no ASCII reprint.

The parallel calibration review distinguishes the missing join from already
available SAME-transfer evidence. `positiveAction_original:118`, at
`lean/YMGap/Continuum/BF4WilsonAllNomePositiveTimePins.lean`, identifies its
positive integer samples with ORIGINAL `completedTime n`. `differenceQuotient:60`
and `derivativeAction:274`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicDerivative.lean`, define the root-defect
derivative, not T^-1-I. `core:86` and `graph_time_pin:97`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraph.lean`, retain the original
core and exact transfer relation. The witnessed negative Taylor derivative is
`real_taylor_bound:126`, at
`lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraphReal.lean`.
No scalar logarithm identity follows from the graph relation. The actual
Euclidean action/maximal physical graph join is under review; lattice-spacing
and changing-family calibration are still separate OPEN obligations.
Complete signed scaling, continuum survival, finite positive physical mass,
full continuum QFT, every actual group and Clay remain OPEN.

## Original Euclidean time preserves the physical derivative graph

This checkpoint proves graph transport and finite commutation on the ORIGINAL
fixed-nome, fixed-width carrier, not physical-time calibration or continuum QFT.

In `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativePositiveTimeCommutation.lean`,
`positiveAction_root_commutes:65` uses the actual real semigroup and original
dyadic pins. `positiveAction_differenceQuotient:90` transports the actual finite
derivative quotient. `derivativeAction_positiveAction_commutes:128` compares
the TWO represented derivative limits at the maximum of their own computed
rates, using original positive-action contraction and the squared triangle.

In `lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSDerivativeTime.lean`,
`timePoint:58` retains both original range witnesses; its graph equation follows
from that proved commutation. `realTimeDomain:68` descends by Quotient.lift,
without representative selection. `realTimeDomain_input:72` and
`realTimeDomain_output:83` keep the original real time pins. `timeDomain:95`,
`timeDomain_input:98` and `timeDomain_output:104` transport EVERY complex physical
domain class. `timeAction_adjoint_pair:112` uses the already constructed actual
domain witness for every intrinsic adjoint pair, not a smaller represented core.

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyEuclideanCommutation.lean`,
`action_add:92` and `action_smul:100` retain actual complex linearity and both
supplied scalar moduli. `plus_timeDomain:116` and `minus_timeDomain:128` prove
exact transported imaginary shifts. `cayley_action_commute:141` identifies
the transported plus inverse through its actual left/right inverse pins,
then transports minus. `iterate_action_commute:160` extends it to EVERY finite
power on EVERY physical class. No assumed invariance or commutation is added.

All three focused checks emitted `.olean`s. All seventeen source-site gates
report {propext,Quot.sound}; independent source/math/log/hash reviews passed:

| Module suffix | Gates | Accepted log in `/tmp` | SHA256 |
| --- | ---: | --- | --- |
| `DerivativePositiveTimeCommutation` | 3 | `ym-derivative-positive-time-commutation-first-20261001.log` | `19f954c3a41ba726a84ba113c241b70562d58694c2a3afd59cea2c05681686da` |
| `ComplexBondOSDerivativeTime` | 8 | `ym-physical-derivative-time-second-20261001.log` | `50f6cb7342952480eb94b929c117c1629d33d996716fe6134116a3346a63916b` |
| `ScaledCayleyEuclideanCommutation` | 6 | `ym-cayley-euclidean-commutation-first-20261001.log` | `10c940f1d160cf80e6c21d7f1efdf6086a69cd81001593c2a476136d415ab09e` |

The rejected graph-transport draft used unavailable core Quotient.map and a
local notation collision; Quotient.lift and an unambiguous local name repair
those seams without changing the proposition. Accepted sources/logs contain
no sorryAx or forbidden construct. Verification retained one serialized
20-GiB worker and a 12-GiB OS reserve; current preflight found zero swap and no
competing Lean/Lake/pytest/runner executable. Three root imports were added;
full root/tree/build/audit/guard NOT run. CI and safety limits unchanged.
No canonical displayed claim changed; no ASCII reprint.

NEXT: original Euclidean contraction and the computed product-limit rates
must pass the finite identity to the ACTUAL limit. This is an available
fixed-carrier join, not an inhabitant of the continuum QFT root. Generator
identification, physical spacing/scaling, useful complete signed scaling,
survival, finite positive physical mass, full QFT, every group and Clay remain
OPEN.

## Original Euclidean action commutes with the actual Cayley limit

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyEuclideanLimit.lean`,
`actionRows:49` constructs the actual time-acted original sector Rows, retaining
BOTH range witnesses. `actionRows_pin:53` pins their quotient class to the
original positive-time action. `product_action_limit_bound:70` uses the finite
iterate identity and original Euclidean distance contraction to transport the
ACTUAL product bound. It uses the unchanged `productLimitRate X t ht`: no
second rate, assumed continuity or new analytic field is needed.

`limitMap_action_commute_ofRows:91` invokes the actual completion's
`productLimit_unique` with those constructed Rows and that computed rate.
`limitMap_action_commute:118` extends the Prop-valued equality by quotient
induction to EVERY original complex physical class. It constructs no quotient
representative-selection function. The proved statement is

`F_t(S_s x) = S_s(F_t x)`

for positive rational t and supplied original positive Euclidean time s, at
fixed nome and width. It is NOT a generator identity, physical-time
calibration, real-parameter Cayley extension or continuum QFT construction.

The first focused check emitted an `.olean`. All five printed gates report
{propext,Quot.sound}; independent source/math/log/hash review passed. Accepted
log: `/tmp/ym-cayley-euclidean-limit-first-20261001.log`, SHA256
`2031a25e5e1f6cbdeabe91cc104a4ba94b2ce0f4f2472e92c117fb69ecb17493`.
No sorryAx, forbidden construct, new premise or frontier change. One serialized
20-GiB worker and 12-GiB OS reserve were retained. One root import added;
full root/tree/build/audit/guard NOT run. CI unchanged. No displayed chart
claim changed; no ASCII reprint.

## Parallel endpoint assignments and results

User requested independent work on survival, physical calibration, QFT and
every compact simple group. Three agents handled survival, QFT and groups;
the parent handled calibration and all serialized compiler checks. The QFT
agent supplied the finite/limit commutation proofs above. The other findings
below are bounded source reviews, not additional mathematical closures.

- **Survival.** Original `denseToUnion:91` and
  `completedTime_denseToUnion:134`, at
  `lean/YMGap/Continuum/BF4WilsonSpatialUnionNaturalTransformation.lean`,
  retain fixed-nome width inclusion. `normalizedCertificate:165`, at
  `lean/YMGap/Continuum/BF4WilsonSpatialUnionNormalizedExcitation.lean`,
  supplies an actual fixed-nome unit excitation. `nonzeroExcitation:93`, at
  `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicExcitation.lean`, supplies per-nome
  states, while `dyadic_response_floor_of_relative_energy:124`, at
  `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRelativeSurvival.lean`, requires
  the SAME-state relative-energy estimate. These do not supply changing-nome
  pairing-compatible maps or a uniform surviving response.
- **Calibration.** `logRate_le_of_sampled_response:161`, at
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointSurvivalCalibration.lean`,
  consumes a positive sampled response and norm ceiling on the SAME carrier;
  it does not construct those changing-family inputs or a Hamiltonian pin.
  `fixedCarrierDynamicFamily:62` and
  `noPhysicalRateBand_of_fixedCarrier:125`, at
  `lean/YMGap/Continuum/BF4WilsonFixedCarrierDynamicFamily.lean`, exhibit and
  refute a finite physical-rate band on the constant-nome shrinking-spacing
  route. `currentRateFloor_cofinal:204` and
  `fixedMass_no_finite_physical_ceiling:240`, at
  `lean/YMGap/Continuum/BF4WilsonSpatialUnionPhysicalCalibration.lean`,
  record the fixed-rate obstruction. A changing calibrated family is still
  missing; adding spacing labels to the fixed carrier does not supply it.
- **QFT.** The new actual limit commutation supplies an independent
  fixed-carrier time/operator join. `PositiveTimeOSRoot:268`, at
  `lean/YMGap/Continuum/CanonicalOSRoot.lean`, still requires the canonical
  limiting algebra, geometric positive support and reflected-form pins.
  `act_root_pin:100`, at
  `lean/YMGap/Continuum/BF4WilsonAllNomeBondOSInsertion.lean`, describes the
  physical buffered insertion as R_half M R_half.
  `completedMultiply_comm:160`, at
  `lean/YMGap/Continuum/BF4WilsonSpatialUnionTimeZeroCommutation.lean`,
  proves ambient multiplier commutation, not translated buffered locality.
  No such locality/root identification was constructed in this assignment.
- **Every group.** `CompactSimpleGlobalFormCode:318`, at
  `lean/YMGap/RepTheory/CompactSimpleGlobalForm.lean`, carries Cartan validity
  and finite center-subgroup code, not compact topology, Haar or heat action;
  the module's boundary at lines29--37 states those exclusions.
  `group:419`, at
  `lean/YMGap/RepTheory/RationalQuaternionUnitNormGroup.lean`, constructs an
  algebraic rational unit-quaternion group, not its compact completion.
  The review found no compatible general-group realization to plug into the
  current physical construction. No extra classification wrapper was added.

The unchanged continuum/Clay target remains OPEN. The available next operator
proposition is constructive-real parameter extension of the actual rational
limit with source moduli; physical generator identification, spacing/scaling,
useful signed-energy control, survival and all-group realization are separate
obligations, not consequences of the commutation identity.

## Constructed positive-real Cayley parameter

This extends the ACTUAL rational Cayley limit on the SAME physical bond
carrier, at fixed nome and width. No continuum or physical clock is identified.

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyParameterContinuity.lean`,
`parameter_ordered_distance:65` proves EXACTLY
`D(F_b x,F_a x)=D(F_(b-a) x,x)` for 0<a<b, using actual addition and isometry.
`parameter_close_bound:83` handles both rational orders and semantic equality
with the ONE original source-computed zero-time radius; no second modulus.

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTime.lean`,
`timeRows:60` supplies actual original product-limit Rows at positive numerical
samples. `timeModulus:68` composes the supplied numerical QCauchy modulus with
the original source radius. `timeRows_cauchy:71` proves the all-tail physical
bound; `timeSequence:91` feeds the existing ORIGINAL completion.
`timeLimitCertificate:110` returns output Rows and their computed rate.
`timeLimit_congr:118` compares actual limits, so `positiveAction:131` descends
to EVERY original physical class without representative selection.
`positiveAction_rational:141` recovers the original rational limit exactly.

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePins.lean`,
`positiveAction_time_congr:141` handles different real presentations, start
offsets, floors and moduli. Numerical Equiv is eliminated only locally in
the Prop-valued equality proof; no Type rate is extracted from it. The original
two limit rates and parameter comparison at epsilon/16 pay10epsilon/16.
`positiveRealAction:182` descends to the already defined carrier-free numerical
positive-time quotient; `positiveRealAction_pin:186` and
`positiveRealAction_rational:190` retain the actual action and rational recovery.

All three focused checks emitted `.olean`s. All nineteen source-site gates
passed: two {propext}, seventeen {propext,Quot.sound}. Independent
source/math/log/hash reviews passed:

| Module suffix | Gates | Accepted log in `/tmp` | SHA256 |
| --- | ---: | --- | --- |
| `ScaledCayleyParameterContinuity` | 3 | `ym-cayley-parameter-continuity-first-20261001.log` | `497fa10157c47b8d710d90b4bd7c312036311e99b8599c3fbab850e092a1e82a` |
| `ScaledCayleyPositiveTime` | 12 | `ym-cayley-positive-time-third-20261001.log` | `13dd4cfb2f712def909b96fe8c1a782c91f8a9c44c602e91069fc9e7750f79b0` |
| `ScaledCayleyPositiveTimePins` | 4 | `ym-cayley-positive-time-pins-first-20261001.log` | `4164ac93f747e87921d6cbac88df425b3fd66dec936173dcf6366794430accd9` |

The first PositiveTime draft's rational-recovery rewrite did not expose the
ofRows constructor after quotient induction; explicit `change` repairs only
that elaboration seam. The final check also directly gates four additional
public pins. Accepted sources/logs contain no sorryAx or forbidden construct.
One serialized20-GiB worker and12-GiB OS reserve were retained; preflight found
zero swap and no competing compiler/test/runner. Three root imports added;
full root/tree/build/audit/guard NOT run. CI and safety limits unchanged.
No displayed canonical claim changed; no ASCII reprint.

NEXT: actual positive-real addition and FULL Hermitian pairing preservation,
then the signed-real unitary group. These are available original-limit joins,
not new assumed analytic fields. Generator identification, physical spacing/
scaling, useful signed-energy control, survival, finite positive physical mass,
full continuum QFT, every group and Clay remain OPEN.

## Positive-real addition, full pairing and constructed inverse

The user-requested parallel work now supplies three ACTUAL laws on the SAME
original completed complex Wilson bond, at fixed nome and width. Sol built
pairing preservation and the constructive inverse in separate modules; the
parent built addition and serialized every compiler check. Luna independently
reviewed the mathematics, current sources, exact gate sites and accepted logs;
the pairing author also reviewed the inverse argument. No unavailable survival,
spacing, continuum or compact-group input was assumed to make this progress.

### Addition uses the actual numerical sum constructor

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeAddition.lean`,
`sum_sample_close:62` compares the sum-time's UPPER dyadic samples with the sum
of the original raw samples. Each error is at most half^n; the computed
`halfCutoff(half*r)` pays both errors. This needs no numerical Cauchy rate.
Only numerical `addTime`/`addTime_comm` are reused from the legacy semigroup
module; its operator and physical carrier are NOT reused.

`additionRate:84` takes the maximum of the rounding cutoff at the ORIGINAL
source radius and BOTH original time-limit rates, all at epsilon/16.
`sum_composition_limit_bound:124` compares the actual sum-time sample with
the actual two-stage output: parameter closeness controls rounding; rational
addition/commutation and isometry transport the inner original limit bound;
the outer original limit bound supplies the last bridge. Squared triangles
cost10epsilon/16<=epsilon. No sum-time forward rate is additionally required.

`positiveAction_sum_ofRows:162` invokes original limit uniqueness, not an
assumed composition law. `positiveAction_sum:172` covers EVERY original class;
`positiveRealAction_addTime:180` and `positiveRealAction_commute:187` descend
to the already constructed numerical positive-real time quotient.

### Full Hermitian pairing, not separate component invariance

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimePairing.lean`,
`positiveAction_pairing_rows:170` compares the same positive rational sample
on both original sources. The real sum passes through `sum_pairing_limits_eq`.
The imaginary cross difference is first rewritten to a cross-add equality,
passed through that same original limit lemma, and recovered by exact
subtraction. No individual real-component pairing is claimed invariant.

`positiveAction_pairing_preserved:226` and
`positiveRealAction_pairing_preserved:241` cover EVERY original physical class.
`positiveAction_distance:248`, `positiveRealAction_distance:256`,
`positiveAction_injective:264` and `positiveRealAction_injective:275` follow
from original physical pairing/definiteness; no onto hypothesis is used.

### Computed inverse with the unchanged original forward rate

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeInverse.lean`,
`inverseAction:57` is the actual formula K U_t K.
`inverseTimeRows:61` constructs original output Rows using physical conjugation
and the existing actual time-limit Rows; `inverseTimeRows_pin:65` pins them.
`inverseTimeRate:75` is EXACTLY the existing forward rate on conjugate input.

`inverseTimeRows_sample_distance:80` uses the already proved rational inverse,
rational isometry and physical conjugation isometry to identify the candidate's
sample inverse defect EXACTLY with the original forward time-limit defect.
`inverseTimeRows_sample_bound:116` thus retains the original computed rate.
Original limit uniqueness proves `positiveAction_inverse_right:126`; proved
injectivity proves `positiveAction_inverse_left:142`.
`inverseRealAction:149`, `positiveRealAction_inverse_right:152` and
`positiveRealAction_inverse_left:159` retain those laws on the existing
numerical time quotient. `positiveRealPreimage:166` returns its witness in
Type, with no quotient representative selection or Prop-to-Type extraction.

### Exact verification boundary

All three focused checks emitted `.olean`s. All27 source-site gates passed:
one {propext}, twenty-six {propext,Quot.sound}. Independent reviews passed.

| Module suffix | Gates | Accepted log in `/tmp` | SHA256 |
| --- | ---: | --- | --- |
| `ScaledCayleyPositiveTimeAddition` | 8 | `ym-cayley-positive-time-addition-third-20261001.log` | `3b12708fad26c2efe50558a3cf6de740f3d31298b75103c0ba56639b67d8457d` |
| `ScaledCayleyPositiveTimePairing` | 7 | `ym-cayley-positive-time-pairing-first-20261001.log` | `3f150445869d4316cb116fe62fa69516f7e7afd40bf6401a488f76490115cee7` |
| `ScaledCayleyPositiveTimeInverse` | 12 | `ym-cayley-positive-time-inverse-final-20261001.log` | `11d3c36667d90238911daf45c6a336e858cc4c59091ff48ce45dd6ab7c66a57c` |

Addition's rejected drafts had only an antitone-lemma namespace error and a
let-bound radius rewrite seam. Opening the defining namespace and explicitly
exposing the radius argument repaired these; the accepted proof has no sorryAx.
Pairing passed its first check. The inverse passed its first check and was
rechecked after a docstring-only once/twice correction. Accepted sources/logs
contain no sorry, forbidden axiom or new analytic premise.
One serialized20-GiB worker and12-GiB OS reserve were retained; preflight found
zero swap and no competing compiler/test/runner. Three root imports added;
full root/tree/build/audit/guard NOT run. CI and safety limits unchanged.
No displayed canonical claim changed; no ASCII reprint.

NEXT: complex linearity using the FULL pairing and computed preimage, then
signed-real parameter/group and source-derived continuity joins. Preserve
the proved -2i normalization. These fixed-carrier laws do not produce the
missing changing-scale pairing maps, uniform nonzero response, spacing-matched
energy estimates, translated continuum locality or compact-group Haar/heat
realizations. Generator identification, physical spacing/scaling, useful
signed-energy control, survival, finite positive physical mass, full continuum
QFT, every actual compact simple group and Clay remain OPEN.

## Positive-real complex linearity from constructed preimages

The parallel inverse author supplied this short SAME-carrier consumer in
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeLinear.lean`.
`positiveRealAction_add:51` and `positiveRealAction_smul:70` use original
physical `eq_of_pairings`. For each test z, the ACTUAL
`inverseRealAction time z` is an explicit preimage: the already proved right
inverse rewrites z as U_t(preimage). FULL Hermitian preservation and the
original `inner_add_left`/`inner_smul_left` laws then give the exact identities.
No surjectivity field, representative selection or duplicated polarization
algebra is needed. BOTH supplied scalar QCauchy witnesses remain explicit.

The parent focused check emitted the module's `.olean`; both source-site
gates90--91 passed within {propext,Quot.sound}. Luna independently reviewed
the mathematics, source, sites, accepted log and SHA256:

- `/tmp/ym-cayley-positive-time-linear-first-20261001.log`
- `7a7fb52c5984d6912b41c44a23f3f1638ab8d36ffef5f41f834d82f0e85e7d11`

No sorry, forbidden axiom, new analytic premise, safety-limit change or
canonical frontier weakening. One serialized20-GiB worker and12-GiB reserve
retained. One root import added; full root/tree/build/audit/guard NOT run.
CI unchanged. No displayed chart claim changed; no ASCII reprint.

NEXT: signed-real group and source-derived strong continuity. Complex-linear
positive-time bijective isometries alone do not supply those parameter laws,
the physical clock/maximal-generator calibration or any changing-scale input.
Complete signed scaling, continuum survival, finite positive physical mass,
full continuum QFT, actual every-group realization and Clay remain OPEN.

## Signed-time group and source-computed continuity

This closes an ORIGINAL operator join, not the continuum target. Two Sol
agents constructed numerical signed time and positive-real continuity while
the parent proved the actual signed action and its continuity consumer. Luna
independently reviewed current sources, mathematics, exact gate sites and
accepted logs/hashes. The continuity author also reviewed both signed proofs.
All operators stay on the SAME original completed complex Wilson bond.

### Genuine numerical coverage without a real-sign decision

In `lean/YMGap/Continuum/SignedRealTimeData.lean`,
`pair_value_cross:58` turns equality of numerical differences into equality
of crossed positive sums. `SignedTimeValue:71` identifies precisely positive
pairs with the same ORIGINAL RC value. `addTime:149`, `negTime:166` and
`zeroTime:184` have proved value pins and additive-group identities.
`positiveTime:190` embeds the existing positive-real values with
`realValue_positiveTime:201`.

`shift:209` computes |r.approx(cr.M1)|+2 from ONE rational sample and a
SUPPLIED Type-level QCauchy witness. `shiftedPositive:250` constructs the
actual stream r+shift with explicit scalar-add Cauchy data, start cr.M1 and
floor1 proved from cr.bound1. `shiftedRight:265` is the actual positive rational
shift. `ofSuppliedReal:269` therefore represents EVERY supplied pair
(r:CReal,cr:QCauchy r.approx); `realValue_ofSuppliedReal:274` pins its difference
EXACTLY to the original RC value. No CReal.abs stream, decision of a real sign,
or extraction from the legacy Prop-valued r.cauchy field occurs. Coverage of
such supplied data is proved; no canonical representative/modulus selector for
an arbitrary bare RC quotient is claimed.

### Signed action descends through actual positive cancellation

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime.lean`,
`positive_inverse_commute:57` and `inverse_addTime:63` derive their laws from
the ACTUAL positive action, inverse and injectivity; they are not inputs.
`pairAction:98` is U_(positive) V_(negative).
`positive_sum_pairAction_cancel:100` cancels actual operators through a positive
sum. `pairAction_congr:108` applies the common injective U_(p.2+q.2): both
outputs reduce to the crossed positive sums already pinned numerically.
No selected physical or numerical quotient representative is used.

`signedAction:125` descends to EVERY original physical class.
`signedAction_addTime:139`, `signedAction_zero:146`,
`signedAction_neg_left:179` and `signedAction_neg_right:185` prove the actual
group laws. `signedAction_positiveTime:152` EXACTLY recovers the previous
positive-real action. `suppliedRealAction:160` consumes the computed numerical
presentation; `suppliedRealAction_congr:163` proves independence of supplied
real presentations/moduli. `signedAction_pairing_preserved:191`,
`signedAction_distance:198`, `signedAction_add_state:205` and
`signedAction_smul:213` retain the FULL original Hermitian pairing and both
supplied complex-scalar Cauchy witnesses.

`pairAction_displacement:224` proves EXACTLY
D(U_a V_b x,x)=D(U_a x,U_b x), even for two large positive times. This is the
specific consumer of the independently constructed positive parameter bound.

### Source-computed continuity, with actual real-value hypotheses

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeContinuity.lean`,
`parameterDelta:65` is one sixteenth of the ORIGINAL source radius at e/16;
`parameterDelta_positive:68` proves positivity. The legacy module contributes
ONLY numerical `time_close_eventually`, not its physical carrier/estimate.
Actual RC order gives eventual dyadic closeness; the upper approximation error
and computed half-power cutoff turn it into raw-sample error <=3delta, below
the original rational radius. These logical eventual witnesses stay within
the Prop-valued bound proof. The original rational parameter estimate and BOTH
original timeLimitRates then cost10e/16<=e in squared physical distance.
`positiveAction_parameter_close_ofRows:159` and
`positiveRealAction_parameter_close_ofRows:204` bound the SAME original source.
`parameterContinuityCertificate:219` returns the computed radius in Type.

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleySignedTimeContinuity.lean`,
`signedAction_difference_distance:68` moves an arbitrary-center distance to
zero by ACTUAL group isometry/inverse laws. `signedAction_near_zero_ofRows:80`
translates the two bounds on the ACTUAL signed numerical value and its negative
into the positive-parameter hypotheses, then uses the exact displacement
identity. `signedAction_parameter_close_ofRows:99` uses the SAME source radius
around EVERY signed center. `signedContinuityCertificate:111` returns that
radius, positivity and the whole bound in Type. Source Rows remain SUPPLIED;
no physical quotient representative or canonical class-to-radius selector is
manufactured. This is source-computed continuity, not an operator-norm or
spacing-uniform estimate.

### Verification and remaining causal frontier

All four focused checks emitted `.olean`s. All60 exact source-site gates
passed: one empty, one {propext}, fifty-eight {propext,Quot.sound}.
Independent reviews passed:

| Module suffix | Gates | Accepted log in `/tmp` | SHA256 |
| --- | ---: | --- | --- |
| `SignedRealTimeData` | 26 | `ym-signed-real-time-data-final-20261001.log` | `21f72e988be220075a4b890b518efa405ac1635a807e56741f39ef0f39a7e5dd` |
| `ScaledCayleyPositiveTimeContinuity` | 5 | `ym-cayley-positive-time-continuity-second-20261001.log` | `ff22e8001b9108ed56666816acff3546388e61111efdb103cbee9cd2f560daf2` |
| `ScaledCayleySignedTime` | 25 | `ym-cayley-signed-time-second-20261001.log` | `9da589d192d0a2af9d0c171cc9fb977afda2a5c7084fbf85cc988cee7541906b` |
| `ScaledCayleySignedTimeContinuity` | 4 | `ym-cayley-signed-time-continuity-second-20261001.log` | `b2fce993fa239c9cd1ae8825970f49bc2cb5082770d72ce5ee755f758f4cbd04` |

Rejected drafts had only explicit namespace/private-visibility, associativity,
quotient-motive and constructor-rewrite seams. The first signed target found
its numerical dependency unbuilt; it was not a meaningful action check.
The accepted signed action passed on its first dependency-complete check.
The numerical module was also rechecked after its docstring clarified the
proved supplied-QCauchy coverage; proof code, gate sites and log hash are unchanged.
Accepted sources/logs contain no sorryAx, forbidden axiom, new analytic premise
or canonical statement weakening. One serialized20-GiB worker and12-GiB OS
reserve retained; live preflight found zero swap and no competing compiler,
test or runner. Four root imports added; full root/tree/build/audit/guard NOT
run. CI and safety limits unchanged. No displayed chart claim changed;
no ASCII reprint.

NEXT: identify the signed infinitesimal action with the SAME maximal physical
derivative graph, preserving the checked second-core -2i normalization and
joining to ORIGINAL Euclidean integer sampling/right derivative. The group
and source moduli alone do not identify that maximal generator or a physical
clock. Spatial/spacing scaling, useful complete signed-energy/variance control,
changing-family nonzero survival, finite positive physical mass, full continuum
QFT, actual every-group realization and the Clay target remain OPEN.

## Parallel maximal-graph transport and second-core graph approximation

The user requested parallel work on continuum survival, physical mass,
full QFT and every compact simple group. Two Sol workstreams and one Luna
review ran alongside the parent. Compiler checks remained serialized. The
new mathematical results are generator prerequisites on the ORIGINAL
fixed-nome/fixed-width carrier, not independent continuum endpoints.

### Actual resolvent commutation and constructed signed graph image

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyResolventLimit.lean`:

- `pairResolvent_distance_bound:78` derives SAME-distance contraction from
  the original real `resolvent_sub` and `norm_bound`; it is not an assumed
  bounded-operator field.
- `resolventRows:84` and `resolventRows_pin:89` construct BOTH original
  range-bearing state images before quotienting.
- `iterate_pairResolvent_commute:94` uses the actual finite Cayley law.
  `product_resolvent_limit_bound:104` preserves the ORIGINAL product rate.
  `limitMap_pairResolvent_commute:127` identifies actual rational limits
  on EVERY physical class by original limit uniqueness.
- `time_resolvent_limit_bound:136` preserves the ORIGINAL positive-real
  time-limit rate. `positiveRealAction_pairResolvent_commute:171` passes
  that identity through the numerical time quotient, with no representative
  selected to compute a physical rate.

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleySignedGraph.lean`:

- `inverseRealAction_pairResolvent_commute:58` follows by applying the
  actual positive action's injectivity to its computed inverse.
  `signedAction_pairResolvent_commute:67` therefore holds for signed time.
- `signedGraphMap:112` constructs the ORIGINAL unit-resolvent domain of
  G_t(input(d)+output(d)). `signedGraphMap_input:115` uses resolvent
  commutation and the original inverse law to pin input to G_t(input(d)).
- `signedGraphMap_output:140` uses the SAME witness, original graph-sum
  law and actual signed linearity to pin output to G_t(output(d)).
  The maximal domain is not assumed invariant; its image is constructed.
- `signedGraphMap_addTime:150`, `signedGraphMap_zero:157` and
  `signedGraphMap_neg_left:162` transport the original signed group laws
  through maximal-domain input injectivity.

The word "maximal" refers to the ORIGINAL intrinsic adjoint graph in
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSDerivative.lean`:
`Domain:52`, `adjointDomain:156` and `ofAdjoint:177`. It does not assert
that the newly constructed signed action's infinitesimal graph has already
been identified with that derivative graph.

### Independent simultaneous second-core graph approximation

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSSecondCoreGraphDensity.lean`:

- `second_input_tail:64` proves the actual identity
  T^2(inverseSum_k X)=T X-defectPower_k(T X).
- `second_output_tail:72` uses the original derivative/inverse-sum
  commutation to prove T A(inverseSum_k X)=A X-defectPower_k(A X).
- `coreInputRange:78` and `coreOutputRange:82` retain actual range
  witnesses for BOTH target coordinates. `coreDepth:87` is the maximum
  of their supplied defect moduli.
- `graphSecondSource:113` first samples the ORIGINAL graph at its
  explicit outer modulus, then applies that inner inverse sum.
  `graph_second_input_bound:118` and `graph_second_output_bound:141`
  control both coordinates using two squared-distance triangles.
- `physicalSecondSource:166` applies the construction to both components
  of a SUPPLIED original physical Point. `physical_second_input_bound:181`
  and `physical_second_output_bound:213` use the SAME second-core witness
  and the actual original graph pins.
- `physicalGraphCertificate:248` returns that computed preimage and both
  bounds in Type. This is graph approximation, not merely input density.

Coverage comes from the existing actual point data:
`lean/YMGap/Continuum/BF4WilsonAllNomeSectorDerivative.lean`:
`graph:74`, `sourceRepresentative:80`, `sourceRepresentative_pin:84`
and `corePoint:137`. No Type-valued modulus is selected from an arbitrary
quotient Domain class. The intended consumer is extension of
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyLimitInfinitesimal.lean`:
`limitMap_secondCore_tangent:153`; that extension is NOT proved here.

NEXT short argument: pass
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyProductContinuity.lean`:
`product_domain_distance_le_four:86` to the actual limit. Apply it to a graph
difference before time normalization; the graph OUTPUT error, rather than a
fixed input error divided by t^2, then controls the tangent comparison.
The represented graph certificate supplies that output approximation. This
is the remaining operator proposition, not a physical spacing estimate.

### Endpoint source findings, not newly closed proofs

Survival: the available original spatial comparison remains small-nome.
`lean/YMGap/Continuum/QuaternionHaarCharacterInterval.lean:80`, `heatRatio`,
is exactly 32*w^3; and
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSpatialComparison.lean:186`,
`chartScalar_spatial_bound`, requires heatRatio(w)<=1/2. This guard excludes
w>1/4 and therefore a near-one nome trajectory. Fixed-nome spatial-union
floors and fixed-width all-nome bond floors are not a pairing-compatible
changing-spacing family. Naive width/time transport is also obstructed by
`lean/YMGap/Continuum/BF4WilsonAllNomeFringeTimeKernel.lean:94`,
`completedTime_one_not_injective_width_one`, and `:130`,
`no_centered_plaquette_time_transport`.
`lean/YMGap/Continuum/BF4WilsonSpatialUnionPhysicalCalibration.lean:240`,
`fixedMass_no_finite_physical_ceiling`, rules out a fixed dimensionless rate
as a finite physical-rate band along spacing to zero. No duplicate survival
consumer was added. The missing producer is an original-action spatial
comparison on the justified changing family, with an explicit pairing modulus
and retained excitation floor.

QFT: `lean/YMGap/Continuum/BF4WilsonAllNomeBondOSInsertion.lean:100`,
`act_root_pin`, pins physical insertion to R*M*R.
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexObservables.lean:96`,
`complexMultiply_comm`, concerns bare multipliers.
NOT FOUND: a translated-source/locality intertwining theorem joining the
constructed signed group to the buffered physical word action. Searched these
modules, `BF4WilsonAllNomeBondOSSeparatedWords.lean`,
`BF4WilsonAllNomeComplexBondOSSeparatedWords.lean`, and the signed-time modules.
The two different actions cannot be identified by bare commutation.

Every group: `lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:53`,
`productHeat`, is quaternion-specific. Classification and global-form codes
are not compact Haar/heat realizations:
`lean/YMGap/RepTheory/CartanType.lean:58`, `CartanType`;
`lean/YMGap/RepTheory/CompactSimpleGlobalForm.lean:318`,
`CompactSimpleGlobalFormCode`; and
`lean/YMGap/RepTheory/ConstructiveRepresentationDescent.lean:230`,
`descendRepresentation`, supply codes or algebraic descent only.
NOT FOUND: a compatible non-SU(2) compact-group Haar/heat/action producer for
the pinned physical carrier. Searched those modules,
`RationalQuaternionUnitNormGroup.lean`, `G2RootCoordinateCertificate.lean`
and the current group endpoint reports. No group-realization closure is claimed.

### Exact verification boundary

All three narrow checks emitted `.olean`s. All33 source-site gates passed,
each exactly {propext,Quot.sound}; independent mathematical and exact
source/log/hash reviews passed.

| Module suffix | Gates | Accepted log in `/tmp` | SHA256 |
| --- | ---: | --- | --- |
| `ScaledCayleyResolventLimit` | 11 | `ym-cayley-resolvent-limit-second-20261001.log` | `b75c39a224fcb76f5a6de7effa496e3c56a07b749f125d3d7d3c7421ed320a36` |
| `ScaledCayleySignedGraph` | 8 | `ym-cayley-signed-graph-second-20261001.log` | `8f0ff0031c0f2a281e7b8af8465c4fce77f5b37d08797eadf30874bac74a4bbb` |
| `SecondCoreGraphDensity` | 14 | `ym-second-core-graph-density-20261001.log` | `7126820ec18c76cda79c73922f898a19feaa2bcaaebefe0a16619939003e773e` |

The rejected main drafts needed only explicit timeLimitRows folding and a
final definitional equality for pairAction. Graph density passed first check.
Accepted sources/logs contain no sorryAx, forbidden axiom, new analytic premise,
erased Type witness or frontier weakening. One20-GiB worker and12-GiB OS reserve
were retained; preflight found zero swap and no Lean/Lake/test/runner conflict.
Other user computation was left untouched and live telemetry remained enabled.
Three root imports added; full root/tree/build/audit/guard NOT checked.
CI and safety limits unchanged. No exact displayed chart claim changed;
no ASCII reprint.

The original maximal-domain invariance and represented graph approximation
are proved. The maximal tangent/physical-clock identification, primary useful
signed scaling, changing-family survival, finite positive physical mass,
full continuum QFT, every compact simple group and Clay remain OPEN.

## Original maximal-graph right-rational tangent and parallel endpoint review

The requested parallel work used two Sol workstreams and one Luna review;
Lean checks remained serialized. The new proved component belongs to the
generator branch on the SAME original fixed-nome/fixed-width physical carrier.
The endpoint reviews below identify missing producers; they do not close them.

### Proved output-controlled tangent extension

- `lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyDomainDisplacement.lean:92`,
  `point_limit_distance_le_eight`, uses the ORIGINAL product rate and its
  supplied input Rows. The squared-distance triangle gives coefficient 8;
  no sharp coefficient-4 distance-limit lemma is assumed. `:136`,
  `limitMap_domain_distance_le_eight`, covers EVERY original domain class.
- `lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyGraphTangentComparison.lean:152`,
  `graphDifference`, constructs the actual original difference domain;
  `:196`, `graphDifference_reconstruct`, uses input injectivity.
  `:209`, `tangentError_add`, splits the exact -2i residual.
  `:293`, `graph_tangent_comparison`, gives squared bound
  736*t^4*normSq(second output)+48*t^2*distance(original output,first output).
  There is NO input-error term to divide by t^2.
- `lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyMaximalTangent.lean:73`,
  `approximation`, computes the existing original second-core witness at
  epsilon/128. `:99`, `tangentRadius`, uses its original preimage ceiling.
  The coefficient 48*(epsilon/128)<=epsilon/2 and the computed radius's
  736*t^2*ceiling<=epsilon/2 give `:167`, `physicalPoint_tangent_bound`:
  squared residual <=t^2*epsilon.
- In that SAME module, `:222`, `normSq_realScale`, and exact rational
  reciprocal cancellation give `:255`, `physicalPoint_normalized_bound`.
  `:272`, `normalizedTangentCertificate`, returns a positive rational radius
  with squared normalized residual <=epsilon as Type data. `:281`,
  `signedAction_positive_rational`, pins the map to the constructed signed
  group's actual positive rational action. Moduli belong to SUPPLIED original
  Points; no quotient representative is chosen to compute them.

This proves the RIGHT-RATIONAL -2i tangent on represented points of the
ORIGINAL maximal graph. It does NOT prove negative/full-real differentiability,
the converse infinitesimal-domain characterization, physical-clock/spacing
calibration or a physical Hamiltonian mass gap. The original Euclidean pins
remain available at
`lean/YMGap/Continuum/BF4WilsonAllNomePositiveTimePins.lean:118`,
`positiveAction_original`, and
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSDerivative.lean:325`,
`realTaylorCertificate`; no new scalar-logarithm premise was introduced.

### Endpoint review: exact remaining producer seams

Survival's all-nome original-action comparison exists, but is NOT volume-free:
`lean/YMGap/Continuum/BF4ExactSlabTwoNomeExpectationBound.lean:48`,
`finiteSetCap`, is exactly |ids|*(2*c*relativeVariation), and `:100`,
`expectation_difference_bound`, retains it after cutoff removal.
`lean/YMGap/Continuum/BF4ExactSlabWilsonFiniteWindowCoupling.lean:60`,
`finiteWindow_difference_bound`, uses a face set growing with time and outer
extent. The volume-free alternative at
`lean/YMGap/Continuum/BF4ExactSlabSummedCouplingPath.lean:172`,
`full_slab_original_change_bound`, retains hsmall/hd/hs; so do
`lean/YMGap/Continuum/BF4ExactSlabSpatialTwoNomeExpectationBound.lean:110`,
`expectation_difference_bound`, and
`lean/YMGap/Continuum/BF4ExactSlabLocalizedCouplingBound.lean:93`,
`localized_coupling_bound`. NOT FOUND in these producers: an all-nome,
outer-volume-uniform comparison of the SAME reflected pairing along a justified
changing family. Repackaging the growing face cap as a variance consumer
would not supply that input; no such wrapper was added.

QFT's exact source operation is
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSInsertion.lean:67`, `bufferedSource`,
namely multiply(L,i,advance(1,x)); `:100`, `act_root_pin`, is R*M*R.
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSSeparatedWords.lean:49`,
`sourceWord`, retains each buffer, and
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSSeparatedWords.lean:173`,
`wordAct_ofSource`, pins the same complex physical action. Two letters therefore
have middle factors M_L*T*M_R and M_R*T*M_L, not merely M_L*M_R and M_R*M_L.
NOT FOUND in these modules or the signed-time modules: an original-source
translated-buffered-locality identity or a controlled buffer-removal estimate.
Formal signed conjugation alone does not supply that input; no generic
conjugated-word wrapper was added.

Every-group review: the actual current finite producer
`lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:53`, `productHeat`,
is SU(2)-specific. `lean/YMGap/RepTheory/CompactSimpleGlobalForm.lean:318`,
`CompactSimpleGlobalFormCode`, explicitly stores no group realization or
analytic data; `lean/YMGap/RepTheory/ConstructiveRepresentationDescent.lean:21`
documents its algebraic-only boundary. NOT FOUND in these modules, CartanType,
G2RootCoordinateCertificate or the endpoint review: a compatible non-SU(2)
compact Haar/heat/action producer. A further finite classification-code check
would not provide it. The consumers
`lean/YMGap/Continuum/CanonicalOSRoot.lean:84`, `ReferenceWeightStageFamily`,
and `:268`, `PositiveTimeOSRoot`, still require the actual shared stage,
Schwinger/support/reflection/transfer and nonzero-probe data.

### Verification and residue

All three focused checks emitted `.olean`s; all 25 source-site gates passed:
one {propext}, 24 {propext,Quot.sound}. Independent mathematical and exact
source/log/hash reviews passed. Rejected drafts' private-zero and rational-add
namespace seams were repaired before acceptance; their sorryAx-bearing error
logs are NOT accepted evidence. No source sorry, new axiom, analytic premise,
erased witness or weakened canonical frontier was introduced.

| Module suffix | Gates | Accepted log in `/tmp` | SHA256 |
| --- | ---: | --- | --- |
| `ScaledCayleyDomainDisplacement` | 4 | `ym-domain-displacement-20261001.log` | `e2d3406105b6b43b8c62d34ed2783b253c39c98d3965556ffa648335a491dec5` |
| `ScaledCayleyGraphTangentComparison` | 7 | `ym-graph-tangent-comparison-second-20261001.log` | `74fb43e09e14c5a4ded8ae807ce549ced0d53b6ed2a552dee9c440bbeef184fa` |
| `ScaledCayleyMaximalTangent` | 14 | `ym-maximal-tangent-second-20261001.log` | `34193b2fdd7488598ee27e4922934c3d844d0cb04eb00c9d1b058156a0403c03` |

The worker cap remains 20 GiB, the OS reserve 12 GiB, with ONE compiler and
continuous safety telemetry. Preflight found zero swap and no Lean/Lake/test/
runner conflict; other user work was left alone. Three root imports added;
full root/tree/build/audit/guard NOT checked. CI and resource thresholds
unchanged. No exact displayed chart claim changed; no ASCII reprint.

Next operator joins are negative/full-real tangent and the converse
infinitesimal-domain argument using the ORIGINAL `AdjointPair` and `ofAdjoint`
in `BF4WilsonAllNomeComplexBondOSDerivative.lean:115` and `:177`.
These remain separate from the original changing-family volume-uniform pairing
estimate, translated buffered locality and actual compact-group producers.
Physical spacing/scaling, nontrivial continuum survival, finite positive
physical mass, full QFT, every compact simple group and Clay remain OPEN.

## Original right-rational domain converse and parallel endpoint producers

After `63f406e`, the requested parallel work produced a short ORIGINAL-resolvent
domain converse while separate agents investigated survival, physical
normalization, QFT and compact-group consumers. The theorem below concerns the
SAME fixed-nome/fixed-width carrier; it is not a continuum closure.

### Proved rational tangent and reconstructed domain

- `lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyTangentData.lean:64`,
  `slope`, is exactly -2i times the supplied output. `:67`, `rightQuotient`,
  uses the ACTUAL original Cayley limit. `:72`, `RightTangent`, defines its
  witnessed rational differentiability, with the radius as Type-level data.
  `:202`, `ofPointTangent`, computes this from a supplied original Point.
  `:219`, `eq_of_distance_small`, and `:241`, `RightTangent.unique`, use
  physical definiteness and both supplied radii, without choosing representatives.
- `lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyResolventTangent.lean:67`,
  `pairResolvent_add`; `:74`, `pairResolvent_realScale`; `:95`,
  `pairResolvent_imagScale`; and `:106`, `pairResolvent_diff`, are laws of the
  ORIGINAL graph inverse. `:128`, `unitDomain`, and `:132`, `unitDomain_input`,
  compute its original domain; `:140`, `unitDomain_graph_sum`, pins input+output.
- `lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyGeneratorConverse.lean:48`,
  `rightQuotient_pairResolvent`, transports the actual quotient. `:55`,
  `transportTangent`, uses original distance contraction and UNCHANGED radius.
  `:81`, `resolvent_output`, pins the resolvent output by original tangent
  uniqueness. Quotient induction is only in that equality proof. `:90`,
  `reconstructedDomain`, computes unitDomain(u+v); `:92`,
  `reconstructedDomain_input`, and `:102`, `reconstructedDomain_output`, pin
  BOTH original graph coordinates. `:112`, `ofRightTangent`, returns the
  original Domain and both pins as Type data. There is no spectral theorem,
  pairing-limit proof, new estimate or class-to-radius selection.
- Independently,
  `lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSPairingContinuity.lean:94`,
  `inner_pairing_close`, passes FOUR original real two-slot estimates into the
  FULL Hermitian diagonal sum and signed cross difference, with explicit
  rational cap and tolerance. This is not needed for the shorter converse.

### Requested parallel endpoint work

Survival's exact finite cancellation is already proved:
`lean/YMGap/Continuum/BF4ExactSlabFaceInsertionDeterminant.lean:59`,
`face_insertion_determinant`, and
`lean/YMGap/Continuum/BF4ExactSlabCouplingCenteredResponse.lean:81`,
`face_centered_response_pin`, retain the SAME background and normalized source.
`lean/YMGap/Continuum/BF4ExactSlabHeterogeneousConnectedExpansion.lean:108`,
`connectedNumerator_zero`, and `:185`, `connectedNumerator_filtered`, remove
genuinely separated selections, not remote faces joined by intermediate faces.
The missing producer is a near-one-nome, cutoff- and volume-uniform SUMMABLE
bound on that actual connected face response. No duplicate cancellation
theorem or assumed-survival wrapper was added.

The physical-normalization agent is drafting an actual original
Euclidean/Cayley slope comparison; the QFT agent is drafting the original
unit-source vacuum graph and signed-group invariance. They are UNVERIFIED and
not included in the gate count or committed proof scope here. Neither would
supply physical spacing, a scaling rate band or translated buffered locality.

Group review distinguishes center gauge symmetry from independent link-sign
descent. `lean/YMGap/Continuum/SU2QuaternionProductHeatCenterSign.lean:348`,
`heatAt_centerSign`, changes BOTH paired endpoints. It does not prove an
independent q-to-minus-q quotient law for the original all-spin heat. The
rational sign quotient supplies no compact Haar/OS consumer; no parity-only
module or SO(3) Yang--Mills claim was introduced.

### Exact verification boundary

All FOUR focused checks emitted oleans. Twenty-four source-site gates passed:
one empty axiom set, 23 exactly {propext,Quot.sound}. Independent mathematical
and exact source/log/hash reviews passed. The first converse error log is
rejected evidence; its missing CReal namespace was fixed before acceptance.
No new sorry, axiom, analytic estimate, erased witness or weakened frontier.

| Module suffix | Gates | Accepted log in `/tmp` | Log SHA256 |
| --- | ---: | --- | --- |
| `ComplexBondOSPairingContinuity` | 1 | `ym-complex-bond-pairing-continuity-20261001.log` | `fbb753f7672d79b2f4104aeb63af280ad5aabf1b37bcdd0b0bfdae06cd221361` |
| `ScaledCayleyResolventTangent` | 9 | `ym-resolvent-tangent-20261001.log` | `83d2e7578c7198c622a311e29b2752401cc03eca5e49d5b7795f9d27499e73b9` |
| `ScaledCayleyTangentData` | 7 | `ym-tangent-data-20261001.log` | `d8b11f0be0e94193cda4a0d1f8af731d023591f69e990ec68f90df33b5562f4e` |
| `ScaledCayleyGeneratorConverse` | 7 | `ym-generator-converse-second-20261001.log` | `287a152b8503f5c10e01562d8c568f0358f919549fda0a73e6c6fb686c97a30e` |

The corresponding source SHA256 values are, in table order:
`d22f3e7d928aace7b5d4a607b833a5b24d03f6d05f4991a3a8a8e0aee5210c54`,
`264f30157a1cdc31ffc18b2d24e418620c2f2d6c7febf9ef1387d7235b3e1342`,
`6896cf605300077d53d5922a8f0eed7bba08a3ab7163237416b9c09d181213cc`,
`957ec6e3398cf1a372ac1c3c90b747f21bc4456705e5334f3c9fa509209348cd`.

Four root imports added; full root/tree/build/audit/guard NOT checked. ONE
20-GiB compiler and 12-GiB OS reserve were retained with continuous telemetry;
other user computation was left alone. CI and resource thresholds unchanged.
No exact displayed chart claim changed; no ASCII reprint.
Negative/full-real differentiation, physical spacing and useful signed scaling,
nontrivial continuum survival, finite positive physical mass, full same-theory
QFT, actual every-group realization and Clay remain OPEN.

## Original negative-rational tangent

After `ebf625e`,
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyNegativeTangent.lean:81`,
`outputRows`, retains the supplied graph Point's ACTUAL output State; `:84`,
`outputRows_pin`, pins its original physical class. `:103`, `negativeRadius`,
is the minimum of the positive graph tangent radius at epsilon/4 and that
output's original Rows continuity radius at epsilon/16. No representative is
selected, and the output need not itself be a derivative-domain input.

In the same module, `:286`, `negative_error_identity`, is exactly
E_minus=-G_minus(E_plus)+2it(G_minus(y)-y). Original isometry and output
continuity give squared norm <=2*t^2*(epsilon/4)+8*t^2*(epsilon/16)
=t^2*epsilon. `:448`, `normalizedNegativeResidual`, divides by signed time
-t; `:451`, `physicalPoint_negative_normalized_bound`, preserves the SAME
-2i derivative convention. `:487`, `negativeTangentCertificate`, returns
the positive radius and all-tail bound as Type data.

The focused check emitted an olean; all NINE source-site gates are exactly
{propext,Quot.sound}. Independent updated-source mathematical and exact
source/log/hash reviews passed. The first error/sorryAx-bearing log is rejected,
not proof evidence. Accepted log: `/tmp/ym-negative-tangent-second-20261001.log`,
SHA256 `09e6ec91260e6480d614e0cc079ba4854f48935102735ec96bd302a4fd21562c`.
Source SHA256:
`a0320ae59302789003bfc2b3fe092acb309df57be98395048592c8bc702bc434`.

No new analytic premise, sorry, axiom, erased witness or weakened frontier.
One root import added; full root/tree/build/audit/guard NOT checked. ONE
20-GiB worker with 12-GiB OS reserve and continuous telemetry; CI and safety
limits unchanged. No displayed claim changed; no ASCII reprint. Full-real
differentiation, physical spacing/scaling, continuum survival, finite positive
physical mass, full QFT, every actual group and Clay remain OPEN.

## Parallel original Euclidean/Cayley slope comparison

After `d84fcd3`, the parallel Sol normalization workstream joined the two
original actions at their ACTUAL common graph slope.
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSWickSlopeComparison.lean:111`,
`euclideanRemainder_eq`, pins the original rational Euclidean remainder to
`(I-S_t)u-t*a` for u=input and a=output of the SAME original Point.
The actual Cayley error is `(U_t-I)u+2it*a`. In that module, `:247`, `wickRemainder_pin`,
cancels the shared derivative terms EXACTLY, leaving `(U_t-I)u+2i(I-S_t)u`.
`:262`, `wickRadius`, computes the minimum of BOTH original positive radii at epsilon/10.
`:319`, `wick_remainder_bound`, uses 2+8=10 copies in the squared triangle/scaling
budget and proves norm squared <=t^2*epsilon. `:350`, `euclidean_integer_original`,
pins positive integer samples to the original completed transfer on EVERY
original physical class. No scalar-logarithm identification is assumed.

This is a dimensionless SAME-graph first-order normalization, not Wick analytic
continuation, physical spacing or a mass estimate. Source-dependent radii are
computed from the supplied Point, not selected from a quotient class. The
separate original-vacuum producer remains UNVERIFIED at this checkpoint.

The focused check emitted an olean; all TEN source-site gates are exactly
{propext,Quot.sound}. Independent mathematical and exact source/log/hash reviews
passed. The first explicit-private-zero error log is rejected evidence.
Accepted log: `/tmp/ym-wick-slope-comparison-second-20261001.log`, SHA256
`8aef0a7f779d93c4e914e13c29869c834db7f76cda75efa17a9cce9aca68032e`.
Source SHA256:
`219eaf8ebaf37d61aef868349b4d2e54d9cf14a25e725e308b7db82627b5c416`.
No new analytic premise, sorry, axiom, erased witness or weakened frontier.
One root import added; full root/tree/build/audit/guard NOT checked. ONE
20-GiB worker, 12-GiB OS reserve and continuous telemetry; CI and safety limits
unchanged. No displayed claim changed; no ASCII reprint. Full-real
differentiation, physical spacing/scaling, useful signed scaling, survival,
finite positive physical mass, full QFT, every actual group and Clay remain OPEN.

## Original vacuum stationarity

After `57e8497`,
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyVacuum.lean:57`,
`vacuumPoint`, constructs the actual original unit-source derivative-graph
Point with its supplied time-range witness. In the same module, `:61`,
`vacuumPoint_input`, pins the SAME original vacuum; `:72`,
`vacuumPoint_output`, pins zero. Neither a quotient representative nor an
analytic vacuum hypothesis is selected.

`:127`, `vacuumPoint_shifts`, pins both actual shifts to that vacuum.
`:187`, `cayley_vacuum`, and `:200`, `iterate_vacuum`, give exact finite
stationarity. `:208`, `vacuumRows`, supplies the actual input representation;
`:213`, `vacuumRows_pin`, identifies it. `:228`, `limitMap_vacuum`, uses
the original product-limit uniqueness with the explicit constant rate zero.
`:243`, `positiveAction_vacuum`, and `:256`, `positiveRealAction_vacuum`,
pass the same pin through the original real-time limits. `:265`,
`inverseRealAction_vacuum`, fixes the vacuum under the actual inverse;
`:273`, `signedAction_vacuum`, fixes it under every constructed signed time.
`:283`, `signedAction_vacuum_pairing`, retains the FULL Hermitian pairing
against every original physical vector. This is fixed nome/width stationarity,
NOT translated buffered locality, cyclicity, continuum vacuum survival or QFT.

The focused check emitted an olean; all FOURTEEN source-site gates are exactly
{propext,Quot.sound}. Independent mathematical and exact source/log/hash reviews
passed. The first three error logs are rejected evidence. Accepted log:
`/tmp/ym-cayley-vacuum-fourth-20261001.log`, SHA256
`157a7341e9914fa0abff843e9bfbd4b5b344799e17c1f1fbfbbb941ab6b3ae99`.
Source SHA256:
`567652f8caa40c33dc813b6263c181ac84c6a4d1233513d18560434e4a4e8e02`.
No new analytic premise, sorry, axiom, erased witness or weakened frontier.
One root import added; full root/tree/build/audit/guard NOT checked. ONE
20-GiB worker, 12-GiB OS reserve and continuous telemetry; CI and safety limits
unchanged. No exact displayed chart claim changed; no ASCII reprint.
Full-real differentiation, physical spacing/scaling, useful signed scaling,
nonzero continuum survival, finite positive physical mass, full QFT,
every actual compact simple group and Clay remain OPEN.

## Original Euclidean rational-sample limit

After `749cdb3`,
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSEuclideanSampleLimit.lean:138`,
`original_time_close`, compares the actual original all-nome Wilson action
at two numerically close times. It uses the original mesh bound and original
source range modulus, with the three-segment completed-distance estimate.
The numerical time floor, proximity and radius helpers from
`BF4ExactSlabThermodynamicPositiveRealContinuity` do NOT supply a legacy
action or completion bound. The legacy `realTimeAction_close_bound` is not
used: its carrier is different.

In the new module, `:218`, `euclideanSampleRate`, computes a Nat cutoff
from the supplied time QCauchy modulus and the separate radii of BOTH
original input-range representatives. `:226`, `euclidean_sample_bound`,
pins those coordinates to the SAME original physical graph input and proves
that the actual Euclidean action at rational samples approaches its action
at the supplied positive real time. Rates remain Type-level data; local
eventual-order witnesses occur only inside inequality proofs. The rational
Cayley samples and Euclidean mesh stages are NOT identified.

The focused check emitted an olean; all THREE source-site gates are exactly
{propext,Quot.sound}. Independent mathematical and exact source/log/hash reviews
passed. Accepted log: `/tmp/ym-euclidean-sample-limit-20261001.log`, SHA256
`4aa725a7ef7c51b2dc624cf60dca018d899d746923bcadd38c468dfc50559deb`.
Source SHA256:
`0fa7bfb0318afe0b69d89722dd8d8ce871e9d22bcfa2807731b5fa1608feef1b`.
No new analytic premise, sorry, axiom, erased witness or weakened frontier.
One root import added; full root/tree/build/audit/guard NOT checked. ONE
20-GiB worker, 12-GiB OS reserve and continuous telemetry; CI and safety limits
unchanged. No exact displayed chart claim changed; no ASCII reprint.
At that checkpoint the raw real-time slope join (now proved below), full-real tangent, physical spacing/scaling,
nonzero continuum survival, finite positive physical mass, locality/full QFT,
every actual compact simple group and Clay remain OPEN.

## Original positive-real graph estimate and supplied-time reciprocal

After `5bcaca9`, the two original action limits join on the supplied numerical
positive time, without identifying different sample streams or using a legacy
carrier. In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSWickPositiveRealLimit.lean:202`,
`realWickRemainder` is exactly `(U_D-I)u+2i(I-S_D)u`, with original graph input
u. In that module, `:369`, `realWickRadius`, computes half the existing rational
radius at half epsilon; `:382`, `real_wick_bound`, gives squared norm
<= time^2*epsilon. BOTH the original Cayley and Euclidean convergence rates
control the action at their common supplied rational sample. Their difference
pays 2+8=10 copies of sample error. The final closed-ball order passage uses
only generic CReal scalar/order lemmas; Prop-local eventual indices do not
select radius data.

In
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveRealTangent.lean:72`,
`realOutputTerm` scales the SAME actual graph output by the supplied time value.
`:80`, `realError`, retains the exact -2i derivative convention. `:85`,
`remainder_eq`, pins the original Euclidean Taylor remainder; `:151`,
`realError_decomposition`, proves E_D=W_D-2i*R_D exactly. `:162`,
`realTangentRadius`, takes the minimum of the original mixed radius at epsilon/4
and original Euclidean Taylor radius at epsilon/16. `:212`,
`real_tangent_bound`, closes 2*(epsilon/4)+8*(epsilon/16)=epsilon.
`:236`, `realTangentCertificate`, returns the radius, positivity and all-small-time
bound as Type data. `:244`, `realError_signed_pin`, pins the actual signed action.
This is a positive-real first-order NUMERATOR/error estimate, not yet the
normalized real difference quotient, negative-real derivative or full-real
domain identification. It is not Wick analytic continuation or physical time
calibration.

In `lean/YMGap/Continuum/PositiveTimeReciprocalData.lean:28`, `sampleCauchy`,
the SAME supplied positive sample stream uses the original time QCauchy modulus.
`:36`, `sample_floor`, retains its supplied positive floor. `:52`,
`sampleLimit_equiv`, pins its limit to the ACTUAL supplied real value.
`:67`, `reciprocalStreamCauchy`, and `:77`, `reciprocalRealCauchy`, construct
Type-level moduli. `:87`, `reciprocal_product`, proves the product of that SAME
time value and the constructed reciprocal equals one. No inverse hypothesis,
quotient-selected representative or physical-clock premise was introduced.
The next consumer is normalization of the actual positive-real graph estimate.

All THREE focused checks emitted oleans. The 24 source-site gates are exactly:
two empty, three {propext}, nineteen {propext,Quot.sound}. Independent
mathematical and final source/log/hash reviews passed. Accepted evidence:

- Wick limit source SHA256
  `26d2d4bd908a4a8b49cb258dd9e579f898c624369eda4009aaf0d9500ebbfc05`;
  `/tmp/ym-wick-positive-real-limit-third-20261001.log`, SHA256
  `70f56e7125b58b6cc48c3e82cac3ad191947786150591d13106cab692bd96e0a`;
  four gates, all {propext,Quot.sound}.
- Tangent source SHA256
  `6d89493c471b7452f88660913a01b4bea8ae7b8c313ea533939546b9af45d330`;
  `/tmp/ym-positive-real-tangent-second-20261001.log`, SHA256
  `c26f989b9b44a6034a33d59fe39ee257ff353bd6f813a910f6311a7fb6f7692f`;
  nine gates, all {propext,Quot.sound}.
- Reciprocal source SHA256
  `6866aac7e47d1383fd51d60734ebec56d88dad592725ea8dc1f67a980518d826`;
  `/tmp/ym-positive-time-reciprocal-20261001.log`, SHA256
  `28017aab67a55bc528d2494982c0ac42f16dda6843d9f24c7a2631320d0d36ef`;
  eleven gates: two empty, three {propext}, six {propext,Quot.sound}.

The first two Wick error logs and first tangent error log are REJECTED, not
proof evidence. No new analytic premise, sorry, axiom, erased witness or
weakened frontier. Three root imports added; full root/tree/build/audit/guard
NOT checked. ONE serialized 20-GiB worker, 12-GiB OS reserve, continuous
pressure/swap telemetry; CI and safety limits unchanged. No exact displayed
chart claim changed; no ASCII reprint. Normalized/full-real differentiation,
physical spacing/scaling, useful signed original-energy/SAME-variance control,
nonzero continuum survival, finite positive physical mass, full QFT, every
actual compact simple group and Clay remain OPEN.
