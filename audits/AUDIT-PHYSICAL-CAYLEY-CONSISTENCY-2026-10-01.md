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
