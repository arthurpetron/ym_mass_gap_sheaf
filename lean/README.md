# Lean Formalization

This folder holds the Lean 4 formalization of the constructive
mathematical steps of the Yang–Mills mass gap program, instantiated
per gauge group [SU(2), SU(3), ...] with a uniform reduction toward
all compact simple groups.

The purpose is to make the program's **constructive law** —
"every existence claim returns an object, a witness, and a computable
modulus" (`docs/outline.md` §0.2) — *mechanically enforced* rather
than merely intended. A Lean proof that typechecks under the
discipline below is a machine-checked certificate that a given step is
genuinely constructive.

**Constructed positive-real Cayley parameter (2026-10-01 UTC):**
`ParameterContinuity.parameter_ordered_distance` reduces parameter differences
EXACTLY to zero-time displacement using rational addition and isometry.
`PositiveTime.timeModulus` composes the supplied numerical QCauchy modulus with
the SAME source radius. `timeLimitCertificate` returns actual original Rows
and their convergence rate; `positiveAction` descends without representative
selection. `PositiveTimePins.positiveAction_time_congr` proves presentation
independence before `positiveRealAction` descends to numerical time values;
positive rationals recover the original limit. Nineteen focused gates and
independent reviews passed within {propext,Quot.sound}. Real addition, full
pairing preservation, signed-real unitary group and physical calibration remain
OPEN. Evidence: positive-real parameter addendum in
`audits/AUDIT-PHYSICAL-CAYLEY-CONSISTENCY-2026-10-01.md`.

**Original Euclidean graph transport and Cayley limit commutation (2026-10-01 UTC):**
the bounded original dyadic derivative commutes with the original positive-time
action. Constructed `DerivativeTime.timeDomain` transports EVERY physical graph
class and both pins; it also preserves every intrinsic adjoint pair. Actual
linearity and imaginary-shift inverses prove `cayley_action_commute` and
`iterate_action_commute` on the SAME complex bond completion. Seventeen focused
gates and independent reviews passed within {propext,Quot.sound}.
`ScaledCayleyEuclideanLimit.actionRows` now retains both original range witnesses;
the unchanged product-limit rate and Euclidean contraction prove
`limitMap_action_commute` on EVERY class. Five further gates and independent
review passed. No physical-spacing or continuum generator calibration follows.
Evidence: Euclidean limit-commutation addendum in
`audits/AUDIT-PHYSICAL-CAYLEY-CONSISTENCY-2026-10-01.md`.

**Original physical quotient limit, rational addition and tangent (2026-10-01 UTC):**
`ScaledCayleyLimitMap.limitMap` acts on EVERY original complex physical
class, with representative independence proved before Quotient.lift2.
`ScaledCayleyLimitPairing.limitMap_pairing_preserved` retains the FULL
Hermitian real sum and imaginary difference through constructed limits;
exact squared-distance isometry and injectivity follow without surjectivity.
Full pairing and physical definiteness now prove `limitMap_add` and
`limitMap_smul`, retaining both supplied scalar moduli without an onto premise.
Physical conjugation now constructs its two-sided inverse and Type-valued
preimage. An exact finite-product distance identity reuses the SAME forward
rate unchanged. Seventeen new focused gates and independent reviews passed.
Exact finite squaring now proves `limitMap_double` on EVERY original class,
with a computed maximum of two supplied-Rows rates. Finite-product continuity
on graph inputs has the bound 4*t^2 times the ORIGINAL output norm, independent
of depth. Ten focused gates and independent reviews passed at that checkpoint.
`ScaledCayleyLimitContinuity.continuityCertificate` now returns a positive
rational t-to-zero radius computed from supplied ORIGINAL Rows and tolerance.
`MixedIdentity`, `MixedBound` and `CompositePowerComparison` prove the actual
mixed-step identity, quartic local budget and 4^n squared-error amplification.
Their sixteen focused gates and independent reviews passed. The later actual
all-Rows mixed comparison now feeds `LimitAddition.limitMap_add_parameter`
and `limitMap_commute` for EVERY original class and all positive rational
parameters. `LimitInfinitesimal.limitMap_secondCore_tangent` uses constructed
core Rows and the actual rate to prove the exact -2i phase with squared
error <=368*t^4*||second output||^2. Seventeen further focused gates and
independent reviews passed. Full-real time and physical-spacing/maximal
generator calibration remain OPEN. Evidence: rational-addition addendum in
`audits/AUDIT-PHYSICAL-CAYLEY-CONSISTENCY-2026-10-01.md`.

**Parallel product-limit extension to every supplied physical Rows (2026-10-01 UTC):**
`ScaledCayleyAllRowsLimit.productLimitCertificate` constructs original
physical Rows and an explicit rate for arbitrary represented inputs. Its
computed Cauchy modulus combines actual second-core density and exact finite
Cayley isometry, with no choice or new analytic premise. Sixteen focused
gates and independent review passed. Quotient operator/group/continuity laws,
physical-time identification and continuum remain OPEN. Evidence: all-Rows
addendum in `audits/AUDIT-PHYSICAL-CAYLEY-CONSISTENCY-2026-10-01.md`.

**Constructed represented second-core product limit (2026-10-01 UTC):**
`ScaledCayleyDyadicProducts.product_consecutive_norm_le` bounds ACTUAL
consecutive squared error by `22*t^4*(1/4)^n*preimageNorm Y`.
`ScaledCayleyDyadicLimit.productLimitCertificate` computes original physical
limit Rows and a Type-level modulus from the supplied ORIGINAL source streams.
The doubled-step estimate and finite-power comparison are proved, not fields.
The separate `PlaquetteAuxiliaryWardSign` module proves an OWN-centered
negative residual for a literal auxiliary weight, not a terminal heat source.
All 51 focused gates and independent reviews passed within the constructive
gate. All-Rows extension, physical time, signed scaling and continuum remain
OPEN. Evidence: product-limit addendum in
`audits/AUDIT-PHYSICAL-CAYLEY-CONSISTENCY-2026-10-01.md`.

**Represented finite products and first graph differences (2026-10-01 UTC):**
`ScaledCayleyRows.iterateRows_pin` constructs actual original Rows for every
finite Cayley iterate, retaining range witnesses and moduli without quotient
selection. `ScaledCayleyRefinement.cayley_domain_difference_norm_le_four`
proves the first-order graph ceiling `4*t^2*||output d||^2`, NOT the doubled-step
estimate. `SU2QuaternionPlaquetteQuarticHaar` proves literal bare cubic/quartic
moments 0 and 2, NOT weighted source/Ward control. All 23 focused gates and
independent reviews passed within {propext,Quot.sound}. Product convergence,
physical time, useful signed scaling and continuum requirements remain OPEN.
Evidence: addendum in
`audits/AUDIT-PHYSICAL-CAYLEY-CONSISTENCY-2026-10-01.md`.

**Local Cayley consistency and commutation (2026-10-01 UTC):**
`ScaledCayleyConsistency` and `ScaledCayleyErrorBound` retain the ORIGINAL
linked graph and prove the explicit `4*t^4` squared ceiling on actual represented
second-core points, against their ORIGINAL PREIMAGE norm. Real resolvent and
complex Cayley `Commutation` modules construct graph witnesses and parameter
reordering without assumed domain invariance. All 38 focused gates and independent
reviews passed within {propext,Quot.sound}. Product limits, physical time/logarithm
calibration, mass and continuum remain OPEN. Evidence:
`audits/AUDIT-PHYSICAL-CAYLEY-CONSISTENCY-2026-10-01.md`.

**Original marginal Ward transport (2026-10-01 UTC):**
`BF4ExactSlabFixedSpatialProjectedWard.completeCenteredError_projected_pair`
rewrites the integrated Ward term in the actual complete centered error,
keeping the original mean, partition and coefficient `-(1-w)`. Four focused
gates and independent review passed within {propext,Quot.sound}. This does
not equate marginal/projected weights or supply a sign or scaling estimate.
Evidence: `audits/AUDIT-PROJECTED-WARD-2026-10-01.md`.

**Scaled original physical Cayley operators (2026-10-01 UTC):**
`BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts` and `ScaledCayley`
construct both inverses of input±i*t*output for t>0 and the SAME graph's
complex-linear unitary Cayley map, preserving the full Hermitian pairing.
All 24 gates and independent reviews passed within {propext,Quot.sound}.
Local consistency, product moduli, physical-time calibration and continuum
remain OPEN. Evidence: `audits/AUDIT-SCALED-PHYSICAL-CAYLEY-2026-10-01.md`.

**Finite G2 group groundwork (2026-10-01 UTC):**
`RepTheory.G2RootCoordinateCertificate` checks six positive/twelve signed
roots, coroot pairings, lengths and simple reflections. Thirteen focused
gates passed: eleven empty, two {propext,Quot.sound}; independent review
passed. The existing Cartan/center code pins are not group realizations;
no compatible root-datum consumer or physical G2 Haar/heat/OS object is
supplied. Every-group continuum YM remains OPEN. Evidence:
`audits/AUDIT-G2-ROOT-COORDINATES-2026-10-01.md`.

**Complex original Wilson-word action (2026-10-01 UTC):**
`BF4WilsonAllNomeComplexBondOSSeparatedWords` extends the actual buffered
real action to the existing complex carrier. Word reversal gives the full
Hermitian adjoint, both constructive scalar moduli remain, and source/vacuum
pairings are the original limits. All ten focused gates passed: one empty,
nine {propext,Quot.sound}; independent review passed. Equal-time algebra,
locality, cyclicity, time group, cross-scale maps and continuum QFT remain OPEN.
Evidence: `audits/AUDIT-COMPLEX-WILSON-WORDS-2026-10-01.md`.

**Parameterized original physical resolvents (2026-10-01 UTC):**
`BF4WilsonAllNomeBondOSScaledResolvent` constructs the two-sided original
graph inverse for input+t*output, for every positive rational t. Its
`ScaledReflection`, `ScaledResolventNeumannLimit` and `ScaledDenominator`
successors construct the SAME resolvent denominator inverse with explicit
represented approximation rates. All 71 focused gates passed within
{propext,Quot.sound}, with independent reviews. The uniform denominator
floor 1/2 and squared inverse norm ceiling 4 are not physical gap bounds.
Scaled imaginary shifts, Cayley time products and continuum remain OPEN.
Evidence: `audits/AUDIT-SCALED-PHYSICAL-RESOLVENT-2026-10-01.md`.

**Sharp original source-energy retention (2026-10-01 UTC):**
`BF4WilsonAllNomeSectorSharpEnergyTransfer.retention_square_identity` proves
`||Tx-(1-c)x||^2+2*(1-c)*(c*N-E)=||Tx||^2-(1-c)^2*N` on the ORIGINAL carrier.
`relative_norm_retention` requires only c<=1 and E<=c*N, including zero norm.
The actual core-form ratio is c/(1-c)^2 for 0<=c<1; original source floors
retain the square factor. Ten focused gates and independent reviews passed:
one empty, two {propext}, seven {propext,Quot.sound}. This is a sharper consumer,
not a producer of useful complete signed error/SAME-variance scaling. Survival,
physical mass/time, full continuum QFT and all groups remain OPEN. Evidence:
`audits/AUDIT-SHARP-ORIGINAL-SOURCE-RETENTION-2026-10-01.md`.

**Explicit density of represented physical second-core inputs (2026-10-01 UTC):**
`BF4WilsonAllNomeComplexBondOSSecondCoreDensity` returns actual source
representatives, source-dependent finite inverse-sum depths, second-core
domain points and a Type-valued all-tail modulus for supplied physical Rows.
The physical squared-distance bound is invSucc(n), with tolerance modulus
e.den. Each point has the existing adjoining second-domain witness. All eight
focused gates and independent reviews passed within {propext,Quot.sound}.
No ambient T^2-range density, uniform second-derivative sequence bound,
arbitrary-domain invariance or unitary time group is claimed. Primary signed
scaling, continuum survival, physical mass and the Clay target remain OPEN.
Evidence: `audits/AUDIT-PHYSICAL-SECOND-CORE-DENSITY-2026-10-01.md`.

**Represented physical second-domain witnesses (2026-10-01 UTC):**
`BF4WilsonAllNomeComplexBondOSSecondCore` computes sources representing T y
and the original bounded derivativeAction L y, then constructs actual linked
physical graph points `(T^2 y,T L y)` and `(T L y,L^2 y)` componentwise.
The first output equals the second input on the SAME physical carrier.
The second output's squared norm is bounded by the ORIGINAL PREIMAGE norm,
not the norm of T^2 y. All 14 focused gates and independent reviews passed
within {propext,Quot.sound}. No arbitrary-domain invariance, density, logarithm,
scaled Cayley, time-group or continuum claim is made. Useful signed scaling,
survival, physical mass, continuum QFT and all groups remain OPEN.
Evidence: `audits/AUDIT-PHYSICAL-SECOND-GRAPH-STEP-2026-10-01.md`.

**Physical graph limits and score-envelope obstruction (2026-10-01 UTC):**
`BF4WilsonAllNomeComplexBondOSGraphNorm` proves the original full Hermitian
graph pairing and exact squared-distance decomposition. Its constructed
`graphRowsLimit` controls both input and output with the supplied `limitRate`,
without representative choice or a new analytic field.
`BF4ExactSlabFixedSpatialScoreCalibrationObstruction` proves the EXISTING
score-ceiling coefficient at least 24 for nonempty lists and `1/2<=w<1`,
excluding calibration of that envelope alone, NOT bounding actual energy below.
All 18 focused gates and independent reviews passed within {propext,Quot.sound}.
Useful joint complete-error scaling, continuous unitary time, survival, physical
mass, continuum QFT and all groups remain OPEN. No full-root build is claimed.
Evidence: `audits/AUDIT-GRAPH-NORM-AND-SCORE-CALIBRATION-2026-10-01.md`.

**Centered original remainder square (2026-10-01 UTC):**
`SU2QuaternionCompleteRemainderSquare` proves
`A-H[B^2]=H[(q*f)^2]/4-H[(B-q*f/2)^2]`, with an explicit supported square
certificate. `BF4ExactSlabFixedSpatialCenteredRemainderSquare` centers by the
SAME odd mean and retains `H[(q*psi)^2]=Z*Var_odd-sourceCorrection` exactly.
Its original signed/repeated-family bound has leading rate `12*h+h^2/8`
and an explicit complete error, including signed source and Ward corrections
and changing-source mode/cutoff budgets. No useful scaling bound is asserted.
Twenty-eight gates passed two accepted focused checks within the constructive
gate, with independent reviews. No new analytic premise or full-root build.
Useful signed scaling, survival, physical mass, continuum QFT and all groups
remain OPEN. Evidence: `audits/AUDIT-CENTERED-REMAINDER-SQUARE-2026-10-01.md`.

**Complete original signed remainder cancellation (2026-10-01 UTC):**
`SU2QuaternionCompleteRemainderCancellation` proves exact cancellation of the
quadratic source-curvature flux against the angular-weight Taylor coefficient,
constructs the retained commutator square certificate, and keeps signed cubic,
omitted-mode and angular-pair debt. `BF4ExactSlabFixedSpatialRemainderCancellation`
pins it to the ORIGINAL depth-n projected endpoint, SAME oddMass, mean and
variance, with arbitrary signed/repeated-family identity and ceiling consumers.
Twenty-four gates passed two accepted focused checks within the constructive
gate, with independent reviews. No new analytic premise or full-root build.
Useful complete signed scaling, survival, physical mass, continuum QFT and all
groups remain OPEN. Evidence:
`audits/AUDIT-COMPLETE-SIGNED-REMAINDER-CANCELLATION-2026-10-01.md`.

**Complete signed-family angular/SAME-variance producer (2026-10-01 UTC):**
`QuaternionHaarLocalRelativeWard` pays the actual signed weight derivative
with the same centered square and angular square on each original block.
`BF4ExactSlabFixedSpatialFamilyFootprint` counts at most four actual slots
per listed face, including repeats, and supplies computed active physical links.
`BF4ExactSlabFixedSpatialFamilyRelativeWard` constructs original marginal
score certificates only on that footprint and combines Casimir 12 with the
actual centered-square pin: `A<=(24+6*|J|*C(w)^2)*Z*Var_odd`.
Normalization cancels only SAME positive Z; the width-independent envelope
charges at most `4*qs.length` links. The original temporal energy retains its
COMPLETE normalizedRemainder. Seventeen gates passed three accepted focused
checks within {propext, Quot.sound}, with independent reviews. No new analytic
premise, full-root build or scaling claim. Useful complete signed scaling,
survival, physical mass, continuum QFT and all groups remain OPEN. Evidence:
`audits/AUDIT-WHOLE-FAMILY-RELATIVE-WARD-2026-10-01.md`.

**Local angular cost of the complete signed family (2026-10-01 UTC):**
`QuaternionHaarLocalAngularFamily` constructs filtered-row finite Cauchy
certificates under ONE positive weight, preserving all signed cross terms.
`BF4ExactSlabFixedSpatialFamilyIncidence` computes literal block-face rows
and proves their length at most six for Nodup families.
`BF4ExactSlabFixedSpatialFamilyLocalAngular` joins the actual four-link
Gamma identity to the SAME odd marginal, giving
`normalizedAngular(F)<=24*sum c_p^2*(4-middleRatio(f_p^2))`.
Its Ward and original Taylor energy consumers retain signed corrections.
Seventeen gates passed three focused checks within {propext, Quot.sound},
with independent review; no full-root build or new analytic premise.
Useful SAME-variance scaling, survival, physical mass, continuum QFT and all
groups remain OPEN. Evidence:
`audits/AUDIT-LOCAL-SIGNED-FAMILY-ANGULAR-2026-10-01.md`.

**Actual-mean one-loop radial budget (2026-10-01 UTC):**
`QuaternionHaarRadialMeanYoung` supplies an exact Young square under ONE
certified Haar weight. `BF4ExactSlabFixedSpatialWilsonMeanRadial` identifies
the edge center and centered square with the SAME odd mean and interacting
variance, and proves the literal trace mean has square at most four.
`QuaternionHaarWordQuadratic` sums all four coordinate Cauchy squares before
charging the exact link budget. `WilsonMeanQuartic` computes both cutoff
guards and proves `t*E<=t^2*Var+(t+c^2)*R+t*(4-c^2)*L`, with
`L=6*(1-w)*length^2` and the actual log-quartic rate R. No mixed radial
moment remains in this literal one-loop ceiling. Thirty-eight accepted focused
gates and independent reviews passed; no new analytic premise or broad build.
Useful COMPLETE signed SAME-variance scaling, spatial/spacing control, survival,
physical time/mass, full continuum QFT and all groups remain OPEN. Evidence:
`audits/AUDIT-ORIGINAL-MEAN-RADIAL-BUDGET-2026-10-01.md`.

**Sharper original-source fourth moments (2026-10-01 UTC):**
`SU2HeatQuarticLogDyadicBudget` proves the complete head/tail budget
`888*r^4*h^2` for `h=2^(-6r)`, spin split `r*2^(3r)` and `r>=22`.
`BF4ExactSlabFixedSpatialLogQuartic` applies it to the ACTUAL word chordal
fourth moment, fundamental trace-jump fourth moment and original radial energy
formula. The trace jump is pinned on the SAME doubled carrier and pays the
exact factor sixteen; normalization uses only the SAME positive odd partition.
Thirty-seven gates passed four focused checks, within {propext, Quot.sound}.
Independent reviews passed; no new analytic premise, broad build or raised limit.
The literal one-loop mixed term is now bounded above; useful signed scaling,
survival, physical mass, continuum QFT and all groups remain OPEN. Evidence:
`audits/AUDIT-ORIGINAL-LOG-QUARTIC-2026-10-01.md`.

**Whole-family kinetic upper on the original carrier (2026-10-01 UTC):**
`BF4ExactSlabFixedSpatialFamilyKineticUpper` joins existing exact active-link
alignment to the WHOLE signed family under the original complete edge law.
`QuaternionHaarUniformFamilyCost` uses normalized Gram/Young to pay
`(sum abs c)^2`, with no separate list-length factor or assumed orthogonality.
`BF4WilsonAllNomePlaquetteFamilyKineticUpper` passes this bound through the
actual energy CReal and SAME centered time-loss pin, then telescopes the
positive transfer: `B(v,v)-B(v,T(n)v)<=192*n*(1-w)*(sum abs c)^2`.
The cutoff onset depends on nome only. These are absolute estimates, not
useful SAME-variance scaling or completed width maps. Thirty-four gates
passed four focused checks within {propext, Quot.sound}; seven are axiom-free.
Independent reviews passed; no broad build or new analytic field. The primary
signed scaling estimate, survival, physical mass, continuum QFT and all groups
remain OPEN. Evidence:
`audits/AUDIT-WHOLE-FAMILY-KINETIC-UPPER-2026-10-01.md`.

**Actual complex physical Cayley operator (2026-10-01 UTC):**
`BF4WilsonAllNomeComplexBondOSImaginaryShifts` consumes the constructed
denominator inverse and pins the original positive-resolvent graph output
to `I-R`. Explicit paired original domain classes give BOTH imaginary-shift
preimages on every existing complex physical bond class.
`BF4WilsonAllNomeComplexBondOSCayley` proves uniqueness from original
Hermitian symmetry and physical pairing tests, then constructs the actual
two-sided Cayley inverse, FULL Hermitian pairing preservation and complex
linearity. Both scalar QCauchy witnesses are retained; no analytic field,
choice or spectral theorem is added. Twenty-five gates passed two focused
checks within {propext, Quot.sound}, with independent review. The final
proof uses default heartbeats and one 20 GiB worker; no full-tree audit.
This is fixed-parameter unitary operator structure, not a continuous unitary
time group, physical-time calibration or continuum Hamiltonian. Primary
signed scaling, survival, physical mass, continuum QFT and all groups remain
OPEN. Evidence: `audits/AUDIT-PHYSICAL-BOND-CAYLEY-2026-10-01.md`.

**Actual physical resolvent-denominator inverse (2026-10-01 UTC):**
`BF4WilsonAllNomeBondOSResolventReflection` proves the actual
`S=2(I+A)^(-1)-I` symmetric/contractive and `N=2R(I-R)` squared-distance
contractive by `1/4` on every physical bond class.
`BF4WilsonAllNomeResolventNeumannLimit` retains original range witnesses
in the normalized geometric recurrence and constructs its limit, explicit
modulus and exact fixed-point equation. Congruence of original values lets
`BF4WilsonAllNomeBondOSResolventDenominator` descend that limit without
representative choice and construct BOTH inverse laws for
`D=I-N=R^2+(I-R)^2`. Its form floor is `1/2`; the inverse squared-norm
ceiling is `4`. `inverseCertificate` returns an actual inverse and explicit
row-approximation rate, paying the scaling factor four at epsilon/4.
Forty-nine gates passed three final focused checks within
{propext, Quot.sound}, with independent review. No new analytic field or
canonical closure. Its complex imaginary-shift/Cayley consumer is now supplied
above; useful signed scaling, physical time/mass and continuum QFT remain OPEN.
Evidence: denominator addendum in
`audits/AUDIT-PHYSICAL-BOND-INTRINSIC-ADJOINT-2026-10-01.md`.

**Quantified passive channel/Ward gain (2026-10-01 UTC):**
`SU2QuaternionProductHeatChannelNomeComparison` retains every original
channel normalizer and computed Casimir; nonzero charge is at least three.
`ChannelVacuum` identifies the literal zero-nome channel contribution.
`PassiveChannelStrictAngular` proves A0<=Araw and
A_ch<=(1-w^3)*A0+w^3*Araw for the SAME supported source/observable.
`BF4ExactSlabFixedSpatialFamilyChannelVacuumGain` instantiates the actual
terminal source and signed family, preserving all Taylor/cutoff debt.
`padded_family_energy_ward_gain` gives
E<=12*h*(Z*Var)+D_ch-h*(angularDefect+WardResidual+(1-w^3)*(Araw-A0)),
h=1-w. The gain is second-order near w=1; no variance-relative reserve or
changing-source scaling smallness is supplied. Sixteen gates passed four
focused checks, all {propext, Quot.sound}, with independent review. No broad
run, canonical-field change or continuum closure. Evidence: quantified-gain
addendum in `audits/AUDIT-WHOLE-FAMILY-BAND-RESPONSE-2026-10-01.md`.

**Completed whole signed-family response (2026-10-01 UTC):**
`BF4WilsonAllNomePlaquetteFamilyBondFloor` transports the existing finite
interior-family band through the ACTUAL variance and transfer limits,
proving rho*ambientVariance <= original connected bond covariance.
Distinct faces give its positive coefficient-square floor.
`BF4WilsonAllNomePlaquetteFamilyBondOrbit.connected_source_time_pairing`
pins EVERY original source's bond lag k to ambient centered time k+1;
the actual family Rayleigh input then yields a geometric coefficient-square
lower floor and nonzero response at every integer lag. Coefficients depend
only on strict nome and family-list size, not width or regulators. Twelve
gates passed two final focused checks within {propext, Quot.sound}, with
independent read-only review. No scaling survival, physical mass, continuum
QFT or canonical frontier closure; no broad build. Evidence: completed
addendum in `audits/AUDIT-WHOLE-FAMILY-BAND-RESPONSE-2026-10-01.md`.

**Actual temporal energy and marginal variance limits (2026-10-01 UTC):**
`BF4WilsonAllNomeTemporalEnergyLimit` pins twice the original normalized
finite energy to one fixed signed squared-increment Wilson insertion,
constructs its independent cutoff/time QCauchy data, and identifies its
limit with the existing centered vector's ORIGINAL one-step time loss.
`BF4WilsonAllNomeMarginalVarianceLimit` proves finite Var=Energy+Bond,
constructs the actual oddVariance's own rectangular modulus and CReal,
and pins that limit to the original AMBIENT centered norm. Its
`bond_connected_time_pairing` keeps the physical bond covariance distinct
from the ambient diagonal norm. `CenteredAngularBondBound` supplies a finite
one-sided angular bound against a completed bond representative WITHOUT an
angular limit. Twenty-eight final focused gates are {propext, Quot.sound},
with independent source/log review; no broad run, new analytic field or
canonical frontier closure. Nome and width remain fixed. The useful complete
signed scaling estimate, continuum survival, physical mass, full QFT and
every group remain OPEN. Evidence:
`audits/AUDIT-ACTUAL-TEMPORAL-ENERGY-VARIANCE-LIMIT-2026-10-01.md`.

**Original centered-transfer/bond limit (2026-10-01 UTC):**
`BF4ExactSlabFixedSpatialCenteredTransferCovariance` equates the actual
normalized moving-center quadratic with a one-partition finite covariance.
`BF4WilsonAllNomeCenteredTransferBondLimit.transferCauchy` constructs its
QCauchy witness for a supplied radius-zero Wilson source. Independent
`cutoffThreshold`/`timeThreshold` and `transferLimit_approx` control the
whole late rectangle. `transferLimit_completed_pin` identifies the RC limit
with the original connected zero-lag bond pairing. This does NOT equate
single-slice oddVariance or a finite angular reserve with that norm.
Fifteen focused gates passed: one empty, fourteen {propext, Quot.sound}.
Width/nome are fixed; angular passage, signed scaling, survival, physical
mass and continuum QFT remain OPEN. Evidence:
`audits/AUDIT-CENTERED-TRANSFER-BOND-LIMIT-2026-10-01.md`.

**Actual complex physical derivative/adjoint (2026-10-01 UTC):**
`BF4WilsonAllNomeComplexBondOSDerivative` pairs the existing real physical
domain quotients on the SAME complex BondCompletion. `ofAdjoint` returns
the unique actual domain class for full Hermitian adjoint tests on EVERY
complex physical class. `add`/`smul` construct graph operations with exact
input/output pins, retaining both supplied constructive scalar moduli.
`densityCertificate` consumes explicit physical Rows; `realTaylorCertificate`
consumes explicit original graph Point data. Neither selects a representative
from an arbitrary quotient class. Positivity and `form_gap` retain the original
complex vacuum and fixed coreMargin(w,width), using full Hermitian vacuum
orthogonality. Thirty gates passed the final focused check within
{propext, Quot.sound}; no broad run or canonical frontier closure. Scaling,
survival, physical mass and continuum QFT remain OPEN. Evidence: complex
addendum in `audits/AUDIT-PHYSICAL-BOND-INTRINSIC-ADJOINT-2026-10-01.md`.

**Intrinsic real physical bond adjoint (2026-10-01 UTC):**
`BF4WilsonAllNomeBondOSAdjoint.ofAdjoint` returns a Type-valued domain
class and both exact input/output identities for EVERY intrinsic adjoint
pair on the existing BondCompletion. Its `adjointDomain` is the actual
resolventDomain at shift one applied to u+v, independent of the adjoint
proof. Original symmetry, surjectivity and physical difference tests prove
the identities and uniqueness without representative selection. The existing
fixed-nome/width vacuum-complement form bound is retained. Eight gates
passed one final focused check within {propext, Quot.sound}; no broad run
or canonical frontier closure. The complex physical join is supplied above;
physical scaling, survival and continuum QFT remain OPEN. Evidence:
`audits/AUDIT-PHYSICAL-BOND-INTRINSIC-ADJOINT-2026-10-01.md`.

**Centered-transfer SAME-variance reserve (2026-10-01 UTC):**
`BF4ExactSlabFixedSpatialCenteredTransferReserve.centered_transfer_quadratic_pin`
proves E+B=Z*Var for the actual g=T^depth1 and original odd-marginal center.
`centered_transfer_angular_reserve` pays h*Angular(T(g*centered(f))) inside
that budget. `normalized_centered_transfer_angular_reserve` and
`centered_output_angular_le_variance` normalize only by SAME oddMass:
h*Angular(T(g*centered(f)))/Z<=Var, h=1-w. Every supported signed f, width
and depth works at the original headCutoff guard and 0<w<1. No family/fringe
restriction or width/depth/floor constant is supplied. This does NOT bound
the full signed endpoint cost by a useful scaling-small fraction or supply
a lower bound on the reserve. Four gates passed one final focused check;
no broad run, new analytic field or canonical frontier closure. Evidence:
centered-transfer addendum in
`audits/AUDIT-ACTUAL-FIRST-ORDER-SAME-VARIANCE-2026-10-01.md`.

**Original full-transfer and terminal angular smoothing (2026-10-01 UTC):**
the full-product and actual interacting-transfer joins are now checked.
`SU2QuaternionProductHeatSmoothing.productMap_angular_smoothing` proves
h*Angular(P_full p)<=H[p*P_full p] from the actual degree paths, per-slot
Casimir eigenpins, derived heat eigenpairings and positive diagonal masses.
`BF4ExactSlabFixedSpatialTransferSmoothing.transferStep_angular_smoothing`
retains the COMPLETE V*f and exact inactive-coordinate integration, giving
h*Angular(T f)<=H[V*f*T f]. `terminalMessage_angular_smoothing` pins this
to h*Angular(g_(n+1))<=oddMass(n). Here h=1-w; EVERY cutoff, width/depth
and 0<=w<=1 are included, without a volume factor or heat-floor inverse.
Unweighted output angular energy is NOT the complete endpoint observable
energy or SAME centered variance. That signed scaling comparison remains
OPEN. Six focused checks passed 22 gates, including seven existing gates;
no broad run or canonical frontier closure. Evidence: full-product addendum
in `audits/AUDIT-ACTUAL-FIRST-ORDER-SAME-VARIANCE-2026-10-01.md`.

**Earlier original one-head angular smoothing (2026-10-01 UTC):**
`SU2QuaternionHeadHeatSmoothing.headMap_angular_smoothing` proves
(1-w)*H[angularSquare(P_head p)]<=H[p*P_head p] for the actual
spectator-preserving head update, arbitrary signed input and every cutoff.
`SU2HeatSquaredCasimirSmoothing` supplies the division-free scalar estimate;
exact output degree groups retain signed cross terms. The RHS is uncentered,
not interacting variance. The full-transfer OUTPUT join is now supplied above;
the endpoint-observable/physical scaling join remains OPEN. Three focused
checks passed eight gates; no broad run or Clay closure.

**Generic-source Ward obstruction (2026-10-01 UTC):**
`SU2QuaternionConcentratedSourceWard` constructs nonnegative radial sources
and exact mass/angular identities. `ConcentratedSourceMoments` proves strict
Haar mass and second moment by the recurrence (2k+4)*Z_(k+1)=(2k+3)*Z_k.
`ConcentratedSourceHeatFence.obstruction` returns N,w with 0<w<1 that defeat
EVERY C>=0 in E<=C*(1-w)*actualUncenteredMoment, for EVERY guarded cutoff.
No positive-step centered variance or 4D terminal identification is asserted.
Three focused target checks passed 30 gates; no broad run or Clay closure.
Evidence: concentrated-source addendum in
`audits/AUDIT-ACTUAL-FIRST-ORDER-SAME-VARIANCE-2026-10-01.md`.

**Original fixed-source heat-step limits (2026-10-01 UTC):**
`SU2QuaternionProductHeatSourceSlope.slopeCertificate` returns a positive
radius for h*(A-e)<=E_original<=h*(A+e), with h=1-w and the actual angular
coefficient A. `ProductHeatSourceMomentLimit.momentCertificate` returns a
radius for signed original moments H[(a*p)*P(a)] around H[(a*p)*a]. Both
retain EVERY K>=sufficientCutoff(w); their caps are computed from the fixed
source and insertion. Two focused checks passed 13 axiom gates. No uniform
changing-terminal-source, thermodynamic or physical continuum claim follows.
Evidence: fixed-source addendum in
`audits/AUDIT-ACTUAL-FIRST-ORDER-SAME-VARIANCE-2026-10-01.md`.

**Complex physical bond completion and time (2026-10-01 UTC):**
`BF4WilsonAllNomeComplexBondOSCompletion` constructs the two-way isometry
from paired ORIGINAL physical bond Cauchy classes to the existing complex
sector quotient, with four physical source-pairing pins, represented density
and limits. `ComplexBondOSTime` joins complex scalar/Hermitian laws and the
original numerical positive-time action, with source time-one and explicit
min-of-half-tolerance continuity radii. Both final focused checks passed
42 gates within {propext, Quot.sound}. No representative choice, new analytic
input, broad run, canonical field or continuum/Clay closure. Evidence:
complex addendum in `audits/AUDIT-BOND-COMPLETION-REAL-TIME-2026-10-01.md`.

**Sharp complex mixed decay (2026-10-01 UTC):** a rational orthogonal
phase-vector argument proves constant-one complex Cauchy--Schwarz on the
ACTUAL all-nome reflected finite form and its original joint/completion
limits. `BF4WilsonAllNomeComplexBondOSConnectedDecay` gives
|M_(2n)(X,Y)|^2<=(q^n*Var(X))*(q^n*Var(Y)) for every completed complex
physical bond pair, retaining original variances and four signed source
terms. No extra prefactor or variance inverse. Nome/width and rate remain
fixed; scaling and continuum claims remain OPEN. Four focused checks
passed 16 gates within {propext, Quot.sound}; no broad run. Evidence:
complex addendum in `audits/AUDIT-BOND-MIXED-CONNECTED-DECAY-2026-10-01.md`.

**Actual CHANNEL first order without full-width cost (2026-10-01 UTC):**
`SU2QuaternionPassiveChannelMomentFactorization` supplies one exact common
mass for the original spectator heat and square-inserted source moment.
`BF4ExactSlabFixedSpatialFamilyChannelVarianceBound` proves A_ch<=C*Z*Var,
with C=12*u^2/l^2 depending only on nome/family size, not width/cutoff/depth.
`FamilyChannelTaylorVariance` gives exact original E=(1-w)*A_ch+D_ch and
normalizedEnergy<=(1-w)*C*Var+D_ch/Z. Original signed/repeated faces,
source, mean, partition and omitted cutoff modes remain. The signed debt
and changing-coupling coefficient still need scaling control. Three focused
checks passed 28 gates; no broad run or continuum/Clay closure. Evidence:
actual-channel addendum in `audits/AUDIT-WHOLE-FAMILY-BAND-RESPONSE-2026-10-01.md`.

Follow-on `FamilyChannelRetainedSquare` now retains a nonnegative channel
square in the original signed quadratic debt and SAME-variance energy
consumer, keeping signed curvature and actual cubic/cutoff error.
`ChannelCoefficientFence` proves (1-w)*C>=96 for every nonempty family:
this particular coefficient cannot meet the small-energy guard through
nonnegative debt payment. It does not bound true energy from below. A
sharper actual-source bound or useful joint cancellation remains OPEN.
Two focused checks passed eight gates; no broad run or canonical change.

**Actual RAW source first order versus SAME variance (2026-10-01 UTC):**
`BF4ExactSlabFixedSpatialTerminalSourceBounds` and `FamilyBareHaar` construct
the actual-source/bare-square inputs. `FamilySourceVarianceBound` proves
A<=U(w,width)*Z*Var for the whole signed family at positive depth, without
inverting source mass or variance. `FamilyJointCorrection` combines both
signed first-order corrections exactly, yielding original normalizedEnergy
<=(h+h^2/2)*U*Var+debt/Z, with curvature and cubic/cutoff debt unchanged.
The coefficient is cutoff/depth independent, not width/scaling uniform.
Four focused capped checks passed 35 gates; no broad run or Clay closure.
Evidence: `audits/AUDIT-ACTUAL-FIRST-ORDER-SAME-VARIANCE-2026-10-01.md`.

**Retained source square and literal plaquette curvature (2026-10-01 UTC):**
`QuaternionHaarPolynomialGramDeterminant` constructs finite Gram square data.
`SU2QuaternionSecondOrderRetainedSquare` retains 48*H[(q*f)^2] in the
quadratic correction for Cf=12f. `BF4ExactSlabFixedSpatialFamilyRetainedSquare`
supplies the actual whole signed-family SAME-variance consumer and a proved
nonnegative ceiling gain, preserving source, mean and all signed corrections.
`BF4ExactSlabFixedSpatialPlaquetteCurvature` evaluates the literal full-carrier
curvature as -128*(f^2-1), at arbitrary-insertion Haar-carrier equality.
Scaling-relative signed control remains open; raw source square is not
interacting variance. Six focused capped checks passed 24 gates; no broad
run or continuum/Clay closure. Evidence at repository root:
`audits/AUDIT-RETAINED-SQUARE-AND-PLAQUETTE-CURVATURE-2026-10-01.md`.

**Actual positive Jacobi mixed relative bound (2026-09-30 UTC):**
`JacobiHeatMixedRelativeAngularBound.weightedHeatBound` supplies relative
cost m*R+d*e*R^2 for the ordered mixed derivative, independent of Jacobi
cutoff, with no inverse heat-minimum factor. Follow-on
`QuaternionHaarHeatMixedRelativeAngularBound.heatPrefixMixedRelativeBoundAt`
removes the weights with an explicit mixed-deficit modulus, giving cost
m*R+d*e*R^2+1 on the SAME original heat prefix. The floor enters only the
cutoff precision. The actual four-link two-plane scalar and ORIGINAL two-link
collar now also check: collar first cost 12*c, mixed cost 12*m+(12*c)^2.
The full dual numerator and signed relative temporal-energy estimate remain
open. These polynomial costs alone do not resolve calibration. The weighted
milestone passed 20 gates, weight removal 15, and physical collar 19, all in
focused capped checks; no broad run or Clay closure. Evidence:
`audits/AUDIT-MIXED-RELATIVE-HEAT-2026-09-30.md`.

**Signed-family floor on the literal Wilson completion (2026-09-30 UTC):**
`BF4WilsonAllNomePlaquetteFamilyVariance.familyExcitation_norm_floor`
transfers the ALREADY existing finite original-action signed-family bound
through exact mean/square source pins to the actual Wilson centering stream.
No completed-carrier identification is assumed. The constant is uniform in
width/family size at fixed nome, not along a changing-coupling limit; its
known calibration obstruction remains. Both focused capped checks passed
15 gates; no broad run or canonical Clay closure. Evidence:
`audits/AUDIT-WILSON-SIGNED-FAMILY-JOIN-2026-09-30.md` at repository root.
Follow-on `QuaternionHaarRelativeReciprocalDualNorm` proves a uniform finite
reciprocal-dual square/weighted norm cap from signed relative numerator
certificates, without an extra heat-minimum factor. Both gates passed a
focused capped check. The required physical mixed relative certificate and
useful coupling cost are still OPEN.

**Finite original-weighted moment tail (2026-09-30 UTC):**
`BF4ExactSlabFiniteMomentTail.physicalSweep_tail_bound` consumes an executable
finite moment-zero check and bounds the actual sweep on EVERY supported
polynomial passing it. Exact reverse adjoint and its bounded-degree range
justify the test list; sphere/radical dependencies are retained. Twenty-three
gates passed five focused capped checks. The subsequent
`BF4ExactSlabCompletedMomentTail.completed_sweep_tail_bound` extends this to
EVERY completed input with the same zero moments, by dense dual testing;
ten further gates passed three focused capped file checks. No broad run,
finite-core strict bound, invariant tail, patch lifting or Clay closure.
Evidence: `audits/AUDIT-COMPLETED-MOMENT-TAIL-2026-09-30.md` at repository root.

**All-input original conditional sweep approximation (2026-09-30 UTC):**
`BF4ExactSlabPolynomialSweepApproximation.approximation_error` and
`approximation_degree` join a common relative-error modulus to an
input-independent output-degree bound on the SAME finite supported carrier.
All 50 gates passed five final focused capped checks; no broad run. This
is not yet a completed finite-rank operator, finite Gram gap certificate,
OS-time or scaling theorem. Evidence:
`audits/AUDIT-ALL-INPUT-POLYNOMIAL-SWEEP-2026-09-30.md` at repository root.

**Finite-volume coefficient limitation (2026-09-30 UTC):**
`BF4ExactSlabFiniteVolumeChebyshevObstruction.factor_approaches_one`
proves the ACTUAL covariance multiplier approaches one with an explicit
extent modulus, uniformly in nome and degrees n<=physical face count.
This also covers n<=extent by literal slab geometry. It limits the existing
estimate, not actual correlations. Eleven gates passed three focused capped
checks; no broad run. Useful signed spatial/scaling control remains open.
Evidence: `audits/AUDIT-FINITE-VOLUME-CHEBYSHEV-OBSTRUCTION-2026-09-30.md`.

**Positive bounded regularized operator (2026-09-30 UTC):**
`BF4WilsonAllNomeLogOperator` proves symmetry, positivity, squared-norm cap
one, rational and supplied-modulus real linearity, distance contraction and
vacuum-complement output for the SAME previously constructed series limit.
Actual completed pairing continuity and explicit row-pairing moduli pass
the finite estimates to that limit. All 39 gates passed four focused capped
checks; no broad run. No generator, spatial/scaling or Clay closure follows.
Evidence: `audits/AUDIT-ALL-NOME-REGULARIZED-OPERATOR-2026-09-30.md`.

**Same-carrier regularized series (2026-09-30 UTC):**
`BF4WilsonAllNomeLogPartial` supplies the finite reciprocal tail bound;
`BF4WilsonAllNomeLogSeries.regularizedLogCertificate` constructs the actual
limit of `sum_{k=1}^N (I-T)^k T x/k`, with explicit representative and
convergence data on the ORIGINAL all-nome completion. Finite time/kernel/
vacuum laws are in `BF4WilsonAllNomeLogPartialLaws`. No spectral theorem,
representative choice, full-carrier injectivity, physical Hamiltonian or
continuum result is asserted. Exact verification and scope:
`audits/AUDIT-ALL-NOME-REGULARIZED-SERIES-2026-09-30.md` at repository root.

**Original positive-time range approximation (2026-09-30 UTC):**
`BF4WilsonAllNomeTimeDefectMoments` proves positive mixed time/defect
moments. `BF4WilsonAllNomePositiveTimeTail` and `PositiveTimeRange` construct
explicit T^2-images approximating T x with squared error
`||x||^2/(n+1)^2`, and a computed relative-tolerance cutoff. This respects
the actual boundary kernel: no full-carrier inverse, range density,
continuous-time or physical gap claim is made. All 32 printed gates passed
three final focused capped checks; no broad run. Evidence:
`audits/AUDIT-ALL-NOME-POSITIVE-TIME-RANGE-2026-09-30.md` at repository root.

**Actual finite-width time kernel (2026-09-30 UTC):**
`BF4WilsonAllNomeFringeCorrelation` passes exact original inactive-face
cancellation through the joint limit. `BF4WilsonAllNomeFringeTimeKernel`
proves a positive-norm width-one plaquette is killed by T(1), refuting
full-carrier injectivity there. The padded positive-response counterpart
also excludes zero-preserving, centered-probe-preserving, time-intertwining
transport between these carriers. Syntactic width naturality and strict
upper contraction are unchanged. All nine gates passed focused capped
checks; no broad run. Controlled bulk/spatial comparison and Clay remain open.
Evidence: `audits/AUDIT-ALL-NOME-BOUNDARY-TIME-KERNEL-2026-09-30.md`.

**Uniform fundamental-loop norm cap (2026-09-30 UTC):**
`BF4WilsonAllNomeLoopNormBound` proves centered squared norm <=4 independent
of nome, width and loop size. `BF4WilsonAllNomePlaquetteUniformCapResponse`
uses that SAME-carrier cap to obtain lag-two floor u^2/4, relative floor
u^2/16 and calibration against the existing rate. The original one-step
floor u remains nome/width dependent. All 11 gates passed focused serialized
capped checks; no broad run. Scaling survival and Clay remain open. Evidence:
`audits/AUDIT-ALL-NOME-LOOP-NORM-CAP-2026-09-30.md` at repository root.

**All-nome complex observables (2026-09-30 UTC):**
`BF4WilsonAllNomeTimeZeroCommutation` proves equal-time commutation on the
existing real completion. `BF4WilsonAllNomeComplexObservables` constructs
the corresponding complex-linear, symmetric, bounded commuting maps on the
existing complexification, with the original unit/loop/time-correlation pin.
All 16 gates passed focused serialized capped checks; no broad run. This
is fixed-width observable structure, not continuum locality or signed
scaling control. Full QFT and Clay remain open. Evidence:
`audits/AUDIT-ALL-NOME-COMPLEX-OBSERVABLES-2026-09-30.md` at repository root.

**All-nome Wilson vacuum generation (2026-09-30 UTC):**
`BF4WilsonAllNomeWindowPins` and `BF4WilsonAllNomeWindowRealization`
prove exact finite-program generation of every bounded signed Wilson
expression on the same literal-width completion. Explicit approximating
programs use the supplied Cauchy representative's own squared-distance
modulus. All 20 gates passed focused serialized capped checks; no broad run.
No small-nome guard or new analytic premise is used. This is fixed-width
Wilson-syntax coverage, not full continuum reconstruction; the useful signed
scaling estimate and Clay target remain open. Evidence:
`audits/AUDIT-ALL-NOME-WILSON-GENERATION-2026-09-30.md` at repository root.

**All-nome time-zero observables (2026-09-30 UTC):**
`BF4WilsonAllNomeTimeZeroBound` and `BF4WilsonAllNomeTimeZeroOperator`
construct bounded symmetric Wilson multiplication on the existing literal-width
reflected completion, with explicit moduli and constructive-real linearity.
The cap depends only on spin; no small-nome premise or spatial-union carrier
is used. `BF4WilsonAllNomeTimeZeroVacuum` pins the multiplier-created state
and its time correlation to the existing loop and original lag moment.
All 25 printed gates passed focused serialized capped checks; no broad run.
Spatial/scaling control and the same-theory continuum/Clay target remain open.
Evidence: `audits/AUDIT-ALL-NOME-TIME-ZERO-OBSERVABLES-2026-09-30.md`.

**Original energy-relative residual approximation (2026-09-30 UTC):**
`BF4ExactSlabStarEnergyRelativeApproximation` sharpens the polynomial
kernel-test error to `inverseRate(w)^(2n)*||R_i p||^2`. The existing finite
rational dual value has a relative residual-energy bracket, and summed
local squared errors have no number-of-links loss. The explicit iteration
cutoff is unchanged and still nome-dependent. All five gates passed a
focused one-worker/20 GiB check within `{propext, Quot.sound}`. Signed
collective control, useful scaling and the same-theory continuum/Clay
target remain open. Evidence:
`audits/AUDIT-ENERGY-RELATIVE-RESIDUAL-2026-09-30.md` at repository root.

**Original residual variational completeness (2026-09-27 UTC):**
Explicit polynomial kernel tests now approximate the SAME completed local
residual with squared error at most `inverseRate(w)^(2n)*||p||^2`.
The finite signed dual value brackets that residual energy to any requested
absolute or relative tolerance. The relative iteration count depends only
on nome and tolerance, not volume, late heat cutoff or link position.
All 29 gates passed focused serialized checks within `{propext, Quot.sound}`.
This is local approximation, not global coercivity, physical scaling or
continuum/every-group Clay closure. Evidence:
`audits/AUDIT-ORIGINAL-RESIDUAL-VARIATIONAL-2026-09-27.md` at repository root.

**Original weighted test cost and explicit scalar calibration (2026-09-27 UTC):**
The exterior-modulated kernel tests now have checked exact original pair
and cost H[B*r*Phi] and H[B*r^2*D*Phi]. Their completed identity feeds the
existing test-ray optimizer without replacing the actual normalizer.
In parallel, an explicit Heron calibration and rational reciprocal-pair
parameters give a computable scalar Chebyshev normalization cutoff.
All 41 gates passed focused serialized checks within `{propext, Quot.sound}`.
The actual weighted approximation, useful interacting lower estimate,
rescaled operator contraction, physical scaling and continuum/every-group
Clay remain open. Evidence:
`audits/AUDIT-ORIGINAL-WEIGHTED-TEST-COST-2026-09-27.md` at repository root.

**Exact original polynomial test-ray optimization (2026-09-27 UTC):**
`BF4ExactSlabStarOptimizedPolynomialTest` constructs the best rational
scaling of each supplied actual conditional-kernel test, handles null cost
constructively, and bounds the SAME completed residual energy from below.
Parallel scalar Chebyshev normalization and residual-energy order invariance
are checked. All 35 gates passed seven focused serialized checks within
`{propext, Quot.sound}`. Useful summed-test lower coercivity, accelerated
spatial/physical scaling and continuum/every-group Clay remain open.
Evidence: `audits/AUDIT-ORIGINAL-DUAL-OPTIMIZATION-2026-09-27.md` at repository root.

**Original completed operator-polynomial stability (2026-09-27 UTC):**
`GNSChebyshevEnergy` and `GNSChebyshevRecurrence` prove a coupled quadratic
invariant and the literal first-kind recurrence. `BF4ExactSlabFullActionScalar`
and `BF4ExactSlabSweepChebyshev` realize it on the actual full-action
completion, with completed centered preservation and an unconditional
all-order NON-STRICT norm bound for `T_n(2*S* S-I)`. Four focused checks
passed within `{propext, Quot.sound}`. Useful strict centered coercivity,
normalized acceleration, physical scaling and continuum/Clay remain open.
Evidence: `audits/AUDIT-ORIGINAL-SWEEP-CHEBYSHEV-2026-09-27.md` at repository root.

**Original conditional variance and polynomial tests (2026-09-27 UTC):**
`SU2QuaternionConditionalVarianceReplica` and `BF4ExactSlabStarVarianceReplica`
retain shared spectators and the actual exterior action in the weighted
two-copy variance identity. `BF4ExactSlabStarPolynomialResidual` constructs
polynomial tests in the actual completed conditional kernel and proves a
rational dual lower bound on its residual energy. Separately,
`GNSProjectionSweepAdjoint` constructs the same-completion positive product
S* S. All four focused checks passed within `{propext, Quot.sound}`.
Useful original centered coercivity, accelerated spatial decay, physical
scaling and continuum/Clay closure remain open. Evidence:
`audits/AUDIT-CONDITIONAL-VARIANCE-REPLICA-2026-09-27.md` and
`audits/AUDIT-SWEEP-ACCELERATION-2026-09-27.md` at repository root.

**SAME complex Wilson carrier (2026-09-24 UTC):**
`BF4WilsonAllNomeComplexification` realifies the existing all-nome Wilson
completion into two copies of that completion, with explicit constructive-real
scalar data, a Hermitian positive-definite pairing, real embedding, and the
original completed time map.  The 27-declaration focused check is axiom-clean
within `{propext, Quot.sound}`.  This is fixed-nome/fixed-width J02 structure;
it is not the reflected continuum OS reconstruction, a scaling-uniform gap,
or a Clay conclusion.  Evidence:
`audits/AUDIT-WILSON-COMPLEXIFICATION-2026-09-24.md` at repository root.

`BF4WilsonAllNomeComplexGap` consumes that same carrier, existing unit and
original completed transfer.  Its 11-declaration focused check proves unit
fixation, complex vacuum-sector preservation, and the strict two-step form
bound for every complex vacuum-orthogonal state at fixed nome/width.  The rate
is not scaling-uniform and is not a physical Hamiltonian gap.  Evidence:
`audits/AUDIT-WILSON-COMPLEX-GAP-2026-09-24.md` at repository root.

The same module now exposes `complex_twoStep_translated`, the exact discrete
correlator form of that bound at indices `n` and `n+2` for every translated
vacuum-orthogonal state.  This is still fixed nome/width completed time; it is
not a spacing-uniform, continuum, Hamiltonian or Clay mass-gap result.
Evidence: `audits/AUDIT-WILSON-COMPLEX-TRANSLATED-GAP-2026-09-24.md` at
repository root.

It also exposes `complex_oneStep_norm_gap`, an exact rewrite of that translated
correlator as a norm-square contraction at the intervening time slice `n+1`.
The estimate is uniform in the discrete time index but remains fixed in nome
and width; it is not a spacing-uniform, continuum, Hamiltonian or Clay result.
Evidence: `audits/AUDIT-WILSON-COMPLEX-ONE-STEP-NORM-GAP-2026-09-24.md` at
repository root.

`complex_iterated_norm_gap` iterates this estimate constructively, giving
`twoStepRate^n` norm-square decay for every discrete power on the same carrier.
The rate remains nome/width-dependent and is not a spacing-uniform,
continuum, Hamiltonian or Clay result. Evidence:
`audits/AUDIT-WILSON-COMPLEX-ITERATED-NORM-GAP-2026-09-24.md` at repository
root.

`complex_even_lag_corr_decay` rewrites the same iterated estimate as the
same-object correlator bound at even lag `2*n`, via the exact completed-time
pairing identity. It remains fixed nome/width discrete evidence, not a
spacing-uniform, continuum, Hamiltonian or Clay result. Evidence:
`audits/AUDIT-WILSON-COMPLEX-EVEN-LAG-CORRELATOR-2026-09-24.md` at repository
root.

Even-lag correlators are nonnegative, and `complexRateCutoff` with
`complexRateCutoff_bound` supplies an explicit `powBaseCutoff` for the scalar
rate under a strict-positivity premise. This is only coefficient-level
fixed-parameter evidence; a norm cap and uniform positivity/rate bridge are
still required for an absolute observable modulus. Evidence:
`audits/AUDIT-WILSON-COMPLEX-RATE-MODULUS-2026-09-24.md` at repository root.

`complex_even_lag_response_power_floor` composes that same-object decay with
an explicit norm-cap and response-floor hypothesis, yielding the rational
comparison `floor ≤ twoStepRate^n*C` on the SAME complex carrier. This is a
conditional response compiler: it constructs neither hypothesis and makes no
spacing-uniform, continuum, physical-mass or Clay claim. Evidence:
`audits/AUDIT-WILSON-COMPLEX-RESPONSE-FLOOR-2026-09-24.md` at repository root.

`CRealSeminormPairingCompletion.completedInner_diagonal_le_normCeiling`
transports the existing computed per-stream ceiling to the completed
diagonal. `centeredVector_norm_ceiling` and
`dyadicExcitation_norm_ceiling` specialize it to actual centered Wilson and
padded dyadic-square states. These caps depend on the supplied expression,
width and nome; they are not uniform scaling bounds and do not provide a
response floor or continuum result. Evidence:
`audits/AUDIT-WILSON-COMPLETED-NORM-CEILING-2026-09-24.md` at repository root.

`BF4WilsonAllNomePlaquetteTwoStepResponseCore` now squares the checked
same-carrier one-step plaquette response using completed Cauchy--Schwarz and
exact time balance. `BF4WilsonAllNomePlaquetteTwoStepResponse` divides by the
actual completed diagonal ceiling and returns a positive explicit lag-two
floor; `BF4WilsonAllNomePlaquetteTwoStepResponsePadded` transports it through
spatial-face inclusion. These are fixed nome/width certificates only: their
focused checks are axiom-clean within `{propext, Quot.sound}`, while scaling,
continuum, physical-mass and Clay obligations remain open. Evidence:
`audits/AUDIT-WILSON-PLAQUETTE-TWO-STEP-RESPONSE-2026-09-24.md` at repository
root.

`BF4WilsonAllNomePlaquetteRateCalibration` composes the same-carrier positive
lag-two floor with the existing completed strict transfer bound and diagonal
ceiling, proving the explicit rational constraint
`twoStepFloor ≤ twoStepRate * plaquetteNormCeiling`. This remains fixed in
nome and width and is not a physical mass or continuum calibration. Evidence:
`audits/AUDIT-WILSON-PLAQUETTE-RATE-CALIBRATION-2026-09-24.md` at repository
root.

`BF4WilsonAllNomePlaquetteRelativeFloor` normalizes that same lag-two floor by
the actual completed diagonal ceiling and proves a positive Rayleigh-style
lower witness for the true `T²` matrix coefficient. It then cancels the
positive plaquette norm floor to obtain `relativeFloor ≤ twoStepRate` and
strict positivity of the fixed-parameter rate. This remains nome/width/face
dependent and is not a uniform mass or continuum result. Evidence:
`audits/AUDIT-WILSON-PLAQUETTE-RELATIVE-FLOOR-2026-09-24.md` at repository
root.

`BF4ExactSlabFixedSpatialTwoStepRateWidthObstruction.no_width_uniform_computed_twoStepRate`
proves that the existing computed `twoStepRate = mixRate^2` exceeds every
rational `0 ≤ q < 1` at an explicit positive width. This is an honest
obstruction to treating the fixed-width scalar rate as spacing-uniform; it is
not a refutation of the actual transfer operator or a Yang--Mills result.
Evidence:
`audits/AUDIT-WILSON-TWO-STEP-RATE-WIDTH-OBSTRUCTION-2026-09-24.md` at
repository root.

`BF4WilsonAllNomeOriginComplexCutoff.origin_twoStepRate_positive` consumes the
literal origin plaquette after two explicit padding layers and discharges the
strict positivity premise for the existing complex rate. Its companion
`origin_complexRateCutoff_bound` supplies the `powBaseCutoff` coefficient
modulus for every positive rational target. This remains a finite
nome/width-dependent certificate; it does not provide a spacing-uniform rate,
continuum survival or physical mass gap. Evidence:
`audits/AUDIT-WILSON-ORIGIN-COMPLEX-CUTOFF-2026-09-24.md` at repository root.

`BF4WilsonAllNomeDyadicRelativeSurvival` consumes the actual padded dyadic
square's completed norm floor and centered loss. Its
`dyadic_response_floor_of_relative_energy` returns a positive same-carrier
response under an explicit relative-energy budget, while
`dyadic_relative_energy_of_loss_budget` composes the existing cubic loss bound
with an explicit SAME-norm budget and constructively cancels the factor two.
The budget remains open along changing scale; this is not a uniform gap or
continuum result. Evidence:
`audits/AUDIT-WILSON-DYADIC-RELATIVE-SURVIVAL-2026-09-24.md` at repository root.

`dyadic_relative_energy_of_rational_loss_budget` further reduces that input to
the explicit rational inequality
`dyadicLossBound ≤ 2*delta*starRatio w`, using the existing norm floor. This
removes quotient-real budget plumbing but does not prove the inequality along
scaling. Evidence is recorded in the same audit.

`BF4WilsonAllNomeDyadicRationalBudgetObstruction.no_rational_loss_budget`
checks the arithmetic obstruction behind that open premise: for the explicit
cubic formula and any `rho ≤ 1-w`, no admissible `delta,theta` can satisfy
`dyadicLossBoundFormula ≤ 2*delta*rho`. The theorem is deliberately
parameterized by `rho` and does not identify it with `starRatio` without a
separate defect instance. This compares certificate numbers only; it is not
a lower bound on the actual completed loss, a uniform gap, or a continuum
result. Evidence: `audits/AUDIT-WILSON-DYADIC-RATIONAL-BUDGET-OBSTRUCTION-2026-09-24.md`.
The same module's `CoarseBudgetData` is a Type-level witness bundle for that
proposal, and `coarse_budget_data_empty` proves constructively that the bundle
is uninhabited whenever `0 < 1-w`.

`BF4WilsonAllNomeTwoStepMargin` adds the backward calibration on the SAME
completed carrier: a nonzero vacuum-complement state with relative lag-two
loss `delta` forces `1-delta ≤ twoStepRate`, equivalently
`1-twoStepRate ≤ delta`. This constrains the fixed-parameter rate but does not
construct the loss estimate or identify a physical Hamiltonian edge. Evidence:
`audits/AUDIT-WILSON-TWO-STEP-MARGIN-2026-09-24.md` at repository root.

**SAME real scaling, vacuum projection and connected correlators (2026-09-24 UTC):**
The existing all-nome Wilson completion now has real scaling with explicit
QCauchy scalar data, proved algebraic laws and actual-time compatibility.
`BF4WilsonAllNomeUnitProjection` computes the actual unit projection and
centers arbitrary completed states, with the exact same-operator identity
B(Cx,T(n)Cy)=B(x,T(n)y)-B(x,U)*B(U,y). `BF4WilsonAllNomeCenteringPin`
identifies this with the previously constructed dense centered vectors.
No representative is chosen from a quotient. This is fixed-parameter
algebra, not useful scaling control or full Hilbert/OS/QFT closure.
Five narrow checks passed 56 permitted gates; no full-root audit. Evidence:
`audits/AUDIT-WILSON-REAL-SCALING-PROJECTION-2026-09-24.md` at repository root.

**Preceding iterated channel-floor limitation (2026-09-24 UTC):**
`BF4DyadicChannelFloorObstruction` proves that the proposed floor
rho_L=(1/2)*w^(L*M(w)) is at most (1/2)*(1-w^L)^2 for 0<w<1 and L>=2.
Any coefficient paying the current quadratic remainder through this number
is at least 1920. No original-partition comparison or physical energy lower
bound is asserted. The useful SAME signed-aggregate/centered-variance scaling
estimate remains open; this candidate normalization cannot provide a small
coefficient. One narrow check passed seven permitted gates; no full-root audit.
Evidence: `audits/AUDIT-DYADIC-CHANNEL-FLOOR-2026-09-24.md` at repository root.

**Preceding original growing-square spectator-channel budget (2026-09-24 UTC):**
`BF4DyadicWilsonSquarePassiveChannels` proves the exact original energy and
odd-moment/mass decomposition with every spectator heat factor retained.
`BF4DyadicWilsonSquareChannelCost` evaluates the complete signed cost in
these actual computed channels. `ChannelGeometry` constructs the actual
fundamental cap four and proves A>=0 and G=4A-M>=0; `ChannelBudget` gives
4E+D_ch<=2*(8*(1-w^L)*G+960*(1-w^L)^2*A), with K>=2 and 0<=w<=1.
A is the heat-retaining conditional channel quadratic, NOT the original
partition. The useful SAME centered-variance/scaling comparison remains open.
Five narrow checks passed 31 permitted gates; no full-root audit. Evidence:
`audits/AUDIT-DYADIC-WILSON-CHANNEL-BUDGET-2026-09-24.md` at repository root.

**Preceding original growing-word square heat and complete signed cost (2026-09-24 UTC):**
`SU2QuaternionProductHeatWilsonSpinTwo` proves original spin-two transmission
with w^(8*perimeter), preserving ordered prefixes, remaining heat factors and
arbitrary supported tests. Its fundamental-square image is 1+w^(8*perimeter)*chi_2.
`BF4DyadicWilsonSquareQuadraticHeat` derives b=w^(32*L) for the actual padded
square and evaluates the full original terminal formula:
4E+D=2*((1-2*w^(12*L)+b)*H[q*q*f*f]+(1-b)*H[q*q]).
The actual projected source q and signed correction D remain. Useful SAME
interacting variance/scaling control, physical survival and continuum closure
are not supplied. Six narrow checks passed nineteen permitted gates;
no full-root audit. Evidence:
`audits/AUDIT-DYADIC-WILSON-SQUARE-HEAT-2026-09-24.md` at repository root.

**Preceding original growing-word heat and signed cost (2026-09-24 UTC):**
`SU2QuaternionProductHeatWilsonWord` proves exact fundamental transmission
with multiplier w^(3*perimeter), preserving quaternion order and arbitrary
supported tests. `BF4DyadicWilsonSquareNodup` and `HeatImage` derive the actual
growing square's distinct indices, fringe independence and multiplier w^(12*L).
`BF4DyadicWilsonSquareSignedCost.paddedSquare_terminal_young_identity`
retains the original terminal source q and correction in
4E+D=2*((1-2*w^(12*L))*H[q*q*f*f]+H[q*q*P(f*f)]).
The square image remains literal. No interacting-transfer eigenvalue,
useful relative-variance estimate, or scaling survival is supplied.
Four narrow checks passed thirteen permitted gates; no full-root audit.
Evidence: `audits/AUDIT-DYADIC-WILSON-HEAT-SIGNED-COST-2026-09-24.md` at repository root.

**Preceding SAME nonzero dyadic Wilson family (2026-09-24 UTC):**
`BF4ExactSlabWilsonWordVariance` proves original selected-action variance
at least starRatio(w)*(1+mean^2), with the actual selected mean/partition.
`BF4DyadicWilsonSquarePlacedGeometry` supplies the exact moving-slice
geometry. `BF4WilsonAllNomeDyadicVariance` applies the bound to the actual
chainIds window sequence, not all ambient faces, and passes through the
existing joint limits to the SAME completed centered square. Its norm
is at least starRatio(w) for every fitting width/scale at fixed nome.
`BF4WilsonAllNomeDyadicExcitation.nonzeroExcitation` constructs the actual
nonzero family; its correlators and strict two-step bound use the existing
completed time. No cross-width identification, scaling-survival, physical
response or continuum theorem. The coarse floor/cubic-loss mismatch remains.
Five narrow checks passed 34 permitted gates; no full-root audit. Evidence:
`audits/AUDIT-DYADIC-WILSON-SAME-VARIANCE-2026-09-24.md` at repository root.

**Preceding original dyadic Wilson one-link moments (2026-09-24 UTC):**
`OriginalBlockCoordinateMoments` and `IndependentTailMoments` retain arbitrary
independent spectators in exact original-Haar first/second moments. The
literal-word locality and moment consumers derive the required independence;
`BF4DyadicWilsonSquareSingleLinkMoments` specializes them to the growing
padded square with explicit side/width/ambient guards.
`BF4DyadicWilsonSquareShiftedMoment.paddedSquare_shifted_complement_moment`
gives H[(chi-c)^2 R]=(1+c*c)*H[R] for every rational c and the unchanged
complementHeat R. This is an unnormalized complementary-action identity,
not full interacting variance or scaling survival. The incident-factor
comparison and SAME completed-variance/scaling join remain open; the
coarse starRatio/cubic-loss limitation is unchanged. Six narrow checks
passed twelve permitted gates; no full-root audit. Evidence:
`audits/AUDIT-DYADIC-WILSON-SINGLE-LINK-MOMENTS-2026-09-24.md` at repository root.

**Preceding SAME all-nome Wilson represented limits (2026-09-24 UTC):**
`BF4WilsonAllNomeDistance` proves the actual completed squared-distance laws.
`CauchyRows` instantiates computed diagonal limits using supplied inner and
outer moduli, with outer rate `R.modulus(epsilon/16)`. Limits are independent
of supplied representatives of the same points; actual discrete time
commutes with the limit. `limit_orthogonal` and `orthogonalLimit` prove closure
of the existing vacuum complement under these represented limits, using
the SAME sharp Cauchy--Schwarz and distance bound. No arbitrary quotient-row
selection, real-scalar extension, or full Hilbert/QFT closure is claimed.
`BF4DyadicWilsonSquareUniqueEdge` separately proves a literal head-tail
decomposition and selected underlying-link absence from the tail. The
original arbitrary-word Haar moments and useful scaling variance remain open.
Three narrow checks passed 40 permitted gates; no full-root audit. Evidence:
`audits/AUDIT-ALL-NOME-WILSON-REPRESENTED-LIMITS-2026-09-24.md` at repository root.

**Preceding SAME all-nome Wilson rational algebra and definite pairing (2026-09-24 UTC):**
`BF4WilsonAllNomeLinear` and `LinearLaws` construct explicit-modulus rational
operations and prove their laws on the existing completion. `BilinearTime`
proves bilinearity, actual time linearity and the exact signed double-correlator
formula, retaining all cross terms. `Geometry.completedInner_posdef` identifies
zero norm with the actual zero state; its strict-gap consumer rules out a
nonzero two-step fixed vector in the vacuum complement at fixed nome/width.
`TimeDifference` proves B(x-T(2)x,x-T(2)x)>=(1-q)^2*B(x,x) and supplies an
actual plaquette-difference state with positive norm floor at every positive
width. No arbitrary-filter nonvanishing, scaling survival, full real
Hilbert/QFT or continuum claim. Five narrow checks passed 61 permitted gates;
no full-root audit. A03/full J02 and all scaling/physical-mass obligations
remain open. Evidence:
`audits/AUDIT-ALL-NOME-WILSON-LINEAR-GEOMETRY-2026-09-24.md` at repository root.

**Preceding nonzero SAME all-nome Wilson excitation (2026-09-24 UTC):**
`BF4WilsonAllNomeCenteredVector` constructs rational centering with an explicit
mean modulus; its actual completed time correlations are the centered scalar
moments. `PlaquetteVariance` proves exact original mean/variance/response pins.
`PlaquetteExcitation.nonzeroExcitation` and `.positiveResponseExcitation`
return actual states and quantitative proofs, with no face-existence or
analytic activity assumption. The existing strict bound acts on these SAME
states. `centered_dyadic_loss_bound` retains the cubic budget on actual centered
square vectors, without supplying their missing scaling norm comparison.
`StarVarianceLossObstruction` proves the six-face floor is too small to pay
the available nome-linear loss budget; this limits that certificate pair,
not actual positive response. Four narrow checks passed 33 permitted gates;
no full-root audit. A03/full J02, scaling/continuum and physical mass remain open.
Evidence: `audits/AUDIT-ALL-NOME-WILSON-EXCITATION-2026-09-24.md` at repository root.

**Preceding strict bound on the SAME all-nome Wilson completion (2026-09-24 UTC):**
`BF4WilsonAllNomeSeparatedCovariance` proves the original connected lag
envelope for arbitrary intrinsic expressions. `CenteredMoments` obtains the
even-time positivity and dyadic laws by rational centering with explicit
approximation data; `DenseGap` removes the expression-dependent prefactor.
`CompletedGap.completed_twoStep_form_gap` gives B(x,T(2)x)<=q*B(x,x) for
EVERY unit-orthogonal vector on the existing literal-width completion.
The computed q=mixRate(w,width)^2 is strictly below one at fixed parameters.
No small-nome or face-span carrier is substituted. Spatial/spacing control,
centered survival, full Hilbert/QFT and continuum/physical mass remain open.
Four narrow checks passed 33 permitted gates; no full-root audit. Evidence:
`audits/AUDIT-ALL-NOME-WILSON-COMPLETED-GAP-2026-09-24.md` at repository root.

**Preceding all-nome SAME Wilson completion and time (2026-09-24 UTC):**
`BF4WilsonAllNomeCompletedInner` constructs the represented Cauchy completion
of the literal-width reflected form, with explicit pairing data and sharp
Cauchy--Schwarz. `BF4WilsonAllNomeTimeContraction` proves actual advance is
nonexpansive using the original finite interval cap and midpoint doubling.
`BF4WilsonAllNomeCompletedTime` descends the actual semigroup, proves its
fixed norm-one unit, invariant orthogonal sector, balance, contraction and
one-step positivity. Original loop moments and the dyadic absolute loss
bound are SAME-operator matrix coefficients. No older small-nome/face-span
completion is substituted. The strict-bound residue is now supplied above;
centered survival, full Hilbert/QFT, scaling/continuum and physical mass remain
open. Eight narrow checks cover
67 permitted gates; no full-root audit. Evidence at repository root:
`audits/AUDIT-ALL-NOME-WILSON-COMPLETED-TIME-2026-09-24.md`.

**Literal Wilson family and SAME reflected time pin (2026-09-24 UTC):**
`WilsonSquare.squareLoop` and `DyadicWilsonSquare` construct actual closed
words of side 2^s with assigned spacing 2^-s and explicit geometric modulus.
`BF4WilsonAllNomeReflectedForm` uses the literal-width ORIGINAL joint limit,
with symmetry, positivity and temporal-chart invariance at every 0<w<1.
`LoopTimePin.time_pairing_lag` identifies two advances with lag(m+n), and
`dyadic_reflected_loss_bound` consumes the existing increment estimate in
2*(F(x,x)-F(x,advance L x))<=384*L^3*(1-w). No face-span completion substitution, centered
norm floor or scaling/continuum claim. Four narrow checks cover 33 permitted
gates; no full-root audit. Evidence at repository root:
`audits/AUDIT-DYADIC-WILSON-REFLECTED-FAMILY-2026-09-24.md`.

**Coefficient limitation and sharp original-energy cap (2026-09-24 UTC):**
`EndpointEnergyCoefficientFence.normalizedCoefficient_ge_thirtyTwo` proves
that any delta with kappa(w)<=2*rho(w)*delta must satisfy delta>=32.
This concerns the computed certificate, not actual energy. The valid
original-partition floor remains available, but that coarse coefficient
cannot supply a small loss. `EnergyNormBound.energy_le_norm` independently
proves E(f)<=marginalPair(f,f) using ORIGINAL transfer positivity, with no
stationarity or late-cutoff assumption. `CenteredFringeExtraction.centered_error_energy_le_same_tolerance`
retains epsilon in the existing approximation's energy error, without
changing its modulus. No coercivity or scaling conclusion. Three narrow
checks cover 17 permitted gates; no full-root audit. Evidence:
`audits/AUDIT-ENDPOINT-ENERGY-COEFFICIENT-FENCE-2026-09-24.md` at repository root.

**Preceding original-partition floor (2026-09-24 UTC):**
`EndpointChannelHeatFloor.padded_channelNorm_le_originalPartition` proves
`rho(w)*Q_F(q)<=H[marginalWeight]` for the COMPLETE original source and its
SAME spectator channels. The computed positive rho and cutoff depend only on
nome; four active links bound the aggregate first Casimir moment by 24*C(w)^2.
`EndpointEnergyPartitionBound.padded_endpoint_energy_le_originalPartition`
then gives 2*rho(w)*E_original<=kappa(w)*Z with computed kappa(w).
SAME centered-variance and changing-spacing control remain open. Six narrow
checks cover 34 permitted gates; no full-root audit. Evidence:
`audits/AUDIT-CHANNEL-PARTITION-FLOOR-2026-09-24.md` at repository root.

**Preceding conditional-channel regularity and tail (2026-09-24 UTC):**
`FamilyChannelCone` proves mixed positivity using the actual heat kernel and
a spectator-only coordinate swap, retaining shared active links.
`EndpointChannelTail.projectedEndpoint_plaquetteChannel_highTail_small`
transfers the complete original source's computed epsilon-to-degree threshold
to the SAME channel-summed norm. Width/depth/sufficiently late cutoff remain
uniform at FIXED nome; signed channel sources need not be positive.
The joint retained-heat floor is now proved; SAME centered-variance/scaling
comparisons remain open. Six narrow checks passed 31 permitted gates; no full-root audit. See
`audits/AUDIT-CONDITIONAL-CHANNEL-TAIL-2026-09-24.md` at repository root.

**Spectator-retaining refinement (2026-09-24 UTC):**
`PassiveGeometricBudget` supplies the actual terminal-source energy bound;
`ChannelActiveMoments` preserves the SAME odd moments with exactly four active
heat blocks; `ChannelGeometricContraction` proves the new budget is no larger
than its raw predecessor. Channel-aggregated SAME-variance/scaling control is
still open. Four narrow checks passed 26 permitted gates; no full-root audit.
See `audits/AUDIT-PASSIVE-GEOMETRIC-LOCALIZATION-2026-09-24.md`.

**Original-energy geometric budget (2026-09-24 UTC):**
`BF4ExactSlabFixedSpatialSourceYoungGeometricBudget.padded_terminal_plaquette_signed_geometric_budget`
proves 4E+D<=16eps*C+1920eps^2*A, where A=H[q^2], C=H[q^2*(4-f^2)],
eps=1-w, and q is the complete ORIGINAL projected terminal source. The
positive-heat version gives 2E<=8eps*C+960eps^2*A. No source derivatives
or new analytic premise are used; SAME interacting-variance/scaling control
remains open. Three narrow checks passed 13 permitted gates; no full-root
audit/guard. See `audits/AUDIT-SOURCE-GEOMETRIC-BUDGET-2026-09-24.md`.

**Sharp complex pairing on the SAME completion (2026-09-24 UTC):**
`BF4ExactSlabFixedSpatialJointComplexCauchySchwarz.inner_cauchySchwarz`
and `BF4ExactSlabFixedSpatialJointComplexSharpContinuity.time_pairing_converges`
give the constant-one inequality and its explicit pairing-modulus consumer.
The original carrier and all supplied Cauchy data are retained. This is a
fixed-width Hilbert-space prerequisite, not full QFT or scaling closure.
Six focused leaf checks cover 22 permitted gates; no full-root audit/guard.
See `audits/AUDIT-SHARP-COMPLEX-PAIRING-2026-09-24.md` at repository root.

**Positive-source variance shortcut fenced (2026-09-24 UTC):**
`SU2QuaternionPositiveSourceVarianceFence.bare_loss_variance_bound_false`
checks the actual one-link counterexample with `q=1+(1+f)^2`, `w=1/2`,
`K=3`, SAME source moments and positive centered variance. The actual heat
also has an explicit quarter-floor certificate. Positivity alone does not
give the bare-rate comparison; no original terminal/YM counterexample or
scaling conclusion follows. Two narrow checks passed sixteen permitted gates;
no full-root audit. Evidence:
`audits/AUDIT-POSITIVE-SOURCE-VARIANCE-FENCE-2026-09-24.md`.

**Actual four-link square image and original energy cost (2026-09-24 UTC):**
`SU2QuaternionProductHeatSpinTwoPlaquette.productMap_spinTwoPlaquette_of_perm`
composes the four actual w^8 transmissions into w^32. The fundamental square
image and both original spatial-plaquette images are checked in supported-Haar
equivalence, not free coefficient equality. `SourceYoungExplicit` consumes
them in the original padded terminal-plaquette `4E+D=2J`, with full source
and correction retained. The explicit raw q-squared cost is not SAME
interacting variance. Seven narrow checks passed 24 permitted gates;
no full-root audit or new hole/axiom. Evidence:
`audits/AUDIT-FOUR-LINK-SQUARE-YOUNG-2026-09-24.md`.

**Previous selected-link checkpoint (2026-09-24 UTC):**
`SU2QuaternionSpinTwoHeatTransmission.selectedCharacterTwo_heat_pairing`
proves the w^8 transmission for K>=2 with every orientation and arbitrary
supported head-independent spectators. The retained substitution is computed;
radius removal uses the SAME Haar carrier, not coefficient equality.
The four-link w^32 image and signed-energy/SAME-variance scaling bound remain
open. Four narrow checks passed 17 permitted gates after a startup reserve
refusal and recovery; no new hole/axiom or full-root audit. Evidence:
`audits/AUDIT-SELECTED-SPIN-TWO-HEAT-2026-09-24.md`.

**Original-source Young identity (2026-09-24 UTC):**
`BF4ExactSlabFixedSpatialSourceYoung.projected_young_moment_identity` proves
`4E+D=2H[q^2(f^2+P(f^2)-2fP(f))]` on the unchanged original action and
projected terminal source. Positivity at the explicit heat cutoff gives
`2E<=J`, with no source derivatives. The raw q-squared weight is NOT the
original q*P(q) marginal; SAME-variance/scaling control remains open. Separate
scalar bounds do not identify the four-link spin-two heat image. Four narrow
checks passed eleven permitted gates after a safety stop and recovery;
no full-root audit or new hole/axiom. Evidence:
`audits/AUDIT-SOURCE-YOUNG-2026-09-24.md`.

**Angular-only shortcut refuted (2026-09-24 UTC):**
`SU2QuaternionAngularOnlyEnergyFence.angular_only_energy_bound_false`
kernel-checks an actual one-link energy counterexample with source `1+2*f^2`,
nome 1/2 and cutoff 3 satisfying the sufficient-cutoff guard. Energy is
97727/8192, while the proposed angular-only budget is 23/2. Positivity of the
source does not justify discarding the signed remainder. One narrow check
passed seven gates; no physical/continuum claim or full-root audit. Evidence:
`audits/AUDIT-ANGULAR-ONLY-ENERGY-FENCE-2026-09-24.md`.

**Actual path second moment and original derivative-cost consumer (2026-09-24 UTC):**
`SU2QuaternionCyclicCasimirSquare.full_squareMoment_eq_sweep` identifies the
original full-path second moment with the computed differential square.
Actual character-product/path eigenaction, self-adjointness and SAME-tree
reassembly prove this without a projector premise. The exact remainder is
bounded by `(1-w)^2` times that square. `PassiveChannelRemainderSobolev` and
the original BF4 padded-plaquette consumer contract only the two POSITIVE
remainder sums to active Casimir squares of the complete original source;
the negative channel remainder and all cross terms remain. This closes the
previous checkpoint's finite join, NOT SAME-variance/scaling control.
Six final narrow checks passed 22 permitted gates (eight existing); no new
hole/analytic premise, changed safety limit or full-root audit. Existing
semantic imports cover the new modules. Evidence:
`audits/AUDIT-PATH-SECOND-MOMENT-2026-09-24.md`.

**Exact spectator-remainder contraction (2026-09-24 UTC):**
`SU2QuaternionFamilyChannelLoss` bounds the actual conditional norm loss by
the passive angular cost. `ChannelAngularContraction` bounds channel Casimir
cost by the active cost. `RemainderChannelContraction` combines those bounds
with EXACT original kinetic recombination, proving coefficient-one contraction
of the positive remainder, also with spectator-independent insertions.
The original BF4 plaquette consumer contracts its two positive channel sums
and retains the negative one. No interacting-variance or changing-scale bound
is supplied; the global positive diagonals can still retain bulk-source costs.
Six final serialized 4 GiB checks passed 27 permitted gates (11 existing), with
no safety interruption, new hole/axiom, canonical-field change or full-root
audit. Evidence: `audits/AUDIT-REMAINDER-CHANNEL-CONTRACTION-2026-09-24.md`.

**Exact remainder form and original energy bound (2026-09-24 UTC):**
`SU2QuaternionCyclicCasimirBilinear` proves symmetry and test-side algebra;
`ExactRemainderForm` identifies the actual Taylor remainder with a positive
symmetric bilinear form and proves sharp Cauchy--Schwarz. `ExactRemainderEnergy`
polarizes before estimating. `PassiveChannelRemainder` and the original BF4
plaquette consumer retain the full channel weights and the favorable negative
diagonal, with no absolute mode-tree budget. The stronger version retains both
negative squares. This finite auxiliary form is not a physical OS completion;
useful SAME-variance/scaling control and all continuum/Clay joins remain open.
Five final narrow checks passed 23 permitted gates (five existing), after
memory-reserve interruptions and observed recovery at unchanged limits.
No new hole/axiom or full-root audit. Evidence:
`audits/AUDIT-EXACT-REMAINDER-FORM-2026-09-24.md`.

**Complete spectator-family angular contraction (2026-09-24 UTC):**
`SU2QuaternionSelectedHeatGramBessel` and `FamilyHeatGramBessel` extend the
coefficient-one estimate to arbitrary distinct valid blocks, at every finite
cutoff and 0<=w<=1, including independent squared insertions. The actual
`PassiveChannelAngularBudget` and original padded-plaquette consumer remove
the channel sum from the angular cost, retaining the full mixed remainder
sum. The raw q-squared Haar weight is not the interacting variance; the
changing-scale analytic comparison and continuum/Clay joins remain open.
Four final narrow checks passed ten permitted gates (four existing), after
replacing a detected classical core dependency with constructive range
distinctness. Two memory-reserve interruptions preceded safe recovery;
no threshold changed and no full-root audit ran. Evidence: full-family
follow-up in `audits/AUDIT-PASSIVE-HEAT-CHANNEL-LOCALIZATION-2026-09-24.md`.

**One-link channel Bessel bound (2026-09-24 UTC):**
`SU2QuaternionHeadHeatGramBessel` proves the exact shared-spectator pairing
and coefficient-one norm bound for the complete channel list of one head heat
factor, at every finite cutoff and 0<=w<=1. Its weighted consumer retains a
head-independent squared insertion. `ProductHeatGramLocality` proves actual
selected-block locality, not locality of the interacting source. The full
spectator-family bound is subsequently checked above; its raw Haar norm is
still not the original partition or SAME variance. Four final narrow checks
passed; no full-root audit or continuum/Clay closure. The one-link result is
recorded in the one-link follow-up to
`audits/AUDIT-PASSIVE-HEAT-CHANNEL-LOCALIZATION-2026-09-24.md`.

**Exact spectator-channel localization (2026-09-24 UTC):**
`SU2QuaternionProductHeatGramChannels.productHeat_gram_carrier` constructs
the actual finite weighted Gram list, with supported channel polynomials and
nonnegative weights. `ProductHeatPassiveChannels` preserves moments and full
energy after projecting each dressed source, not after discarding passive
heat. `BF4ExactSlabFixedSpatialPassiveChannels` supplies the ORIGINAL padded
plaquette consumer and its summed angular/mixed-budget bound. Channels are
not individually declared probability laws; common normalization and centering
remain unchanged. `ProductHeatSharpAngularDefect` separately proves the
factor-one ordinary product bound. Five serialized 4 GiB leaves passed
twenty-two permitted gates. The summed-budget/SAME-variance scaling estimate,
survival, EVERY-vector scaling gap and continuum/Clay joins remain open.
No full-root build/audit/guard. Evidence:
`audits/AUDIT-PASSIVE-HEAT-CHANNEL-LOCALIZATION-2026-09-24.md`.

**Original energy with one mixed remainder budget (2026-09-24 UTC):**
`SU2QuaternionCyclicDiagonalRemainder.pairRemainder_diagonal_nonnegative`
realizes each valid full degree path by its original product-character Gram
kernel. Finite nome-one prefix subtraction proves the branch selector; no
commuting Fischer-projector family is assumed. The actual consumer
`BF4ExactSlabFixedSpatialSourceTaylor.padded_plaquette_energy_le_angular_add_mixed_quadratic`
retains q=P_F(V*g) and replaces the two-budget estimate by the single mixed
budget `pairBudget(q,q*f^2)`. The same cutoff guard covers omitted modes.
This does not bound that source-dependent quantity against SAME variance
along changing scales. Five serialized 4 GiB leaves passed twenty-eight
permitted gates; a safety-preflight refusal was followed by memory recovery,
without weakening thresholds. No full-root build/audit/guard or Clay closure.

**SAME-carrier conditional survival/calibration (2026-09-24 UTC):**
`BF4ExactSlabFixedSpatialJointEnergySurvival.centered_response_floor` turns
the supplied one-state relative energy and `n*delta+theta<=1` into an
original connected-response floor. Its `margin_le_twice_relative_energy`
cancels the SAME positive norm to prove `1-twoStepRate<=2*delta`, without
a norm cap or sampling premise. `JointSurvivalCalibration` separately
constructs the sampled-response margin/logarithmic-rate ceilings on the
actual all-nome fixed-width carrier, with computed thresholds and TWO-step
spacing. Neither scalar is identified with a Hamiltonian spectral edge.
The changing-scale observable and useful SAME-variance bound remain inputs,
as does the separate EVERY-vector scaling estimate. Two serialized 4 GiB
checks passed twelve permitted gates; no full-root build/audit/guard.
See `audits/AUDIT-SURVIVAL-QUANTIFIERS-2026-09-24.md`.

**Full-product source cancellation (2026-09-24 UTC):**
`SU2QuaternionCyclicCasimirSweep` identifies the computed degree-path
coefficient with the differential sweep; weighted cyclic transport and
integration by parts cancel every first-order source derivative.
`SU2QuaternionProductHeatAngularTaylor.sourceFirstOrder_eq_weightedAngularEnergy`
gives exactly `sum_i H[a^2*Gamma_i(f)]`, with no joint-orthogonality premise.
`BF4ExactSlabFixedSpatialSourceTaylor.energy_le_angular_add_quadratic` and its
padded-plaquette consumer retain the original energy, q=P_F(V*g), and BOTH
quadratic remainder budgets. The weight q^2 is not identified with the odd
marginal. Useful SAME-variance and changing-scale control remain open.
Seven serialized 4 GiB leaves passed thirty-four permitted gates; no new
hole/axiom, canonical-frontier closure or full-root build/audit/guard.

**Original energy with exact inactive-source reduction (2026-09-24 UTC):**
`SU2QuaternionProductHeatProjectedSourceEnergy` projects the complete source,
preserving full energy and every inactive-independent insertion.
`BF4ExactSlabFixedSpatialProjectedSourceEnergy` pins this to the original
transfer and odd marginal; strict padding supplies the literal plaquette's
independence. Its angular estimate has no separate fringe residual, but
retains all projected-source derivatives and the signed source correction.
Useful SAME-variance/scaling control remains open. Five serialized 4 GiB
leaves passed twenty gates within {propext, Quot.sound}; no new hole/axiom,
canonical-frontier closure or full-root build/audit/guard.

**Represented complex limits and their pairing consumer (2026-09-24 UTC):**
`BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness` constructs limits
from supplied complex Cauchy representatives in the SAME actual norm, with
explicit rates, represented uniqueness and actual discrete-time compatibility.
`JointComplexPairingContinuity.pairing_converges` and `time_pairing_converges`
compute squared complex matrix-coefficient error moduli from supplied test
representatives. The continuity bound has an explicit factor two; sharp
complex Cauchy--Schwarz is not claimed and the strict gap rate is unchanged.
Two serialized 4 GiB leaves passed twenty-two permitted gates. No full-root
build/audit/guard; no full Hilbert/QFT, scaling or canonical-frontier closure.

**Positive heat-law angular/variance obstruction (2026-09-24 UTC):**
`QuaternionHaarHeatAngularVarianceObstruction.positiveCounterexample` computes
a nome and late cutoff, returns the actual exposed-holonomy heat positivity
certificate, and refutes a nome-uniform `E_h[Gamma(f)] <= C*Var_h(f)` bound.
The same-law variance and selected-link angular moment are pinned exactly;
`variance_le_eight_scaled_angular` shows the first-order angular budget does
not become a vanishing fraction of that variance. This is not a temporal
energy lower bound or the interacting odd marginal. Source-specific scaling,
survival and all continuum/Clay obligations remain open. Five serialized
4 GiB leaves passed forty permitted gates; no full-root build/audit/guard.

**Complex pairing and gap on the SAME joint carrier (2026-09-24 UTC):**
`BF4ExactSlabFixedSpatialJointComplexification` uses two copies of the actual
all-nome `JointCompletion`, proving positive definiteness, conjugate symmetry,
additivity, witnessed sesquilinearity and compatibility with discrete time.
`JointComplexGap` embeds the original vacuum, retains BOTH orthogonality
conditions, and proves all-integer-time positivity and the SAME norm/form
decay for every complex centered state. The rate still depends on nome and
width. Full complex Hilbert/OS/QFT, scaling and physical mass remain open.
Two serialized 4 GiB leaves passed thirty-eight permitted gates; no full-root
build/audit/guard. Accepted logs are recorded in `work_plan.md`.

**Centered Ward identity in the SAME odd marginal (2026-09-24 UTC):**
`QuaternionHaarCenteredLinearWard` proves the arbitrary-weight head-linear
identity, retaining its signed derivative-of-weight term. The actual
plaquette degree is constructed by `BF4ExactSlabFixedSpatialPlaquetteDegree`;
`BF4ExactSlabFixedSpatialCenteredWard.plaquette_centered_ward` pins the result
to the original `marginalWeight`, `oddMass` and centered `middleRatio` variance.
The weight is `(V*g_n)*g_(n+1)`, not `(V*g_n)^2`. Residual control and the
full temporal-energy join remain unproved. Three serialized 4 GiB leaves
passed fourteen permitted gates; no full-root build/audit/guard.

**SAME-carrier real-scalar algebra (2026-09-24 UTC):**
`BF4ExactSlabFixedSpatialJointRealScalarAlgebra` proves scalar addition,
multiplication, zero/one and negation laws for the existing `completedRealSmul`,
with explicit scalar Cauchy data. Exact norm/distance scaling and a real action
on the actual unit complement preserve the same pairing and discrete time.
The scalar witness constructors are reused without substituting their legacy
vector carrier. This is not arbitrary quotient-sequence completeness, full
Hilbert/OS/QFT or a scaling theorem. One serialized 4 GiB check passed fourteen
gates within {propext, Quot.sound}; no full-root build/audit/guard.

**Error-free original kinetic alignment (2026-09-24 UTC):**
`SU2QuaternionProductHeatExactAlignment` absorbs the finite fusion endpoint
at a computed cutoff and proves a `6*(1-w)` chordal bound relative to the
SAME full-product mass, accepting signed endpoint sources.
`BF4ExactSlabFixedSpatialExactKineticAlignment` consumes it with the original
spatial weight, terminal message, odd mass and existing normalized mean.
There is no cutoff-error term or width/depth coefficient. Nome dependence and
the missing same-Wilson-variance comparison remain. Four serialized 4 GiB
checks passed twelve permitted gates; no full-root build/audit/guard.

**Intrinsic inverse bound on the SAME carrier (2026-09-24 UTC):**
`BF4ExactSlabFixedSpatialJointNeumannBound.inverse_norm_centered_bound`
proves `||inverse x||^2 <= g^2 ||center x||^2`, with computed
`g=1/(1-twoStepRate(w,width))`, independent of the source. Completing a square
avoids division by a vector norm. The estimate supplies distance stability
and an approximate-preimage residual-to-error certificate. `JointNeumannAlgebra`
proves rational linearity, symmetry and discrete-time commutation. Nome/width
dependence remains; no physical Hamiltonian or continuum theorem is claimed.
Two serialized 4 GiB checks passed seventeen permitted gates; no full-root
build/audit/guard. See the bounded-inverse follow-up in
`audits/AUDIT-JOINT-NEUMANN-INVERSE-2026-09-24.md`.

**Exact discrete inverse on the SAME vacuum complement (2026-09-24 UTC):**
`BF4ExactSlabFixedSpatialJointNeumannInverse.inverse` is constructed by a
geometric Cauchy limit, actual residual continuity, and quotient descent by
uniqueness. `inverse_right` and `inverse_left` prove both inverse laws for
`I-T^2` on the actual completed unit complement. The finite-tail proof retains
every time-translate cross term; its Cauchy modulus covers q=0 without dividing
by q. The source-independent norm bound is now proved above; no Hamiltonian/
continuum claim is made. Five serialized 4 GiB leaves passed thirty-six permitted gates;
no full-root build/audit/guard. Evidence:
`audits/AUDIT-JOINT-NEUMANN-INVERSE-2026-09-24.md`.

**Represented completeness of the SAME joint carrier (2026-09-24 UTC):**
`BF4ExactSlabFixedSpatialJointPresentedCompleteness.PresentedNormCauchy.limit_converges`
constructs a limit and explicit convergence modulus measured in the actual
completed squared norm. The required representative comparisons are derived
from the existing pairing rate, not added as assumptions. Supplied candidate
limits are unique, and `JointPresentedLimitLaws.PresentedNormCauchy.mapTime_limit`
proves commutation with the existing discrete transfer. No quotient
representative selection, full Hilbert/QFT closure or scaling theorem is claimed.
Three serialized 4 GiB leaf checks passed twenty-three permitted axiom gates;
no full-root build/audit/guard. See
`audits/AUDIT-JOINT-REPRESENTED-COMPLETENESS-2026-09-24.md`.

**Finite local weighted heat with first-order source cancellation (2026-09-24 UTC):**
`SU2QuaternionHeadHeatWeightedTaylor.weightedEnergy_le_angular_add_quadratic`
proves `E(a,f) <= (1-w) H[a^2 Gamma(f)] + (1-w)^2 B(a,a*f^2)` for the actual
shared-spectator head heat. B is a computed mixed Casimir-squared budget,
not a source-independent constant. The existing sufficient-cutoff guard
covers omitted harmonic modes, without restricting the source degree to K.
The source derivatives cancel at first order; the diagonal defect is bounded
as a whole. Source-budget scaling and the full-product/physical joins remain
open. Three final 4 GiB leaf checks passed eleven permitted axiom gates;
no full-root build/audit/guard. Evidence:
`audits/AUDIT-LOCAL-WEIGHTED-HEAT-TAYLOR-2026-09-24.md`.

**Kernel score is not temporal energy (2026-09-24 UTC):**
`SU2QuaternionProductHeatScoreSource.productHeat_lower_score_eq_source_pair`
identifies a lower one-end response with `-B(Da,a*f)`. For a=1 it vanishes
for every signed direction and supported test. The actual one-link example in
`SU2QuaternionProductHeatScoreEnergyObstruction` has positive SAME mass and
jump energy at every cutoff meeting `relativeCutoff w 32 <= K`; its normalized
energy cannot be bounded above by any scalar times the squared one-end score.
The previous response/variance theorem remains valid. No physical Wilson
estimate or Yang--Mills claim is refuted. The live producer target is the
direct full mixed temporal form, with the SAME source/variance and useful
spatial/spacing behavior, not reversal of the score bound. Two focused
8 GiB checks, eight permitted gates; no full-root build/audit/guard. Evidence:
`audits/AUDIT-KERNEL-SCORE-ENERGY-DIRECTION-2026-09-24.md`.

**Actual whole-product score versus SAME variance (2026-09-23):**
`SU2QuaternionProductHeatScoreVariance.productHeat_normalized_coefficientSquare_variance_bound`
proves `(H[R*(D W)*f]/Z)^2 <= m*C(w)*S*Var_RW(f)` for the actual selected
product W, R=a(x)*a(y), certificate-nonnegative supported a and positive
Z=H[R W]. Both derivatives localize to the factor's selected block; product
curvature costs add. Finite Cauchy gives the coefficient-square budget S with
an explicit LOCAL term-count bound m, retaining repeated factors and terms.
Symmetry and signed Haar integration by parts make the score mean zero;
the existing polynomial centering therefore yields the exact SAME variance.
No automatic canonical-six-plane regrouping or useful scaling asymptotic is
claimed. The response is not identified with Wilson jump energy; the source
correction, physical-time/scaling and continuum/all-group joins remain open.
Eleven focused 8 GiB leaves passed thirty-three permitted axiom gates;
semantic import added, no full-root build/audit/guard. Evidence:
`audits/AUDIT-ORIGINAL-PRODUCT-HEAT-SCORE-VARIANCE-2026-09-23.md`.

**Preceding actual normalized local dual score (2026-09-23):**
`SU2QuaternionRelativeHeatDualScore.relativeHeat_normalized_dual_score_bound`
constructs the single relative-heat estimate with the same positive endpoint
source, same edge normalization, and arbitrary signed supported test. Positive
finite reciprocal polynomials plus an explicit vanishing-error modulus remove
the extra multiplier only after Haar integration; no completed reciprocal
observable is needed. Curvature and the integrated Hessian sign are supplied
by actual heat theorems. Cancellation adds no inverse-floor loss beyond the
existing nome-dependent C(w). The whole-product response estimate with an
explicit local multiplicity bound and SAME centered variance is now proved
above. The Wilson-energy comparison, scaling and physical/continuum/all-group
obligations remain open. Seven focused leaves, twenty permitted gates;
root imports added but no full-root build/audit/guard. Evidence:
`audits/AUDIT-ORIGINAL-HEAT-DUAL-SCORE-2026-09-23.md`.

**Actual local heat curvature (2026-09-23):**
`SU2QuaternionHeatLogCurvature.heatLogHessianBounds` constructs both
denominator-cleared mixed log-Hessian bounds for the original relative heat.
The actual second derivative is bounded using a positive character recurrence,
explicit degree-six/four Gaussian prefix budgets, and the relative scalar's
mixed cap 64. All block/plane overlap is allowed. The local curvature constant
is computed from w, not supplied; it has no cutoff or ambient-size factor.
Its nome dependence and cutoff onset remain explicit. Local normalized dual
score and whole-family response assembly are now checked above; the SAME
normalized Wilson-energy/variance comparison and scaling behavior remain open.
Five serialized leaves passed twenty-one permitted gates; no full-root
build/audit/guard. Evidence:
`audits/AUDIT-ORIGINAL-HEAT-LOG-CURVATURE-2026-09-23.md`.

**Whole signed-direction kinetic Hessian (2026-09-23):**
`SU2QuaternionProductHeatAngularHessian.productHeat_upperHessian_eq_neg_square`
identifies the upper second derivative of the actual selected product kernel,
integrated with both complete sources, with minus the kinetic square of the
full signed source derivative. `productHeat_upperHessian_nonpositive` proves
its sign for `0 <= w`, at every finite cutoff and valid selected list.
Simultaneous relative-heat invariance and arbitrary-block Haar IBP supply the
proof, without deleting mixed terms or introducing a direction-count factor.
The SAME normalized Wilson temporal/variance bound and all physical/continuum
joins remain open. Seven focused leaves passed twenty-four permitted gates;
no full-root build/audit/guard. Evidence:
`audits/AUDIT-SIGNED-KINETIC-ANGULAR-HESSIAN-2026-09-23.md`.

**Full mixed temporal form and finite locality fence (2026-09-23):**
`SU2QuaternionWeightedProductDualEnergy.full_jump_pairing` keeps both sources
in the actual mixed jump identity. `SU2QuaternionDisjointTemporalCrossTerm`
constructs a positive two-block heat example with disjoint observables already
centered in the same marginal, but normalized mixed energy `98/4097`, not zero.
This prunes automatic temporal orthogonality from static locality; it does not
refute a joint coefficient-square estimate or identify the diagnostic source
with physical V*g. The next producer must control the whole signed temporal
form against actual normalization/variance. Two focused leaves passed
twenty-eight permitted gates; no full-root build/audit/guard. Evidence:
`audits/AUDIT-DISJOINT-TEMPORAL-CROSS-TERM-2026-09-23.md`.

**Coefficient-one angular contraction under Haar averaging (2026-09-23):**
`SU2QuaternionSelectedHaarDerivative.ratDerivative_project_of_ne` proves
coefficientwise commutation on distinct original quaternion blocks.
`SU2QuaternionHaarFamilyAngularContraction.familyProject_angularSum_le`
combines it with Pythagoras to bound every projected block energy and their
sum by the original energy, without a block-count factor. The actual
`energy_le_fringeResidual_add_angular_add_correction` consumer uses the
COMPLETE `u=(V*g)*f`, preserving its inactive residual and signed correction.
No source derivative is removed. Relative source/residual/correction control
and all physical/continuum joins remain open. Four serialized leaves passed
thirteen permitted gates; no full-root build/audit/guard. Evidence:
`audits/AUDIT-HAAR-ANGULAR-CONTRACTION-2026-09-23.md`.

**Proper active product and original energy (2026-09-23):**
`SU2QuaternionHaarFamilyPythagoras` and
`SU2QuaternionProductHeatInactiveProjection` prove ordinary-Haar orthogonality
and the original partial/full-product pairing join. The resulting
`productMap_defect_le_projected_angular` retains the inactive residual square
and bounds the projected full-product defect. The actual consumer in
`BF4ExactSlabFixedSpatialProjectedAngularEnergy` now bounds the original energy
on `u=(V*g)*f`, retaining its signed correction. This is an upper bound with
explicit support, positive block count, coupling and cutoff guards; residual
smallness, derivative/correction control and all physical/continuum joins
remain open. Four serialized leaves passed thirteen permitted gates; no
full-root build/audit/guard. Evidence:
`audits/AUDIT-INACTIVE-PROJECTED-ANGULAR-ENERGY-2026-09-23.md`.

**Original full-product angular defect (2026-09-23):**
`SU2QuaternionProductHeatAngularDefect.productMap_range_defect_le_two_angular`
now gives `H(p*p)-H(p*P p) <= 2*(1-w)*sum_i H(blockAngularSquare i p)`
on the actual fully active n-block product, n>0, for supported signed inputs,
`0 <= w < 1`, and `sufficientCutoff w <= K`. The prefactor is independent
of n and K. `PositiveContractionProductDefect` uses a quadratic potential;
`SU2QuaternionCyclicRotationPeriod` and `SU2QuaternionCyclicAngularEnergy`
return the rotating reference and all local costs to the original carrier.
No inter-step commutation, spectral theorem or realization assumption.
The sharper factor-one target stays open, as do quantitative inactive-residual
and signed-correction control, physical-time/scaling and all continuum
obligations. Four narrow checks passed sixteen permitted gates. Evidence:
`audits/AUDIT-PRODUCT-HEAT-ANGULAR-DEFECT-2026-09-23.md`.

The entries below record preceding checkpoints; their open product-defect
claims are superseded by the factor-two estimate above, not by a physical gap.

**Original product map as a conditional-link sweep (2026-09-21 UTC):**
**All-cutoff actual norm bounds (2026-09-23):**
`SU2QuaternionHeadHeatPositiveContraction` proves bilinear symmetry of the
computed `headMap`, its positive form interval, and
`headMap_square_le_pair`, using rational form Cauchy--Schwarz. For supported
polynomials and rational `0 <= w <= 1`, no cutoff onset or pointwise heat
floor is needed. `SU2QuaternionProductHeatCyclicContraction` transports the
norm bound through actual cyclic steps to the ORIGINAL full-range product
operator at every K. The multiplier is 1: no strict gap, angular defect
telescope, interacting estimate or physical/continuum closure follows.
See `audits/AUDIT-HEAD-HEAT-ALL-CUTOFF-CONTRACTION-2026-09-23.md`.

**Ordinary-head factorization (2026-09-23):**
`SU2QuaternionHeadHeatSpectatorEquivariance` proves the actual `headMap`
commutes with any block involution fixing its active head. The concrete
consumers `cycleReturn_step_headMap_carrier` and `cycleStep_headMap_carrier`
remove the tail-reversal conjugation: C=R headMap under every Haar insertion
on the supported carrier. These algebraic identities hold at every w,K.
Two focused checks passed seven permitted gates; the remaining target is
distinct-update commutation and the full-product angular defect, not another
operator-realization assumption. Evidence:
`audits/AUDIT-HEAD-HEAT-SPECTATOR-EQUIVARIANCE-2026-09-23.md`.

**Rotation-separated local estimate (2026-09-23):**
`SU2QuaternionProductHeatCyclicRotation.cycleReturn_step_carrier` identifies
the derotation of the actual fresh-output step with a computed conjugated
head map. `cycleStep_rotated_defect_le_head_energy` consequently bounds
`H(p*p)-H(cycleRotation p * cycleStep p)` by `(1-w)*H(blockAngularSquare 0 p)`
for supported inputs, `0 <= w < 1`, and `sufficientCutoff w <= K`.
Two explicit block reversals retain every spectator and signed pairing.
This closes the local rotation/estimate join, not the multi-step product
bound, inactive projection residual, interacting signed correction or any
physical/continuum obligation. Eleven public gates passed in two narrow
checks; see `audits/AUDIT-PRODUCT-HEAT-CYCLIC-ROTATION-2026-09-23.md`.

**Fresh-output replacement (2026-09-23):**
`SU2QuaternionProductHeatCyclicFold.productMap_range_cycle_carrier` proves
the fully active original product map is n computed cyclic steps: append a
fresh last output, integrate/remove the first source, repeat. The all-prefix
invariant uses n+m source variables and leaves n survivors; at m=n it returns
the original upper-slice ordering. The join preserves arbitrary signed
insertions, support, and (for n>0) the Haar mean. It assumes no selected-link
identification. Cyclic rotations are not positive local smoothing maps; the
full-product angular defect estimate and interacting/physical joins remain open.
Focused verification: `audits/AUDIT-PRODUCT-HEAT-CYCLIC-FOLD-2026-09-23.md`.

**Correction (2026-09-23):** The exact endpoint sweep identity below remains
valid. The subsequent universal selected-link/head-map identification is
refuted by `SU2QuaternionSelectedLinkHeadObstruction`, including admissible
cutoff guards. Its existing-neighbor projection is not fresh-head smoothing
with unchanged spectators. The corresponding conditional local-defect
compilers are not usable estimates; preserve their statements as a record.
The endpoint product operator, signed correction, and inactive projection
residual are the next quantitative targets, not those refuted certificates.

`SU2QuaternionProductHeatHybridSweep.hybridMap_carrier` proves the actual
operator join with every surviving insertion. The sweep retains all
spectators and its final integration includes inactive Haar projections.
Support, cleared lower slots, unused upper partners and pair commutation
are checked; the head step is literally the existing `headMap`.
`BF4ExactSlabFixedSpatialHybridEnergy.energy_eq_hybrid_add_correction`
retains the complete original signed source and endpoint correction.
This is an exact identity, not quantitative tensorization or a weighted
energy bound. SAME-variance, scaling, physical mass, QFT and every-group
obligations remain open. Three focused checks passed 16 permitted gates;
no new hole, axiom or full-root audit. See
`audits/AUDIT-PRODUCT-HEAT-HYBRID-SWEEP-2026-09-21.md`.

The same module now also proves `hybridMap_square` and
`hybridMap_centered_square_bound`: the all-insertion carrier identity
transfers the existing width-independent ordinary-Haar product contraction
to the explicit conditional-link sweep, with its `squaredHeatRate w` and
`headCutoff w ≤ K` guard unchanged. This is still not an OS/interacting
spectral gap or a continuum statement.

**Selected projection recoding (2026-09-22 UTC):**
`SU2QuaternionSelectedProjectionReindex.reindex_integrateQuaternionBlock`
proves coefficient-probe transport of an arbitrary selected quaternion Haar
projection through an explicit block involution.  The companion theorem
`exposeTranslationPair_project` composes the head and tail permutations and
identifies the doubly recoded selected projection with the literal head
projection of `exposeTranslationPairPolynomial`, retaining all spectator
coefficients.  The focused check reports only `{propext, Quot.sound}` for all
five public declarations, including `reindex_project_haar` and
`reindex_project_pairing`, which make the transport usable under the finite
Haar functional and with an arbitrary right insertion.  The supported-carrier
form `reindex_project_pairing_carrier` also moves a supported original pairing
to the recoded selected block while reindexing its insertion.  This is a
finite carrier identity only: the angular
telescope, inactive-projection control, signed endpoint estimate, SAME-object
OS/GNS passage, continuum survival, physical mass, QFT axioms and every-group
construction remain open.  See
`audits/AUDIT-SELECTED-PROJECTION-REINDEX-2026-09-22.md`.

**Conjugated finite head defect (2026-09-22 UTC):**
`SU2QuaternionConjugatedHeadHeat.conjugatedHeadMap` transports the literal
head conditional update by an explicit quaternion-block involution, and
`conjugatedHeadMap_defect_le_angular` transports the checked finite Haar
angular defect bound to that recoded carrier.  Support, reindex
multiplicativity, and Haar invariance are explicit; the right-hand side is
the angular energy of the recoded polynomial.  This does not identify the
module's `conjugatedHeadMap_pairing` and `conjugatedHeadMap_mean` also expose
the exact recoded `heatPair` and finite mean preservation.  This does not
identify the conjugated map with the physical interacting selected-link kernel, and does
not provide the missing product tensorization, SAME-object OS/GNS passage,
continuum survival, physical mass, QFT axioms, or every-group construction.
See `audits/AUDIT-CONJUGATED-HEAD-HEAT-2026-09-22.md`.

**Padded-safe angular block transport (2026-09-22 UTC):**
`SU2QuaternionAngularReindex.reindex_ratDerivative` proves that formal
coordinate differentiation commutes with an explicit quaternion-block
involution at coefficient level.  The stronger
`reindex_blockAngularSquare_haar` transports the complete six-plane angular
energy of any selected block through the recoding.  It uses prefix
equivalence and the finite Haar support guards, so it does not identify
trailing-zero-padded monomials by false raw list equality.  This is a finite
SU(2) carrier identity only: the interacting selected-link identification,
signed multi-factor covariance estimate, SAME-object OS/GNS passage,
continuum survival, physical mass, QFT axioms, and every-group construction
remain open.  See
`audits/AUDIT-ANGULAR-REINDEX-2026-09-22.md`.

**Selected-block defect corollary (2026-09-22 UTC):**
`SU2QuaternionConjugatedHeadHeatBlockEnergy.conjugatedHeadMap_defect_le_selected_block_energy`
joins the preceding two finite results: the conjugated head defect is bounded
by the Haar angular energy of the original block `s.map 0`, not merely by an
unidentified recoded energy.  The support guard is explicit and the proof
uses only nonnegative multiplication and equality transport.  This still
does not identify the conjugated map with the physical interacting
selected-link update, control signed multi-factor cross terms, or establish
the SAME-object gap, OS/GNS passage, continuum survival, physical mass, full
QFT axioms, or every-group construction.  See
`audits/AUDIT-SELECTED-BLOCK-DEFECT-2026-09-22.md`.

**Computed arbitrary-input harmonic decomposition (earlier checkpoint, 2026-09-21 UTC):**
`SU2QuaternionFischerDecomposition.decomposeHomogeneous` returns actual
finite radial-harmonic modes by degree recursion, with the explicit
positive denominator 4(k+1)(d+k+2) and signed coefficient reassembly.
`SU2QuaternionPolynomialHarmonicExpansion` splits arbitrary supported
input, respects padding and consumes the result in the original heat
pairing. `SU2QuaternionProductHeatHarmonicExpansion.productMap_selected_expansion`
reaches the ACTUAL product map without assuming input harmonicity; every
unselected factor remains. A computed fixed-input mode cutoff is not
uniform control of V_K*g_K*f. Signed weighted energy, spatial/scaling,
physical mass, full QFT and every-group joins remain open. Five focused
checks passed 54 gates within `{propext, Quot.sound}` and the dependency-
complete consumer target passed. No new hole/axiom or full-root audit.
Source, scope and next estimate:
`audits/AUDIT-CONSTRUCTIVE-HARMONIC-DECOMPOSITION-2026-09-21.md`.

**Actual product-kernel selected-factor join (earlier checkpoint, 2026-09-21 UTC):**
`SU2QuaternionSelectedHarmonicHeatTransmission.lean` transports all-degree
reproduction to arbitrary original block pairs and consumes it in the
actual `productMap` pairing. All untouched kinetic factors and an arbitrary
supported upper test remain. The substituted image is computed in the
original coordinate order with proved support; the cutoff guard stays
explicit. Degree is at the selected original block; harmonicity is tested
in its explicit exposing chart. This is not a harmonic decomposition of
V*g*f or a weighted energy estimate. Three focused checks passed 15 gates
within `{propext, Quot.sound}` and the dependency-complete consumer target
passed. No new hole/axiom or full-root audit. Scope and next mathematical
input: `audits/AUDIT-SELECTED-HARMONIC-TRANSMISSION-2026-09-21.md`.

**Exact all-degree original heat reproduction (earlier checkpoint, 2026-09-21 UTC):**
`SU2QuaternionRelativeHarmonicReproduction.lean` now proves the missing
dimension-normalized diagonal identity and combines it with all-label
selection. The FULL original two-link packet acts on a degree-n head
harmonic by `w^(n*(n+2))` times its computed retained-link substitution,
or zero when K<n, with every retained coefficient and arbitrary boundary.
Euler substitution, exact radial/factorial cancellation and the character
recurrence supply the normalization; it is not an input. Four focused
checks passed 19 gates within `{propext, Quot.sound}` and the dependency-
complete consumer target passed. This is a local kinetic identity, not
yet arbitrary-polynomial product propagation, changing-source cutoff
control or a weighted finite-time/SAME-variance estimate. The continuum/
physical-mass/QFT/every-group goal remains open. No new hole/axiom or
full-root audit. See `audits/AUDIT-HARMONIC-REPRODUCTION-2026-09-21.md`.

**Terminating actual-kernel harmonic recurrence (earlier checkpoint, 2026-09-21 UTC):**
`SU2QuaternionRelativeHarmonicLowering.lean` computes the original
partial Haar pairing with `(x.y)^n`, multiplied by its explicit radial
denominator, as the head-independent polynomial obtained by n applications
of `sum_i y_i*partial_(x_i)`. Degree drops and harmonicity survives each
step; all retained coefficients remain. The proof consumes the new
derivative-commutation and Gaussian harmonic-power recurrence modules.
Identifying that output with normalized substitution, hence the full
diagonal character reproduction, remains OPEN; no identity-at-nome-one
or finite-time interacting estimate is assumed. Three focused checks
passed 17 gates within `{propext, Quot.sound}` and the dependency-complete
consumer target passed. No new hole/axiom or full-root audit. See
`audits/AUDIT-HARMONIC-LOWERING-2026-09-21.md`.

**All-label two-link selection (earlier checkpoint, 2026-09-21 UTC):**
`SU2QuaternionRelativeHarmonicSelection.lean` proves that the actual full
heat packet paired with any homogeneous harmonic of degree d retains
only its label-d pairing (or zero when K<d), with all boundary variables
retained. It also proves exact `w^(d*(d+2))` dependence relative to the
same finite packet at nome one. The all-degree diagonal reproducing
normalization remains OPEN; nome one is not assumed to be the identity.
The supporting differential specialization and this consumer passed eight
axiom gates within `{propext, Quot.sound}` and a dependency-complete target.
No new hole/axiom or full-root audit. Source/remaining join:
`audits/AUDIT-ALL-LABEL-TWO-LINK-SELECTION-2026-09-21.md`.

**Exact original endpoint-weight cancellation (earlier checkpoint, 2026-09-21 UTC):**
`BF4ExactSlabFixedSpatialGroundStateEnergy.lean` writes the actual energy
for a=V*g as `H[(a*f)^2]-H[(a*f)*P(a*f)] + H[a*f^2*(P(a)-a)]`,
keeping the sign-indefinite correction and full original product kernel.
`QuaternionHaarWeightedAngularCancellation.lean` proves the local
differential identity `H[Gamma(a*f)]+H[a*f^2*L(a)]=H[a^2*Gamma(f)]`
by an explicit flux and Haar divergence cancellation. This holds for
signed a,f and is instantiated on the original source. It is not yet a
finite-time energy comparison. Inactive slots are Haar projections, so
the local angular L is not automatically the generator of the whole P.
The dependency-complete target and two focused checks passed eight gates
within `{propext, Quot.sound}`. No new hole, axiom or canonical field;
no full-root audit. The follow-up inventory locates the already-proved
concrete fringe reduction in `BF4ExactSlabFixedSpatialActiveEnergy`:
reuse its energy and marginal identities for the original terminal
messages, then address the missing all-label two-link operator pin. See
`audits/AUDIT-ENDPOINT-WEIGHT-CANCELLATION-2026-09-21.md`.

**All-label local angular Casimir (earlier checkpoint, 2026-09-21 UTC):**
`QuaternionHaarAngularCasimir.lean` proves the six-plane identity
`L = radius*Delta - secondEulerSum - 3*Euler`, hence `L p = -n(n+2)p`
for every harmonic homogeneous degree n on the SAME quaternion Haar
carrier. `SU2QuaternionHeadDerivativeEuler.lean` supplies the active-
derivative Euler calculation. `QuaternionHaarExposedHeatCasimir.lean`
uses existing harmonicity and degree producers to reach every ordinary
exposed character, then the actual finite heat prefix with its individual
label Casimir factors. Arbitrary Haar insertions remain; no coefficient
equality between solid and ordinary representatives is claimed.
Three focused checks passed ten gates within `{propext, Quot.sound}`.
This is not a heat semigroup or interacting transfer-energy comparison.
The small SAME-variance temporal bound, scaling survival, physical mass,
full QFT and every-group construction remain open. No full-root audit.
See `audits/AUDIT-ALL-LABEL-ANGULAR-CASIMIR-2026-09-21.md`.

**Relative Jacobi control of the ORIGINAL terminal source (earlier checkpoint, 2026-09-21 UTC):**
`BF4ExactSlabFixedSpatialTerminalJacobiAngularBound.lean` now proves
`B(w)*g +/- Dg >= 0` and `H[R(Dg)^2] <= B(w)^2 H[Rg^2]` for the actual
`g=T^(n+1)1`, every active link rotation and every certified positive R.
Here `B=32*JacobiShiftedRelativeSlope.budget w+1`. Positive-product
relative costs add; explicit differentiated Jacobi-weight removal reaches
the SAME original unweighted heat prefix. Its heat floor absorbs only
the approximation errors and enters the late cutoff, not B. Full spatial
action and terminal history remain in the message. B is independent of
width, depth and admissible cutoff but explicitly nome-dependent.
The dependency-complete target and eight direct checks passed 54 gates
within `{propext, Quot.sound}`; no new hole or canonical field. This is
source regularity, not the missing SAME-variance temporal energy bound,
changing-spacing survival or continuum theorem. No full-root audit.
See `audits/AUDIT-JACOBI-RELATIVE-ANGULAR-BOUND-2026-09-21.md`.

**Actual terminal-message angular control (earlier checkpoint, 2026-09-21 UTC):**
`BF4ExactSlabFixedSpatialTerminalAngularBound.lean` constructs both
`C(w)*g +/- h(w)*Dg` positivity certificates for the ORIGINAL `g=T^(n+1)1`.
Here D rotates any active link, `h=headFloor`, and
`C=heatDerivativeCap w 32`. Differentiation passes through the original
input Haar integral and hits only the matching kinetic factor; the entire
spatial action and terminal history remain. Multiplying the two certificates
gives `h^2 H[R(Dg)^2] <= C^2 H[Rg^2]` for any certified positive R.
The constants have no width, depth or cutoff power; the guard
`headCutoff w <= K` and all nome dependence are explicit. No near-one-nome
energy bound, completed derivative, spacing survival or continuum theorem
follows yet. The consumer target and seven direct checks passed 38 printed
gates within `{propext, Quot.sound}`. No new hole or canonical field.
See `audits/AUDIT-TERMINAL-ANGULAR-BOUND-2026-09-21.md`.

**Coefficient-level shortcut obstruction (earlier checkpoint, 2026-09-21 UTC):**
`SU2InverseHeatRemainderObstruction.lean` pins the four adjacent heat-weight
ratios to `(1-w^2)*(w^(-(2*j+3))+w^(2*j+1))` for physical labels j>=1.
`SU2InverseHeatRemainderUnbounded.lean` computes an escaping spin for every
strict nome and rational cap, so this separated remainder has no spin-uniform
bound even with nome-dependent constants. The full diagonal retains a
cancelling negative-square term. This is not an interacting `productMap`
eigenvector theorem or a Yang--Mills energy counterexample. It prunes the
separate-remainder estimate, not the original relative-energy frontier.
The consumer target and both direct checks passed 15 printed gates within
`{propext, Quot.sound}`; the index construction is axiom-free. One 20 GiB
worker; no full-root audit, new hole, analytic assumption or canonical-field
change. See `audits/AUDIT-INVERSE-HEAT-REMAINDER-2026-09-21.md`.

**Actual all-nome one-step positivity and whole-state temporal energy (earlier checkpoint, 2026-09-21 UTC):**
`BF4ExactSlabFixedSpatialSpanReversal.lean` identifies the common chart of an
arbitrary physical signed span and its one-step advance with the existing odd
kinetic product. Every signed coefficient and ordered face product is retained.
`BF4ExactSlabFixedSpatialJointTimePositive.lean` uses the original finite
kinetic/spatial quadratic and removes the chart's one extra slice only through
the proved boundary-limit padding law. It follows that the actual fixed-width
one-step map is positive semidefinite on the SAME `JointCompletion`, and every
integer-time autocorrelation `B(x,T^n x)` is nonnegative.

`BF4ExactSlabFixedSpatialJointTemporalEnergy.lean` applies this positivity to
the exact signed difference `x-Tx`. Its pairing is the discrete curvature
`r_n-2*r_(n+1)+r_(n+2)`, so the autocorrelation is convex and
`E_n(x)=B(x,x)-B(x,T^n x) <= n*E_1(x)` for every completed state, including
every finite signed `orbitSum`. Existing centering identifies the corresponding
connected scalar as nonnegative. `centered_relative_energy` is a conditional
consumer of a supplied SAME-variance one-step estimate; it does not produce
that estimate.

This milestone adds no near-one rate, changing-width/nome/spacing survival,
full Hilbert/Hamiltonian construction, all-group result, or continuum QFT
claim. A retained-weight double-commutator/carre-du-champ estimate is one
candidate route to the still-missing quantitative producer, not a proved
equivalent bridge. No hole, analytic assumption, or canonical field changed.
The dependency-complete
`+YMGap.Continuum.BF4ExactSlabFixedSpatialJointTemporalEnergy:olean` target
and three serialized direct checks passed all 21 printed gates (5 span
reversal, 6 time positivity, 10 temporal energy), within
`{propext, Quot.sound}`, without warnings or `sorryAx`. Checks used one
20 GiB-capped worker; no full-root audit was run. Logs:
`/tmp/ym-gap-joint-temporal-build.log`,
`/tmp/ym-gap-joint-span-reversal-check.log`,
`/tmp/ym-gap-joint-time-positive-final.log`, and
`/tmp/ym-gap-joint-temporal-energy-final.log`.

**Constructive real scalars and vacuum projection on the actual joint carrier (earlier checkpoint, 2026-09-21 UTC):**
`BF4ExactSlabFixedSpatialJointRealScalarCauchy.lean` uses a supplied
constructive-real rational stream and its supplied `QCauchy` modulus to scale
a supplied representative of the existing fixed-width `JointCompletion`.
Its explicit rate uses that representative's actual joint `normCeiling`;
neither a scalar nor vector representative is selected from a quotient.
`BF4ExactSlabFixedSpatialJointRealScalar.lean` descends this construction by
pairing separation, proves independence from equivalent scalar streams and
vector representatives, and proves compatibility with the existing completed
pairing, rational scaling, addition and physical time.

`BF4ExactSlabFixedSpatialJointVacuumProjection.lean` applies that real action
to the constructed coefficient `B(x,U)`. The resulting projection is
self-adjoint and idempotent on the SAME carrier, its complementary `center`
is orthogonal to the existing unit, and `centered_time_pairing` identifies its
time pairing with the pre-existing `completedCenteredScalar`.
`center_embedSpan` agrees with the earlier literal dense centering. The actual
strict two-step form bound proves `T^2 x=x` exactly when `x` lies in the unit
projection; `fixedScalarWitness` returns the scalar and its QCauchy data for
a supplied fixed representative, and coefficient one singles out U.
This is a discrete two-step fixed-space theorem, not a continuous
Hamiltonian or physical-mass statement. It adds no choice of representatives,
metric/Hilbert completeness, scaling limit, continuum QFT conclusion, new
analytic assumption, canonical field or hole. The dependency-complete
projection target and three final serialized direct checks passed all 62
printed gates (7 scalar-Cauchy, 11 real-scalar, 44 projection) within
`{propext, Quot.sound}`, without warnings or `sorryAx`. One explicitly
capped 20 GiB worker; no full-root audit was run.

**Actual joint geometry and finite approximate range for `I-T^2` (earlier checkpoint, 2026-09-21 UTC):**
`BF4ExactSlabFixedSpatialJointGeometry.lean` proves positive definiteness and
pairing extensionality on the existing all-nome fixed-width
`JointCompletion`. A zero completed diagonal constructs an explicit closeness
witness using the actual `pairRate`; subtraction pairings and equality from
all pairing tests therefore require neither quotient representative choice
nor identification with a stage-indexed carrier. Each supplied Cauchy
representative also carries its computed `normCeiling` bound.

`BF4ExactSlabFixedSpatialJointRangeApproximation.lean` constructs the finite
sum `x+T^2x+...+T^(2*(n-1))x`. Its approximation error after applying
`I-T^2` is exactly the tail `T^(2*n)x`; the existing strict unit-complement
norm contraction and the supplied representative's ceiling give a computable
epsilon cutoff, including the zero-rate branch. For the actual centered plaquette stream,
`plaquettePreimage` has the same explicit error and orthogonality pins, and is
nonzero whenever `0<epsilon<starRatio`. This is a finite approximate preimage,
not an exact inverse or a convergence theorem for the preimages. It supplies
no continuous generator, changing-width/nome/spacing control, physical mass,
or continuum QFT conclusion. No hole, canonical field or analytic assumption
changed. The dependency-complete consumer target and two final serialized
direct checks passed all 29 printed gates (13 geometry, 16 range/consumer)
within `{propext, Quot.sound}`, without warnings or `sorryAx`. Final checks
used one explicitly capped 20 GiB worker; no full-root audit was run.

**Actual all-nome rational linear joint carrier and finite orbit sums (earlier checkpoint, 2026-09-21 UTC):**
`BF4ExactSlabFixedSpatialJointLinear.lean` constructs addition, rational
scaling, zero, negation and subtraction directly on the existing
fixed-width `JointCompletion`. The finite-stage squared-distance estimates
are passed through `distSq_converges_joint`, and the generic completion maps
retain their explicit addition and scalar moduli. Finite-stage pairing
equalities at every cutoff give joint-limit nullity, so the rational additive
and scalar laws and the dense embedding pins descend without identifying
this carrier with a stage-indexed or legacy completion.

`BF4ExactSlabFixedSpatialJointBilinearTime.lean` proves bilinearity of the
existing `completedInner`, compatibility of completed physical time with
these rational operations, and constructs finite signed `orbitSum`s of time
translates. `orbitSum_pairing` is the exact double signed correlator sum
`sum_m c_m sum_n d_n B(x,T^(m+n)y)`, with every cross term retained in the
same original pairing. Unit orthogonality is preserved, so the existing
strict two-step form bound applies to each such filtered vector. Empty and
cancelling coefficient lists are allowed: no theorem says an arbitrary
filter is nonzero or produces a near-one Rayleigh witness. Metric/Hilbert
completeness, real-scalar extension, a full Hilbert-space/QFT construction,
and changing-width/nome/spacing survival remain open. No hole, canonical
field or analytic assumption changed. The dependency-complete
`+YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime:olean`
target and two final serialized direct checks passed all 48 printed gates
(28 linear, 20 consumer), within `{propext, Quot.sound}`, without warnings
or `sorryAx`. Sol supplied the linear construction, source inventory and
independent review; main supplied the pairing/time/smearing consumer and
serialized verification. One monitored 20 GiB worker; no full-root audit.

**All-nome fixed-width plaquette-orbit non-erasure (earlier checkpoint, 2026-09-21 UTC):**
`BF4ExactSlabFixedSpatialJointQuadraticForm.lean` proves positivity of the
scaled difference `x-rho*y` directly through the existing
`JointCompletion` pairing, without constructing new completed linear
operations. `BF4ExactSlabFixedSpatialJointOrbitResponse.lean` combines that
quadratic form with the existing time semigroup, time-balance identity and
sharp Cauchy--Schwarz inequality. It proves adjacent even-moment
log-convexity, propagation of any supplied nonnegative rational relative
two-step floor under pure time translates, and the corresponding even-time
geometric lower bound. These are time powers/translates, not finite-sum time
smearing or a spectral filter.

For the actual centered fundamental-plaquette excitation,
`BF4ExactSlabFixedSpatialPlaquetteOrbitResponse.lean` retains the existing
active-edge premise and its strict-padding discharge and proves
`timeNormFloor(n) = relativeFloor^n*starRatio` below the squared norm of the literal
time-`n` image. Since this rational floor is positive at every finite `n`, the
actual image is not the completed zero. Nome and width remain fixed, the
carrier and original pairing are unchanged, and no legacy thermodynamic or
spatial-union carrier is identified with them. This is finite-time
non-erasure, not fixed-physical-time survival or near-one calibration: the
proved coarse ceiling `relativeFloor <= 1/25` remains in force, and the
missing useful relative analytic producer is unchanged. No hypothesis,
canonical field or hole changed. The dependency-complete
`+YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteOrbitResponse:olean`
target and three final serialized direct checks passed all 17 printed gates
(3 quadratic-form, 7 orbit, 7 consumer), within `{propext, Quot.sound}`,
without warnings or `sorryAx`. Sol supplied the quadratic-form proof and
independent review; main supplied the orbit and concrete consumer proofs.
One monitored 20 GiB worker; no full-root audit.

**Checked limitation of the affine calibration route (earlier checkpoint, 2026-09-21 UTC):**
`BF4ExactSlabHeadFloorNomeCeiling` bounds the retained heat-head witness by
`(1-w)^2`. `BF4ExactSlabPlaquetteAffineCalibrationObstruction` consequently
proves `600*varianceFloor <= ((1-w)^2)^24` and
`computedLossRatio >= 115200`, where the numerator is the existing
single-plaquette `192*(1-w)` loss budget. Direct subtraction cannot certify
positivity, and a computed spacing threshold excludes a linear-spacing
bound for this ratio. These conclusions concern the certificates, not the
actual variance or response. Completed-family nontriviality is unchanged;
a useful SAME-action relative one-step estimate remains open. No canonical
field, hole or analytic assumption changed.
The dependency-complete obstruction target and two final direct checks passed
ten printed gates (3, 7) within `{propext, Quot.sound}`, warning-free and
without `sorryAx`. One monitored 20 GiB worker; no full-root audit.

**Selected-action affine and completed signed-family variance floor (earlier checkpoint, 2026-09-21 UTC):**
`BF4ExactSlabPlaquetteAffinePairing.lean` and
`BF4ExactSlabPlaquetteAffineCoercivity.lean` extend the boundary-dual
coefficient detector to every rational center while retaining the arbitrary
Nodup physical selected-action list and its own partition.  For every Nodup
physical plaquette family, at every finite stage with the late-cutoff guard,
the checked finite statement is
`L(w)/(600*U(w))*sum_p c_p^2 <= Var_W(sum_p c_p chi_p)`.
`BF4ExactSlabFixedSpatialPlaquetteFamily.lean` realizes the same signed family
as an exact radius-zero physical span and pins its first and diagonal second
chart moments to those literal finite selected-action moments.
`BF4ExactSlabFixedSpatialPlaquetteFamilyVariance.lean` passes the common
cutoff/boundary-time stream to the existing joint pairing and completed
carrier.  Its `familyExcitation_norm_floor` gives the same coefficient-square
floor for the completed centered-vector norm,
`familyExcitation_ne_zero` excludes zero when the budget is positive, and
`familyExcitation_correlator_pin` uses the existing completed physical time
and connected correlator for that same vector.

The constant has no additional width or family-cardinality factor at fixed
strict nome; the coefficient-square budget itself may grow, and different
widths still have different carriers.  No uniform bound as the nome changes,
spacing-limit survival, one-step/variance scaling comparison, full observable
algebra, continuum QFT, or extension to all compact simple groups is supplied.
No canonical field, analytic assumption or hole changed. The dependency-complete
`+YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilyVariance:olean`
target and six serialized final direct checks passed all 53 printed gates
(18, 9, 3, 11, 5, 7), including existing gates in the two edited support
modules, within `{propext, Quot.sound}` and without warnings or `sorryAx`.
Only three unchanged support proofs were exported and gated in those two
modules. Sol supplied the affine pairing, literal family pins, independent
review and supporting documentation; main supplied the coercivity and
completed-limit consumers. One monitored 20 GiB worker; no full-root audit.

**Actual centered variance coercivity for signed plaquette sums (earlier checkpoint, 2026-09-21 UTC):**
The new angular-family chain keeps the literal signed observable
`F = sum_f c_f chi_f`, the full interacting weight W, and the original
partition. Incident head-linearity and source pins reduce each selected-link
observable to its genuine degree-one head dependence. The exact six-direction
angular Casimir identity then reuses the existing full-square coercivity;
the all-physical-link incidence theorem counts each face through exactly four
edges. With `B = sum_f c_f^2`, `alpha = floorCoefficient`,
`beta = costCoefficient`, and `Cscore = scoreCoefficient`,
`BF4ExactSlabPlaquetteAngularFamily.variance_coercivity` proves

`(4*alpha(w))^2*B <= beta(w)^2*(21600*Cscore(w)^2)*Var_W(F)`

for `0<w<1` and `headCutoff w <= K`. All six angular directions are included,
and no extra extent or family-cardinality factor appears. The coefficients are
cutoff- and extent-independent at fixed nome, while `B` may itself grow. No
uniform bound as the nome changes is supplied. The positive rational
`varianceFloor(w,hw0) = (4*alpha(w))^2 /
 (beta(w)^2*(21600*Cscore(w)^2))` is checked and satisfies
`varianceFloor(w,hw0)*B <= Var_W(F)` at every extent and late cutoff. This is
centered variance under the original action, not an OS-transfer or continuum
estimate. The dependency-complete
`+YMGap.Continuum.BF4ExactSlabPlaquetteAngularFamily:olean` target and seven
serialized final direct checks passed all 40 gates (9, 7, 4, 6, 5, 1, 8), each within
`{propext, Quot.sound}`, with no warnings, errors or `sorryAx` in the new-file
logs. One monitored 20 GiB worker was used; no full-root audit was run. Main supplied the generic
Casimir and actual coercivity/variance consumers; Sol supplied incident
head-linearity/source pins, exact all-link incidence coverage, scalar support,
and independent review. No canonical field or hole changed. The
angular-to-SAME-completed-transfer one-step/variance scaling join, observables
beyond the fundamental plaquette span, changing-nome control, continuum
construction, and all compact simple groups remain open.

**Explicit whole-plaquette gradient score cost (earlier checkpoint, 2026-09-21 UTC):**
`QuaternionHaarSecondAngularBounds.lean` constructs coordinate, product and
Haar-carrier second angular-derivative bounds.
`BF4ExactSlabPlaquetteSecondAngularInterval.lean` gives the actual ordered
four-link scalar caps 2048 and 16384, hence fundamental-character caps 4096
and 32768. `BF4ExactSlabWardIncidenceSum.lean` supplies the local six-face
coefficient budget and global four-links-per-face incidence count.
`BF4ExactSlabPlaquetteGradientCost.lean` applies them to the exact signed
gradient tests under the SAME original full W and partition. For
`L_l = sum_{f incident to l}|c_f|` and
`C(w) = wardScoreCap w 4096 32768`, the checked bounds are
`E_W[S_l^2] <= 6*C(w)^2*sum_{f incident to l}c_f^2`,
`sum_l E_W[S_l^2] <= 24*C(w)^2*sum_f c_f^2`, and
`energySum^2 <= Var_W(F)*(25*(24*C(w)^2*sum_f c_f^2))` for a Nodup family.
There is no extra family-cardinality multiplier; the coefficient-square sum
itself may grow. At fixed nome, `C(w)` is independent of cutoff and extent
under `headCutoff w <= K`, but no uniform near-one nome bound is supplied. By
itself this is not a strict angular-energy/response floor or an OS/scaling
result. The current milestone above subsequently combines all six
nondegenerate directions and complete physical-link coverage with the existing
`family_partition_coercivity`; arbitrary fixed directions and empty families
remain outside that coercive statement.
The dependency-complete target and five final direct checks passed all 32
printed gates (4, 16, 2, 4, 6) within `{propext, Quot.sound}`, warning-free
and without `sorryAx`, on one monitored 20 GiB worker. In the existing
coordinate module, only two private helpers were exported and gated; their
proofs are unchanged. No canonical field or hole changed. No full-root audit
was run.

**Whole signed plaquette Ward-gradient energy (earlier checkpoint, 2026-09-21 UTC):**
`BF4ExactSlabPlaquetteGradient.lean` constructs
`F = sum_f c_f chi_f`, its incident part at each witnessed physical link,
and the original-coordinate pulled-back angular-gradient test. It proves
support, complete-star locality, and the coefficient identity
`D_l F = D_l F_inc`, retaining every signed coefficient.
`BF4ExactSlabWardGradientEnergy.lean` then proves under the SAME original
full action and common partition that one score response is the negative of
`H[R_l*A_l^2*(D F_l)^2]/H[W]`, where F_l is the whole F in link l's head
frame. The additional incident factor `A_l` is essential because the frame
weight is `R_l*A_l`.
`BF4ExactSlabPlaquetteWardEnergy.lean` sums this identity and proves
`energySum >= 0` and
`energySum^2 <= Var_W(F)*(25*sum_l E_W[S_l^2])` for Nodup witnessed
physical links. This does not give a strict response floor. The quantitative
diagonal bound is now supplied above; the current milestone supplies the
six-direction all-link angular lower comparison and centered-variance
coercivity. The SAME completed-transfer scaling join remains open. No scaling
ratio, OS gap or continuum closure is proved. The
dependency-complete target
and three final direct checks passed all 14 gates (6, 4, 4) exactly within
`{propext, Quot.sound}`, without warnings or `sorryAx`, on one monitored
20 GiB worker using default heartbeats. No full-root audit was run.

**Bounded-overlap original Ward-score family cost (earlier checkpoint, 2026-09-21 UTC):**
`QuaternionHaarSparseFamilyCost.lean` proves the exact normalized
full-sum-square/ordered-signed-Gram identity and a sparse-family bound.
`BF4ExactSlabWardStarGeometry.lean` defines the symmetric relation “equal or
contained in a common original physical face” and proves the conservative
row bound `25 = 1+6*4`. `BF4ExactSlabWardFamilyCost.lean` applies these facts
to a Nodup list of witnessed physical links with tests supported on their
complete stars. Off-star original-W covariances vanish, and the checked
bounds are
`E_W[(sum S_l)^2] <= 25*sum E_W[S_l^2]` and
`E_W[F*sum S_l]^2 <= Var_W(F)*(25*sum E_W[S_l^2])`.
The full interacting weight and actual positive partition are unchanged.
The coefficient 25 is independent of family, extent, cutoff and nome; the
diagonal sum can grow with the family, diagonal score bounds are nome-dependent,
and arbitrary test caps may depend on cutoff or extent. No response lower
bound, scaling ratio, OS gap or continuum closure is proved. The actual
incident-gradient family, exact energy response and quantitative diagonal
control are now supplied above; the current milestone supplies the resulting
six-direction coercivity for the complete physical-link family.
The dependency-complete target and three final direct checks passed all
21 printed gates within `{propext, Quot.sound}`, without warnings or
`sorryAx`, on one monitored 20 GiB worker. No full-root audit was run.

**Exact original Ward-score orthogonality (earlier checkpoint, 2026-09-21 UTC):**
`BF4ExactSlabOriginalWardLocality.lean` puts different selected-link scores
in common original coordinates and proves their cross moment is zero when
one selected link is excluded from the other score's entire star/test source.
Angular differentiation preserves that proved source support. The normalized
two-score cost is bounded by the sum of the diagonal cap-squares, with no
generic factor two and the SAME full action and partition. Distinct links
alone do not suffice. The bounded-overlap aggregation for the explicit
star-local Nodup family is now supplied above; unrestricted test families
are not covered. Useful response floors and spatial/nome scaling control remain open.
This is not spatial clustering or an OS gap. Three final checks passed all 15 gates within
`{propext, Quot.sound}`; no hole/field changes or full-root audit.

**Actual six-face Ward score cost (earlier checkpoint, 2026-09-21 UTC):**
`BF4ExactSlabLocalWardScoreBound.lean` now bounds the actual incident
product and its derivative using the at-most-six physical faces. Explicit
Leibniz recurrences give a score cap and hence
`normalizedResponse^2 <= Var_(R*A)(f)*scoreCap^2`, with the SAME full action,
partition and signed observable. The cap is independent of cutoff/extent
at fixed nome and fixed test caps; coordinate tests construct caps (1,2).
It is not uniform near nome one. Useful response floors and spatial/scaling
relative control remain open. Three final narrow checks passed all 15 gates
within `{propext, Quot.sound}`; Sol supplied scalar proofs and independent
review. No hole/field changes or full-root audit.

**Actual selected-link face derivatives (earlier checkpoint, 2026-09-21 UTC):**
`BF4ExactSlabPlaquetteAngularInterval.lean` constructs the previously
missing scalar-derivative input, retaining the exact ordered quaternion
word in the Ward frame. Tangential integration by parts transports
derivatives through original Haar-carrier equalities, including padding.
`BF4ExactSlabHeatAngularInterval.lean` consequently bounds the ACTUAL
reindexed face heat derivative by `4096*prefixBudget w`, independently
of cutoff and extent at each strict nome. Squared costs retain arbitrary
positive original backgrounds. The cap is not nome-uniform near one;
the incident-product/score cap is now supplied above, while response floors
and spatial/scaling control remain open. Five final narrow checks passed all 31 gates within
`{propext, Quot.sound}`; no hole/field changes or full-root audit.

**Original character/heat angular derivatives (earlier checkpoint, 2026-09-21 UTC):**
`QuaternionHaarCharacterDerivative.lean` proves the exact coefficient
chain rule using a positive lower-character expansion and constructs its
cubic Haar interval cap. `QuaternionHaarHeatAngularDerivative.lean`
then bounds the literal original heat-prefix derivative independently of
cutoff by `2*d*prefixBudget w`, given a certificate of cap d for the
original scalar derivative. The selected-link plaquette certificate is
now constructed above; the cap remains nome-dependent, not uniform as w approaches one.
Useful Ward response/score estimates and spatial/scaling joins remain
open. Three final narrow checks passed all 17 gates within
`{propext, Quot.sound}`; no hole/field changes or full-root audit.

**Actual normalized Ward variance comparison (earlier checkpoint, 2026-09-21 UTC):**
`SU2QuaternionAngularSupport.lean` supplies support and centering laws.
`BF4ExactSlabLocalWardVariance.lean` constructs positivity of the SAME
full W=R*A at the explicit late cutoff and proves
`E_W[A*g*(D f)]^2 <= Var_W(f)*E_W[S^2]`, with the actual computed mean
and S=A*(D g)+2*(D A)*g. Explicit partition, moment and variance pins
identify the selected-link frame with the original supported observable
and full action. The explicit score-cost estimate for the constructed whole-
plaquette gradient family is now supplied above, with its nome dependence
visible. The current six-direction complete-link milestone also supplies the
angular coercivity and original-action centered-variance floor; the required
SAME completed-transfer spatial/nome-relative control remains open.
Both final narrow checks passed
all 15 printed gates within `{propext, Quot.sound}`; no hole/field change
or full-root audit.

**Original-action local Haar identity (earlier checkpoint, 2026-09-21 UTC):**
`SU2QuaternionAngularDerivative.lean` and `SU2QuaternionHaarAngularIBP.lean`
prove exact tangential integration by parts for the original quaternion
Haar functional, preserving every tail coefficient.
`BF4ExactSlabLocalHaarWard.lean` pins the original full-action numerator
to the selected-link frame and differentiates only the actual incident
heat product A, retaining the entire complement R. The computed local
score `S=A*(D g)+2*(D A)*g` has zero R*A mean and satisfies
`H[R*A*(f*S+A*g*(D f))]=0`. No heat-weight inverse is used.
Useful response/score-norm estimates, the required one-step/variance
comparison and all spatial/scaling joins remain open. Three final narrow
checks passed all 15 printed gates within `{propext, Quot.sound}`;
no hole/field changes or full-root audit.

**Whole signed time-zero observable control (earlier checkpoint, 2026-09-21 UTC):**
`BF4WilsonTimeZeroOffsetLaws.lean` proves exact shift/reversal geometry
for the entire signed syntax. `BF4WilsonTimeZeroMomentConvexity.lean`
applies original site/bond reflection positivity to its adjacent difference,
uses joint-limit padding to identify both parities with lag-moment
curvature, and proves `timeIncrement_linear`: `I_n(F)<=n*I_1(F)` for
every `Within 0` expression. No coefficientwise estimate or family-size
factor is used. All strict nomes are allowed, at each fixed width.
The one-step energy/variance comparison, actual scaling family and
continuum survival remain open; ordinary and reflected whole carriers
are not identified by this result.
`BF4WilsonSignedPairTimeControl.lean` proves the exact source-square pin
to the preceding `combinedTimeIncrement` and its whole-pair linear bound.
Three final direct checks passed 16 printed gates within
`{propext, Quot.sound}`; no holes/fields changed or full-root audit.

**Mixed ordinary increments; exact signed combination (earlier checkpoint, 2026-09-21 UTC):**
`BF4WilsonJointOrdinaryCauchySchwarz.lean` proves square positivity, sharp
ordinary CS and rational homogeneity for the SAME original joint limit.
`BF4WilsonAllNomeMixedTimeIncrement.lean` applies these to two literal
time differences and bounds the squared cross moment by the product of
their explicit nome/lag/path-length budgets. The exact signed quadratic
expansion keeps `2*c*d*mixedTimeIncrement`; opposite copies of the same
loop cancel to zero. Neither ordinary/reflected pairing identification
nor spatial decay is assumed. Strict padding discharges both active-link
premises, without identifying states at different widths. The missing
spatially aggregated, relative-to-variance estimate and actual scaling
family remain open. Two final checks passed 12 printed gates within
`{propext, Quot.sound}`; no hole/field changes or full-root audit.

**Two-step response; coarse-witness scaling obstruction (earlier checkpoint, 2026-09-21 UTC):**
`BF4ExactSlabFixedSpatialJointCauchySchwarz.lean` proves sharp CS on the
existing bespoke completion, using its actual pairing limits.
`BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse.lean` combines this with
time balance, the proved one-step floor delta and a computed positive norm
cap P. It returns `twoStepFloor=delta^2/P>0`, its actual response bound,
and the homogeneous lower coefficient `relativeFloor=delta^2/P^2`.
`BF4ExactSlabFixedSpatialResponseFloorCeiling.lean` bounds the witness
numbers by `delta<=1/5`, `twoStepFloor<=1/25`, `relativeFloor<=1/25`.
`relativeFloor_no_linear_defect` gives an explicit spacing threshold
beyond which this witness cannot have defect at most `M*a`. These ceilings
do NOT upper-bound actual responses or Rayleigh quotients. They rule out
calibrating this particular coarse lower witness, not physical survival.
All three final checks passed 20 printed gates within `{propext, Quot.sound}`.
No holes/fields changed; no full-root audit. Spatial/scaling estimates,
physical mass, canonical OS/full QFT and all-group closure remain open.

**Positive response on the SAME existing completion (earlier checkpoint, 2026-09-21 UTC):**
`BF4ExactSlabFixedSpatialWindowEndpointMean.lean` and
`BF4ExactSlabFixedSpatialWindowCenteredProduct.lean` replace the varying
finite centered product by the two-point value minus its endpoint means'
product. `BF4WilsonAllNomePlaquetteConnectedFloor.lean` applies the existing
fixed-source joint convergence and stationarity to those three terms.
`BF4WilsonPlaquetteSourcePin.mixedProduct_mean` and
`BF4WilsonAllNomePlaquetteMeanPin.lean` identify the same completed mean.
`BF4ExactSlabFixedSpatialPlaquetteCompletedResponse.lean` concludes
`delta(w,width) <= B(v,T(1)v)` on the already constructed `faceExcitation`.
The existing explicit delta is positive; strict padding proves activity.
Nome/width dependence remains. No spatial/scaling survival or physical-mass
claim follows. All six final narrow checks passed the 14 printed gates
within `{propext, Quot.sound}`; no holes/fields changed or full-root audit.

**Cutoff/depth-uniform original response floor (earlier checkpoint, 2026-09-21 UTC):**
`BF4ExactSlabFixedSpatialPlaquetteDualCost.lean` computes the test cost
`w^(-12)+m^2` and bounds the actual marginal mean by [-2,2].
`BF4ExactSlabFixedSpatialResponseMassBounds.lean` retains the same
`M=H[V*T^n1]` in the detector floor `ell*M` and original partition cap
`U*M^2`. `BF4ExactSlabFixedSpatialPlaquetteUniformResponse.lean` cancels
that scale and constructs `ell^2/((w^(-12)+5)*U)>0`, independent of late
cutoff and terminal depth at least one. Nome/width dependence remains.
The SAME completed-response join is now proved above; spatial/scaling
survival and the Clay target remain open. Three final narrow checks passed all 23 gates within
`{propext, Quot.sound}`; no holes/fields changed or full-root audit.

**Positive original finite plaquette response (earlier checkpoint, 2026-09-21 UTC):**
`SU2QuaternionProductHeatPlaquette.lean` and
`BF4ExactSlabFixedSpatialPlaquetteKinetic.lean` prove the literal
four-active-link kinetic eigenvalue `w^12`, with activity discharged by
strict spatial padding. `SU2QuaternionProductHeatConstant.lean` fixes
constants under supported Haar tests. `BF4ExactSlabFixedSpatialPlaquetteHaar.lean`
gives bare mean zero, second moment one, and the arbitrary-center square
floor, using two unchanged density-variance lemmas now publicly exposed.
`BF4ExactSlabFixedSpatialPlaquetteResponsePositive.lean` constructs
`b=w^(-12)*f-m`, proves `P(b)=f-m`, and obtains a positive original finite
response from the preceding computed dual floor. The interacting endpoint
`V*T^n1` and original odd partition remain intact. The later result above
supplies the cutoff/depth-uniform floor and completed-response passage;
spatial/scaling survival is not concluded. Six final narrow checks passed all 35 printed gates within
`{propext, Quot.sound}`. No holes or canonical fields changed; no full-root audit.

**Computed original finite-response floors (earlier checkpoint, 2026-09-21 UTC):**
`SU2QuaternionProductHeatDualForm.lean` proves sharp Cauchy--Schwarz for
the actual kinetic product-map form and arbitrary signed supported inputs.
`BF4ExactSlabFixedSpatialResponseDual.lean` retains the full endpoint
`V*(T^n1*h)` and pins its quadratic to the existing original one-step
window numerator. Its computed `responseFloor` is nonnegative and no
greater than that SAME normalized response. It can be zero for arbitrary
tests; later modules above supply a detecting plaquette test and its
cutoff/time-uniform positive floor and completed passage. The spatial/scaling
join remains open. Both final checks passed all 14 gates within
`{propext, Quot.sound}`. No holes/fields changed or full audit.

**All-nome completed plaquette time control (2026-09-21 UTC):**
`BF4WilsonPlaquetteSourcePin.lean` and `BF4WilsonAllNomePlaquetteTimePin.lean`
identify the actual fixed-width joint plaquette pairing with the literal
Wilson lag moment, using the same finite window ratio and proved padding.
`BF4AllNomeCompletedPlaquetteIncrement.lean` gives completed centered loss
`0 <= B(v,v)-B(v,T(n)v) <= 192*n*(1-w)` on the existing `faceExcitation`.
`BF4AllNomePlaquetteDisplacement.lean` constructs the embedded literal
time-difference vector, proves unit orthogonality, and bounds its squared
norm by `384*n*(1-w)` via the original time contraction. Every strict nome
and padded width is allowed; no state equality across widths or carriers
is inferred. The existing variance floor does not imply positive-time
survival from these bounds. All four final checks passed the 15 public
gates within `{propext, Quot.sound}`; no holes/fields changed or full audit.

**Original all-nome multi-step Wilson increments (2026-09-21 UTC):**
`BF4WilsonJointFunctionalLaws.lean` proves signed linearity on the existing
original joint limits. `BF4WilsonAllNomeMomentConvexity.lean` combines their
padding stationarity with site and bond reflection positivity to prove
discrete convexity at every lag. `CRealDiscreteConvexity.lean` supplies the
constructive finite telescope, and `BF4WilsonAllNomeTimeIncrement.lean`
pins the literal squared difference to `2*(r(0)-r(n))`. The actual result is
`0 <= D(n) <= n*D(1) <= 24*n*L^2*(1-w)` for every `0<w<1`, fixed base loop
and strictly padded width. No new probability carrier, physical-time
calibration, spatial limit or variance floor is inferred. Four final
narrow checks passed all 35 public gates within `{propext, Quot.sound}`;
no holes/fields changed, and no full-root audit. Sol handled bounded
telescoping and independent scope/pinning reviews.

**Original Wilson joint-limit kinetic increment (2026-09-21 UTC):**
`BF4WilsonAllNomeKineticIncrement.lean` pins the literal adjacent-time
Wilson squared difference to twice the existing normalized Dirichlet
energy, then passes its bound through the EXISTING `originalJointLimit`.
`incrementCutoffStage` pays the signed expression's exact `4*L^2` cost
with a computed heat threshold independent of external depth and width.
`joint_increment_bound` removes the cutoff error. The scalar factorization
in `SU2FundamentalNomeDisplacement.lean` yields the bound `24*L^2*(1-w)`;
`nomeTolerance` and `padded_joint_increment_small` return its explicit
positive nome-defect tolerance. Fixed padded loops have the same bound at
every larger width, but their states are not identified across widths.
This is adjacent lattice time, not a fixed physical-time interval or a
variance floor. Both final narrow checks passed all 21 axiom gates within
`{propext, Quot.sound}`; no holes/fields changed, and no full-root audit.

**Original Wilson-loop kinetic increment (2026-09-21 UTC):**
`QuaternionHaarFiniteCauchyCertificate.lean`, `QuaternionHaarWordDifference.lean`,
`QuaternionHaarChordalDifference.lean`, and `QuaternionHaarWordLift.lean`
preserve ordered products and the full shared weight, giving squared
path-length control. `BF4ExactSlabFixedSpatialWilsonActivePadding.lean`
proves activity of each literal source edge at strictly larger width.
`BF4ExactSlabFixedSpatialWilsonKineticIncrement.padded_wilson_energy_tolerance`
then proves `2*normalizedEnergy <= 4*L^2*(2-2*w^3+epsilon)` for the SAME
fundamental Wilson character, original transfer, terminal messages and
existing odd partition. The computed cutoff depends on nome and tolerance,
not width or terminal depth. No variance lower bound, inter-width state
identification, new spectral gap, or continuum survival is supplied.
Seven final narrow checks passed all 44 gates within `{propext, Quot.sound}`;
no hole or frontier field changed, and no full-root audit was run.

**All-nome original kinetic alignment (2026-09-21 UTC):**
`SU2HeatNeighborConvexity.lean` and `SU2HeatFusionCoefficientPositive.lean`
prove nonnegative bulk coefficients using the original dimensions/Casimirs.
`SU2HeatFusionCutoffError.lean` computes a modulus for the remaining error
`(K+2)(K+1)*w^((K+1)(K+3))`.
`SU2QuaternionHeatFusionQuadratic.lean` uses SAME-endpoint quadratic
positivity, not pointwise character positivity.
`BF4ExactSlabFixedSpatialKineticAlignment.lean` supplies the actual product
kernel, `a=V*T^n1`, and existing positive odd-window partition, proving
`2*w^3 <= alignmentMean + epsilon` at an explicit late cutoff. Its constants
and threshold are independent of spatial width and terminal depth, but
depend on nome; there is no arbitrary-observable spatial variance bound.
Eight final narrow checks passed all 45 printed gates within
`{propext, Quot.sound}`. No hole or frontier field changed; no full-root audit.

**Original signed cross-term reduction (2026-09-21 UTC):**
`SU2QuaternionWeightedResidualOrthogonality.lean` proves that an actual
weighted residual annihilates link-independent tests.
`QuaternionHaarWeightedTestReduction.lean` computes a scalar subtraction
with exact Pythagorean accounting, including null directions.
`BF4ExactSlabFixedSpatialClearedCovarianceReduction.lean` applies both to
the SAME original temporal defect. Its full Cauchy budget is no larger
than the preceding raw-test bound. The gain can be zero; the remaining
norm and aggregate spatial/scaling control are still open. No original
weight, transfer or mean correction is removed. Four narrow final checks
passed all 16 axiom gates within `{propext, Quot.sound}`; no full-root audit.

**All-nome Wilson time-limit coupling checkpoint (2026-09-21 UTC):**
`BF4ExactSlabWilsonFiniteWindowCoupling.lean` and
`BF4WilsonAllNomeTimeCoupling.lean` compare the EXISTING original Wilson
`originalJointLimit` at two nomes throughout `0<u<=v<=W<1`. A finite time
pivot carries the original finite-face coupling estimate; two proved
geometric errors connect it to the infinite-time, cutoff-removed states.
There is no small-nome/entropy guard and no replacement carrier or operator.
The computed `comparisonDepth` makes both tail errors small, but width,
coupling and finite-pivot cost remain explicit. No spatial-uniform modulus,
continuum survival, physical calibration or OS/QFT closure is supplied.
The narrow target and 11 final direct axiom gates passed within
`{propext, Quot.sound}`, without warnings or `sorryAx`; no full-root audit.

**Descent-count / whole-old-guard scaling checkpoint (2026-09-21 UTC):**
`FiniteRootedAnimalPaddedDescentCode.lean` preserves the existing padded tour
and decoder while recording neighbor choices only on descent. The same
physical core family receives the smaller `96^m` count instead of `625^m`.
`BF4ExactSlabDescentDistanceDecay.lean` retains signed cancellation and the
actual partition square; its selected-covariance consumer cancels that same
normalization. `BF4WilsonDescentUniformConnectedDecay.lean` reaches the
original Wilson scalar, and `BF4WilsonDescentCompletedGap.lean` proves the
two-step form bound with constant `1/16` on the EXISTING `UnionCompletion`,
inner product, time map and unit complement. All old heat and 625-entropy
guards remain; no carrier or action is substituted.

`BF4WilsonOldGuardScalingObstruction.lean` now supplies an explicit
`scaleModulus` without a fixed nome ceiling or an extra common-rate input.
Throughout that OLD guarded region, a fixed polynomial squared-norm cap
`C*a_j^(-p)` forces the original centered response at positive INTEGER
physical time to vanish as the supplied TWO-step spacing tends to zero.
Thus approaching the old guard boundary cannot supply this survival.
Leaving that region and faster-than-polynomial norm growth are outside the
conclusion. Physical calibration, canonical continuum OS/full QFT, every
group and the Clay target remain open. All seven modules passed narrow
verification and 60 printed axiom gates within `{propext, Quot.sound}`,
without warnings or `sorryAx`; no full-root build/audit was run.

**Uniform lattice-rate scaling checkpoint (2026-09-20):**
`PhysicalSeparationSamplingEscape.lean` gives an explicit spacing escape
modulus: at positive integer physical time, `floorLatticeSteps` eventually
reaches every prescribed step count. `BF4WilsonUniformLatticeRateScalingObstruction.lean`
then proves that the original even-time Wilson autocorrelation, with nome,
carrier, and state allowed to vary, tends to zero when one certified upper
rate `q < 1` and one finite squared-norm cap `C` hold uniformly. A surviving
positive response floor forces the actual certified rate above every fixed
test `q`; `q` is an upper bound, not an exact spectrum. The concrete current
fixed-nome normalized Wilson excitation has zero-time norm one, while no
positive late-tail floor survives this scaling. Here `PhysicalSpacing` is the
duration of two original lattice steps; no one-step identification is built.
All 17 exported declarations passed direct axiom checks with only
`{propext, Quot.sound}` and no `sorryAx`. Changing-coupling variation,
physical normalization, continuum QFT, and all-group closure remain open.

**Original-Wilson survival ceiling checkpoint (2026-09-20):**
`PhysicalSamplingSurvivalMargin.lean`, `DirectLogMarginUpper.lean`, and
`BF4WilsonSurvivalPhysicalRateCeiling.lean` prove conditionally that a
same-state sampled positive response floor `f` and squared-norm cap `C` give
`(1-q)/a ≤ C/(f*(t/2))` once `a ≤ t/2`; after the computed tail threshold, the
exact binary logarithm obeys `-log(q)/a ≤ (9/4)*C/(f*(t/2))`. Here `C`, `f`,
and positive integer `t` are explicit inputs, `a` is the supplied duration of
TWO original lattice steps, and `q` is the actual certified upper rate, not a
spectral edge. No upper ceiling is assumed; the response floor remains an
input, not a constructed survival theorem. Existing
same-carrier finite-time lower bounds `rayleighFloor^n` do not supply a
uniform sampled floor. Cross-scale same-operator estimates, physical
normalization, positive physical mass, continuum OS/QFT, and all-group closure
remain open. The narrow build and all 23 direct axiom gates passed with only
`{propext, Quot.sound}`, no warnings and no `sorryAx`; no full audit was run.

**Guarded coupling escape checkpoint (2026-09-20):**
`BF4ExactSlabCouplingRateMonotonicity.lean` derives rate monotonicity from
the existing heat and collar formulas. `BF4WilsonGuardedCouplingEscape.lean`
then proves that bounded-norm survival of the same original positive-time
response forces the nome above every fixed guarded ceiling at a computed
threshold. A family remaining below one such ceiling has zero response
limits; the `W=1/1024` guard instance is already proved. This older result
alone does not exclude approaching the entropy-guard boundary. The newer
`BF4WilsonOldGuardScalingObstruction.lean` above excludes that route
throughout the OLD 625 guard under any fixed polynomial squared-norm cap,
with an explicit modulus. Faster-than-polynomial growth remains outside
scope. None of these results constructs physical calibration or a continuum
theory.
The narrow target and all 14 exported axiom gates passed within
`{propext, Quot.sound}`; no full-root audit or frontier closure is claimed.

**Centered coupling-response checkpoint (2026-09-21 UTC):**
`BF4ExactSlabCouplingCenteredResponse.lean` constructs a zero-mean normalized
heat-factor contrast under the retained original background. The exact
two-nome expectation change is its centered covariance with the observable,
and its square is bounded by observable variance times contrast second
moment. Positivity is constructed for all `0<u,v<1` at explicit late heat
cutoffs, including the actual shared-link spectator product. The subsequent
`BF4ExactSlabCouplingScoreBound.lean` now bounds the contrast variance with
an explicit coupling-dependent budget independent of cutoff, extent and
retained background. Its narrow build and all 11 direct gates passed.
This checkpoint alone gives no spatial summability; later entries below
construct it in a guarded region. No weak-coupling-uniform estimate,
changing-score limit, OS-norm identification or continuum closure is proved. The four touched
centered-response modules' 28 direct axiom gates and narrow dependency build
passed within `{propext, Quot.sound}`; no full-root audit was run.

**Isolated-defect spatial checkpoint (2026-09-21 UTC):**
`BF4ExactSlabCouplingSpatialResponse.lean` combines a constructed linear
score interval, its four-link locality, and exact background-mean cancellation
with the existing connected-distance bound. The full-slab instance changes
exactly one heat factor and proves its old endpoint is the original full
expectation. Cutoff and ambient face count do not enter the final budget.
The retained background is homogeneous and obeys explicit small-nome spatial
guards. The later isolated-defect sum below closes location summation, but
not heterogeneous paths or continuum control. The narrow build and all 17
direct gates passed within
`{propext, Quot.sound}`; no full-root audit was run.

**Summed isolated-defect checkpoint (2026-09-21 UTC):**
`Z4LinfShellCount.lean` and `Z4LinfGeometricSum.lean` combine explicit
four-dimensional ball counts with a computed blocking length. For every
`0<=r<1`, the finite location sum is bounded independently of volume, with
an explicit tail radius. `BF4ExactSlabSummedCouplingDefects.lean` applies
this to the actual isolated changes of the full original homogeneous slab.
The sum is not a heterogeneous path or a simultaneous many-face change.
All 23 direct gates and the narrow build passed within `{propext, Quot.sound}`;
no full-root audit was run. Continuum/OS and all-group closure remain open.

**Heterogeneous-background checkpoint (2026-09-21 UTC):**
`BF4ExactSlabHeterogeneousDistanceDecay.lean` proves the original connected
distance bound with independent face nomes and cutoffs. Constructed local
certificates, relative partition bounds and signed spectator resummation
feed the existing physical core count. The SAME varying-action partition
square is retained; one explicit small-nome ceiling and probe constants
control the budget. The next checkpoint supplies normalized coupling-path
consumption; viable continuum scaling, survival, calibration, OS/QFT and
every group remain open.
The narrow build and 36 direct gates passed within `{propext, Quot.sound}`;
no full-root audit was run.

**Actual spatial coupling-path checkpoint (2026-09-21 UTC):**
`BF4ExactSlabHeterogeneousCouplingResponse.lean` cancels the actual
partition and applies the existing mean-zero local score. The literal
two-nome schedule and `BF4ExactSlabSpatialCouplingPath.lean` telescope
through the true intermediate products. `BF4ExactSlabSummedCouplingPath.lean`
uses the proved four-dimensional location sum to bound the ONE simultaneous
change independently of cutoff and ambient face count. Its endpoints are
the original homogeneous full-slab expectations; its `pathRadius` is an
explicit modulus for selected distant changes. All coupling, probe, and
small-nome guards remain explicit; no scaling or continuum closure follows.
`BF4ExactSlabSpatialTwoNomeExpectationBound.lean` transfers the cap to the
pre-existing CReal expectations with the SAME fixed observable and no new
convergence assumption. All 21 printed gates across the five new modules
and the narrow dependency-complete target passed within
`{propext, Quot.sound}`, without warnings or `sorryAx`. No full-root audit
was run, and no canonical field or existing proof obligation changed.

> **Read `AGENTS.md` before contributing.** It contains both the
> non-negotiable constructivity rules and the host-safety contract. They are
> easy to violate accidentally; in particular, do not start a bare or broad
> Lean build on the development host.

---

## Why Lean, given that Lean is classical

Lean 4 and Mathlib admit `Classical.choice`, excluded middle, and
non-constructive existence as axioms. Left unconstrained, Lean will
happily prove `∃ x, P x` with no extractable witness. That is exactly
what this program forbids.

We therefore work in a **constrained fragment**:

1. Every load-bearing theorem is checked with `#print axioms` to
   confirm it does **not** depend on `Classical.choice`,
   `Classical.em`, `Quot.sound`-via-choice, or `propext` used to
   erase computational content. The maintained baseline is
   `AXIOM_AUDIT.md` (auto-generated; CI fails on drift).
2. Existence is stated using `Σ` (sigma types) / constructive
   existence, not `∃` (`Exists`), wherever a witness is required.
   `∃` is permitted only for genuinely propositional side conditions
   that carry no computational content.
3. Real numbers and moduli use the project's constructive reals
   (`Constructive/Reals.lean` and the `CReal*` modules) with explicit
   Cauchy moduli, not Mathlib's `ℝ` (which is classical via
   Cauchy-sequence quotients plus choice for completeness). Exact
   rational arithmetic lives in the project's `Q'`
   (`Constructive/Rationals.lean`); Lean core's `Rat` was rejected for
   load-bearing use because `Rat.decEq` depends on `Classical.choice`.
4. Estimates return the witnessing constant, not just its existence.
   A bound `μ ≤ C · exp(...)` is formalized as a function returning
   `C` together with the proof, not as `∃ C, μ ≤ ...`.

This is the same discipline as Bishop-style constructive analysis,
mechanized. The `#print axioms` gate is the enforcement mechanism;
see `AGENTS.md`.

**Substrate: MLTT / HoTT.** Lean is the Calculus of Inductive
Constructions, an extension of Martin-Löf Type Theory. We hold ourselves
to what is valid in MLTT and its homotopy-type-theory extension: the
only permitted axioms are `propext` and `Quot.sound` (both HoTT-valid —
`propext` is univalence for mere propositions, `Quot` is the set-quotient
HIT); `Classical.choice`/LEM (invalid in MLTT/HoTT) and `native_decide`
(trusts the compiler, not a kernel reduction) are banned. Because the
proof's worth is its computational content, we prefer **canonicity**:
axiom-free, `decide`-checkable proofs, and witnesses carried as
`Type`-level data (`Σ`, functions `ε ↦ N`) rather than erased inside a
proof-irrelevant `Prop` `∃`. See `AGENTS.md` Rule 8.

**No external dependencies.** The library is Mathlib-free — the Lake
manifest has zero packages. Everything builds from Lean core
(`leanprover/lean4:v4.29.1`, pinned in `lean-toolchain`).

---

## Folder structure

```
lean/
├── README.md                  # This file.
├── AGENTS.md                  # Constructivity contract — read first.
├── AXIOM_AUDIT.md             # Auto-maintained axiom-gate baseline.
├── SORRY_LEDGER.md            # Every sorry, logged. Currently: library is sorry-free.
├── CLASSICAL_LEDGER.md        # Every quarantined classical input (Rule 4). Currently empty.
├── lakefile.toml              # Lake build configuration (no external packages).
├── lean-toolchain             # Pinned Lean version (v4.29.1).
├── YMGap.lean                 # Selective semantic/reflection-audit root.
├── docs/                      # Lean-local design notes (KP limit, RG transport, ...).
└── YMGap/
    ├── Constructive/          # Group-independent constructive substrate:
    │                          #   Q' exact rationals; CReal with explicit moduli
    │                          #   (arithmetic, exp/log, sqrt/cbrt, trig, π, completion);
    │                          #   geometric/finite-sum machinery; SU(3) character-tail
    │                          #   factorization; soundness bounds.
    ├── RepTheory/             # Per-group representation data: SU2, SU3, Spin4 (+H₄
    │                          #   reflection data), CasimirData, RepData, SimpleGroup
    │                          #   (the compact-simple-G interface).
    ├── BufferShell.lean       # Single-plaquette buffer-shell tail bound (κ, β, C as data).
    ├── Sheaf/                 # Bound-witness sheaf framework: Site, BoundWitness
    │                          #   (flabby presheaf), Summability (KP certificates),
    │                          #   Gluing (domGlue_preserves_KP), PolymerDomination, SU2KP.
    ├── RG/                    # RG induction + the uniform-group reduction: BlockSpin,
    │                          #   InductiveState, PolynomialTree, production/directed
    │                          #   interface transports, stable-tail/dynamics certificates,
    │                          #   SigmaHatPilot(+UV), UniformBudget,
    │                          #   character-tail majorant/antitone chain, EtaPackaging,
    │                          #   SUNWeylData / WeylDimGeneral / RankCollapse.
    ├── MassGap/               # Headline composition theorems: SU2 (mass_gap_SU2),
    │                          #   SimpleGroup (mass_gap_simple_group).
    ├── Categorical/           # Site/presheaf/2-cell scaffolding; ScaleSheaf cocycles;
    │                          #   budget functors and closure transports.
    ├── Codynamic.lean         # Codynamic transfer template (EKF ↔ YM signature port).
    ├── HigherCategorical.lean # 2-categorical RG-flow packaging.
    ├── Continuum/             # The large continuum campaign: finite-volume
    │                          #   functionals and partition positivity (S2–S6), KP
    │                          #   increment engine, reflection positivity (OS2 via
    │                          #   Osterwalder–Seiler), OS axioms + reconstruction
    │                          #   interfaces, complete GNS Hilbert space, transfer
    │                          #   calculus, spectral gap/localization, Bakry–Émery and
    │                          #   codynamic floors, Mayer/Ursell/tree-graph reductions,
    │                          #   6j/pentagon track, O(4)/H₄ restoration groundwork,
    │                          #   AF-rate calibration, and the Tier-0 frontier files
    │                          #   (Tier0Scorecard, ContinuumFrontierScorecard,
    │                          #   FourDExistence, ...). Many `*Progress`/`*Close`
    │                          #   modules are stepwise reductions of named frontier
    │                          #   atoms — check `YMGap.lean`'s annotations and the
    │                          #   scorecard docstrings for load-bearing status.
    ├── Rubric/                # Machine-checked transcription of the Clay rubric:
    │                          #   ClayScorecard (fixed-spacing line PROVED; ClayTarget
    │                          #   deliberately uninhabited), ContinuumScorecard,
    │                          #   Loop/Reconstruction scorecards.
    ├── PolyAtlas.lean         # Compile-only expository/design scaffolding.
    ├── ModuliAlgebra.lean     # Compile-only expository/design scaffolding.
    └── ...
```

The dependency direction runs upward from `Constructive/` (depends on nothing
but Lean core) through `RepTheory/`, the lattice layers (`Sheaf/`, `RG/`,
`MassGap/`), into `Continuum/` and finally the `Rubric/` scorecards. Compile
coverage and semantic aggregation are deliberately separate:

- `lakefile.toml` explicitly sets `globs = ["YMGap.*"]`, so a full `YMGap`
  library build compiles every `YMGap/**/*.lean` module independently.
- `YMGap.lean` imports the single coherent semantic environment inspected by
  the axiom, frontier, and statement guards.
- The only modules outside that semantic closure are classified by the
  reviewed roots in `SEMANTIC_ROOT_EXCLUSIONS.txt`. At present those roots are
  `YMGap.ModuliAlgebra`, `YMGap.PolyAtlas`,
  `YMGap.Continuum.ScratchGraphFour`,
  `YMGap.Continuum.HarmonicLowerSixTailBaseSemanticFactors`, and the mutually
  incompatible alternative certificate modules
  `YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartA` and
  `YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateE8ChartAXPascal`.

The compile-only modules are still kernel-checked by the full library target;
they are kept out of the shared semantic environment because they are
non-load-bearing, dormant scratch/factor data, or declaration-colliding
alternative certificates. Any change to this set requires a reasoned manifest
change and review.

---

## Relationship to the rest of the repository

The Lean formalization mirrors, but does not replace, the Python
`computations/` and the LaTeX `formal/`:

| Concern | Python `computations/` | LaTeX `formal/` | Lean `lean/` |
|---|---|---|---|
| role | compute explicit constants | state the argument for humans | machine-check constructivity |
| trust | numerical, regression-tested | peer-readable | kernel-verified |
| output | the numbers $(\kappa, \beta, C, \rho, K, \ldots)$ | the prose proof | the certified theorem |

The intended workflow per milestone:

1. `computations/` produces the explicit constants and a numerical
   sanity check.
2. `formal/` states the argument in prose with those constants.
3. `lean/` certifies that the argument's existence claims are
   constructive, using the constants as inputs.

A milestone's Lean obligation is **not** "formalize everything" — it
is "formalize the *constructivity-critical* existence claims," i.e.
the ones where a classical proof would be unacceptable. The
`AGENTS.md` file lists which claims those are per phase.

---

## Safe local consistency checks

```sh
make lean-build  # from repository root; monitored full build
python3 scripts/safe_lean_build.py -- YMGap.MassGap.SU2
python3 scripts/safe_lean_build.py -- YMGap.Continuum.Tier0Scorecard
python3 scripts/safe_lean_build.py -- YMGap.PolyAtlas YMGap.ModuliAlgebra
```

Every PR-equivalent change must pass the monitored `make lean-build` and the axiom check
described in `AGENTS.md` (`make lean-audit` at the repo root; refresh
the baseline with `make lean-audit-update` only for deliberate,
reviewed changes).

---

## Current status (2026-07-03)

**Active BF4 milestone (2026-07-28).** The canonical retained spatial
carrier is now literal Lean data: 24 lower faces, 48 physical links, an
explicit 25-link tree, 23 chord coordinates, and the five transmitted chord
indices `{0,4,5,6,10}`.  Rational unit quaternions define the actual SU(2)
relative class coordinate and finite Cauchy--Schwarz proves its `[-1,1]`
range.  Complete source/target/path/factor locations, an explicit nonempty
identity carrier, and the 23-factor kinetic Harnack instantiation are in
`BF4CanonicalClassCoordinateCarrier`.

The closed-sheet route is now decisively classified.  The exact row-mass
budget makes binary-multicover existence constructively decidable, but
`BF4SU2OuterBinaryMulticoverNoGo` proves that the universal normality theorem
is false: a literal positive cutoff-two row has a four-link cocircuit
certificate excluding every binary multicover.  The same row is proved to
belong to the enumerated global joint carrier in
`BF4SU2OuterJointCarrierStrictEnlargement`.  Thus the live combinatorial
obstruction is not binary-sheet normality.

`BF4SU2OuterJointCarrierRawRowMass` identifies nonemptiness of the
four-preimage coarse carrier exactly with one scalar statement about that
specific BF4 row:
`wholeSlabJointCarrierCodes` has positive length if and only if the finite
sum of its nonnegative whole-slab recoupling weights is strictly positive.
The reverse implication is constructive: positive total mass selects a
positive coarse target, then positive face channels and shared-link fusion
witnesses.  It also constructs the literal normalized
`CoherentSlabRecouplingSource` and proves division-safe lower/upper order
transfer from raw numerator and partition bounds.
`BF4SU2OuterRawRowMassRetainedHarnack` conditionally feeds this scalar
certificate into the grouped retained Feynman--Kac floor.  The certificate
is not universal.  `BF4SU2OuterRawRowMassCounterexample` constructs a
positive cutoff-two fine row whose only nonvacuum coarse packet is
`(2,0,0,0)` and whose adjacent coarse packets are vacuum.  Every positive
face channel therefore produces the forbidden link word `(2,0,0)`.
Consequently the raw-row mass vanishes in the strict-order sense and
`SU2OuterRawRowMassPositive` is contradictory for the pinned geometry.

`BF4SU2OuterFineIntertwinerRetainedCarrier` makes the corrective pivot.
Before the lossy four-preimage projection, the literal finite fine
link-intertwiner carrier is canonically inhabited on every positive row.
`BF4SU2FineIntertwinerConditionalKernel` normalizes the exact unit-counting
Haar fiber on that carrier and proves partition positivity, nonnegativity,
strict member positivity, and row mass one.
`BF4SU2FineIntertwinerChoiCPOrder` then performs the all-label source/target
Choi contraction on the same retained carrier.  It proves exact conditional
expectation, finite and matrix-amplified Gram positivity, and lower/upper
Loewner domination from a pointwise window on the complete interior spatial
weight.  The collar row killing the old carrier is instantiated with row
mass one.
`BF4SU2FineIntertwinerPhysicalDisintegration` proves that this normalized
row is the conditional law of the literal production spin foam.  Its
partition is exactly the `Q'` image of the corrected-slab SU(2) link
multiplicity, the sum of the per-witness face contributions is the genuine
`SlabPhysicalData.physicalTerm`, and multiplying the conditional row by that
physical term recovers each unnormalized witness contribution.  Thus the
base Haar carrier and normalization are physically identified.

The fixed-plane grouped identification is now exact.
`BF4SU2FixedIntertwinerPhysicalChoi` identifies the source and target
half-amplitudes with `centralHalfAmplitude`, the interior insertion with the
fixed-plane heat factor, and the resulting Choi entry with the genuine
`centralPhysicalReflectedKernel`.
`BF4SU2FixedMagneticMehlerCarrier` then refines every spin-\(s\) fixed-face
channel by its literal \(s+1\) magnetic indices.  Conditional summation
recovers the representation dimension exactly, while each refined channel
carries only the heat eigenweight \(w^{C_4(s)}\).  Hence the physical and
reference spatial insertions have the spacing-independent pointwise window
\([1,1]\); the local magnetic tail is controlled by the proved heat
majorant.  This equality concerns the spatial insertion on the enlarged
carrier, not a completed Gaussian endpoint Mehler comparison.

Here “magnetic” is representation-theoretic: it is the full Peter--Weyl
matrix-index fiber on a face whose spin label is fixed during the
conditional sum.  It is not a restriction to a prescribed monopole,
center-vortex, background-field, or topological magnetic-flux sector.
The implementation sums this full fiber dynamically; fixing one magnetic
matrix index would fail to reconstruct the representation dimension.

`BF4SU2FixedMagneticPositiveKernelConvergence` identifies every normalized
kernel entry with a cutoff-stable lower/reflected-upper Yang--Mills cylinder
expectation.  The arbitrary-nome degree-thirteen envelope therefore gives
an executable two-cutoff modulus; degree thirteen pays the full link
intertwiner growth together with the magnetic dimension.
`BF4SU2FixedMagneticPhysicalHSCauchy` compensates the complete square
carrier dimension: on a base carrier of size \(N\), it requests entry
tolerance \(\varepsilon/N\) and proves exactly
\[
  \|J_{K_1}-J_{K_2}\|_{\rm HS}^2
  \le N^2(\varepsilon/N)^2=\varepsilon^2
\]
for all later cutoffs beyond the displayed modulus.

Finally, `BF4SU2FixedMagneticPhysicalMarkov` performs the physically correct
normalization of the symmetric joint law.  It filters precisely the
positive row marginals, proves discarded rows decouple, divides each
retained row by its own marginal, and obtains a nonempty reversible Markov
carrier with normalized stationary marginal.  Constants are fixed, the
marginal-weighted mean is preserved, and the corresponding physical
mean-zero subspace is invariant.  Its marginal vacuum projector is
constructed and removed exactly.  Uniform counting measure is no longer
substituted for the physical vacuum.  The exact marginal-weighted inner
product is also constructed, and finite Fubini plus detailed balance proves
that the physical conditional BF4 operator is self-adjoint in it, without
adjoining square roots of rational marginal weights.

The same-carrier HS route is now vacuum-correct.  In
`BF4NormalizedSameCarrierPerron`, normalized nonlinear and Mehler matrices
are compared after removing the same rank-one vacuum projector; raw
mean-zero eigenmodes are proved unchanged.  A cutoff-indexed convergence
datum with growing carrier dimension and explicit error modulus yields the
eventual `7/100` perturbation and `q ≤ 1/4` for an actual dominant finite
eigenmode.  The remaining analytic task is a distinct Gaussian endpoint
Mehler kernel on the same physical weighted carrier, with an interacting
physical-minus-Mehler entry estimate (not merely the now-exact spatial
insertion window), followed by a constructive contraction or dominant-mode
identification on the physical marginal-mean-zero subspace.  A raw
normalized matrix is deliberately never subjected to the false global
quarter bound because it contains the vacuum eigenvalue one.

The Peter--Weyl endpoint interface is now exact at the constructive
finite-dimensional level.  `BF4CentralPositivePeterWeylEndpoint` proves the
fundamental rational-complex \(\mathrm{SU}(2)\) Haar Schur table and exhibits
a negative matrix coefficient, then defines nonvacuous all-spin boundary and
double-Haar endpoint-projection targets on the literal physical labels.
`BF4FiveHolonomyNormalizedKernel` constructs the exactly Haar-normalized
finite product heat kernel on the five rational-unit-quaternion coordinates,
proves its endpoint symmetry, and supplies an inhabited expansion-level
all-spin character transform on the exact positive BF4 carrier.  Its
mixed-radix state mode is faithful, its one-term character expansions
synthesize pointwise, and the genuine all-mode \(\mathrm{SU}(2)^5\) Haar
Kronecker table proves normalization and orthogonality.  This is explicitly a
faithful character-coordinate realization: it does not yet identify those
characters with the geometric BF4 spin networks obtained after integrating
the eighteen non-transmitted chords.  The same module also proves that
`generalizedA = K^{-1}S` is not symmetric, so the coupled endpoint must retain
the symmetric pair `(kineticK24, spatialS24)` (or construct its symmetric
conjugate) rather than treating `generalizedA` itself as a scalar Hessian.
`BF4SymmetricReferenceOperatorComparison` therefore treats the projected
endpoint as the signed symmetric positive-semidefinite operator it naturally
is; its weighted quarter consumer does not require an entrywise-positive
endpoint law or a matching endpoint marginal.
`BF4AFUniformRowRelativeBudget` completes the cross-numerator,
numerator/partition, carrier-growth, marginal-floor, and AF-family algebra
feeding that consumer.  The unproved inputs are now purely analytic and
physical: the coupled normalized five-holonomy endpoint kernel, the geometric
BF4 spin-network identification of the constructed all-spin character
carrier, its spectral certificate, and uniform Yang--Mills estimates
inhabiting the displayed budgets.

The grouped endpoint has since been pinned much more tightly to the physical
action. `BF4GroupedPhysicalActionShift` proves under every arbitrary
ten-holonomy insertion that the positive exponent
`source complement + target complement + kinetic cross` differs from the
genuine compact BF4 action by exactly the two one-sided sphere shifts; after
the explicit scalar normalization, its abstract located packet endpoint is
the compact negative-action endpoint. `BF4GroupedCarrierMertens` supplies the
finite same-carrier producer: it regroups all ordered feature labels into the
physical kinetic Taylor partial, identifies both source and separately
compiled target diagonal partials, transports canonical padding through
reflection, and proves that every actual grouped packet square at finite
cutoffs is one common reflected boundary times those three genuine Taylor
partials. The remaining endpoint obstruction is no longer finite
source/target geometry: it is the constructive three-factor cofinal Mertens
theorem identifying this rectangular net with the single grouped exponential
limit. That limit theorem, and the later Wilson-slab/Perron/AF estimates, are
not asserted here.

`BF4CanonicalFiniteNumeratorPartitionBudget` now inhabits the complete
numerator/partition/marginal interface at every fixed finite physical BF4
scale for every signed symmetric endpoint.  Its tolerance is the executable
exact rational
\[
  \varepsilon_{\rm fin}
  = |S|\,\frac{\sum_{x\in S} b(x)}{\pi_{\min}},
\]
where each \(b(x)\) is formed from literal physical-minus-endpoint numerator
and partition differences.  The module also locates the vacuum row and
proves that the canonical order-one Cauchy--Schwarz rate is at least one.
Since \(\varepsilon_{\rm fin}\geq0\), that particular rank-one rate can never
satisfy \(r+\varepsilon\leq1/4\).  Thus the live spectral route must use
centered cancellation or the higher positive-Gram endpoint; the still-open
analytic task is spacing-uniform smallness of the exact physical comparison
budget for that sharper endpoint along the genuine AF trajectory.

`BF4CanonicalFiniteMehlerGramSpectralBudget` constructs that sharper
fixed-scale spectral datum.  It subtracts the exact physical vacuum joint
\(V(x,y)=\pi(x)\pi(y)\), proves its quadratic form vanishes on the physical
\(\pi\)-mean-zero carrier, and defines the executable centered Schur rate
\[
  r_{\rm cen}
  =\max_{x\in S}
    \frac{\sum_{y\in S}|M(x,y)-\pi(x)\pi(y)|}{\pi(x)}.
\]
Every denominator is positive by membership in `centralPositiveHalfStates`.
The resulting positive-Gram `MehlerGramEndpointSpectralData`, its raw
endpoint, and its complete exact finite comparison budget are unconditional
constructive definitions.  A further normalization audit proves
\[
  1-\pi(0)^2\leq r_{\rm cen}\pi(0).
\]
Consequently the previously proposed all-scale bound for
`matchedExactCenteredMehlerGramQuarterCostAt = r_cen + epsilon_fin`
would force \(\pi(0)>1/2\) at every scale, independently of the truncation
orders.  Neither `CubicMarginLaw` nor `PhysicalSpacingEnvelope` contains
such a stationary-marginal hypothesis.

`BF4VacuumCalibratedFiniteMehlerGramSpectralBudget` removes this artificial
obstruction.  It proves that square-scaling a raw endpoint preserves
symmetry, PSD, and the physical-mean-zero Rayleigh bound, then scales the
Mehler Gram by \(\pi(0)^2\).  The calibrated vacuum entry is exactly
\(\pi(0)^2\), and its certified spectral rate is no larger than the original
one.  On matched coordinates the corrected exact scalar is
`matchedVacuumCalibratedMehlerGramQuarterCostAt`.  Its spacing-uniform
quarter theorem is reduced without hidden finite data to the two genuine
Yang--Mills estimates: calibrated spectral rate at most \(1/8\), and exact
physical comparison tolerance at most \(1/8\).

The grouped-action layer removes one of those hidden identifications.
`BF4PhysicalBoundaryCommonKernelAction` uses the complete fixed-interface
carrier after the eighteen non-transmitted chords have been integrated and
constructs the literal activity
\[
  a_{\rm phys}(b)=W(b)B(b)/Z_{\rm phys}.
\]
It proves constructively that the vacuum boundary coordinate is strictly
positive and that the transposed physical half-amplitude acts on this
activity as the exact marginal:
\[
  \sum_b A(x,b)a_{\rm phys}(b)=\pi(x).
\]
For an exact grouped gluing
\(A(x,b)=\sum_m P(x,m)T(m,b)\), finite Fubini pushes this activity through
\(T\), producing a nonzero positive activity on the enlarged middle carrier
and identifying \(P(x,m)\) with the same physical marginal.

The preferred construction now keeps the common positive kernel on the
boundary carrier instead:
\[
  J(b,x)=\sum_m P(x,m)T(m,b).
\]
The certificate for \(J\) is the transpose of the terminal-smoothed
certificate.  It is therefore constructed from the primitive terminal
certificate and the nonnegative/nonzero prefix rows, its projective spread
is definitionally the primitive terminal spread, and no strict-positivity
certificate is required for the generally zero-containing fusion prefix.
The same exact gluing theorem identifies \(J a_{\rm phys}=\pi\).
`BF4GroupedCommonKernelPerronAction` installs this boundary-carrier theorem
into the scale-uniform core/tail consumer; the physical activity,
certificate, and action-identification fields are theorem outputs.

There are now two certified quantitative continuations.  A terminal
Perron-form estimate
\(C_s^2\le 1+C_b^2q_s^{m-2}\) implies the required Harnack bound, but the
minimal interface asks directly for
\(C_s^2\le65/64\).  Independently, a genuine local stationary slice with
centered contraction \(q_s\le1/4\) feeds the endpoint-free local-contraction
consumer, so the physical \(1/32\) core, two \(1/64\) tails, and both
rowwise \(1/8\) estimates no longer require a separate endpoint-spread
buffer theorem.  The stronger Faraut buffer remains an alternative.
`PhysicalBF4OneStepContractionGluingRow.toFarautBufferedRow` also turns an
exact one-step stationary density gluing on the literal retained carrier
into the full witness-bearing \(C_s^2q_s^{m-2}\) buffer, and the
scale-family producer forces that gluing to use definitionally the same
bit, depth, and nonlinear-rate schedule as the grouped profile.  The
remaining BF4 analytic inputs are now explicit: construct the genuine
grouped half-amplitude gluing and a positive primitive terminal certificate
whose squared spread is at most \(65/64\), identify the calibrated
Peter--Weyl boundary activity under this same terminal-smoothed kernel, and
prove the actual local stationary BF4 slice gluing with \(q_s\le1/4\)
(or, alternatively, the stronger endpoint-buffer estimate).  The physical
`CubicMarginLaw` and `PhysicalSpacingEnvelope` also remain to be
constructed.  Those Yang--Mills estimates are not yet inhabited.

**Ledger state.** The `YMGap` library builds sorry-free (`make lean-build`
reports zero `declaration uses 'sorry'`; see `SORRY_LEDGER.md`, whose
remaining entries are closure records and named-hypothesis
bookkeeping, not open holes). `AXIOM_AUDIT.md` currently records namespace
digests for more than 18,000 canonical audited declarations; every full build
separately verifies exact current source-gate coverage. Those declarations are
axiom-gated to `∅` / `[propext]` /
`[propext, Quot.sound]` — no `Classical.*`, no `sorryAx`, no
`native_decide`. `CLASSICAL_LEDGER.md` has zero entries (see the
Minlos caveat below).

**Proved — the fixed-spacing Clay line.**
`Rubric.ClayScorecard.clay_fixed_spacing_met` genuinely inhabits every
fixed-lattice-spacing clause of the transcribed Clay rubric, each
discharged by a concrete named theorem about a specific YM object:
positive located spectral gap of the reconstructed transfer operator,
geometric clustering of the real Wilson connected correlator,
nontriviality, OS2 reflection positivity (via the Osterwalder–Seiler
diagonalization `ReflectionPositivity.reflSchwinger_nonneg`, which
retired the previous P_N/product-form walls from the critical path),
and infinite-volume mass positivity. Supporting closed work includes
the constructive-reals substrate, the SU(2)/SU(3) KP-certificate
derivations, the S2–S6 finite/infinite-volume functional stages
(partition positivity, reweighted state, KP increment engine, limit
with modulus), the complete constructive GNS Hilbert space
(`GNSComplete`), and the uniform-group reduction
(`mass_gap_simple_group` via the proven character-tail majorant chain,
with SU(2)/SU(3) discharged end-to-end).

**Deliberately open — the machine-checked frontier.** The continuum
(`a → 0`) Clay problem is carried as *uninhabited* bundles, never
faked, in **two complementary enumerations** whose unification is
planned (`work_plan.md` Milestone 11.14). On the measure/RG side,
`Continuum.Tier0Scorecard` enumerates: Sub-wall A (loopy geometry:
(T′) tree-graph, (D1) Mayer–Ursell bridge, (D2) separation metric,
(A2) 6j pentagon), Sub-wall B (Balaban RG: the `SpectralMarginInput`
atoms `hlocalize` / `hbridge` / `hadd`), and the orthogonal
`CitedMinlosLift` (σ-additive continuum measure — note: this
cited-classical input is not yet processed through the Rule-4
quarantine, hence the empty classical ledger currently *understates*
the continuum chain's classical content; resolving this is
`work_plan.md` Milestone 11.9). On the operator/OS side,
`Rubric.ReconstructionScorecardFinal` names five open tokens:
`OpenNode1FiniteSMargin`, `OpenTrueMargin` (the genuine dimensionless
physical margin `Δ_k = m_lat(a_k)/a_k`, distinct from the proved
survival-product *surrogate* in the green line — see AGENTS.md
Rule 9(6)), `OpenPhysicalWilsonBridge`, `OpenBoundedHamiltonian`, and
`OpenContinuumMinlos`. `ClayScorecard.ClayTarget` additionally names
O(4) restoration, coupling-uniformity, gauge content, asymptotic
freedom, and nontriviality (`Continuum/FourDExistence.lean`); the
Jaffe–Witten local-field/stress-tensor/OPE layer is currently only
two bare `Prop` fields there and is scoped as Milestone 11.17.
`ContinuumFrontierScorecard` proves that the codynamic, curvature, and
OS-reconstruction continuum routes all converge on the single
uninhabited scalar `UniformSpacingFloor`.

The active Core-B reduction now reaches the canonical row-one origin
square-gap quotient.  `CoreBUniversalSquareGap` gives the exact all-index
factorization, `CoreBConsumerOrigin` and `Rubric/CoreBPhysicalBridge` give the
consumer composition, and `CoreBAtomwiseGapBounds` proves the parity content
floors, sharp coefficient maxima/reserves, endpoint degrees, adverse-chain
length bound, and homogeneous-chain endpoint estimate for all eleven bounded
selector families.  `CoreBCanonicalSquareShell` supplies the exact parity
four-square shell, and `CoreBLowGapBudget` kernel-checks the finite
coefficientwise envelope budget conditional on its explicitly transcribed
mass lists.  `CoreBCubicEvenTail` now proves the exact all-index cubic
even-gap tail `3311/884736`, with a nonnegative geometric remainder and an
explicit modulus; the comparison from actual adverse mass to that majorant
remains open.  `CoreBLowGapClassifier` closes the first actual classifier
fiber: for every stable odd length, the real bounded adverse endpoint-gap-two
atoms are equivalent to five explicit selector patterns, with a computable
Boolean classifier.  Summing those five actual contributions into the
transcribed `oddMass2Formula` remains open.  A parallel exact scout found
strictly positive Bernstein
coefficients cell-by-cell through canonical length eight after the physical
change of variable `u=4w²`.  `CoreBBernsteinConsumer` kernel-checks the direct
typed composition from an all-index actual-cell Bernstein family to the
row-one quotient certificate, and `Rubric/CoreBPhysicalBridge` carries that
family all the way to the guarded bridge.
`BernsteinSignedMonomialReconstruction` now closes the generic algebraic seam:
any finite integer-signed monomial ledger is computably compiled into one
common Bernstein row with an exact evaluation theorem.
`CoreBActualBernsteinRow` now closes the Core-B-specific enumeration seam: it
constructs the actual eleven-family integer row and proves exact signed-ledger
reconstruction, then reduces the physical cell certificate to coefficient
nonnegativity plus one explicit `u=4w²` scaling identity.  No all-index
Core-B-specific certificate family is yet inhabited, so Core B remains open
at those two final row obligations.

On the compact-dual lane, `CompactDualPinnedPhysicalData` pins the physical
coupling, cutoff, box, observable, packet graph, spin-foam data, and RG state.
`CompactDualBoundaryReflectionCone` closes the rational one-interface
reflection cone: every actual finite boundary packet has an exact rational
sum-of-squares Gram and an exact constructive-real equivalence to the existing
diagonal reflection form.  The rational weight
`ofQ'(w^(4*C₂(s)))` is not yet identified with the Schwinger weight
`exp(-t*C₂(s))`, and no RG block-map preservation theorem is claimed.

`CompactDualPositiveChannelDoor` records the supplied `(1,1,1,1)` rim
survival probe at the exact rational level.  Its twelve page-spin sectors are
carried as four exact permutation orbits with multiplicities `1,6,4,1`;
their nonnegative orbit contributions resum to
`1/4 + (9/2)s^16 + 6s^24 + (21/4)s^32` and feed a conditional
activity-times-square consumer.  This is a finite positive-channel candidate,
not a physical block theorem.  The module names the remaining all-label
source-dependent kernel obligation over the actual fine/coarse physical
labelling lists; no inhabitant, semantic Haar-network bridge, complete
channel decomposition, or overlap remainder is constructed.

The executable companion has since derived an all-label theorem for the
wheel topology: trivalent Haar projection writes each fixed-label wheel as a
positive dimension factor times a squared Clebsch--Gordan norm, so every
fixed-rim heat-kernel channel is coefficientwise nonnegative.  This analytic
identity is documented and independently regression-checked, but is not yet
formalized in Lean or identified with the pinned physical spin-foam fiber.
The canonical unit-rim manifest is exported by
`computations/dual_positivity_manifest.py`.

The exact-slab normalization lane now closes the first even spin on the
literal 116-quaternion carrier.  `SU2QuaternionSpinTwoConditionalHaar` proves
that integrating the selected block of `chi_2(A U B)` produces the tail
radius defect and that this defect vanishes against every head-independent
polynomial insertion after the exact tail sphere relations.  The other 115
blocks are therefore retained as polynomial coefficients.  The all-spin
solid-zonal recurrence is proved Haar-equivalent to the ordinary character
and homogeneous of the exact representation degree.  The accompanying
`SU2QuaternionHeadHomogeneousGaussian` and
`SU2QuaternionHeadGaussianLaplacian` modules prove the common radial-factor
identity and `d E_G[P] = E_G[Delta P]` with retained tail coefficients.  The
all-spin rational differential-algebra atom has now also been closed.
`SU2QuaternionSolidZonalHarmonic.laplacian_U_solidZonal_AUB_zero` proves
coefficient-sensitive `Δ_U Z_j(AUB) = 0` for all sixteen orientations, while
retaining the other 115 quaternion blocks.  The proof combines exact finite
certificates for `Δs = 0` and `|∇s|² = ρ` with Euler homogeneity and a
simultaneous solid-zonal harmonic/directional recurrence.  It audits to
`[propext, Quot.sound]`.  The finite Gaussian transport is now also closed:
`SU2QuaternionSolidZonalGaussianTransport.headGaussianTail_headLaplacian`
identifies Gaussian integration after the formal selected-head Laplacian with
the existing termwise Gaussian-Laplacian functional, without deleting any
tail coefficient.  Consequently every positive even-spin solid or ordinary
BF4 character has zero exact Haar integral on the 116-block carrier, including
after multiplication by an arbitrary selected-head-degree-zero polynomial.
The selected-face geometry is now extracted exactly by
`BF4ExactSlabSelectedFaceFold`: a constructive face-list permutation isolates
the chosen character, the erased 23-face fold is proved head-independent from
literal link incidence, and a three-disjoint-transposition tail map sends the
four selected word blocks to canonical blocks `0,1,2,3` with orientation
pattern `[false,false,true,true]`.
`BF4ExactSlabSelectedFaceCanonicalWord` now closes the corresponding algebraic
and Haar gate structurally, without expanding the 116-block polynomial.  It
proves that the doubly reindexed selected scalar is prefix-equivalent to
`(exposedFourWord false false true true).scalar`, transports the equivalence
through every `characterPolynomial`, and retains the other 23 factors as a
head-degree-zero multiplier.  Positive even labels are then killed by the
existing solid-zonal harmonic theorem and odd labels by the existing
one-block Fubini theorem.  Prefix-Haar transport and both block-involution
changes of variables inhabit `ExactFixedFaceConditionalHaarOrthogonality` and
`ExactVacuumNontrivialHaarTermsVanish K` for every finite cutoff `K`.  These
are exact finite-slab statements; the spacing-uniform AF comparison,
continuum limit, Osterwalder--Schrader reconstruction, and mass gap remain
open.

The first AF comparison cut now has an exact spectral fence and a sharper
growth interface.  `BF4ExactSlabHaarSpectralFence` constructs a cutoff-one
Haar-mean-zero observable of weighted square `2` whose lowest-order grouped
Mehler quadratic is `1`; hence
`no_grouped00_HaarBoundary_spectral_eighth` proves that the `(0,0)` grouped
endpoint cannot have rate at most `1/8` on the currently stated
Haar-diagonal zero space.  Higher orders and an eventual common-Perron
recentering remain open.  On the comparison side,
`AllCutoffExactSlabGroupedRowSummableEighthData` now consumes a
target-dependent majorant through its actual row sum.  The earlier uniform
entry budget with `(K+1)^24` growth is proved to be a sufficient adapter, not
the minimal analytic obligation.  Thus the composite spectral/error/growth
node remains open, but the false lowest-order start is excluded and the
remaining row estimate is stated at the strength an actual locality bound
can supply.

`BF4ExactPhysicalPerronReroute` now makes that grouped node optional rather
than mandatory.  It proves exactly that zero-marginal filtering preserves
the normalized full physical OS quadratic, so the full physical carrier and
the positive-row Perron carrier have the same finite quadratic form.  The
proposed signed-to-positive seam is the explicit `Type`-level input
`ExactHaarPhysicalPerronSameActionAt`.  Its consumers remain valid: from it,
the existing symmetric Perron comparison transfers a quarter bound.  More
directly, genuine
one-slice stationary density gluing with local rate at most `1/4` transfers
the already-proved physical centered-row `1/16` estimate to the literal
exact Haar-network quadratic.  The latter route uses neither a grouped
spectral eighth nor a row-error eighth nor a carrier-growth payment.
`BF4ExactPhysicalPerronSameActionFence` now proves, however, that the seam
itself is uninhabited at cutoff one for every positive coupling.  The vacuum
code delta has exact-Haar quadratic one, whereas its normalized positive
physical quadratic is strictly below one because the explicit non-vacuum
cube row carries positive marginal mass.  Thus exact equality to the current
multiplicity-product law is not an open resummation theorem; a correct route
must compare the two actions with nonzero error or construct a different
positive representation of the signed Haar network.  Quantitatively, for
`w >= 8/9` the physical vacuum-delta value is at most `1/8`, so its absolute
quadratic defect from the exact value is at least `7/8`.  Hence a small-error
adapter to the current law is also excluded in the high-nome AF window.  The
fence and bypass consumers audit only to `[propext, Quot.sound]`.

The vacuum delta separating the two full quadratics is not physically
mean-zero, so that fence does not by itself refute equality on the centered
consumer space.  `BF4ExactPhysicalPerronCenteredReroute` therefore replaces
the false all-observable premise by the strictly weaker
`ExactHaarPhysicalPerronCenteredSameActionAt`.  The old premise maps to this
one, while both the symmetric-reference quarter and the local-gluing
sixteenth are proved to need only centered equality.  Its AF wrapper retains
the genuine rowwise local witnesses without requiring equality on constants
or vacuum point observables.  This is an interface correction, not a new
analytic existence claim: neither centered same action nor local gluing is
inhabited by the module, and the signed/positive fusion problem remains open.
All centered-reroute gates again audit only to `[propext, Quot.sound]`.

`BF4ExactPhysicalCenteredVacuumProbe` now makes the first mandatory test of
that open seam explicit.  It subtracts the normalized physical vacuum row
marginal from the faithful vacuum code delta and proves that the resulting
observable has exactly zero physical stationary mean.  Any centered
same-action certificate must therefore identify the exact and physical
quadratics on this named probe.  This does not yet decide the seam: doing so
requires the exact signed-Haar delta--constant cross moment and constant
moment, which the raw vacuum-diagonal fence did not evaluate.  The probe
module records that residual without an axiom or hidden inhabitant.

`BF4ExactPhysicalCenteredVacuumMomentExpansion` now evaluates the complete
algebra surrounding that probe.  A generic finite bilinear API expands an
affine observable and transports kernel symmetry.  On the physical side the
centered value is exactly the normalized vacuum diagonal minus the square of
the vacuum marginal.  On the signed-Haar side it is the unit vacuum diagonal
plus two copies of one vacuum-row cross moment and the marginal-square
multiple of one constant quadratic moment.  The two cross orientations are
proved equal by literal slab-kernel symmetry, and the remaining cross moment
is identified with the complete signed vacuum row sum.  Thus any centered
same-action witness must solve one explicit scalar moment balance.  Only the
signed vacuum row sum and signed constant quadratic moment remain unevaluated;
the module makes no equality or positivity claim about them.

`BF4ExactPhysicalCenteredVacuumHaarResummation` now performs the missing
finite Fubini step.  It proves that product Haar commutes with one, two, and
three literal finite polynomial sums, moves each heat-kernel face weight into
the signed 116-link polynomial, and packages the complete vacuum row and
constant quadratic moment as `Haar_116(P_row)` and
`Haar_116(P_constant)`.  The centered vacuum balance is restated entirely in
those two explicit polynomial values.

`BF4ExactPhysicalCenteredVacuumTransmittedMarginal` now closes the exact
product-Haar reduction to five surviving blocks.  It computes the raw slab
blocks of the five transmitted tree-gauge chords as `[11,3,6,23,42]`, swaps
them in canonical transmitted order with tail blocks `111,...,115`, and
iterates constructive head Fubini over the other 111 blocks.  For every
supported literal slab polynomial it proves
`Haar_116(P) = Haar_5(M_transmitted(P))`, proves that the marginal is
syntactically supported on twenty real coordinates, and applies the result to
both resummed moments and the complete centered-vacuum expression.  These five
coordinates are still raw chord-link representatives.  The nonlinear
vertex-gauge change of variables identifying them with the five existing
cycle-holonomy coordinates, and the subsequent cutoff-one evaluation, remain
open.  No centered no-go, positivity, or local-gluing inhabitant is claimed.

`BF4ExactSpatialTreeGaugeBasedCycles` now supplies the finite geometry behind
those cycle coordinates.  It enumerates the 26 vertices of the displayed
25-link rooted tree, gives explicit root paths to every chord endpoint, and
proves that all 23 words `P(start) · U_chord · P(end)⁻¹` are closed loops.
Their raw 116-link polynomial holonomies and their tree-gauge specializations
are defined explicitly.  After tree gauge, each loop is constructively proved
prefix-equivalent to its indexed quaternion coordinate; the five transmitted
loops occur in the exact retained order `[0,4,5,6,10]`, and the pre-existing
five-coordinate monomial projection is proved to use precisely those blocks.
The nonlinear Haar-preserving change of variables from the raw five-link
marginal to these based-cycle holonomies remains open, so no equality of those
two fivefold Haar values is claimed.

`SU2QuaternionPolynomialHaarTranslation` now supplies the constructive
one-block algebra needed by that change of variables.  For a left product
`a·u` or right product `u·a`, an executable rational-polynomial certificate
identifies the exact head `S³` moment with the untranslated moment times the
appropriate power of `|a|²`.  The existing sphere ideal then removes that
power after multiplication by an arbitrary supported tail polynomial.  A
termwise scan lifts the result to any finite supported polynomial while
checking only exponent quadruples that actually occur.  Thus every successful
finite certificate has a kernel-checked left/right Haar-invariance theorem;
the load-bearing audit is `[propext, Quot.sound]`.  This remains
certificate-parametric rather than a universal all-degree translation theorem.

`BF4ExactSpatialTreeCycleFiveHaarMarginal` closes the marginal once the
adapted 48-block carrier has been reached.  In the literal order “25 tree
blocks, then 23 based-cycle blocks,” an explicit involution moves cycles
`[0,4,5,6,10]` to the tail.  Exact Fubini integrates the 25 tree variables
and all 18 unused cycles, proving
`Haar_48(P) = Haar_5(M_based-cycle(P))` for every supported adapted-carrier
polynomial.  The raw-link-to-adapted-carrier triangular substitution is still
the open composition step; no raw five-link/based-cycle marginal equality is
claimed yet.

`SU2QuaternionSelectedHaarTranslation` and
`SU2QuaternionSelectedHaarTranslationChain` now close the compositional Haar
layer of that substitution.  A selected block and distinct multiplier are
exposed as blocks zero and one, genuinely substituted by left or right
quaternion multiplication, and restored without changing the carrier size.
Three coordinate sign changes provide the inverse-multiplier cases.  A
successive executable scan then proves full product-Haar invariance for any
finite chain, including a 25-vertex batch interface.  All direct, inverse,
single-step, and iterated theorems audit to `[propext, Quot.sound]`.

`BF4ExactSpatialTreeGaugeTranslationLedger` generates the literal chain from
the certified BF4 root paths.  Across all 23 chords it contains exactly 139
pair shears and constructively checks that chord blocks `25,...,47` are always
distinct from tree multipliers `0,...,24`.  For any supported 48-block
polynomial whose successive scans succeed, applying this concrete ledger
preserves `Haar_48`.  The remaining seam is no longer an unspecified
left/right invariance theorem: it is the syntactic proof that the ledger image
of each chord coordinate is the existing based-cycle polynomial, plus the
concrete scan discharge.  Until those are proved, no raw five-link/based-cycle
marginal equality is claimed.

`BF4ExactSpatialTreeGaugeTranslationSemantics` now makes that last syntactic
proof an exact executable interface.  For each chord it applies the certified
per-cycle shear list to the adapted raw coordinate quaternion and compares the
four canonical rational coordinate polynomials with
`P(start)·U_c·P(end)⁻¹`.  Successful checks soundly yield canonical
`QuaternionPrefixPolyQuaternionEqv 48`, with axiom gate
`[propext, Quot.sound]`.  The all-23 success theorem is not claimed: brute
canonical reduction was memory-safe but too slow even on the first cycle, so
the next implementation should prove the quaternion anti-homomorphism and
composition identities structurally or use small cached batches.

`SU2QuaternionTranslationMomentDegreeFive` and
`SU2QuaternionSelectedHaarTranslationDegree` remove the concrete scan
hypothesis needed by the cutoff-one route.  Exact kernel normalization checks
left and right quaternion translation through total degree five.  Structural
degree lemmas then preserve a monitored block bound through exposure,
translation, conjugate-multiplier steps, restoration, and an arbitrary
compatible chain.  Thus a proof that five selected chord blocks have degree
at most five constructively supplies every successive translation check.

`BF4ExactSpatialTreeGaugeRawCarrier` now composes the complete literal
carrier bridge.  A checked 46-transposition chain places the 25 lower spatial
tree links and 23 chords in adapted order inside the 116-link slab carrier.
Only the path-derived shear words for transmitted cycles `[0,4,5,6,10]` are
needed.  They act on adapted chord blocks `[25,29,30,31,35]`; a final
involution moves those images to blocks `111,...,115`, and exact head Fubini
integrates the other 111 quaternion blocks.  For every supported polynomial
whose five adapted chord degrees are at most five, Lean proves

```text
Haar_116(P) = Haar_5(M_tree-gauge-based-cycle(P)).
```

The five output variables are generated by the literal rooted path shear
ledger in the exact order `[0,4,5,6,10]`.  The Rust sparse normalizer remains
a useful independent regression oracle for expanded word equality; it is not
used as a proof axiom.

`BF4ExactCutoffOneTransmittedDegree` discharges that degree hypothesis for
the two centered-vacuum resummed polynomials at cutoff one.  It follows the
literal 72 plaquette boundaries, proves structurally that a block degree is
bounded by its incidence count, and computes the five raw transmitted counts
as `[4,4,4,5,5]`.  The bound survives every finite boundary/interface sum and
the carrier adaptation.  Consequently both unresolved cutoff-one moments now
have unconditional constructive endpoints on the requested five based
cycles:

```text
R_exact(w,1) = Haar_5(P_row_based_cycles(w)),
C_exact(w,1) = Haar_5(P_constant_based_cycles(w)),
based-cycle order = [0,4,5,6,10].
```

The load-bearing endpoint theorems audit to `[propext, Quot.sound]`.  This is
the exact fivefold marginal target, not a numerical evaluation of the two
five-variable polynomials and not a centered same-action verdict.

**Per-atom partial progress** (the scorecard docstrings may lag these;
Milestone 11.0 re-syncs them): (D2) has a sound, non-tight L¹
inhabitant (`SepLatticeZ4Close.SepLatticeZ4_witness`); (T′) is reduced
to three named legs, of which only the Penrose sign-domination is new
mathematics (`TreeGraphBoundProgress`, with the (P) leg under further
active reduction in `PenroseDomInduction`); the pentagon track has the
Level-1/Level-2 analysis and a refutation of the permutation surrogate
(`PentagonRelation`); `hbridge` has its wiring lemma
(`PinnedBridgeProgress.edgeShift_le_gradedDefect`); and the canonical
`FrontierDAG.bulkCtrl` field is now reviewed and repointed from the refuted
bare-reference `SpectralLocalization w` to
`RebasedBulkLocalizationBridge.CanonicalBulkControl N w pΓ`.  Its spectrum,
cutoff, and positive exponent are physically pinned, its infinite tail is
compiled structurally from `s ≤ 2*N`.  The reflected finite saddle-to-exp
*compiler* is now kernel-checked: each mode selects either the direct rational
shift atom or an explicit dyadic-log tail/separation atom whose false branch
contradicts the faithful saddle estimate.  The physical `pΓ=2` coefficient
route now has one common compiled carrier feeding the same selected spectrum,
`finePin`, `imagePin`, and genuine `BlockingStep.Phi` defect-power theorem.
For every scale `k>=4`, the half-time head `s=1` and the four terminal shells
`s=2*N_k-1` through `s=2*N_k-4` are kernel theorems.  The
remaining coefficient obligation is the pure-Nat reserve sign only for
`2<=s` and `s+4<2*N_k`; the independent theta trapezoid/fine-reserve tail and
later physical recursion remain open.  A corrected conditional transport
now carries canonical bulk localization through one named physical
map-identification bridge to `PhysicalRGInput` and a positive `CRealFloor`.
The older `DeltaFrontierLedger` carrier retains its historical
bare interface and is not treated as definitionally equivalent. Hygiene note: the library
carries exactly 9 `noncomputable` declarations (in `NormExcitedDrift`,
`DominantModeRecursion`, `UniformCouplingFromAF`), pending the
classification ledger required by the AGENTS.md Rule 1 addendum.

**Not claimed.** No inhabitant of `ClayTarget`, `Tier0Scorecard`, or
`UniformSpacingFloor` exists in this library. The Clay Yang–Mills
existence and mass gap problem is OPEN; what is machine-checked is the
fixed-spacing closure and the reduction of the remainder to the named
atoms above. The current campaign against those atoms is
`work_plan.md` Phase 11 (frontier mathematics) and Phase 12
(compliance, publication, hygiene).

---
