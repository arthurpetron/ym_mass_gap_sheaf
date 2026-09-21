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

**Whole signed plaquette Ward-gradient energy (2026-09-21 UTC):**
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
physical links. This does not give a strict response floor. A quantitative
diagonal bound for this gradient family still needs an actual second angular
derivative estimate and local coefficient/incidence accounting. No scaling
ratio, OS gap or continuum closure is proved. The dependency-complete target
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
incident-gradient family and exact energy response are now supplied above;
its quantitative diagonal control remains open.
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
and full action. Response floors and score-cost estimates, including
their spatial/nome control, remain open. The character/heat derivative
join now has its actual face derivative input; the score cost and response
estimates remain open.
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
