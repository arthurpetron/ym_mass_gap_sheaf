# Original OS reconstruction boundary — 2026-09-14

Whole-project goal: construct the same-object four-dimensional continuum
Yang--Mills theory and a strictly positive physical mass gap within the
MLTT/HoTT axiom gate. The results below are fixed SU(2) nome `1/1024` and
fixed spacing, not that continuum theorem.

## What the new response actually supplies

- All positive discrete times have the same kernel:
  `time_positive_kernel_equal`,
  `lean/YMGap/Continuum/BF4ExactSlabThermodynamicTimeKernel.lean:63`.
  `positive_range_no_further_kernel` at line 72 excludes further
  annihilation of a vector already in a positive-time range. Neither
  statement says the common kernel on the entire completion is zero.
- The existing centered probe's orbit is nonzero at every integer time
  (`orbit_nonzero`,
  `lean/YMGap/Continuum/BF4ExactSlabThermodynamicProbeOrbit.lean:43`), and
  no orbit point is fixed by a positive later time (`orbit_not_fixed`,
  same file, line 50).
- This is quantitatively witnessed: `positiveTimeFloor` at
  `lean/YMGap/Continuum/BF4ExactSlabThermodynamicProbeOrbitFloor.lean:81`
  computes `r_0=w^36/16`, `r_(k+1)=r_k^2/P`;
  `positiveTimeFloor_bound` at line 89 gives `r_k <= ||T_(k+1)x||^2`.
  Here `P` is the existing `positivePrefactor`, defined in
  `lean/YMGap/Continuum/BF4ExactSlabThermodynamicTimeDecayRate.lean:111`.
  `orbitCertificate` at line 115 of the orbit-floor module returns the
  positive rational floor, the same moment representative, its QCauchy
  data, and the operator pin. The floors depend on time.

## Normalization update after cd75a56

The RC-valued normalization step is now **CLOSED**. `unitProbe_norm`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicNormalizedProbe.lean:64`,
proves squared norm one for the actual scaled original state.
`normalizedResponse_pin` at line 78 pins its original two-step response;
`normalizedResponse_floor` / `normalizedResponse_upper` at lines 92 and 98
bound it between the positive responseFloor/P and 1/2.
`normalizedCertificate` at line 131 returns the state, both rational
endpoints, response real and QCauchy data, with all these proofs.

The scalar is constructed, not assumed: `sampleCauchy` and `value_square`,
`lean/YMGap/Continuum/PositiveRationalCauchySquareRoot.lean:84` and line 119,
give the Heron sample modulus and square identity;
`inverse_square_source` at line 143 gives original-source cancellation.
`clamped_value`,
`lean/YMGap/Continuum/PositiveCRealNormalizationScalar.lean:41`, preserves
the original positive real; `scalar_normalizes` at line 89 proves its
normalization. None of these declarations changes a canonical root type.

## Original finite spectral-row update after f996e3a

Mixed positivity is **CLOSED**: `mixedMoment_nonnegative`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicTimeDefectMoments.lean:111`,
proves nonnegativity of <x,T2^k (I-T2)^l x> for all completed x,k,l.
`mixedMoment_split` at line 119 supplies the exact two-branch identity;
`momentCertificate` at line 161 retains actual reals/moduli and their pins.

The finite Bernstein-word weights have proved mass and first count moment:
`weights_total` and `weighted_time_count`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicBernsteinWords.lean:120`
and line 133. These are repeated-node finite expansions, not eigenvectors.

For the actual normalized probe, `weight_total`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicBernsteinProbeRows.lean:71`,
proves mass one; `weighted_node_mean` at line 76 pins the first moment to
the original response. `rowCertificate` at line 98 returns nodes in [0,1],
nonnegative real weights, their QCauchy data, total mass and that pin.
It does not construct a limiting spectral measure or prove the finite
rows have support in [0,1/2]; only their mean has that upper bound.

## All-order moment convergence update after c8c0a7b

`weighted_choose` and `weighted_falling`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicBernsteinFactorialMoments.lean:52`
and line 94, prove every exact factorial moment of the ORIGINAL rows.
`power_le_product_error`,
`lean/YMGap/Continuum/BernsteinFallingProductError.lean:90`, bounds the
ordinary-power/falling-product difference by C(r)/N; `modulus` at line
129 and `error_small` at line 132 compute and prove a tolerance threshold.
C is defined by the triangular recursion `coefficient` at line 42.

All monomial moments now converge with a rate: `powerMoment_error`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicBernsteinMomentConvergence.lean:131`,
gives the two-sided C(r)/N bound. `limitMoment_pin` at line 77 pins the
limit to the original operator; `moment_error_le` at line 168 supplies
the tolerance form. `momentConvergenceCertificate` at line 180 returns
the original limiting real, QCauchy data, operator identity and modulus.
`powerCauchy` at line 160 separately retains the finite-row real's modulus.
No limiting spectral measure or full functional calculus is asserted.

## Signed-polynomial and actual cyclic-norm update after c3da7a8

`scale_error`, `lean/YMGap/Continuum/RationalScalarTwoSidedError.lean:21`,
transports two-sided errors through signed rational coefficients with |c|.
`polynomial_error`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicBernsteinPolynomialMoments.lean:148`,
gives the two-sided summed error; `polynomialModulus`, same file at line
165, computes its threshold. `polynomialConvergenceCertificate`, same
file at line 184, returns the CReal limit, QCauchy data, operator pin and
modulus. `rowCauchy` at line 97 retains the finite-row real modulus.

`functional_positive`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicPolynomialFunctional.lean:80`,
and `functional_sup_bound`, same file at line 85, prove positivity and
rational sup-norm bounds from the SAME row limits. `functional_mono` at
line 98 and `functional_congr` at line 121 prove order preservation and
pointwise equivalence invariance. `functional_add` at line 152,
`functional_scale` at line 158 and `functional_one` at line 170 prove
rational linearity and normalization.

`probe_inner_product`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicPolynomialProbeNorm.lean:69`,
proves <p(T2)v,q(T2)v>=F(pq). `probe_norm_bound`, same file at line 86,
then bounds the ACTUAL cyclic polynomial vector norm by a polynomial
sup bound on [0,1]. Uniformity is in polynomial degree at fixed nome and
spacing, not in beta or physical lattice spacing. No supplied diagonal
resolution, full-carrier polynomial operator bound, continuous calculus
or spectral measure is constructed by these declarations.

## Represented Bernstein carrier update after e284003

`probe_distance_bound`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicPolynomialDifference.lean:64`,
controls the ORIGINAL polynomial-vector squared distance by the squared
uniform polynomial difference. `vectorRepresentative` at line 78 and
`vectorRepresentative_pin` at line 83 construct and pin its actual rows.

`polynomialRows`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicPolynomialCarrierLimit.lean:57`,
constructs outer Cauchy data; `polynomialLimitCertificate` at line 87
returns the original representative and rate. `polynomialLimit_unique`
at line 94 and `polynomialLimit_constant` at line 110 prove uniqueness
and constant-sequence compatibility.

`SpectralUnifCauchy`,
`lean/YMGap/Continuum/ContinuousTransferCalculus.lean:207`, has a single
parameter lam, and its `cauchy` field at line 213 only evaluates at lam.
The new `bernstein_uniformCauchy`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicBernsteinCarrier.lean:45`,
instead exposes ALL rational t in [0,1] with one computed rate, using the
existing CtsMod/MOV stage construction. `continuousProbeCertificate` at
line 71 returns the original limit representative and rate;
`continuousProbe_modulus_independent` at line 85 proves that the chosen
vanishing modulus does not change the limit.

`cuspSymbol`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicCuspProbe.lean:68`, and
`cuspVanishing` at line 77 construct min(|t-1/2|,1) with all required
continuity data. `cusp_nonconstant` at line 91 distinguishes its values
at zero and one-half. `cuspVectorCertificate` at line 104 constructs the
original carrier-limit instance. Nonzeroness of this vector is not
asserted. These symbol data are rational-valued, not an assertion that
all CReal-valued continuous symbols or full operator calculus are closed.

## Original limit pairing and norm update after e8713df

`pairing_close`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedPairingContinuity.lean:86`,
proves explicit two-slot continuity of the SAME original completed pairing,
with squared-distance tolerance epsilon^2/(8*(B+1)).
`pairingModulus`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicRowPairingLimit.lean:60`,
computes the outer pairing rate from represented-row distance moduli and
computed rational norm ceilings. `pairingCertificate`, same file at line 97,
retains the original limit real, QCauchy data, same-pairing pin and rate.
`rowLimit_norm_bound` at line 107 passes uniform row norm bounds to the
constructed row limit.

`bernstein_abs_bound`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicBernsteinLimitPairing.lean:45`,
bounds every Bernstein polynomial by its symbol's declared bound at ALL
rational points in [0,1]. `continuousProbe_norm_bound`, same file at line 70,
passes the squared bound to the actual original symbol vector.
`momentPairing_bound` at line 82 and `momentPairingCertificate` at line 103
give two-sided convergence of the SAME original moment functional on
products of Bernstein polynomials to the pairing of their constructed
symbol vectors, with real/Cauchy/rate data retained. `cuspVector_norm_bound`
at line 117 bounds the concrete cusp vector's squared norm by one.
No nonzeroness conclusion is stated for that particular vector.
These are fixed-nome, fixed-spacing laws. The stated uniformity is in
approximation degree and rational spectral point, not beta or spacing.

## Symbol compatibility and cyclic operator-bound update after 910c342

`continuousProbe_congr`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicSymbolCompatibility.lean:86`,
proves equality of the original symbol vectors from rational pointwise
equivalence on [0,1], without equal bounds, moduli or outside values.
`comparisonModulus`, same file at line 67, retains the uniform comparison
stage. `continuousProbe_eq_polynomial` at line 100 identifies the vector
with the actual original p(T2)v for a symbol agreeing with p on [0,1].

`polynomialOperator`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicPolynomialOperator.lean:85`,
is the existing time/scalar/addition polynomial action on the original
completion. `operator_mul`, same file at line 94, proves composition;
`operator_one` at line 102 proves identity; `operator_coordinate` at line
105 recovers the SAME two-step transfer. `operator_symmetric` at line 110
proves symmetry on the original pairing. These are finite polynomial
operator laws, not continuous functional calculus.

`cyclic_norm_bound`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicCyclicOperatorBound.lean:60`,
proves ||p(T2)q(T2)v||^2<=M^2||q(T2)v||^2 for every polynomial q from
|p|<=M on rational [0,1]. `cyclic_distance_bound`, same file at line 77,
gives the relative distance bound. The factor is uniform in q; neither
statement quantifies over all completed input vectors or over varying
physical nome/spacing. No supplied spectral resolution or operator-bound
hypothesis is consumed.

## Original polynomial action on represented cyclic limits after dbaa81b

`normFactor`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicPolynomialContinuity.lean:33`,
computes K([])=0, K(c::p)=2*c^2+2*K(p). `operatorTolerance`, same file
at line 98, is epsilon/(K+1); `operator_close` at line 104 proves
continuity of the existing original polynomial action.

`operatorRows`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicPolynomialRowAction.lean:30`,
constructs mapped original Cauchy rows. `operator_rowLimit`, same file at
line 51, equates their limit with the original polynomial operator on the
input limit. `actionCertificate` at line 65 retains the representative,
same-action pin and computed convergence rate.

`rowLimit_norm_comparison`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicCyclicLimitBound.lean:52`,
passes relative norm bounds to original row limits using the explicit
epsilon/(C+1) error budget. `cyclicLimit_norm_bound`, same file at line 73,
applies this to represented families of original cyclic polynomial vectors.
`continuousProbe_operator_norm_bound` at line 89 proves
||p(T2)F(T2)v||^2<=M^2||F(T2)v||^2 for |p|<=M on rational [0,1].
The continuity coefficient factor is absent from this bound.
`continuousActionCertificate` at line 115 returns the actual polynomial
action on the symbol vector with its image representative and original
polynomial-product approximation rate. No continuous-symbol operator,
full-carrier spectral realization or varying-spacing estimate is asserted.

## Constructed original continuous action after 77aabf9

`CyclicPresentation`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicCyclicPresentation.lean:42`,
retains existing Cauchy rows, polynomial coefficients and point pins.
`state` at line 47 is still in the original completion. `ofSymbol` at
line 49 and `ofPolynomial` at line 55 construct instances.
`approximationTolerance` at line 85 and `polynomial_close` at line 99
compute and prove a tolerance from the represented state's norm ceiling.
This is represented cyclic data, not a new physical analytic premise.

`symbolRows`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicContinuousAction.lean:40`,
constructs actual original Bernstein-polynomial image Cauchy rows.
`symbolAction` at line 52 is their original completion limit.
`symbolAction_norm_bound` at line 82 proves the relative bound
||F(T2)x||^2<=F.bound^2||x||^2. `symbolActionCertificate` at line 90
retains the value's Cauchy representative, explicit rate and norm bound.
No image-Cauchy or spectral-decomposition premise is supplied.

`symbolAction_input_congr`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicContinuousActionCompatibility.lean:40`,
proves independence from representation for equal original states.
`symbolAction_symbol_congr` at line 47 requires symbol equality only on
rational [0,1]. `symbolAction_eq_polynomial` at line 70 recovers the existing
polynomial operator, and `symbolAction_probe` at line 85 recovers the
original symbol vector on the normalized probe. `cuspActionCertificate`
at line 93 supplies all data for a cusp-on-cusp instance; no nonzeroness
conclusion is stated for that value. Represented-sector closure, full
continuous operator algebra and physical-scale/continuum control are
not conclusions of these declarations.

## Constructed cyclic closure and bounded linearity after e26ae24

`cyclicIndex`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicContinuousCyclicClosure.lean:42`,
selects an input row using the polynomial-action modulus at 1/(n+1).
`cyclicPolynomial_error` at line 55 proves the corresponding polynomial
product on the original probe approximates the nth action row.
`actionPresentation` at line 100 constructs output cyclic data;
`state_actionPresentation` at line 116 pins its original state to the
existing action value. `actionPresentationCertificate` at line 123
returns that presentation and an explicit polynomial convergence rate.

`addPresentation`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicCyclicLinear.lean:91`,
constructs represented sums. `polynomialPresentation` at line 101,
`smulPresentation` at line 111 and `subPresentation` at line 117 retain
the corresponding original states, with state pins at lines 98, 108,
113 and 120. These are constructions, not analytic closure hypotheses.

`symbolAction_add`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicContinuousLinear.lean:45`,
and `symbolAction_smul` at line 54 prove rational linearity.
`symbolAction_distance_bound` at line 69 proves the relative original
squared-distance bound F.bound^2*d(x,y). `inputTolerance` at line 76
is epsilon/(F.bound^2+1), with its effect proved by `symbolAction_close`
at line 82. `composition_norm_bound` at line 107 controls actual composed
actions on the constructed sector. No symbol multiplication identity,
full-carrier or physical-scale spectral theorem follows in these files.

## Original product limits and multiplication after 4b7f172

`productModulus`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicContinuousProductRows.lean:66`,
computes a shared rate for actual Bernstein polynomial-product actions.
`product_bound` at line 71 proves convergence to the existing composition.
`productRows` at line 87 constructs its Cauchy family;
`productAction_eq_composition` at line 108 proves the original limit pin.
`productCertificate` at line 116 retains the representative and rate.

`product_symbol_error`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicContinuousMultiplication.lean:63`,
uses one stage for all rational [0,1] points. `symbolAction_mul` at line
115 proves H(T2)x=F(T2)G(T2)x, given existing H continuity/vanishing data
and agreement with F*G on rational [0,1]. It does not construct H's data.
`symbolAction_comm` at line 133 proves commutation for all represented
F,G without an H package. All states and operators are the originals.

`cuspSquareSymbol`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicCuspMultiplication.lean:43`,
has bound 1 and modulus 2*abs(delta). `cuspSquareVanishing` at line 51
supplies epsilon/2. `cuspSquare_composition` at line 65 is a fully supplied
product-law instance on every represented cyclic input. The nonconstancy
at line 62 is about the symbol, not a nonzero original action value.

## Original continuous form order and symmetry after ae243de

`constantRows`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicRowPairingOrder.lean:31`,
retains a supplied original representative with zero outer modulus.
`rowLimit_pairing_le` at line 47, `rowLimit_pairing_eq` at line 63 and
`rowLimit_pairing_nonnegative` at line 69 pass rowwise facts to actual
original limits using the existing pairing modulus.

`cyclic_form_mono`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicCyclicFormOrder.lean:40`,
uses the existing positive moment functional on p*r*r.
`polynomial_form_mono` at line 54 and `polynomial_form_nonnegative` at
line 65 extend this to every represented original cyclic state.

`symbolAction_symmetric`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicContinuousFormOrder.lean:88`,
passes original polynomial symmetry to the continuous action.
`symbolAction_form_mono` at line 98 and `symbolAction_form_nonnegative`
at line 111 use order-preserving Bernstein weights and samples, with the
degree-zero case included. `square_form_identity` at line 121 gives
<H(T2)x,x>=||F(T2)x||^2 for represented H=F*F.
`cuspSquare_form_identity` at line 128 supplies the concrete instance.
These are nonnegative form statements, not strictly positive physical gaps.

## Source-level boundaries before canonical reconstruction

| Boundary | Concrete source | Canonical requirement / status |
| --- | --- | --- |
| Observable carrier | `PlaquetteExpression`, `lean/YMGap/Continuum/BF4ExactSlabPlaquetteObservableAlgebra.lean:49`, has unit, plaquette-character, sum, product and rational-scaling constructors. Its module explicitly excludes a claim to represent all Wilson loops. | `PositiveTimeOSRoot.representativeSupported`, `lean/YMGap/Continuum/CanonicalOSRoot.lean:290`, and `stateEssentiallySurjective`, same file, line 296, concern certified observables of the canonical limiting algebra. A bridge from this concrete carrier to that root was **NOT FOUND** in the search scope below. |
| Scalar codomain | `value`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicLowerFunctional.lean:54`, is RC-valued; `valueRepresentative`, same file, line 62, retains CReal/QCauchy data. | `ProbFunctional.E`, `lean/YMGap/Continuum/ObservableMeasure.lean:82`, and `GNSData.B`, `lean/YMGap/Continuum/GNSQuotient.lean:102`, are Q'-valued. `PositiveTimeOSRoot.positive`, `lean/YMGap/Continuum/CanonicalOSRoot.lean:272`, requires that `GNSData`. These are different declared types; no rational-value conversion is proved here. |
| Completion | `Completion`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicSeminormCompletion.lean:155`, is the existing Cauchy-class carrier. `embedOSQuotient_injective`, same file, line 200, proves the original OS quotient embeds injectively. | `CauchyRows`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicCauchyRows.lean:48`, requires supplied representative rows. `rowLimit` at line 99, `rowLimit_bound` at line 104 and `rowLimit_independent` at line 147 construct their unique limit. These declarations do not take an arbitrary sequence of quotient points without representative data. The module explicitly leaves full quotient-level completeness separate. |
| Time and form pins | `completedTime`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedTime.lean:53`, acts on that completion; `completedTime_moments`, same file, line 153, pins the moments of the same operator. | `PositiveTimeOSRoot.reflectedForm` and `transferRepresentative`, `lean/YMGap/Continuum/CanonicalOSRoot.lean:298` and line 302, require pins to the SAME canonical ambient observable algebra and its `tau`. No inhabitant supplying these canonical pins from the concrete modules was found in the stated search. |
| Probe normalization | `unitProbe_norm`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicNormalizedProbe.lean:64`, now proves the actual RC-valued squared norm is one; `normalizedCertificate`, same file, line 131, retains its strict response interval and QCauchy data. | `PositiveTimeOSRoot.probeNormOne`, `lean/YMGap/Continuum/CanonicalOSRoot.lean:321`, is still a field of the canonical Q'-valued representative form. RC normalization is closed, but the scalar/carrier comparison required to fill this canonical field is not supplied by the new declaration. |
| Continuum approximation | The new orbit and floors have integer-time parameters, but no spacing schedule. | `ReferenceWeightStageFamily.spacingTendsToZero`, `lean/YMGap/Continuum/CanonicalOSRoot.lean:93`, and `CanonicalSchwingerLimit.continuumModulus` / `approximationConverges`, same file, lines 146–147, require an actual second limiting parameter alongside volume. They are not consequences stated by the new orbit declarations. |

Historical search scope at cd75a56 for the missing concrete-to-canonical inhabitant: all
`lean/YMGap/Continuum/BF4ExactSlab*.lean` files were searched for
`CanonicalOSRoot`, `CanonicalSchwingerLimit`, and `PositiveTimeOSRoot`, with
no matches. The destination structures in `CanonicalOSRoot.lean` and the
concrete modules cited above were inspected. This is a scoped **NOT FOUND**,
not a claim of mathematical impossibility or permission to change a field.

## Repointed work boundary

The concrete response-survival obligation is closed, including returned
positive margins. It must not be reopened as another supplied response
hypothesis. The remaining realization work must address the observable
carrier, scalar codomain and completion boundaries above. RC normalization
is now closed by the declarations above, not a new open input.
No canonical type, atom or flag is changed by this increment.

The older functional calculus still requires a supplied diagonal spectral
resolution: `PolyNormData.normDiag`,
`lean/YMGap/Continuum/ContinuousFunctionalCalculusForm.lean:379`, is a
structure field, consumed by `dischargeBTC` at line 390. It is not an
original spectral decomposition constructed by the new normalization.

Mixed positivity, finite normalized rows, signed-polynomial convergence,
the positive bounded normalized polynomial functional, actual polynomial
difference bounds, represented Bernstein carrier limits, their pairing
convergence and symbol-vector norm bounds are now closed by the declarations
above. Symbol-equivalence compatibility, actual polynomial operator algebra
and relative cyclic polynomial bounds are also now closed. Original
polynomial action and sharp relative bounds on represented cyclic limits
are now closed as well. Continuous-symbol action and state/symbol
representation independence are now constructed, as are output cyclic
presentations and bounded rational linearity. Product limits, multiplication
for represented product symbols and commutation are now constructed.
Symmetry, form order and positivity are now proved as well. Next: general
product-symbol data construction, remaining symbol algebra compatibility
and quantitative spectral consequences on the original represented sector.
Neither a spectral measure nor a full continuous operator calculus is claimed.
Full observable realization, continuous-time generator and physical
spectral/non-Wick pins, controlled continuum scaling, other groups and
Clay remain open.

## Verification boundary

The symmetry/form-order increment has three new modules and 21 exactly
matched gates within `{propext, Quot.sound}`, none axiom-free.
The product/multiplication increment has three new modules and 30 exactly
matched gates within `{propext, Quot.sound}`, two axiom-free.
The cyclic-closure/bounded-linearity increment has three new modules and
42 exactly matched gates within `{propext, Quot.sound}`, none axiom-free.
The continuous-action increment has three new modules and 32 exactly
matched gates within `{propext, Quot.sound}`, none axiom-free.
The represented cyclic-limit operator increment has three new modules
and 30 exactly matched gates within `{propext, Quot.sound}`, one axiom-free.
The symbol-compatibility/cyclic-operator increment has three new modules
and 28 exactly matched gates within `{propext, Quot.sound}`, none axiom-free.
The original limit pairing/norm increment has three new modules and 31
exactly matched gates, all with only `{propext, Quot.sound}`; none axiom-free.
The represented Bernstein carrier increment has four new modules and 54
exactly matched gates within `{propext, Quot.sound}`, six axiom-free.
The signed-polynomial/functional/cyclic-norm increment had four new modules
and 57 exactly matched gates within `{propext, Quot.sound}`, three axiom-free.
The all-order moment-convergence increment had three new modules and 61
exactly matched gates within `{propext, Quot.sound}`, five axiom-free.
The mixed-moment/finite-row increment had three new modules and 55 exactly
matched axiom gates within `{propext, Quot.sound}`, four axiom-free.
The normalization increment had three new modules and 60 exactly matched
`#print axioms` gates within `{propext, Quot.sound}`, five axiom-free.
The preceding orbit increment had 28 matched gates. Focused monitored
checks only, one worker and a
20 GiB ceiling. No new hole or analytic input, no increased options, no
full-tree build/audit/guard/progress run, and no root-import rebuild.
Exact logs are listed in `work_plan.md`.
