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
above. Next: symbol-equivalence compatibility and operator calculus on the
original cyclic sector. Neither
a spectral measure nor a full continuous operator calculus is claimed.
Full observable realization, continuous-time generator and physical
spectral/non-Wick pins, controlled continuum scaling, other groups and
Clay remain open.

## Verification boundary

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
