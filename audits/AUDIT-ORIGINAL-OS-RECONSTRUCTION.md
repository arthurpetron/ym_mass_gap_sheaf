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

Mixed positivity and finite normalized Bernstein rows are now closed by
the declarations above. Next unproved targets: higher factorial moments
and quantitative polynomial convergence of these SAME rows. Neither a
spectral limit nor its functional-calculus realization is claimed.
Full observable realization, continuous-time generator and physical
spectral/non-Wick pins, controlled continuum scaling, other groups and
Clay remain open.

## Verification boundary

The mixed-moment/finite-row increment has three new modules and 55 exactly
matched axiom gates within `{propext, Quot.sound}`, four axiom-free.
The normalization increment had three new modules and 60 exactly matched
`#print axioms` gates within `{propext, Quot.sound}`, five axiom-free.
The preceding orbit increment had 28 matched gates. Focused monitored
checks only, one worker and a
20 GiB ceiling. No new hole or analytic input, no increased options, no
full-tree build/audit/guard/progress run, and no root-import rebuild.
Exact logs are listed in `work_plan.md`.
