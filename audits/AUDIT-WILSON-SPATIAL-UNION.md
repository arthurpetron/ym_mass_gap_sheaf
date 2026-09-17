# Coherent original Wilson spatial union and its nonvacuous strict bound

Date: 2026-09-17 UTC. This checkpoint follows pushed `2dc4201` and is
**PROGRESS**, not completion of the whole-project goal.

WHOLE-PROJECT GOAL: construct nontrivial continuum Yang--Mills on R^4,
with the required QFT axioms, isolated vacuum and strictly positive finite
physical Hamiltonian mass gap, for EVERY compact simple gauge group,
within the constructive axiom gate. **The Clay target remains OPEN.**

## Time balance and quantitative decay follow-up

2026-09-17 UTC, after pushed `699bff9`: **PROGRESS**. The original
time-sum identity now passes through each pair's computed common base and
the actual completed pairing limits. Thus `B(T_m x,T_n y)=B(x,T_(m+n) y)`.
The fixed unit implies `B(T_n x,U)=B(x,U)`, so its orthogonal complement
is invariant. The existing two-step form bound then gives
`B(T_1 x,T_1 x)<=q(w) B(x,x)`, and induction proves
`B(T_n x,T_n x)<=q(w)^n B(x,x)` on that SAME complement.

This removes the time/form compatibility join listed at the preceding
checkpoint below. No spectral model, eigenbasis, one-step positivity or
new analytic hypothesis is used. Sharp CS gives
`B(x,T_n y)^2 <= B(x,x) * (q(w)^n B(y,y))`; x is arbitrary and only y
must be orthogonal to U. Original dense correlators retain the literal
time advance. The result applies to the prior actual nonzero vector,
`vector_orthogonal` in `lean/YMGap/Continuum/BF4WilsonSpatialUnionSmallNomeGap.lean:69`.
It does not prove a nonzero positive-time response.

All paths in the following table are under `lean/YMGap/Continuum/`.

| Proved edge | Declaration and module:line |
| --- | --- |
| Computed common base -> original time-sum identity | `pairing_time_sum`, `BF4WilsonSpatialUnionTimeForm.lean:51` |
| Actual pairing limits -> completed time balance | `representativeInner_time_sum`, same file:74; `completedInner_time_sum`, :85; `completedInner_time_balance`, :92 |
| Same fixed unit -> invariant complement | `completedUnitCoefficient_time`, same file:129; `completedTime_preserves_orthogonal`, :132 |
| Actual completed time -> original dense correlator | `completedTime_correlator`, same file:137 |
| Strict two-step form -> one-step squared-norm bound -> iteration | `oneStep_norm_gap`, `BF4WilsonSpatialUnionRelaxation.lean:58`; `norm_decay`, :64 |
| Half-time diagonal / sharp CS -> correlator bounds | `even_autocorrelation_decay`, same file:79; `mixed_correlator_sq_decay`, :85 |
| Supplied scalar Cauchy data -> norm ceiling | `normCap`, same file:93; `norm_le_cap`, :108 |
| Explicit geometric cutoff -> late-tail tolerance certificate | `relaxationModulus`, same file:113; `norm_small`, :116; `relaxationCertificate`, :132 |

The rate is exactly the existing `twoStepRate`,
`BF4ExactSlabFixedSpatialSpatialDenseGap.lean:65`: the square of
`timeRate(w)=entropyRate(625,adjustedCoreRate(w,hd))` (:48). Its strict
positivity and upper bound use the original nome guards (:68, :72).
n counts original ONE-step advances, so the squared-norm exponent is n,
not 2n. The bound is vector/base independent at fixed w, not uniform in
bare coupling or physical spacing.

For supplied X, let s be its actual representative diagonal and cs its
computed rational Cauchy data. `normCap(X)=abs(s.approx(cs.M 1))+1`, using
`scalarCeiling`, `BF4ExactSlabPlaquetteRealScalarCauchy.lean:52`.
The threshold is `geometricCutoff(q(w),normCap(X),epsilon)`, defined in
`PositiveContractionResidual.lean:119` and certified by `geometric_bound`
(:126). It depends on nome, the supplied stream and tolerance. It is not
asserted equal for different representatives, nor selected from a quotient.

Next: completed linear operations and form laws on this Wilson union.
Full Hilbert completeness and the canonical observable/state realization
remain open, as do positive-time response/normalization, full spatial
symmetry, changing-spacing control, finite physical mass calibration,
continuum survival and the every-group theorem. Canonical frontier fields
and the AF obstruction are unchanged. No Clay atom closes.

Both focused checks exited 0, all 23 public axiom gates within
{propext, Quot.sound}, with no warnings/errors. Main alone compiled with
one monitored worker and a 20 GiB ceiling after fresh process/swap checks;
no competing build/test/runner, swap stable at 6869.19 MiB. Root imports
were added; root/full-tree/full audit/guard checks were NOT run. No prior
proof, sorry, axiom, analytic guard or safety limit changed. CI remains
manual and no literature scan ran. Independent read-only review confirmed
time normalization, complement invariance and the mixed bound's one-vector
orthogonality condition; it did not run a build.

Final logs under `/tmp/`:

| Log | Gates | SHA-256 |
| --- | ---: | --- |
| `ym-wilson-union-time-form-20260917.log` | 13 | `c9695db120023807438d09bb43bfd6a18bc713e50c42582d0c524350ced8084b` |
| `ym-wilson-union-relaxation-20260917.log` | 10 | `5b20ae21fa53dc45117938111f72be129c79b9e5f1ef0df117e23e9530abad5e` |

The remaining sections record the preceding coherent-union checkpoint;
their next-step language is historical. Use the follow-up above for the
current time/form and decay status.

## Original checkpoint: result and causal argument

The actual original Wilson limiting form and distance are independent of
enlarging the source-base guard. The proof retains the literal oriented loop
words, spins, offsets and signed coefficients. Under the original ambient
embedding, the smaller selected action becomes the masked target action,
not the full target law. Each law retains its own partition. The signed
boundary estimate compares masked and full laws before taking absolute values.

The support box has side `max(base+1,2*H+1)`, computed from the SOURCE
expression. The error amplitude and the explicit late-margin modulus do
not depend on the larger base, cutoff stage or exterior time buffer. Both
actual three-regulator diagonal convergence witnesses are used; equality
of the limits does not assert equality of their approximations or moduli.

EXPANSION isolates these original-word, action, support, interval, modulus
and limit-identification proofs. CONTRACTION composes them into coherent
mixed pairings and distances at finite common bases. One staged carrier
contains the existing finite-base Wilson windows, and one Cauchy quotient
completes that union. The base/radius/cap may grow along a supplied stream;
there is no whole-stream maximum-base assumption and no union of fixed-base
completions masquerading as a completion of the union.

Original time acts termwise and retains each supplied Cauchy modulus.
Its embedded unit is fixed through actual null distance, not literal equality
of radius-tagged unit syntax. Quantitative four-input continuity supplies
the completed pairing, its symmetry, positivity, normalization and sharp CS.

The prefactor-free centered estimate is applied at each stage's OWN positive
base. The three actual pairing limits then give
`B(x,T_2 x) <= q(w)*B(x,x)` for every unit-orthogonal vector in this SAME
union completion. Here `q(w)=entropyRate(625,adjustedCoreRate(w,hd))^2`.
The original guards give `0<q(w)<1`; the rate is independent of the vector
and its bases, but depends on nome. There is no beta-independent or
changing-spacing physical mass assertion.

The actual fixed-base completion map preserves mixed pairings, time, unit,
zero, and supplied stream/closeness moduli. The original nome-1/1024,
base-one excitation maps to a unit-orthogonal union vector with the SAME
positive norm floor, hence remains nonzero. Finally, the distance-to-zero
identity gives completed positive definiteness, with a computed closeness
modulus. The strict bound therefore forces any two-step stationary vector
in the unit complement to be zero.

## Declaration-to-dependency map

All paths in this table are under `lean/YMGap/Continuum/`.

| Proved edge | Declaration and module:line |
| --- | --- |
| Actual polynomial-level masked/full action estimate | `finiteValue_bound`, `BF4ExactSlabFixedSpatialBaseBoundaryComparison.lean:101` |
| Unchanged original ordered loop | `includeLoop_edges`, `BF4ExactSlabFixedSpatialWilsonBaseInclusion.lean:52` |
| Same ambient Wilson polynomial across source guards | `includeExpression_placed`, same file:128 |
| Original recentered insertion under actual Haar embedding | `aligned_chartInsertion_pin`, `BF4ExactSlabFixedSpatialWilsonBaseCoherence.lean:82` |
| Source-sized locality and uniform original scalar comparison | `included_chartInsertion_local`, same file:114; `chartScalar_inclusion_bound`, :129 |
| Computed larger-base-independent threshold | `inclusionModulus`, same file:153; `chartScalar_inclusion_close`, :160 |
| Actual three-regulator limit equality | `spatialLimit_inclusion`, same file:179 |
| Same intrinsic mixed form and squared distance | `intrinsicForm_inclusion`, same file:203; `distSq_inclusion`, :212 |
| Common-base original scalar and explicit Cauchy data | `pairing_at_base`, `BF4WilsonSpatialUnion.lean:122`; `pairingCauchy`, :118 |
| Actual union distance on finite comparisons | `distSq_at_base`, same file:151 |
| Arbitrary-stage Cauchy quotient and original time | `unionSeminorm`, `BF4WilsonSpatialUnionSeminorm.lean:98`; `UnionCompletion`, :139; `completedTime`, :143 |
| Supplied time-stream modulus unchanged | `time_cauchy_modulus`, same file:163 |
| Actual unit fixed by null distance | `time_unit_null`, same file:170; `completedUnit_fixed`, :176 |
| Four-input continuity, no stream-wide support cap | `pairing_close`, `BF4WilsonSpatialUnionPairingData.lean:75` |
| Actual quantitative completed pairing | `pairingData`, same file:117; `representativeInnerCauchy`, :128; `completedInner`, :132 |
| Each stage's own original centered scalar | `centeredMoment_diagonal_pin`, `BF4WilsonSpatialUnionCenteredForm.lean:83` |
| Same nome-only strict rate at every stage | `centered_twoStep_bound`, same file:102 |
| Arbitrary union streams -> actual scalar limits | `representativeCenteredMoment_converges`, `BF4WilsonSpatialUnionCompletedGap.lean:73` |
| Universal bound on the SAME completed unit complement | `completed_twoStep_form_gap`, same file:153 |
| Fixed-base maps with supplied moduli | `liftCauchy`, `BF4WilsonSpatialUnionFixedBase.lean:52`; `liftClose`, :68; `completionMap`, :82 |
| Exact completed mixed pairing and original time | `completedInner_map`, same file:110; `completionMap_time`, :117 |
| Original unit and zero retained | `completionMap_unit`, same file:125; `completionMap_zero`, :137 |
| Concrete positive strict rate | `rate_strict`, `BF4WilsonSpatialUnionSmallNomeGap.lean:53` |
| Actual nonzero excitation with positive norm and SAME strict bound | `concreteGapCertificate`, same file:102; `concreteGapCertificate_image`, :111 |
| Distance-to-zero/form-diagonal identity | `distance_zero`, `BF4WilsonSpatialUnionPosdef.lean:49` |
| Computed zero-norm closeness and its exact modulus | `closeZeroOfInnerZero`, same file:68; `closeZeroOfInnerZero_modulus`, :74 |
| Positive definite completed form | `completedInner_posdef`, same file:93 |
| No nonzero stationary vector in the unit complement | `fixed_orthogonal_eq_zero`, same file:99 |

## Exact scope and next joins

The spatial union is of the existing syntax, not a coverage theorem for
every gauge observable. Its `Stage.value` is an `IntrinsicExpression` of
spatial loops scheduled in time windows. In particular, this checkpoint
does not identify all loops traversing several time slices with this syntax.
A fixed-base completion map is not asserted to be surjective.

The immediate next carrier work is completed linear structure and time/form
compatibility on this exact union. The old PhysicalSpan union's
`completedAdd` and `completedSmul`,
`lean/YMGap/Continuum/BF4SpatialUnionLinear.lean:241` / :245, are templates,
not operations already proved on this Wilson union. Full constructive
Hilbert completeness is separate from forming a quotient of supplied
Cauchy streams.

Canonical OS realization is still open. `PositiveTimeOSRoot`,
`lean/YMGap/Continuum/CanonicalOSRoot.lean:268`, requires its actual
`positive : GNSData` (:272), representative/state inverse and support
pins, `stateEssentiallySurjective` (:296), `reflectedForm` (:298), and
`transferRepresentative` (:302). The new CReal-valued form cannot silently
replace these canonical fields, nor does a coherent spatial union supply
their missing observable-algebra realization.

Positive-time nonzero response/normalization, full spatial symmetry,
changing-scale original-action control, finite physical mass calibration,
continuum existence/nontriviality and every compact simple group's physical
producers remain open. The prior AF obstruction and canonical frontier
fields are unchanged. Positivity remains an even-time assertion. No
one-step positivity, continuum Hamiltonian, beta-uniform physical mass,
or canonical Clay-atom closure is claimed.

## Verification and source review

Eleven focused final checks exited 0, with all 152 public gates reporting
only {propext, Quot.sound} or no axioms. No final log contains a warning,
error, sorryAx, classical-choice or native-reduction dependency. Development
fixes made zero-shift and identity-inclusion pins explicit, corrected a
namespace/parameter scope, and prevented expensive implicit scalar unfolding
with local opacity. No proof statement, analytic guard or resource limit
was weakened. Failed development logs are not verification evidence.

Main alone compiled serially through `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check <file> --check-output <its olean>`.
Fresh process/swap preflights found no competing Lean/test/runner processes;
swap remained 6869.19 MiB. Root imports added; root/full-tree/full-audit/
guard checks NOT run. No old Lean proof, sorry, axiom or canonical field
changed. CI remains manual; no routine literature scan ran.

Three parallel agents developed inclusion, boundary comparison, union
carrier/seminorm, pairing, centered moments, fixed-base maps and nonvacuity.
Independent source review specifically checked masked/full normalization,
source-sized support, comparison signs, three-moment centering and the absence
of a common-base assumption for streams. Main supplied and checked coherence,
completed-gap passage and the norm-separation/stationarity consequence.

Final logs are under `/tmp/`:

| Log | Gates | SHA-256 |
| --- | ---: | --- |
| `ym-base-boundary-comparison-20260917.log` | 1 | `5a9ed21575af3a37d71a6dfeda262bebbfe89293b2a44aabb990f73b3fca9a2d` |
| `ym-wilson-base-inclusion-20260917-final.log` | 26 | `bbf422b33780f420961043b020c58bdc62bb4730770f07eb19ed9a4aa43349c0` |
| `ym-wilson-base-coherence-20260917-pin.log` | 11 | `57f52a25ee1c3b52825bac05f39dffffca6b2d2074cf61a9e3802dae743f26c8` |
| `ym-wilson-spatial-union-20260917-pins.log` | 27 | `a394a5b4e2a011770cb5cf8636c3b2edb9df2ec6f75884a7edd24ea13f860baa` |
| `ym-wilson-union-seminorm-20260917.log` | 20 | `d2cd5ad8a201af227af9f6748af77fe19794815f8d00a4357a7adbfb77bb6bdb` |
| `ym-wilson-union-pairing-20260917.log` | 15 | `97f5e3ea89da56b2986247656cbbe1bfc0dbb6ee009bd319dc2c73f64d71b562` |
| `ym-wilson-union-centered-20260917.log` | 7 | `c386841fbfe822cde523f3faf90f873f96c472284feeb1bc94a2d1525db28a9a` |
| `ym-wilson-union-completed-gap-20260917.log` | 11 | `49aef83e790777dfa003f7793452d5064734b82e1896a8d8a3e8691c14bce739` |
| `ym-wilson-union-fixed-base-20260917.log` | 13 | `55ae5c054541a6e98c48da0cf82c7b04ca58250ce2fbc3ab77a73cd220d3cfe6` |
| `ym-wilson-union-posdef-20260917.log` | 9 | `54ce5c7af33f513521d4fd63f6c5ae56e2a960f52f01779e93ef31d6300873bc` |
| `ym-wilson-union-small-nome-20260917.log` | 12 | `2a334e76cea0de5a1c0bcc48c78ff00283dab3766a47a1dfaf344360648d5ea4` |
