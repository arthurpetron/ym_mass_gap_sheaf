# Strict form bound on the SAME completed Wilson carrier

Date: 2026-09-17 UTC. Base: `10ffadb`, committed and pushed. The preceding
original-time checkpoint is classified **PROGRESS**.

WHOLE-PROJECT GOAL: nontrivial continuum Yang--Mills on R^4, with the required
QFT axioms and a strictly positive physical Hamiltonian mass gap above the
vacuum, for EVERY compact simple gauge group, within the constructive axiom
gate. **The Clay target remains OPEN.** This result is fixed-spacing,
small-nome SU(2), separately for every positive source base.

## Result

On the existing Wilson Completion and its actual original discrete time,
every vector x with `B(x,U)=0` satisfies
`B(x,T_2 x) <= q(w)*B(x,x)`, where
`q(w)=rho(w)^2` and `rho(w)=entropyRate 625 (adjustedCoreRate w hd)`.
The existing explicit guards prove `0<q(w)<1`. The rate does not depend on
the vector, its expression radius or its positive source base.

At the existing nome 1/1024 and base one, all guards are discharged. The
same previously constructed nonzero centered plaquette has its positive
norm floor and this completed bound. Its vector identity is literal, not
an isometry to an older carrier. No nonzero positive-time response, full
Hilbert completeness or continuum spectral/physical mass claim follows here.

## Mathematical expansion and contraction

EXPANSION separates actual original-action probes and actual OS-form moments.
At H=R+n, the reflected left expression is its radius-reversed schedule
placed at A+H; the advanced right expression is its fixed R chart at A.
Both support boxes have side `N=max(base+1,R+1)`. The inclusive spatial
fringe is retained, and the intervening time gap is in neither box.
Original loop words, noncommutative factor order, spins and signs remain.

The joint moment and BOTH marginals have exactly the same action, cutoff,
extent and partition. The signed covariance theorem cancels that original
partition square before estimating. Its bound is
`A(w,base,R,x,y)*rho(w)^(R+n+1-M)`, with `M=12*N^4` and natural truncated
subtraction. A contains no spatial margin, heat stage, boundary buffer or
time lag. The existing original three-regulator diagonal passes this bound
to the SAME intrinsic connected time moment, not an unrelated covariance.

Independently, the actual rational centering streams identify
`B(centeredVector x,T_n(centeredVector y))` with
`F(x,advance n y)-F(x,U)*F(U,y)`. Their own mean approximations and vector
Cauchy moduli are retained. Existing time balance and sharp CS give actual
even moments m(k) with `0<=m(k)<=m(0)` and
`m(k)^2<=m(k+k)*m(0)`.

CONTRACTION first absorbs M into the explicitly positive prefactor
`P=A/rho^M+1`, then applies the constructive dyadic theorem to
`m(k)<=P*q^k`, obtaining `m(1)<=q*m(0)` without dividing by the norm.
Only this prefactor-free inequality is passed through arbitrary vector
Cauchy streams. Thus their expression caps and radii need not be uniformly
bounded, and their approximants need not be individually orthogonal.
At the completed limit the actual unit coefficient removes the scalar
correction. This proves the universal unit-complement statement.

## Checked declaration map

Paths below are under `lean/YMGap/Continuum/`.

| Mathematical edge | Declaration and module:line |
| --- | --- |
| One common original chart and partition | `chartPairing`, `BF4ExactSlabFixedSpatialWilsonOriginalConnectedCorrelator.lean:37`; `connectedScalar`, :41 |
| Actual three-regulator diagonal -> original connected time moment | `connectedScalar_time_converges`, same file:81 |
| Literal finite schedule reversal | `reverse`, `BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl.lean:47`; `mirror_chart_reverse`, :84 |
| Shifted source = shifted original placement | `placedPolynomial_shift`, same file:89 |
| Fixed support size independent of lag | `probeBoxSize`, same file:116 |
| Exact two-probe polynomial product | `chartInsertion_separated`, same file:131 |
| Actual original probe interval certificates | `upperProbe_interval`, same file:145; `lowerProbe_interval`, :161 |
| Literal fixed-box link locality | `upperProbe_local`, same file:176; `lowerProbe_local`, :186 |
| Explicit support loss and amplitude | `sizeLoss`, `BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay.lean:62`; `decayAmplitude`, :72 |
| Same joint/marginal scalars -> selected-action covariance | `connectedScalar_selected_pin`, same file:127 |
| Signed covariance estimate -> finite uniform envelope | `connectedScalar_uniform_bound`, same file:177 |
| Actual original centered time/even scalars | `centeredTimeMoment`, `BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments.lean:47`; `evenMoment`, :51 |
| Exact rational centered-time expansion | `centerApprox_time_pairing`, same file:86 |
| Original centering streams -> actual time-correlator pin | `centered_time_representative`, same file:109; `centeredVector_time_pairing`, :155 |
| SAME completed time -> even positivity and contraction | `evenMoment_nonnegative`, same file:167; `evenMoment_le_zero`, :173 |
| SAME completed CS -> sharp dyadic inequality | `evenMoment_dyadic`, same file:181 |
| Original finite envelope -> actual limiting moment bound | `centeredTimeMoment_bound`, `BF4ExactSlabFixedSpatialWilsonDenseGap.lean:45` |
| Computed positive prefactor absorbs fixed support loss | `positivePrefactor`, same file:57; `positivePrefactor_pos`, :61 |
| Actual even moments -> geometric envelope | `evenMoment_le_geometric`, same file:76 |
| Generic dyadic theorem -> prefactor-free centered bound | `evenMoment_first_le`, same file:86 |
| Original orthogonality -> dense strict form bound | `dense_unitComplement_twoStep_bound`, same file:112 |
| Explicit strict rational rate | `twoStepRate_strict`, `BF4ExactSlabFixedSpatialWilsonCompletedGap.lean:41` |
| Actual three-pairing scalar and computed Cauchy data | `representativeCenteredMoment`, same file:59; `representativeCenteredMomentCauchy`, :66 |
| Actual dense connected moments -> actual representative limit | `representativeCenteredMoment_converges`, same file:81 |
| Prefactor-free estimate -> every supplied vector stream | `representative_twoStep_form_gap`, same file:106 |
| SAME quotient induction -> completed centered bound | `completedCenteredScalar_twoStep_gap`, same file:116 |
| Actual unit orthogonality -> universal strict completed bound | `completed_twoStep_form_gap`, same file:157 |
| All guards discharged -> concrete rate and universal bound | `rate_strict`, `BF4ExactSlabFixedSpatialWilsonSmallNomeGap.lean:49`; `twoStep_form_gap`, :56 |
| Existing nonzero vector + positive norm floor + SAME bound | `concreteGapCertificate`, same file:61; `concreteGapCertificate_vector`, :71 |

## Reused machinery and exact scope

The finite analytic consumer is `finite_covariance_distance_bound`,
`lean/YMGap/Continuum/BF4ExactSlabSelectedTwoProbeCovariance.lean:86`.
Its inputs are the actual polynomial probes with interval and LinkLocal
certificates; no ordinary weighted-L2 estimate is relabelled an OS bound.

The prefactor-removal consumer is `dyadic_geometric_first_le`,
`lean/YMGap/Continuum/Z4HalfTimeReflectionStrictJointDenseDyadicGap.lean:365`.
Its full moment hypotheses are proved here for the actual Wilson correlators.
Only the scalar definitions and rate facts `timeRate` / `twoStepRate` /
`twoStepRate_lt_one` are reused from
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialDenseGap.lean:48` / :65 /
:72. No dense or completed gap theorem for the older PhysicalSpan carrier
is imported as a bound on this domain.

Uniformity is explicit: the finite amplitude is uniform in spatial margin,
cutoff stage, boundary buffer and lag, but depends on the original expressions,
R, base and nome. The final relative rate is independent of those expressions,
R and positive base, but depends on nome and retains heat-ratio, remainder
and entropy-smallness guards. No beta-independent or spacing-uniform physical
mass is claimed. Time is the same original discrete-time map, not a heat-bath
or link-update generator. Positivity remains an even-time statement.

## Remaining causal joins

All five requested fronts admit some work before the strict-bound join. This
checkpoint used three parallel branches for the original probe geometry,
connected decay/completion passage, and actual centered time moments with
nonvacuity; main supplied the original diagonal pin and dyadic contraction.
These branches now join in a checked theorem, not just an input bundle.

| Requested front | Current independent progress and remaining dependency |
| --- | --- |
| Nonconstant excitation | `concreteGapCertificate`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSmallNomeGap.lean:61`, joins the existing actual nonzero excitation and positive norm floor to the SAME strict bound. Positive-time nonzero response and continuum survival remain open. |
| Full Hilbert/OS/QFT structure | Actual centered-time moment laws and the completed strict form bound are checked above. Full linear/Hilbert structure and the canonical OS/QFT realization are still separate joins, not consequences of naming the carrier a Completion. |
| Spatial and spacing control | `probeBoxSize`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl.lean:116`, and the checked locality/decay declarations separate support size from lag. Base coherence and changing-scale estimates remain open. `no_fine_guard_on_chart` / `no_blocked_guard_on_chart`, `lean/YMGap/Continuum/BF4SmallNomeAFGuardObstruction.lean:126` / :133, are unchanged. |
| Positive physical mass calibration | Scalar conversion `fullMassRate`, `lean/YMGap/Continuum/PhysicalSeparatorFullLogRate.lean:108`, is reusable independently. The actual changing-spacing inputs and `FullRangeLogRateCeiling`, `lean/YMGap/Continuum/PhysicalSeparatorFullLogComparison.lean:163`, are not supplied by this fixed-spacing theorem. |
| Every compact simple group | Group/representation/global-form/Haar/action producers remain independent work. `mass_gap_of_cartanType`, `lean/YMGap/MassGap/AllSimpleTypes.lean:280`, remains conditional on reconstruction/QFT inputs. `so3_spinHalf_rejected`, `lean/YMGap/RepTheory/CompactSimpleGlobalForm.lean:443`, still rules out copying the spin-half probe unchanged to SO(3). No non-SU(2) physical producer was added in this checkpoint. |

The immediate next original-state task is Wilson spatial-base inclusion and
limiting-form coherence, followed by one carrier for arbitrary finite spatial
supports. A separate uniform theorem at each base is not that union. The old
template `spatialPairing_inclusion`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBaseCoherence.lean:294`, concerns
PhysicalSpan, not the enlarged Wilson domain; its Wilson-specific placement
and action pins remain to be supplied. Do not require a common support base
for an entire Cauchy stream.

Full completed linear/Hilbert structure, observable-algebra coverage and
canonical OS/QFT realization remain open. In particular,
`PositiveTimeOSRoot.positive` and `stateEssentiallySurjective`,
`lean/YMGap/Continuum/CanonicalOSRoot.lean:272` / :296, are not filled by this
CReal-valued form bound. The existing fixed-spacing nonzero excitation is
neither a normalized positive-time response nor continuum nontriviality.

Changing-scale original-action control, positive finite physical mass
calibration and every compact simple group's physical producers remain
independent open joins, as recorded in the preceding
`AUDIT-WILSON-ORIGINAL-COMPLETED-TIME.md`. The AF guard obstruction and all
canonical frontier fields are unchanged. No canonical Clay atom is closed.

## Verification

Seven focused final checks exited 0. All 61 public gates report only
{propext, Quot.sound} or no axioms. Final logs contain no warning, error,
sorryAx, classical-choice or native-reduction dependency. The sole failed
development check lacked the defining namespace for two existing polynomial
unit identities; opening that namespace fixed it without changing a proof
statement, analytic guard or resource limit.

Parent plus three agents developed and cross-reviewed the original-action
pins, support-size independence, centering signs, dyadic product order and
arbitrary-Cauchy passage. Main alone compiled, serially, through
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check
<file> --check-output <its olean>`, after fresh process/swap preflights.
Swap stayed 6869.19 MiB at preflight; no competing Lean/test/runner process
was found. Root imports added; root/full-tree/full-audit/guard checks NOT
run. No old proof, sorry, axiom, canonical field, analytic guard or safety
limit changed. CI remains manual; no routine literature scan ran.

Final logs are under `/tmp/`:

| Log | Gates | SHA-256 |
| --- | ---: | --- |
| `ym-wilson-original-connected-20260917.log` | 5 | `2a85110fac91ab4547881d128263e33074ccf685dd5cf68c298f062789a92974` |
| `ym-wilson-separated-probe-20260917.log` | 15 | `1d20105f8bdc53c2b27f2706ae550d6fb5681c7b52b417b5dd60b9c5add3cfa6` |
| `ym-wilson-uniform-connected-decay-20260917-final.log` | 6 | `2d2bc8ebade90b7e5621c648ced0f84f1aa643626f035db8ee082d10015f11bf` |
| `ym-wilson-centered-time-moments-20260917.log` | 10 | `8236433e7b9b13e6676d258ebd1a8f19f79ed516d578d7e08fb983d7b338f09e` |
| `ym-wilson-dense-gap-20260917.log` | 7 | `0f2c76995fc70919e0c93028698326aa9bd21e2d8e4ea9f05b2409042d47a4d1` |
| `ym-wilson-completed-gap-20260917.log` | 12 | `7c931f68071d4cb7b775e9f33a0b7196087700fddc9e60fe88d1dda9357e6a3c` |
| `ym-wilson-small-nome-gap-20260917.log` | 6 | `c64345749788bc2bdb12d0d91c06c4d5a94e1e9984f57a7d6db30b3eba433855` |
