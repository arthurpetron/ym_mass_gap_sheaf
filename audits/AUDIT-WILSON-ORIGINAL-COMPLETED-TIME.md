# Original time on the SAME completed Wilson carrier

Date: 2026-09-17 UTC. Base: `7d01193`, committed and pushed. The preceding
centered-excitation checkpoint is classified **PROGRESS**.

WHOLE-PROJECT GOAL: construct nontrivial continuum Yang--Mills on R^4,
with the required QFT axioms and a strictly positive physical Hamiltonian
mass gap above the vacuum, for EVERY compact simple gauge group, within
the constructive axiom gate. **That goal remains OPEN.** This checkpoint
concerns small-nome SU(2) at fixed physical lattice spacing and source base.

## Result and causal argument

Original discrete time now acts on the EXISTING Wilson completion. Its
maps obey zero and time-addition laws, fix the embedded original unit,
preserve its orthogonal sector, and retain the actual original dense
correlators. They are nonexpansive for the original reflected form.
Every even-time quadratic form is nonnegative and bounded by the original
diagonal. No one-step positivity, strict rate or spectral theorem is asserted.

EXPANSION separates three actual inputs: literal time-advance geometry,
original-action window stationarity, and an absolute scalar cap unchanged
by time advance. The finite stationarity precursor is an UNEQUAL padding
identity, not a false invariance with boundaries fixed. Its existing
boundary modulus removes both external boundaries; the established spatial
convergence then gives stationarity of the same limiting expectation.

CONTRACTION is a short mathematical argument. If
`a(n)=F(advance n x,advance n x)`, exact time balance gives
`a(n)=F(x,advance (2*n) x)`. Reflection positivity of the literal difference
implies `2*a(n) <= a(0)+a(2*n)`. The original-action cap bounds every `a(n)`
by the same rational number. The existing bounded-midpoint-doubling theorem
therefore gives `a(n)<=a(0)` without dividing by a possibly zero norm.
Compatibility with differences proves distance contraction and null
preservation. The existing completion machinery then needs no new analytic
hypothesis and retains every supplied vector Cauchy modulus.

## Checked declaration map

Paths in this table are under `lean/YMGap/Continuum/`.

| Causal step | Declaration and module:line |
| --- | --- |
| Expression-only cap | `intrinsicCap`, `BF4ExactSlabFixedSpatialWilsonIntrinsicCap.lean:40` |
| Original normalized finite action retains that cap | `chartScalar_abs_bound`, same file:54 |
| Every actual limiting-form approximation inherits it | `intrinsicForm_approx_abs_bound`, same file:74 |
| Signed original-form upper bound | `intrinsicForm_upper_bound`, same file:93 |
| Literal original time advance | `advance`, `BF4ExactSlabFixedSpatialWilsonPhysicalTime.lean:33` |
| Actual time semigroup and signed-difference compatibility | `advance_add`, same file:51; `advance_difference`, :81 |
| Exact reflected product = shift of total-time product | `mixed_advance`, same file:151 |
| Its unshifted source fits Within(2H-m) | `mixed_advance_source_within`, same file:161 |
| Independent left/right padding at fixed action and heat cutoff | `windowRatio_padding`, `BF4ExactSlabFixedSpatialWilsonWindowStationarity.lean:96` |
| Pin to original normalized finite expectation | `originalScalar_padding`, same file:109 |
| Explicit common-tail control with four independent boundary lengths | `originalWindow_rectangle`, `BF4ExactSlabFixedSpatialWilsonLimitStationarity.lean:52` |
| Padding of actual joint limits | `originalJoint_padding`, same file:96 |
| Same-window stationarity after spatial passage | `spatialLimit_shift_within`, same file:168 |
| Geometry + stationarity -> intrinsic time sum/balance | `intrinsicForm_time_sum`, `BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm.lean:62`; `intrinsicForm_time_balance`, :85 |
| Actual signed positivity -> midpoint estimate | `intrinsicForm_midpoint_bound`, same file:91 |
| Radius-tagged unit is fixed in the actual seminorm | `advance_unit_null`, same file:127 |
| Time-independent cap + midpoint doubling -> norm contraction | `timeNorm_le_anchor`, `BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction.lean:80`; `intrinsicForm_advance_contraction`, :89 |
| Literal difference compatibility -> distance contraction | `distSq_advance_contraction`, same file:95 |
| Null inputs remain null | `advance_preserves_radical`, same file:100; `advance_preserves_null`, :109 |
| Actual nonexpansive data and semigroup | `timeNonexpansive`, `BF4ExactSlabFixedSpatialWilsonCompletedTime.lean:49`; `timeSemigroup`, :53 |
| Endomorphism of existing Wilson Completion | `completedTime`, same file:68 |
| Exact zero/addition/dense embedding laws | `completedTime_zero`, same file:74; `completedTime_add`, :77; `completedTime_embed`, :80 |
| Supplied Cauchy modulus retained literally | `time_cauchy_modulus`, same file:88 |
| Embedded original unit fixed | `completedUnit_fixed`, same file:92 |
| Separate actual pair limits -> completed time sum/balance | `representativeInner_time_sum`, same file:99; `completedInner_time_sum`, :112; `completedInner_time_balance`, :119 |
| Contraction on every completion vector | `completedInner_time_contraction`, same file:136 |
| Even-time form = half-time diagonal | `completedInner_even_diagonal`, same file:142 |
| Even-time nonnegativity and upper bound | `completedInner_even_nonnegative`, same file:148; `completedInner_even_le_identity`, :153 |
| Unit coefficient/orthogonal sector invariant | `completedUnitCoefficient_time`, same file:159 |
| Dense correlator is the original advanced form | `completedTime_correlator`, same file:163 |

## Same-object and parameter boundaries

The time map changes distance from the reflection plane; it is not merely
an inclusion into a larger chart. The source word, group multiplication
order, spins and coefficients remain unchanged. The unit's radius tag DOES
change, so fixed-unit descent uses proved null distance, not false record
equality. No alternate carrier, heat-bath generator or ordinary-L2 norm is
substituted.

The form cap is independent of lag, placement radii and lattice regulators,
but depends on the expression. It supplies only constant-one contraction.
All limiting theorems retain the actual `0<w<1`, positive base, heat-ratio,
remainder and entropy-smallness guards. This gives neither a strict rate
uniform in beta nor control along changing physical lattice spacing.

The two scalar limits in each completed pairing comparison use their own
`pairSequence_converges` witnesses from
`lean/YMGap/Continuum/CRealSeminormPairingCompletionLimit.lean:95`.
Physical lag and the Cauchy approximation index are separate parameters.
No equality of their representative reindexings or scalar moduli is assumed.

## Five requested parallel fronts

| Front | Independent work achieved or reusable; remaining join |
| --- | --- |
| Nonconstant excitation | The preceding `concreteCertificate`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonExcitation.lean:127`, already supplies a nonzero unit-orthogonal vector on this SAME completion. The new unit-coefficient invariance preserves that orthogonal sector under original time. Nonzero positive-time response, normalization and continuum survival are not inferred. |
| Full Hilbert/OS/QFT structure | Actual time, its same-form compatibility and completion descent are now proved independently of the strict gap. Full completed linear/Hilbert completeness, full observable coverage and canonical OS/QFT realization remain separate obligations. |
| Spatial and spacing control | The original joint/spatial limits now retain unequal padding and discrete-time stationarity. Base inclusions, full spatial symmetry and changing-scale original-action estimates remain open. The existing AF obstruction is unchanged: `no_fine_guard_on_chart` / `no_blocked_guard_on_chart`, `lean/YMGap/Continuum/BF4SmallNomeAFGuardObstruction.lean:126` / :133. |
| Positive physical mass calibration | `fullMassRate`, `lean/YMGap/Continuum/PhysicalSeparatorFullLogRate.lean:108`, remains available scalar conversion machinery. Neither the actual changing-spacing input nor the finite upper bound in `FullRangeLogRateCeiling`, `lean/YMGap/Continuum/PhysicalSeparatorFullLogComparison.lean:163`, is supplied by constant-one time contraction. |
| Every compact simple group | Group/representation/global-form/Haar/action producers can be developed separately, but this checkpoint supplies no non-SU(2) theory. `mass_gap_of_cartanType`, `lean/YMGap/MassGap/AllSimpleTypes.lean:280`, remains conditional on supplied reconstruction/QFT data. `so3_spinHalf_rejected`, `lean/YMGap/RepTheory/CompactSimpleGlobalForm.lean:443`, still prevents copying this spin-half probe unchanged to SO(3). |

Thus parts of all five fronts admit parallel preparation, but their final
physical joins are not independent. This checkpoint allocated the three
parallel branches to actual mathematical prerequisites of the same-carrier
operator, rather than adding new uninhabited frontier bundles.

## Next strict-bound consumer

The generic analytic estimate already accepts actual polynomial probes:
`finite_covariance_distance_bound`,
`lean/YMGap/Continuum/BF4ExactSlabSelectedTwoProbeCovariance.lean:86`.
Wilson locality is supplied by `placed_recenter_local` and `boxCarrier`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonBoxLocality.lean:96` / :105.
The actual action pin is `chartScalar_original_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSpatialComparison.lean:127`.

NOT FOUND in the current `BF4ExactSlabFixedSpatialWilson*.lean` modules:
a Wilson-specific separated-placement, original connected finite-covariance
pin and lag-uniform geometric envelope for arbitrary intrinsic expressions.
The older plaquette-only templates are `chartProbe_separated`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeparatedProbeControl.lean:75`,
and `connectedScalar_selected_pin` / `connectedScalar_uniform_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialUniformConnectedDecay.lean:135` /
:193. Their PhysicalSpan inputs do not accept arbitrary Wilson expressions.

The next geometry must keep the two support boxes' sizes independent of
their separating lag; enclosing the entire gap in one growing box loses
the intended estimate. After the SAME connected-moment envelope is proved,
the existing generic `dyadic_geometric_first_le`,
`lean/YMGap/Continuum/Z4HalfTimeReflectionStrictJointDenseDyadicGap.lean:365`,
removes an observable-dependent prefactor using nonnegative, bounded,
dyadically log-convex moments. This consumer is not evidence that its new
Wilson envelope has already been supplied. The enlarged strict bound remains
open; canonical frontier fields and the Clay target are unchanged.

## Verification and independent review

Seven focused final checks exited 0, reporting 70 public gates with only
{propext, Quot.sound} or no axioms. Final logs contain no warning, error,
sorryAx, classical-choice or native-reduction dependency. Development fixes
were local opacity for the already defined spatial scalar (avoiding costly
definitional unfolding) and a local-notation field-projection syntax fix.
Neither changed a mathematical statement or safety limit. Failed development
logs are not verification evidence.

Parent plus three agents developed and cross-reviewed geometry, stationarity,
the cap, midpoint signs, actual quotient/modulus pins and even-only positivity.
Main alone compiled serially via `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check <file> --check-output <its olean>`, with
fresh process/swap preflights. Swap remained 6869.19 MiB; no competing
Lean/test/runner process was found. Root imports added, but root/full-tree/
full-audit/guard checks NOT run. No old proof, sorry, axiom, analytic guard,
canonical field or safety limit changed. CI remains manual; no routine
literature scan ran.

Final logs are under `/tmp/`:

| Log | Gates | SHA-256 |
| --- | ---: | --- |
| `ym-wilson-intrinsic-cap-20260917.log` | 8 | `e0eb67cb79bf112ada18c699e9b2c40ff5d921bdfb668b2120f9b1fa7b2fe96b` |
| `ym-wilson-physical-time-20260917.log` | 15 | `1a6c86b25b277edd6ffd01a0be131112cef181472f543b38e7e29609bc006f91` |
| `ym-wilson-window-stationarity-20260917.log` | 5 | `a37efa9f0526c1acefdd0c7e2ba0aa386e9880e65b483640a453a70fc609e098` |
| `ym-wilson-limit-stationarity-20260917-opacity.log` | 5 | `8f45728b392b4973d1521e92b224a1571e4b919dd216b1ba717aca4fd3a11836` |
| `ym-wilson-physical-time-form-20260917-final.log` | 7 | `b666288128ccf782dfea39737132e8081834c213a9ce9363cf5baf30efb8d5df` |
| `ym-wilson-physical-time-contraction-20260917.log` | 11 | `0b32b93f5effaa00b6cbd236a9bed5d0e402d9ecdc535641532053192ca61899` |
| `ym-wilson-completed-time-20260917.log` | 19 | `081b370de77fb9b877798dda2df8c8c8622828267a31d88bb4914142e1ccff67` |
