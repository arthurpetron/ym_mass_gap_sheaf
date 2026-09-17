# Same-Wilson completion pairing and positive scalar variance

Date: 2026-09-17 UTC. Base: `0c7cf21`, committed and pushed. The preceding
limiting-form goal turn is classified **PROGRESS**.

The WHOLE-PROJECT GOAL remains a constructive nontrivial continuum Yang--Mills
theory satisfying the required QFT axioms, with an isolated vacuum and a
strictly positive physical Hamiltonian mass gap, for EVERY compact simple
gauge group. **That goal remains OPEN.** This checkpoint is fixed-spacing,
small-nome SU(2), at one positive source base.

## Actual result and causal join

The actual Wilson limiting reflected form now supplies a squared seminorm,
an intrinsic common-window carrier and a pairing on its represented Cauchy
completion. The completed pairing retains the original dense form, symmetry,
nonnegativity, unit normalization and sharp Cauchy--Schwarz. No analytic field
in the seminorm or pairing-continuity interface is left to a caller.

Independently, the original ordered plaquette is an actual closed Wilson
source loop. Its fundamental first and second original moments agree with
the old moments on every chart, and therefore in their separate limits.
The Wilson scalar variance inherits the old positive `starRatio w` floor.
This is NOT yet a completed centered vector, a completed old/new isometry,
an enlarged-carrier strict bound, or a continuum nontriviality theorem.

EXPANSION separated the triangle/null laws, common-horizon transport,
quantitative continuity and literal plaquette word identification.
CONTRACTION fills the existing `SquaredSeminorm` and `PairingData` consumers
with actual proved data and identifies the same scalar moments. A bound on
the older plaquette carrier is not silently transferred to the enlarged one.

## Checked declaration map

All module paths in the table are under `lean/YMGap/Continuum/`.

| Causal edge | Declaration and module:line |
| --- | --- |
| Actual fixed-window reflected form -> squared distance | `distSq`, `BF4ExactSlabFixedSpatialWilsonWindowSeminorm.lean:59` |
| Positive signed difference + parallelogram -> sum bound | `pairing_sum_bound`, same file:107 |
| Telescoping differences + sum bound -> squared triangle | `distSq_triangle`, same file:149 |
| Limiting radical laws -> replacement of null differences | `pairing_null_congr`, same file:162; `distSq_null_congr`, :169 |
| Actual distance laws -> `SquaredSeminorm` | `seminorm`, same file:183 |
| Finite expression + radius/support witness -> intrinsic domain | `IntrinsicExpression`, `BF4ExactSlabFixedSpatialWilsonIntrinsicForm.lean:45` |
| Computed horizon -> centered expression chart | `chart`, same file:52; `chart_step`, :66 |
| Complete reflected expression -> same common source | `chart_mixed_source_step`, same file:80 |
| Actual limiting form -> intrinsic mixed form and modulus | `intrinsicForm`, same file:99; `intrinsicFormCauchy`, :106 |
| Centered-limit identity -> intrinsic form at any admissible common H | `intrinsicForm_chart`, same file:125 |
| Literal signed difference -> intrinsic distance and common-chart pin | `distSq`, `BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.lean:77`; `distSq_chart`, :88 |
| Common-chart laws -> actual intrinsic seminorm | `seminorm`, same file:156 |
| Actual CS -> quantitative two-variable continuity | `pairing_close`, `BF4ExactSlabFixedSpatialWilsonWindowPairingContinuity.lean:89` |
| Signed sum bound -> actual diagonal anchor bound | `diagonal_anchor_bound`, same file:121 |
| One computed horizon for all four operands -> intrinsic continuity | `pairing_close`, `BF4ExactSlabFixedSpatialWilsonCompletedInner.lean:61` |
| Actual estimates -> complete `PairingData` instance | `pairingData`, same file:103 |
| Intrinsic seminorm -> represented completion and embedding | `Completion`, same file:109; `embed`, :111 |
| Supplied vector Cauchy data -> scalar representative and explicit QCauchy | `representativeInner`, same file:116; `representativeInnerCauchy`, :119 |
| Representative independence -> pairing on this SAME quotient | `completedInner`, same file:123 |
| Dense embedding -> original intrinsic form | `completedInner_embed`, same file:126 |
| Dense laws + actual limits -> symmetry, nonnegativity and unit norm | `completedInner_symm`, same file:131; `completedInner_nonnegative`, :136; `completedInner_unit_unit`, :141 |
| Actual dense CS -> completed CS | `completedInner_cauchySchwarz`, same file:147 |
| Original physical four-edge boundary -> closed Wilson source loop | `plaquetteLoop`, `BF4ExactSlabFixedSpatialWilsonPlaquette.lean:62` |
| Associativity and units -> ordered source word and all-spin character pin | `sourceWord_plaquette`, same file:88; `sourceCharacter_plaquette`, :93 |
| Literal placement/recentering -> same old fundamental face insertion | `recentered_fundamental_placedSpan`, same file:182 |
| Same insertion/action/partition -> original finite first/second moment pins | `chartScalar_mean_pin`, `BF4ExactSlabFixedSpatialWilsonPlaquetteMoments.lean:76`; `chartScalar_square_pin`, :91 |
| Separate actual convergence witnesses -> limiting moment pins | `meanLimit_pin`, same file:118; `squareLimit_pin`, :129 |
| Actual first/second moments -> same scalar variance | `variance_pin`, same file:142 |
| Old local-star floor -> positive Wilson variance | `variance_floor`, same file:150; `variance_ne_zero`, :154 |

## Mathematical and constructive boundaries

The squared triangle has the factor-two form
`d(x,z) <= (d(x,y)+d(x,y))+(d(y,z)+d(y,z))`. Its proof expands a
parallelogram and discards the nonnegative difference diagonal; it does not
import square roots or replace the OS form by ordinary weighted L2.
Common charts use `H-radius`, moving both offsets and reflection center.
Nullity is transported at the LIMIT, not asserted on finite charts.

The quantitative consumer is `PairingData`,
`lean/YMGap/Continuum/CRealSeminormPairingCompletionBounds.lean:33`.
The new instance computes one H for all four arguments before applying its
two-distance tolerance and two diagonal bounds. The scalar QCauchy witnesses
belong to the actual representatives; equality of CReal values is not used
to transport an unrelated representative's modulus. Generic scalar limits
descend to `SquaredSeminorm.Completion`,
`lean/YMGap/Continuum/CRealSeminormCompletion.lean:249`, built from supplied
vector Cauchy representatives. Merely defining that quotient is NOT a proof
of arbitrary quotient-level metric/Hilbert completeness.

The plaquette word pin re-associates quaternion multiplication without
commuting factors. First and second moments retain the same original chart
extent, selected chain, heat stage, time buffer and reciprocal partition.
Each old/new stream has its own convergence witness. No equality of their
regularized CReal approximation indices is assumed. The positive scalar
variance does not make its CReal mean a rational expression coefficient.

Finite plaquette identities retain the general supplied physical face and
all spins. Limiting results keep `0<w<1`, `0<base`,
`heatRatio w <= 1/2`, `heatRemainderBound w < 1`, and
`entropyRate 625 (adjustedCoreRate w hd) < 1`. The variance floor is explicitly
`starRatio w`; no beta-independent floor, changing-spacing control or
physical mass calibration is claimed.

## Five requested parallel fronts

| Front | Useful work independent of the enlarged strict bound; residue |
| --- | --- |
| Nonconstant excitation | The actual old/new plaquette moment and scalar-variance bridge above is now checked. Realize that variance as the norm of a centered vector on the SAME enlarged completion next. The older `normalizedCertificate`, `lean/YMGap/Continuum/BF4SpatialUnionNormalizedExcitation.lean:160`, is not automatically a vector of this new carrier. Continuum survival remains open. |
| Full Hilbert/OS/QFT | Actual seminorm and completed pairing are now constructed. Completed linear/separation laws, arbitrary quotient-level completeness, original time, full observable coverage and canonical realization remain. The existing generic separation consumer `completedInner_posdef`, `lean/YMGap/Continuum/CRealSeminormPairingPosdef.lean:71`, still needs the actual dense-zero and distance-to-zero identities. |
| Spatial and spacing control | Common-window coherence is proved at a fixed positive base and fixed spacing. Base inclusions, full spatial symmetry and changing-scale original-action estimates remain independent tasks. The AF guard obstruction is unchanged: `no_fine_guard_on_chart` / `no_blocked_guard_on_chart`, `lean/YMGap/Continuum/BF4SmallNomeAFGuardObstruction.lean:126` / :133. |
| Positive physical mass calibration | Scalar conversion machinery remains available: `fullMassRate`, `lean/YMGap/Continuum/PhysicalSeparatorFullLogRate.lean:108`. No SAME-transfer physical spacing input or finite ceiling is supplied here; `FullRangeLogRateCeiling`, `lean/YMGap/Continuum/PhysicalSeparatorFullLogComparison.lean:163`, remains an input. Form positivity and positive scalar variance do not fill it. |
| Every compact simple group | Representation/global-form, Haar and action producers can be developed separately, but this checkpoint supplies no non-SU(2) physical instance. `mass_gap_of_cartanType`, `lean/YMGap/MassGap/AllSimpleTypes.lean:280`, remains conditional. `so3_spinHalf_rejected`, `lean/YMGap/RepTheory/CompactSimpleGlobalForm.lean:443`, blocks copying this spin-half probe unchanged to SO(3). |

Thus useful parts of all five fronts can be prepared in parallel; their final
joins are not independent. The completed strict bound must concern the same
carrier, action, state and operator, and physical calibration must concern
the same spacing and time normalization. The canonical scalar seam remains:
`PositiveTimeOSRoot.positive`, `lean/YMGap/Continuum/CanonicalOSRoot.lean:272`,
requires `GNSData`, and `stateEssentiallySurjective`, same file:296, requires
actual dense observable realization. Neither is filled by this checkpoint.

## Verification and independent review

Seven focused final checks exited 0. All 86 public gates report only
{propext, Quot.sound} or no axioms. The final logs contain no warning, error,
`sorryAx`, classical choice or native-reduction dependency. Development fixes
were syntax/layout, one dependent rewrite, a local-notation binder collision,
and local opacity for finite/limit scalars; no statement, guard or resource
limit was weakened. Failed development logs are not verification evidence.

Parent plus three agents split and cross-reviewed seminorm/continuity,
intrinsic common-window and plaquette/moment work. Main alone ran Lean,
serially, with fresh process/swap preflights. Checks were paused while the
user's unrelated pytest suite was active; it was not killed. The resumed
checks used one worker with the mandatory 20 GiB cap via
`scripts/safe_lean_build.py --check <file> --check-output <its olean>`.
Resumed preflight swap was 6893.19 MiB. Root imports were added; root/full-
tree/full-audit/guard checks were NOT run. No old proof, sorry, axiom,
canonical field, analytic guard or safety limit changed. CI remains manual.
No routine literature scan ran.

Final logs are local `/tmp/` files; hashes are SHA-256.

| Module suffix after `BF4ExactSlabFixedSpatialWilson` | Gates | Final log | SHA-256 |
| --- | ---: | --- | --- |
| WindowSeminorm | 17 | `ym-wilson-window-seminorm-final-20260917.log` | `2e9fca101efe34f1023399c27979fec748afefecc1e09c11e2c376b93cd73c27` |
| IntrinsicForm | 14 | `ym-wilson-intrinsic-form-20260917.log` | `45b14810d1d9bd2683d9289720dab061f6e95e87a58be36f39a076bf6af12db3` |
| IntrinsicSeminorm | 14 | `ym-wilson-intrinsic-seminorm-final-20260917.log` | `461c8d73e69a2ba86691071fe5e765bc806db09eb40404a9b6ef9d7bb884e4f0` |
| WindowPairingContinuity | 5 | `ym-wilson-window-continuity-20260917.log` | `efc85db02f82ab939ab5233626fdf2a712d4bf05b7baafe3f1612b978e6be5c3` |
| CompletedInner | 14 | `ym-wilson-completed-inner-final-20260917.log` | `0e00c9ec1576c684fba33ccc04dd38f9f3dbb08718e7e697239ce706abc833a2` |
| Plaquette | 14 | `ym-wilson-plaquette-20260917.log` | `d1c7cd2433c500b73a39e62f79c07c1a97035f3400d72a5f63ab79e82b6580bf` |
| PlaquetteMoments | 8 | `ym-wilson-plaquette-moments-checked-20260917.log` | `4eb6181979563c6389197742b58e0c2d4c4d5f2e4c39fea250df9dba31172c86` |
