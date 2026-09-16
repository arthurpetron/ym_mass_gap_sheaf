# Reflected cutoff/time joint limit and its strict centered scalar bound

Date: 2026-09-16. PROGRESS after `3ad2187`.

WHOLE-PROJECT GOAL: nontrivial continuum Yang--Mills on R^4, the required
QFT axioms and a positive physical Hamiltonian gap for EVERY compact simple
group, on the SAME theory, within the constructive axiom gate. This increment
removes the heat cutoff for the selected original fixed-width SU(2) scalar
reflected form. It does not remove the spatial or spacing regulators.

## Mathematical argument

Fix nome, width, physical presentations x,y and a common chart H. Write
S(k,t)=chartScalar(width,k,H,x,y,t). The two indices are retained heat stage
k and receding temporal boundary depth t; neither is the physical lag.

EXPANSION: retain the actual finite extent, selected chain, insertion and
partition, plus two different moduli. At fixed t, the existing finiteCauchy
applies literally to the original expectation stream. Boundary-time control
has a modulus independent of k. For epsilon>0, compute
T=timeModulus(epsilon/4), then K=cutoffModulus_at_T(epsilon/4).

CONTRACTION: compare S(k,t) with S(k,T), then S(j,T), then S(j,u).
Each comparison costs at most epsilon/4, and all constants are computed.
This proves a late rectangle with independent cutoff/depth thresholds.
The diagonal has QCauchy modulus max(T,K). Its constructed CReal limit
controls the whole late rectangle, not merely the diagonal.

The representatives of the existing cutoff-first and time-first limits
are actual samples at QMhat indices, each at least its input index. The
same rectangle therefore proves both iterated-limit identifications.
The time-first object equals the existing intrinsic pairing at each stage.
Taking the computed maximum presentation radius defines jointPairing and
its explicit approximation QCauchy data. Uniqueness of the SAME stage-wise
pairing limit proves independence of every other valid common chart.

For a fixed physical lag n, scalar addition and multiplication give the
joint centered moment from these actual pairings. Its explicit QCauchy
data use computed product ceilings, not an assumed cutoff-independent
modulus for the old connected product. The existing stage-wise even-time
positivity, dyadic inequality and prefactor-free bound pass to this limit:

`jointCenteredMoment(2,x,x) <= q^2 * jointCenteredMoment(0,x,x)`.

The q^2 here is the already proved twoStepRate(w,width)<1, independent of
heat stage. It is not replaced by a freely supplied scalar.

Separately, construct QCauchy data for the LITERAL connected finite
diagonal at stage=buffer=s. Joint observation and both unit marginals have
identical H, extent, action and partition at every s. Its joint limit equals
the centered moment. The separately regularized jointPairing approximants
are NOT asserted to have one common chart/index; their equivalences are
used only after taking limits. Actual unit-time invariance identifies the
advanced right marginal. The finite physical-lag covariance bound gives
both sides of the joint envelope, with prefactor independent of lag:

`-A(x,y)*q^n <= jointCenteredMoment(n,x,y) <= A(x,y)*q^n`.

## Checked declarations

All module paths below have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Role |
|---|---|---|
| `chartCutoffCauchy` | `BF4ExactSlabFixedSpatialChartJointCauchy.lean:39` | Existing original finite cutoff modulus at one fixed depth. |
| `chartJointTimeThreshold`, `chartJointCutoffThreshold`, `chartJointModulus` | `BF4ExactSlabFixedSpatialChartJointCauchy.lean:54`, `:62`, `:70` | Executable independent thresholds and their maximum. |
| `chartJoint_rectangle` | `BF4ExactSlabFixedSpatialChartJointCauchy.lean:102` | Three-hop comparison of independently late parameter pairs. |
| `chartJointCauchy`, `chartJointLimit`, `chartJoint_approx` | `BF4ExactSlabFixedSpatialChartJointCauchy.lean:125`, `:136`, `:150` | Explicit diagonal witness and whole-rectangle approximation. |
| `chartCutoffExpectation_original` | `BF4ExactSlabFixedSpatialChartJointLimits.lean:49` | Literal equality to the original selected-chain expectation. |
| `chartCutoffExpectation_approx_joint`, `chartCutoffExpectation_converges_joint` | `BF4ExactSlabFixedSpatialChartJointLimits.lean:67`, `:81` | Cutoff first, then boundary time. |
| `chartTimeLimit_approx_joint`, `chartTimeLimit_converges_joint` | `BF4ExactSlabFixedSpatialChartJointLimits.lean:95`, `:109` | Boundary time first, then cutoff. |
| `pairing_converges_chartJoint` | `BF4ExactSlabFixedSpatialChartJointLimits.lean:120` | Cutoff convergence of the existing intrinsic reflected pairing. |
| `jointPairing`, `jointPairingCauchy`, `jointPairing_chart` | `BF4ExactSlabFixedSpatialChartJointLimits.lean:129`, `:134`, `:145` | Canonical scalar, actual modulus and chart independence. |
| `jointCenteredMoment`, `jointCenteredMomentCauchy`, `centeredMoment_converges_joint` | `BF4ExactSlabFixedSpatialJointCenteredForm.lean:44`, `:52`, `:65` | Same centered physical-time scalar, with explicit approximation data. |
| `jointEvenMoment_nonnegative`, `jointEvenMoment_le_zero`, `jointEvenMoment_dyadic` | `BF4ExactSlabFixedSpatialJointCenteredForm.lean:89`, `:95`, `:118` | Existing moment inequalities preserved through cutoff removal. |
| `joint_twoStep_form_gap` | `BF4ExactSlabFixedSpatialJointCenteredForm.lean:106` | Prefactor-free strict scalar inequality after both limits. |
| `jointPairing_unit_time` | `BF4ExactSlabFixedSpatialJointConnectedCorrelator.lean:70` | Actual unit coefficient remains invariant under physical advance. |
| `jointConnectedCauchy`, `jointConnectedLimit` | `BF4ExactSlabFixedSpatialJointConnectedCorrelator.lean:91`, `:98` | Literal common-partition connected diagonal and its limit. |
| `jointConnectedLimit_pin`, `jointConnectedLimit_physical_pin` | `BF4ExactSlabFixedSpatialJointConnectedCorrelator.lean:109`, `:130` | Finite family realizes the SAME centered physical moment. |
| `jointCenteredMoment_bounds` | `BF4ExactSlabFixedSpatialJointConnectedCorrelator.lean:141` | Both sides of the geometric physical-lag envelope. |

## Scope and next causal frontier

This removes the scalar reflected cutoff/time interchange obligation at
fixed width. The selected-chain action is not silently replaced by a full
growing-box action. Nome/width dependence is retained; no width-uniform
floor, spacing calibration, continuum semigroup or Hamiltonian is supplied.
The earlier completed strict theorem concerns a different carrier for each
heat stage. These scalar limits do not identify those carriers or prove
operator convergence between them.

NEXT: use jointPairing on the physical signed difference to construct the
limiting squared seminorm required by `CRealSeminormCompletion.lean:39`,
`SquaredSeminorm`. The stage-wise reflexive/symmetric/nonnegative/triangle
laws in `BF4ExactSlabFixedSpatialIntrinsicSeminorm.lean` can be consumed via
scalar limits. Its conditional null law cannot simply be passed through:
limit-null does not imply stage-wise null. Prove limiting sharp CS first,
derive the limiting radical law, and then construct null_congr. The existing
physicalTime map can descend only after its contraction has been proved
for that SAME limiting distance. This paragraph is source review, not a
checked new seminorm or completion theorem.

Nonconstant excitations, the cutoff-removed completed pairing/strict bound,
metric completeness/full Hilbert/OS and required gauge algebra, spatial and
spacing passage, physical mass calibration, continuum QFT and the all-group
Clay target remain open. No canonical frontier field, literal sorry,
analytic premise, axiom or resource limit changed.

## Verification

Four focused serialized one-worker/20 GiB checks passed all 37 public
axiom gates within {propext, Quot.sound}. Every check had a fresh process
and swap preflight. The first ChartJointLimits check found one missing
namespace open for the existing representativeCauchy helper; the corrected
final check passed. Final logs contain no errors, warnings, sorryAx or
classical dependencies. Independent source review covered the independent
indices, retained action/partition, no-choice chart definition, strict-rate
passage and raw connected diagonal. Main alone compiled. Four selective-root
imports were added; root/full-tree/full axiom audit were not run. No new
literature scan was performed.

| Module suffix (prefix BF4ExactSlabFixedSpatial) | Gates | Final `/tmp/<module>.log` SHA-256 |
|---|---:|---|
| `ChartJointCauchy` | 9 | `2ef809b18a995e680c18910b021869c98850960327a4009f4cc58f20659acb1b` |
| `ChartJointLimits` | 13 | `7c3c6f08d28616a8199c773df3def7f6c2c01618679a87210577e3bdc07db93c` |
| `JointCenteredForm` | 8 | `59a9e393455df82012763c398dac63c9847c03a6044cf1b5b6566cdf3cc28031` |
| `JointConnectedCorrelator` | 7 | `574dd391322251ca35a8d036b34532acbd8b9a588dbf5ab967f9adffedbe3e3c` |
