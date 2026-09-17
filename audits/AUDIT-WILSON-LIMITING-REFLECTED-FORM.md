# Same-limit Wilson reflected form: parallel branches joined

Date: 2026-09-17 UTC. Base: `4c0242c`, committed and pushed. The preceding
three-regulator-limit goal turn is classified **PROGRESS**.

The WHOLE-PROJECT GOAL remains constructive continuum Yang--Mills existence,
nontriviality, the required QFT axioms and a strictly positive physical
Hamiltonian mass gap for EVERY compact simple gauge group. **That goal is
OPEN.** This checkpoint concerns fixed-spacing, small-nome SU(2) lattice data.

## Actual result and causal connection

The already constructed original Wilson spatial limit is normalized and
rational-linear. Its mixed reflected form is symmetric, nonnegative on the
diagonal and satisfies sharp Cauchy--Schwarz. Null differences can be replaced
in either argument. Moving the reflection center AND both observable offsets
together preserves this same limiting form.

EXPANSION separated exact finite functional laws, reflected symmetry,
positivity of signed combinations, and centered-window padding. CONTRACTION
uses equality of the original finite scalars and their existing convergence
witnesses to prove the corresponding laws for ONE previously constructed
limit. No new state, caller-supplied positive form, matching representative
moduli, or width-uniform time estimate is assumed.

The concrete consumer is `SquaredSeminorm`,
`lean/YMGap/Continuum/CRealSeminormCompletion.lean:39`, whose triangle and
`null_congr` fields must be filled for the actual enlarged domain. Its
`QuotSpace` and represented `Completion` are at :104 and :249. This checkpoint
supplies form algebra and radical descent; it does not yet construct that
Wilson seminorm/completion or its transfer and strict estimate.

## Checked declarations

The module paths in this table are under `lean/YMGap/Continuum/`.

| Proved arrow | Declaration and module:line |
| --- | --- |
| Same action and partition -> finite coefficient congruence/additivity/signed scaling | `chartScalar_congr`, `BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws.lean:46`; `chartScalar_add`, :51; `chartScalar_smul`, :61 |
| Same partition -> normalized finite unit | `chartScalar_one`, same file:74 |
| Separate convergence witnesses -> limiting functional laws | `spatialLimit_congr`, same file:90; `spatialLimit_add`, :101; `spatialLimit_smul`, :114; `spatialLimit_one`, :125 |
| Literal reflection on the original selected action -> mixed finite symmetry | `chartScalar_reflected_symm`, `BF4ExactSlabFixedSpatialWilsonReflectedSymmetry.lean:75` |
| Same diagonal -> limiting mixed symmetry | `spatialLimit_reflected_symm`, same file:113 |
| Actual signed quadratic positivity -> finite sharp Cauchy--Schwarz | `chartScalar_cauchySchwarz`, `BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz.lean:148` |
| Actual mixed product -> the existing limit as a form | `form`, same file:158 |
| Three actual scalar convergences -> limiting Cauchy--Schwarz | `spatialLimit_cauchySchwarz`, same file:170 |
| Limiting zero diagonal -> zero pairing against every guarded expression | `spatialLimit_radical_zero`, same file:215 |
| Exact limiting algebra -> symmetric positive normalized form | `form_symm`, `BF4ExactSlabFixedSpatialWilsonReflectedFormLaws.lean:46`; `form_nonnegative`, :50; `form_one_one`, :54 |
| Coefficient distribution -> rational bilinearity | `form_add_left`, same file:62; `form_add_right`, :80; `form_smul_left`, :88; `form_smul_right`, :100 |
| Literal signed differences -> diagonal expansion and null replacement | `form_difference_diagonal`, same file:131; `form_null_left`, :142; `form_null_congr`, :153 |
| Shift offsets with center -> literal reflection compatibility | `mirror_shift`, `BF4ExactSlabFixedSpatialWilsonCenteredWindow.lean:59` |
| Whole signed expression -> ONE common source lift | `source_shift`, same file:88; `mixed_source_shift`, :118 |
| Common full chain -> exact finite centered padding | `windowRatio_centered_shift`, same file:148 |
| Same finite ratio -> same original joint limit | `originalScalar_centered_shift`, `BF4ExactSlabFixedSpatialWilsonCenteredLimit.lean:51`; `originalJoint_centered_shift`, :78 |
| Existing per-row limits -> same spatial scalar and mixed form in larger centered window | `spatialLimit_centered_shift`, same file:99; `spatialReflected_centered_shift`, :116 |

## What makes the limit arguments legitimate

The finite functional uses the original selected-chain `finiteValue`, with
the reciprocal partition independent of the insertion. Additivity and signed
scaling therefore do not compare different normalization factors. Unit
normalization uses the existing original-window pin and exact window-ratio
unit cancellation. Coefficient congruence is explicitly required on every
actual placed chart; arbitrary source-presentation or OS-quotient equality
is not silently substituted for this hypothesis.

Each expression has its OWN `spatial_diagonal_converges`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSpatialLimit.lean:78`.
Functional equality is proved on raw `n,n,n` charts, then limits are identified.
No equality of expression-dependent caps, Cauchy moduli or `QMhat` indices is
used. Cauchy--Schwarz similarly passes products of three separate convergent
scalars to their actual limits. The radical proof applies the resulting
inequality with an epsilon-squared tolerance, without division or square roots.
It does NOT infer finite-chart nullity from limit-nullity.

Centered padding is
`R(m,L+2*d,n,shift d e) ≈ R(m+d,L,n+d,e)`, with the SAME nome, cutoff,
total transition count and full partition. It is not finite stationarity.
`originalJoint_approx`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.lean:131`,
controls the smaller-window sequence at cutoff s and time s+d using its
existing explicit joint modulus. Joint-limit equality is proved at each
fixed spatial margin before `jointLimits_spatial_converge`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSpatialLimit.lean:85`,
identifies the spatial limits. The new half-window is H+d and both operand
offsets increase by d; increasing H alone would change reflected separations.

Finite functional/symmetry/CS laws require only `0<w<1`. Spatial-limit laws
retain `0<base`, `heatRatio w <= 1/2`, `heatRemainderBound w < 1`, and
`entropyRate 625 (adjustedCoreRate w hd) < 1`. Physical spacing and nome do
not vary. No beta-uniform physical mass bound is proved.

## Five-front parallel assessment and next joins

| Requested front | Independent useful work and current residue |
| --- | --- |
| Nonconstant excitation | The old completed carrier already has `normalizedCertificate`, `lean/YMGap/Continuum/BF4SpatialUnionNormalizedExcitation.lean:160`. Reusing it on the enlarged carrier requires an actual cross-family pin, not another excitation witness. No such embedding is constructed here. Continuum survival remains separate. |
| Full Hilbert/OS/QFT | This checkpoint joins independently developed algebra, symmetry, CS and chart compatibility. Next construct the actual squared seminorm, intrinsic chart/base inclusions, quotient/completion and original time action. The enlarged strict bound and full observable coverage are still open. |
| Spatial and spacing control | Exact centered-window compatibility is now proved, but it is time-window bookkeeping at FIXED spacing. Full spatial symmetry and changing-scale original-action control remain open. `no_fine_guard_on_chart` / `no_blocked_guard_on_chart`, `lean/YMGap/Continuum/BF4SmallNomeAFGuardObstruction.lean:126` / :133, remain unchanged. |
| Positive physical mass | The existing scalar compiler `fullMassRate`, `lean/YMGap/Continuum/PhysicalSeparatorFullLogRate.lean:108`, can be consumed only after SAME-transfer physical-spacing inputs are supplied. `FullRangeLogRateCeiling`, `lean/YMGap/Continuum/PhysicalSeparatorFullLogComparison.lean:163`, still requires an actual finite upper bound. None is supplied by form positivity. |
| Every compact simple group | Group/global-form representation, Haar and action producers remain independent work. This checkpoint is SU(2), not an all-group producer. `mass_gap_of_cartanType`, `lean/YMGap/MassGap/AllSimpleTypes.lean:280`, remains conditional on supplied OS data; `so3_spinHalf_rejected`, `lean/YMGap/RepTheory/CompactSimpleGlobalForm.lean:443`, prevents blindly reusing the spin-half probe for SO(3). |

These are useful parallel branches, not interchangeable completed theories.
Their joins must retain the same observables, action, state, operator, physical
scale and group. Parent plus three agents developed/reviewed this checkpoint;
all compilation was serialized.

The canonical scalar seam is unchanged: `PositiveTimeOSRoot.positive`,
`lean/YMGap/Continuum/CanonicalOSRoot.lean:272`, uses `GNSData`, whose B is
Q'-valued (`lean/YMGap/Continuum/GNSQuotient.lean:102`). Its
`stateEssentiallySurjective`, `CanonicalOSRoot.lean:296`, is a genuine dense
observable-realization requirement. A CReal-valued form does not fill these
fields, and no canonical field was changed.

### Bounded nonconstant-excitation scout

NOT FOUND: a plaquette `SourceLoop` constructor or old-to-Wilson completed
embedding in the searched `BF4*Wilson*.lean`,
`BF4ExactSlabFixedSpatialFaceCharacter.lean`, and
`BF4ExactSlabFixedSpatialSliceHeat.lean` modules. `SourceLoop`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonProbe.lean:44`, accepts
explicit path/closedness/physical-link witnesses. The old `plaquette`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSliceHeat.lean:66`, and new
`wordWith`, `lean/YMGap/Continuum/BF4ExactSlabTemporalGaugeWilsonWord.lean:76`,
use different associations, so their equality is not definitional.
`character_pin`, `lean/YMGap/Continuum/BF4ExactSlabSpatialWilsonRectangle.lean:80`,
is a checked analogous reassociation argument.

The bounded next parallel target is a literal origin-plaquette loop and its
first/second limiting moment pins. Old finite consumers are
`chartScalar_mean_finiteValue` and `chartScalar_square_finiteValue`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFaceCharacter.lean:126` and :147.
The old norm floor is `excitation_norm_floor`,
`lean/YMGap/Continuum/BF4SpatialUnionExcitation.lean:92`. These are existing
inputs, not a proved cross-family bridge. A completed isometry and time
intertwining remain separate from the scalar moment join.

## Verification boundary

Six focused final checks exited 0. All 38 public gates use only
{propext, Quot.sound} or no axioms. Final logs contain no warnings, errors,
`sorryAx`, classical choice or native-reduction dependency. Early CS/form-law
checks needed an explicit local function type and a qualified existing lemma
name; no mathematical statement or resource limit changed.

Each run used `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check <file> --check-output <its olean>`, after
fresh process/swap inspection. Preflight swap was 6901.19 MiB. Root imports
were added, but root/full-tree/full-audit/guard checks were NOT run. No old
proof, sorry, axiom, analytic guard, canonical field or safety limit changed.
CI remains manual-only. No routine literature scan ran.

Final logs are local `/tmp/` files; hashes are SHA-256.

| Module suffix after `BF4ExactSlabFixedSpatialWilson` | Gates | Final log | SHA-256 |
| --- | ---: | --- | --- |
| SpatialFunctionalLaws | 8 | `ym-wilson-functional-laws-20260917.log` | `dbb27a940a532248fad36b0835f1cea79ea6904f721d424ae59279b1ba9f1e88` |
| ReflectedSymmetry | 2 | `ym-wilson-reflected-symmetry-20260917.log` | `67e9c5097c2eb0025d5f478a829894561bbf82cb86ed179ba1ef2cdb70cd17a2` |
| ReflectedCauchySchwarz | 4 | `ym-wilson-reflected-cs-final-20260917.log` | `8b3fc0e8f5272c16324b36daa2d241803baf3c913ee3caddd7e5681c47e2b867` |
| CenteredWindow | 8 | `ym-wilson-centered-window-20260917.log` | `49f9ff282d75c245ec8f0d97ffd350ffda93b9a086f579f2da45d093d73b720e` |
| ReflectedFormLaws | 12 | `ym-wilson-form-laws-final-20260917.log` | `3d62cd8fa49484a1f9441a57150a9d77bb21abb9a64da74506f3ebc1f14b38a4` |
| CenteredLimit | 4 | `ym-wilson-centered-limit-20260917.log` | `6958447e985adefda36e79212855ff60e36b0dc46eb568088df24ca46cb82e26` |
