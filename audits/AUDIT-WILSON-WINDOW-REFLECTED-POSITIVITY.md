# Original Wilson windows: reflected positivity and the next limit joins

Date: 2026-09-17 UTC. Previous checkpoint `9f5a36f`: **PROGRESS**, committed
and pushed. The unchanged whole-project goal is constructive continuum
Yang--Mills existence, the required QFT axioms, a nontrivial theory and a
positive physical Hamiltonian gap for every compact simple gauge group.
That goal remains **OPEN**.

## Mathematical increment

The original single-loop time realization now extends to finite signed
expressions in closed spatial loop characters at multiple time offsets.
Their literal reflection is the actual original even-slab reflection.
Finite selected-action reflection positivity passes to the already
constructed fixed-width, fixed-cutoff time limit. No alternative action,
partition, observable or limiting state is substituted.

This removes the multi-time source/reflection join identified at the preceding
checkpoint. It does **not** extend the old plaquette-generated completed
union's strict bound to this larger observable family. A positive form on
the new domain is not a proof of its quotient/completion, coverage or gap.

## Causal declaration map

All file paths in this table begin `lean/YMGap/Continuum/`.

| Required input / resulting arrow | Declaration and source |
| --- | --- |
| Signed source syntax records complete loops, offsets, spins and algebra operations | `WindowExpression`, `BF4ExactSlabFixedSpatialWilsonWindow.lean:50`; `Within`, same file:57 |
| Fixed source and literal ambient placement preserve all signed terms | `sourcePolynomial`, same file:65; `placedPolynomial`, same file:74 |
| One chronological source embedding realizes the whole expression | `expression_pin`, same file:172 |
| Source geometry constructs an actual original Wilson-algebra expression | `placeExpression`, same file:197; `evaluate_placeExpression`, same file:210 |
| The entire expression survives the common ledger with an arbitrary supported spectator | `placed_ledger_invariant`, same file:232; `original_chain_pairing`, same file:245 |
| Actual original numerator equals the existing message pairing | `original_window_pairing`, `BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.lean:61` |
| Positive reciprocal cancellation identifies the SAME partition at the SAME heat cutoff | `windowRatio_originalFiniteValue`, same file:84 |
| Actual moving ambient expectation has explicit time Cauchy data | `originalWindowScalar`, same file:117; `originalWindowCauchy`, same file:137; `originalWindowCauchy_modulus`, same file:153 |
| That original stream converges to the EXISTING polynomial window state | `originalWindow_converges`, same file:161; `originalWindow_approx_rectangular`, same file:176 |
| Actual ordered spatial words reflect without replacing them by plaquette trace products | `spatial_character_reflection`, `BF4ExactSlabSpatialWilsonReflection.lean:101`; `placed_reflection`, same file:128; `placed_oneSided`, same file:223 |
| Literal reflection and original coordinate one-sidedness extend to signed expressions | `placed_reflection`, `BF4ExactSlabFixedSpatialWilsonWindowReflection.lean:28`; `placed_oneSided`, same file:44 |
| Complete reflected product retains all cross terms | `reflectedWindowProduct`, `BF4ExactSlabFixedSpatialWilsonWindowReflectionPositive.lean:55` |
| Same-action finite positivity contracts the geometry and normalization pins | `reflectedWindowRatio_nonnegative`, same file:85 |
| Existing CReal representatives inherit reflected positivity | `reflectedWindowLimit_nonnegative`, same file:117 |

## Parameters and exact positivity geometry

The time statements assume `0 < w < 1`, a fixed spatial width, a finite
window `L`, an actual `WindowExpression width`, and its `Within L` proof.
The heat cutoff is `headCutoff w + stage`. Only the two external temporal
boundaries recede. The stored modulus is
`windowTimeModulus hw0 hw1 width (polynomialCap (sourcePolynomial e))`;
its independence of **stage** is exact. It is not uniform in nome, width
or expression. `originalWindow_approx_rectangular` also names the boundary
and representative indices and preserves the existing `mixRate`/`windowTimeCap`
error. No spacing parameter or physical mass is introduced.

For reflection, `Within h e` permits offsets from 0 through h, including
the central slice. Reflection replaces j by `2*h-j` and retains the loop,
orientation, spin, coefficient and operation. The finite proof sets
`radius=width+t+h`, `start=width+1`, and places e at `A=start+t`.
Thus `A+h=radius+1` and the chain has `t+(2*h+t)=2*(t+h)` transitions.
The earlier finite selected-chain positivity theorem applies to precisely
this reflection-centered original action.

The raw `originalWindowScalar` uses a different, not generally centered
ambient. Positivity is therefore proved through its exact compact
`windowRatio` pin, not by assuming the raw ambient is reflection centered.
`finite_reflected_image` in the positivity module retains the selected heat
polynomial, cutoff and reciprocal while replacing only its reflected
insertion by the proved literal image. The final theorem evaluates the
existing CReal at its actual `QMhat` representatives. No interchange of
cutoff and time limits is asserted in this checkpoint.

## Next bounded work: reuse the generic estimates

The following is a source-reviewed plan, **not additional proved Wilson
limit theorems**.

1. Joint time/cutoff removal needs no new cutoff estimate uniform over all
   chain lengths. `finiteCauchy`,
   `lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetExpectation.lean:65`,
   supplies cutoff Cauchy data for any fixed original polynomial/action.
   The new stage-independent time modulus allows a single computed pivot,
   using the argument in `chartJointCutoffThreshold` and `chartJoint_rectangle`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChartJointCauchy.lean:62`
   and `:102`. Those existing wrappers currently take `PhysicalSpan`, not
   the new Wilson expressions. The concrete Wilson joint-limit instance
   and its retained reflected positivity are the next bounded consumer.
2. Spatial comparison is already generic in the polynomial. `finiteValue_bound`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBoxBoundary.lean:120`,
   consumes an actual `Interval` and fixed-box `LinkLocal` proof, under its
   explicit small-nome/core/entropy guards. `finiteValue_pin`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAlignedAction.lean:110`,
   consumes the exact aligned translation identity. The Wilson instances
   of this translation, finite-box locality and one margin-independent cap
   remain open. One-sided reflection locality is not fixed-box locality.
3. `polynomialInterval`,
   `lean/YMGap/Continuum/QuaternionHaarSupportedPolynomialInterval.lean:250`,
   already constructs a cap for arbitrary supported polynomials. The cap
   is `polynomialCap` in the same file:237. A cap for a changing placement
   is not automatically a common cap: transport/preservation must be proved.

Current face-specific spatial producers are `chartProbe_interval` and
`chartProbe_local`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlacedProbeControl.lean:219`
and `:337`, and `aligned_chartInsertion_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTranslatedProbe.lean:219`.
They do not instantiate themselves on `WindowExpression`.

## Parallel fronts and their required common-object joins

| Requested front | Current parallel opportunity and remaining join |
| --- | --- |
| Nonconstant excitation | The old SAME-carrier normalized witness already exists: `normalizedCertificate`, `lean/YMGap/Continuum/BF4SpatialUnionNormalizedExcitation.lean:160`. New work is its realization/survival on the eventual full continuum theory, not another finite norm witness. |
| Full Hilbert/OS/QFT | This checkpoint supplies the multi-time source/reflection/time-form join. Joint cutoff/time removal and spatial observable controls can next proceed separately. Their outputs must define the SAME enlarged reflected form and actual transfer before a gap is claimed. |
| Spatial and spacing control | Concrete Wilson spatial translation/locality/cap proofs can proceed independently of the joint time/cutoff construction. Changing-scale control is separate; `no_fine_guard_on_chart` and `no_blocked_guard_on_chart`, `lean/YMGap/Continuum/BF4SmallNomeAFGuardObstruction.lean:126` and `:133`, still obstruct the old small-nome AF route. |
| Positive physical mass | `fullMassRate`, `lean/YMGap/Continuum/PhysicalSeparatorFullLogRate.lean:108`, remains reusable scalar infrastructure. Actual SAME-transfer spacing/rate inputs, including `FullRangeLogRateCeiling`, `lean/YMGap/Continuum/PhysicalSeparatorFullLogComparison.lean:163`, are not supplied here. |
| Every compact simple group | Physical group/global-form representation, Haar and action producers remain independent work. `mass_gap_of_cartanType`, `lean/YMGap/MassGap/AllSimpleTypes.lean:280`, still assumes OS reconstruction and axioms; it does not construct the physical group theory. `so3_spinHalf_rejected`, `lean/YMGap/RepTheory/CompactSimpleGlobalForm.lean:443`, forbids reusing the SU(2) spin-half probe unchanged for SO(3). |

These are parallel components, not independent solutions that can be joined
by matching names. No new all-group or physical-scale producer is claimed.
The canonical scalar/coverage issue also remains: `PositiveTimeOSRoot`,
`lean/YMGap/Continuum/CanonicalOSRoot.lean:268`, requires `positive : GNSData`
at :272 and actual supported-state essential surjectivity at :296.
No canonical field was weakened. No beta-uniform physical-gap claim is made.

## Verification and independent review

All five focused final checks exited 0. All 35 public axiom gates report
only {propext, Quot.sound} or no axioms. Final logs contain no errors,
warnings, `sorryAx`, classical choice or native-reduction dependencies.
Initial checks needed a missing namespace open, symbolic-polynomial opacity,
transparent data bindings, and unused-binder cleanup; no proof statement or
resource limit was changed to resolve them.
Parent and three agents separated source placement, literal reflection,
same-action/time/positivity integration, and independent next-front review.
The reviews found no substantive mathematical defect and explicitly checked
the centered placement, complete signed product and unchanged partition.
Lean checks are serialized, one worker, 20 GiB, with fresh process/swap
inspection. An unrelated user-owned pytest run caused a pause; it was not
stopped or changed. No root/full-tree build, full audit or full guard run is
claimed. Root imports are integration edits only. No prior proof, sorry,
axiom, analytic guard or safety limit was changed. CI remains manual-only;
no routine literature scan was performed.

Each check used `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check <file> --check-output <its olean>`.
Swap remained at 6917.19 MiB in the preflight inspections. The retained
final logs below are in `/tmp/`; hashes are SHA-256.

| Module | Public gates | Final log | SHA-256 |
| --- | ---: | --- | --- |
| BF4ExactSlabFixedSpatialWilsonWindow | 16 | `ym-wilson-window-final-20260917.log` | `d51531919b11b1bc6dc9e8b75df45b04f283ca4aeab6fa0b85513d8d06e93d6a` |
| BF4ExactSlabSpatialWilsonReflection | 5 | `ym-spatial-wilson-reflection-final-20260917.log` | `e15fe91d0759b5dea5c09935f1133c005f169e86745af775fe95c04b3214375b` |
| BF4ExactSlabFixedSpatialWilsonWindowReflection | 2 | `ym-wilson-window-reflection-final-20260917.log` | `eb393b726566f7649a3a648bdc3d364ef1e8870c44d4958005b738565a57ccb1` |
| BF4ExactSlabFixedSpatialWilsonWindowTimeLimit | 8 | `ym-wilson-window-time-20260917.log` | `e6ad8d0fb8815431716b5cf29d4f4de0de4e44d2108596d4a58669a50a1d7ecd` |
| BF4ExactSlabFixedSpatialWilsonWindowReflectionPositive | 4 | `ym-wilson-window-positive-final-20260917.log` | `60e4f43cef5e675a7d0151e730d8f19dc8f8f501ad5387ac64196a75f9b7645e` |
