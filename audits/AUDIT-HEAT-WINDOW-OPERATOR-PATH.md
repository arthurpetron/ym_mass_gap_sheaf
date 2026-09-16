# From local heat windows to the original operator

Date: 2026-09-15 (local). Source review starts at `b9a9292`.
This is a parallel source audit, not a new proof of the physical gap.

## Whole-project goal

Construct the nontrivial continuum Yang--Mills theory required by the Clay
problem, with its physical positive mass gap, for every compact simple gauge
group. The action, observables, OS reconstruction, time translations and
Hamiltonian must describe the same theory. The constructive axiom gate and
explicit-witness requirements are unchanged.

## Finding: reuse the original temporal identity; do not rebuild it

The original signed bilinear already has the complete change-of-variables
identity needed to expose its crossing interface. An initial search confined
to the older spatial tree-gauge modules missed this later result. The following
are existing declarations, not new achievements of this checkpoint.

| Existing declaration | Source | Exact content relevant here |
|---|---|---|
| `exact_bilinear_eq_productHaar` | `lean/YMGap/Continuum/BF4ExactSlabAllExtentObservableHaarForm.lean:178` | Original signed bilinear equals product-Haar of the lower observable, every original crossing heat factor, and the upper observable. |
| `crossing_face_word` | `lean/YMGap/Continuum/BF4ExactSlabTemporalGaugeFaces.lean:161` | Actual temporal-gauge crossing word reduces to the lower/upper spatial relative word under Haar. |
| `crossing_face_reflected_gram` | `lean/YMGap/Continuum/BF4ExactSlabTemporalGaugeFaces.lean:207` | Its character has the literal reflected spatial-link Gram image. |
| `exact_bilinear_eq_temporalHaar` | `lean/YMGap/Continuum/BF4ExactSlabAllExtentTemporalHaarForm.lean:186` | A common, supported temporal ledger acts on the entire original integrand, at every cutoff and odd extent. |
| `exact_bilinear_eq_spatialGramHaar` | `lean/YMGap/Continuum/BF4ExactSlabAllExtentTemporalHaarForm.lean:241` | Original boundary observables are retained; the full crossing interface is the actual spatial Gram product. |
| `exact_quadratic_nonnegative` | `lean/YMGap/Continuum/BF4ExactSlabAllExtentReflectionPositivity.lean:112` | Reflection positivity of that original signed law, every finite cutoff and odd extent, for nonnegative nome. |

The temporal identity is not restricted to degree five. The separate
`quaternionHaar_116_eq_rawTreeGaugeBasedCycleFiveHaarMarginal`,
`lean/YMGap/Continuum/BF4ExactSpatialTreeGaugeRawCarrier.lean:412`, has a
degree restriction on surviving chords and must not be substituted for the
all-extent temporal theorem.

## The new 23-factor comparison is not an original-operator identification

`retainedHarnack`,
`lean/YMGap/Continuum/BF4RoundedPositiveAFWindows.lean:155`, constructs a
comparison for 23 completed heat factors at supplied class coordinates. It
does not assert an equality with the original bilinear above or its geometric
time transfer.

The historical bridge has three distinct requirements that this constructor
does not fill:

1. `MatchedPhysicalHalfAmplitudeRetainedHarnackRows.physical_identification`,
   `lean/YMGap/Continuum/BF4PhysicalHalfAmplitudeRetainedHarnackBridge.lean:327`,
   targets `centralHalfAmplitude`, not the original signed Haar bilinear.
2. Its `retained_harnack` field at line 305 takes rational
   `RetainedKineticHarnackData`; the new result returns completed
   `DynamicCompletedRetainedHarnackData`.
3. Its `spread_square_le` field at line 322 requires the near-unit
   `anchoredProjectiveCeiling`, defined as `65/64` in
   `lean/YMGap/Continuum/BF4AnchoredProjectiveProfileHarnack.lean:49`.
   The constructed comparison uses `farautRetainedSpread`, defined in
   `lean/YMGap/Continuum/BF4FarautJointCarrierAFBudget.lean:104`, namely
   `4^(23*bits)`. A coarse upper bound is not a proof of the smaller ceiling.

The distinction between actions is substantive. `same_action_uninhabited`,
`lean/YMGap/Continuum/BF4ExactPhysicalCutoffLimitSeparation.lean:135`, refutes
the existing identity-observable same-action interface at every positive nome
and cutoff at least one. `cutoff_limit_separation` in that file at line 160
retains a positive discrepancy after cutoff removal. These declarations do
not refute a correctly transformed comparison; they exclude silently treating
the two existing laws as identical.

## Genuine independent downstream use: six-face conditioning

The original-action local constants are already defined together as
`localFloor`, `localCap`, `lowerFactor`, `upperFactor` and `starRatio` in
`lean/YMGap/Continuum/BF4ExactSlabLocalStarComparison.lean:42` through line 46.
They compare the original action with only the selected link's incident faces
deleted. `original_star_bounds` at line 125 and
`original_star_normalized_cross` at line 144 preserve the complementary
action, shared links and both partition factors.

The local heat-window estimates therefore have a direct original-action
consumer, independently of the 23-factor route. Writing
`N = HeatRoundedCutoff.cutoff w`, `B = 5*N+5`, the new quantitative branch proves
`localCap <= 4^B*localFloor` and hence `1 <= 4^(6*B)*starRatio`.
The exponent counts six incident faces, not the volume. The nome remains an
explicit parameter. The following declarations are in
`lean/YMGap/Continuum/BF4ExactSlabRoundedStarBudget.lean`:

| Declaration | Line | Result |
|---|---:|---|
| `localCap_le_bitBudget` | 79 | Actual one-face cap/floor comparison. |
| `upperFactor_le_bitBudget` | 100 | Actual six-face comparison. |
| `starRatio_paid` | 119 | `1 <= 4^(6*B)*starRatio(w)`. |
| `original_star_normalized_budget` | 135 | Original normalized comparison with both partitions retained. |
| `bit_heat_cost` | 169 | `(6*B)*(t/4) <= 1080` under the existing AF envelope. |

All five printed gates report only `{propext, Quot.sound}`. Two focused safe
one-worker/20 GiB launches were used; direct associativity proofs replaced
two expensive expansions after the first check. No limits were raised and no
dependency refresh was needed. Final log: `/tmp/ym-rounded-star-budget.log`,
SHA-256 `7a6bc1bf9f583b9344f18978d8969e266b2d0d940cf255391e2f8c03ea4cfdbe`.
Own/direct artifacts were fresh. The semantic-root import was added without
running the root or a full-tree check. No old statement, canonical field,
axiom or literal hole changed; CI remains manual-only.

This is a conditioning estimate, not a new mixing result. The actual
`conditionalProjection_freeResidual_norm`,
`lean/YMGap/Continuum/BF4ExactSlabStarLocalInfluence.lean:134`, is an ordinary
original-action weighted-L2 estimate on explicitly free-link-centered inputs.
Its factor is `1-starRatio w`. It is not an estimate on the whole OS vacuum
complement. Moreover `inverseRate_ge_sixtyThreeSixtyFour`,
`lean/YMGap/Continuum/BF4ExactSlabStarRateObstruction.lean:56`, already shows
that this coarse directional factor is at least `63/64`; the new quantitative
lower bound on `starRatio` does not remove that obstruction.

## Remaining analytic edge and actual physical operator

There is a precise original-action consumer for a cancellation-preserving
spatial estimate: `insertion_bound_eventually`,
`lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetComparison.lean:86`.
Its hypothesis bounds the connected one-face insertion determinant by a
coefficient times the two actual partition functions. The theorem cancels
those same partitions and passes the bound to the constructed cutoff limits;
it does not construct a distance-decaying coefficient. Local positivity and
window ratios do not discharge that hypothesis.

The already constructed physical time object is `twoStepTransfer`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedTime.lean:197`.
Its observable pin is `timeCovariance_operator_sum` in that file at line 191.
`complement_twoStep_form_gap`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedGap.lean:99`, bounds
this original geometric transfer on the completed unit complement in the
existing fixed-nome `1/1024`, fixed-spacing construction. It is not an
all-nome or continuum theorem.

An all-nome original geometric-transfer strict bound supplied by the new heat
windows is **NOT FOUND** in the reviewed all-extent reflection/completion,
thermodynamic time/gap, local-star projection/influence, retained-Harnack,
and pointwise dynamic-window modules. No such bridge is claimed here.

### More precise boundary of the original-kernel route

The actual Gram factor already has `faceHeat_pin`,
`lean/YMGap/Continuum/BF4ExactSlabSpatialHeatCertificate.lean:92`, identifying
it with the character heat prefix of the actual two-link `spatialWord`
(defined at line 51). Support and Haar-unit norm are proved at lines 55 and
59. Its existing `spatialFaceCertificate` at line 106 still assumes
small-nome bounds. Extending positive certificates to all nomes at sufficiently
late cutoff is therefore a genuine finite subtask, not a missing coordinate
definition. Ordinary square certificates with arbitrary positive insertions
must not be confused with the already-proved reflected-pairing positivity.

The generic boundary integration identity also already exists:
`partialFactors_boundary_haar`,
`lean/YMGap/Continuum/SU2QuaternionPartialFactorizedHaar.lean:65`, integrates
an explicit number of head blocks while retaining an arbitrary polynomial on
the boundary blocks. No degree bound or Fubini axiom is supplied as a premise.

The following is a proposed next identification, **not a proved declaration**:
recode the actual lower interior and crossing-boundary blocks, integrate the
heat-dressed lower observables over their interior variables, and identify
the original bilinear with their pairing against the actual retained crossing
kernel. This instantiated boundary marginal identity, followed by an
original adjacent-slab composition/normalization pin, was **NOT FOUND** in the
reviewed all-extent, temporal-gauge, partial-factorized-Haar, tube-disintegration
and physical-joint-transfer modules. The search finding is not a theorem of
nonexistence. Even such a kernel identity would not supply centered decay.

## Parallelism and verification boundary

Three bounded branches were reviewed concurrently: quantitative original-star
constants, original temporal/Harnack identification, and the operator/spatial
consumer. The latter two are read-only checks. Only the first was selected for
a new proof after locating a direct existing consumer. No parallel Lean
compilers, replacement scorecard, relaxed frontier field or new assumed
analytic interface is needed.

The substantive continuation is a centered original-action spatial/transfer
estimate with the required nome, volume and physical-scale dependence, reusing
the existing temporal identity. Neither another proof of that identity nor
scalar-only Perron composition supplies it. Continuum QFT, nontriviality,
physical scale calibration and the all-group target remain open.
