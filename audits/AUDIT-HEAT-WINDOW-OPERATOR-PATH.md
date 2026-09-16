# From local heat windows to the original operator

Date: 2026-09-15 (local). Source review starts at `b9a9292`; the six-face
increment is `6ad5cc7`, followed by the all-nome spatial certificates below.
Source review and new finite proofs are distinguished; no physical gap is proved.

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
small-nome bounds. The new all-nome, sufficiently-late-cutoff construction below
removes this restriction without changing the old statement. It is not a new
coordinate definition. Ordinary square certificates with arbitrary positive insertions
must not be confused with the already-proved reflected-pairing positivity.

The generic boundary integration identity also already exists:
`partialFactors_boundary_haar`,
`lean/YMGap/Continuum/SU2QuaternionPartialFactorizedHaar.lean:65`, integrates
an explicit number of head blocks while retaining an arbitrary polynomial on
the boundary blocks. No degree bound or Fubini axiom is supplied as a premise.

At the `50d0d9d` checkpoint, the following was a proposed identification,
**not then a proved declaration**:
recode the actual lower interior and crossing-boundary blocks, integrate the
heat-dressed lower observables over their interior variables, and identify
the original bilinear with their pairing against the actual retained crossing
kernel. This instantiated boundary marginal identity, followed by an
original adjacent-slab composition/normalization pin, was **NOT FOUND** in the
reviewed all-extent, temporal-gauge, partial-factorized-Haar, tube-disintegration
and physical-joint-transfer modules. The search finding is not a theorem of
nonexistence. Even such a kernel identity would not supply centered decay.

**Subsequent update:** the explicit interior marginal and original boundary
pairing pin are now proved without global recoding; see
`audits/AUDIT-ORIGINAL-BOUNDARY-MARGINAL.md`. Adjacent-region composition,
normalization/time identification and centered decay remain open.

## New proof: all-nome original spatial heat certificates

The Jacobi argument now applies to a general supported Haar-unit quaternion
word. Its character intervals bound the finite Jacobi-weight deficit in Haar
certificate order, not just at rational evaluation points. Adding that deficit
to the positive Jacobi polynomial leaves the SAME original unweighted prefix
above the SAME `headFloor(w)` for `K>=headCutoff(w)`.

All entries in this table are in
`lean/YMGap/Continuum/QuaternionHaarAllNomeHeatCertificate.lean`:

| Declaration | Line | Content |
|---|---:|---|
| `termInterval` | 50 | Sharp certificate interval for the actual dimension/Casimir character term. |
| `prefixInterval` | 56 | Cutoff-independent absolute cap `prefixCap(w)`. |
| `prefix_eq_weighted_add_deficit` | 65 | Exact original-prefix recombination. |
| `deficitInterval` | 91 | Existing computed `deficitCutoff` controls an arbitrary word. |
| `weightedFloorCertificate` | 123 | Jacobi constant floor as a square certificate. |
| `prefixFloorCertificate` | 137 | Late original unweighted prefix minus `headFloor(w)` is certified positive. |
| `prefixCertificate` | 159 | Its actual positive certificate. |

The original-action consumer is now implemented in
`lean/YMGap/Continuum/BF4ExactSlabAllNomeSpatialHeatCertificate.lean`:

| Declaration | Line | Content |
|---|---:|---|
| `faceFloorCertificate` | 50 | Floor on the actual Gram heat factor, via existing `faceHeat_pin`. |
| `faceCertificate` | 56 | Its ordinary positive certificate at late cutoff. |
| `faceInterval` | 63 | Absolute cap for actual crossing faces, all cutoffs. |
| `productCertificate` | 72 | Products retain every shared variable. |
| `interfaceCertificate` | 78 | The literal original `interfacePolynomial`. |
| `spectatorCertificate` | 83 | The existing spectator interface with no removed interactions. |
| `face_weighted_floor` | 111 | One-face lower bound with an arbitrary positive background. |
| `product_weighted_floor` | 119 | Lower cost is `headFloor(w)^length`. |
| `product_weighted_upper` | 135 | Upper cost is `prefixCap(w)^length`. |
| `interface_weighted_floor` | 144 | Full original crossing-interface lower comparison. |
| `interface_weighted_upper` | 151 | Full original crossing-interface upper comparison. |

All statements retain `0<w<1`; floors/positivity require the explicit late
cutoff. All-nome does NOT mean a common positive floor as w tends to one.
The interface cost counts all its actual crossing faces; it is not a
volume-independent contraction. Arbitrary positive background certificates
are inputs to the comparison, not assertions that a signed lower-times-upper
observable is pointwise positive.

Twenty printed gates passed within `{propext, Quot.sound}`; `heatTerm` and
`deficitPolynomial` are axiom-free. Four focused one-worker/20 GiB checks
included two namespace/section-parameter correction reruns. Final logs:

- `/tmp/ym-all-nome-word-heat-certificate.log`: SHA-256
  `1ca83080d4693d0af53b50e40faefe175901cbd319925d31750d697b8b8be809`.
- `/tmp/ym-all-nome-spatial-heat-certificate.log`: SHA-256
  `d08e77acd3acecdf88beaa95895d6264ca22c808700f93f3c6d06b519e5e8ad4`.

No raised limits, dependency refresh, changed old statements/fields, custom
axiom or literal hole. Own/direct artifacts were fresh. Two semantic-root
imports were added; root/full-tree verification was not run. CI remains
manual-only. This removes the finite spatial-factor positivity restriction;
it does not construct a strict centered OS estimate or a continuum limit.

Independent source review found no hidden analytic premise in these two new
modules. A further direct consumer is the original bulk-probe background:
`backgroundCertificate` and `background_weighted_bound` in
`lean/YMGap/Continuum/BF4ExactSlabBulkProbePositiveBackground.lean:119` and
line 126 currently use small-nome guards only to obtain positive certificates
for their lower, upper and crossing spectators. An all-nome late-cutoff
version can use the constructed certificates; that additional composition
was not claimed as a declaration of that checkpoint. It is now supplied by
`BF4ExactSlabAllNomeBulkProbeBackground`, documented in
`audits/AUDIT-ORIGINAL-BOUNDARY-MARGINAL.md`. In contrast,
`productErrorInterval`,
`lean/YMGap/Continuum/BF4ExactSlabBulkProbeCollarInterval.lean:88`, retains a
small-nome estimate on the original collar's deviation from the unit
reference. Positive background certificates do not supply that small error.

## Parallelism and verification boundary

Three bounded branches were reviewed concurrently: quantitative original-star
constants, original temporal/Harnack identification, and the operator/spatial
consumer. The initial identification reviews were read-only. They selected two
independent proof branches: the six-face budget and the all-nome original
spatial certificates, each with a direct existing consumer. No parallel Lean
compilers, replacement scorecard, relaxed frontier field or new assumed
analytic interface is needed.

The substantive continuation is a centered original-action spatial/transfer
estimate with the required nome, volume and physical-scale dependence, reusing
the existing temporal identity. Neither another proof of that identity nor
scalar-only Perron composition supplies it. Continuum QFT, nontriviality,
physical scale calibration and the all-group target remain open.
