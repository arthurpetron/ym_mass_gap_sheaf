# Original two-copy action: comparison charged only at the cut

## Goal and mathematical scope

The whole-project goal remains OPEN: constructive continuum Yang--Mills on
R^4 for every compact simple group, with SAME-theory QFT axioms, nontriviality
and a finite positive physical Hamiltonian gap.

This increment concerns the ORIGINAL finite SU(2) face-heat polynomial
action, rational nome 0<w<1 and cutoff K>=headCutoff(w). Let W be its full
shared-link product, ell=headFloor(w)>0, U=prefixCap(w), and S exchange a
selected physical link set between two copies of the original carrier.
If b counts original physical plaquettes meeting both sides, the proved bound is

    ell^(2b) Haar[ W(x)W(y) r ]
      <= U^(2b) Haar[ W(S(x,y)) r ].

Here W(S(x,y)) abbreviates the product of the two swapped action values,
not one action on a doubled lattice. The theorem uses (ell*ell)^b and
(U*U)^b. The insertion r can depend jointly on both copies and must carry
an actual nonnegative square certificate. No independent-face measure,
conditional marginal replacement or positivity of an unknown ratio is
assumed. No all-cutoff limit is taken in this increment.

## Exact cancellation and constructed comparison

Every face wholly outside the selected set is fixed in each replica.
Every face wholly inside has its two factors exchanged, leaving their
product unchanged. The equalities are Haar-carrier equalities, not assertions
of literal polynomial-list equality. For a crossing face, the original pair
has cap U^2 and the swapped pair has floor ell^2. The identity

    U^2 q - ell^2 p = U^2 (q-ell^2) + ell^2 (U^2-p)

constructs its comparison certificate. Product telescoping retains all
overlapping spectator factors and charges scalar loss only on changed
faces. Pair regrouping pins the result back to W(x)W(y) with the full
original shared-link action.

Paths in this table start at `lean/YMGap/Continuum/`.

| Declaration | File:line | Role |
| --- | --- | --- |
| `headFloor`, `headFloor_positive`, `headCutoff` | `BF4ExactSlabRetainedHeatHeadComparison.lean:50`, `:52`, `:55` | Explicit nome-dependent floor and late-cutoff guard |
| `prefixCap` | `BF4ExactSlabAllNomeTailInterval.lean:117` | Explicit nome-dependent original prefix cap |
| `selected_pair_fixed`, `unselected_pair_fixed` | `SU2QuaternionReplicaPairSwap.lean:110`, `:130` | Exact whole-side two-copy invariance |
| `pairFloorCertificate`, `pairCapCertificate` | `SU2QuaternionReplicaPairBounds.lean:131`, `:162` | Constructed squared floor and cap |
| `reindexedPairFloorCertificate`, `reindexedPairCapCertificate` | `SU2QuaternionReplicaPairBounds.lean:200`, `:222` | Same bounds on the actually reindexed pair |
| `uncrossed_face_pair`, `facePair_product_pin` | `BF4ExactSlabReplicaCutLocality.lean:75`, `:115` | Physical face cancellation and original full-action pin |
| `masked_product_gap_certificate_cap` | `QuaternionHaarChangedProductComparison.lean:206` | Shared-coordinate product telescope with changed-count exponent |
| `cutCrossingFaces_time_locality` | `BF4ExactSlabCutFaceGeometry.lean:57` | Every crossing face lies in the two layers adjacent to a time-ordered cut |
| `cutCrossingFaces_length_le_area`, `crossingMask_length_pin` | `BF4ExactSlabReplicaCutArea.lean:89`, `:123` | Two-layer area count and exact original face-ID count pin |
| `crossingCount`, `crossingCount_le_area` | `BF4ExactSlabReplicaCutComparison.lean:58`, `:63` | The action certificate's actual count is at most 12*(extent+1)^3 for time-layer cuts |
| `originalPair_pin`, `swappedPair_pin` | `BF4ExactSlabReplicaCutComparison.lean:119`, `:124` | Both action products remain on the original doubled carrier |
| `swappedPair_mass_pin` | `BF4ExactSlabReplicaCutComparison.lean:134` | Exchange preserves the full original pair partition |
| `facePairComparison`, `cutComparisonCertificate` | `BF4ExactSlabReplicaCutComparison.lean:157`, `:176` | Local comparison and full original-action certificate |
| `weighted_cut_comparison` | `BF4ExactSlabReplicaCutComparison.lean:216` | Quantitative order under every certified nonnegative joint insertion |

The geometric theorem permits arbitrary selection of links based at the
current time t, provided all physical links below t are selected and all
above t are unselected. It yields t<=faceTime+1 and faceTime<=t. Each layer
has at most six orientations at each of (extent+1)^3 spatial bases, so the
checked bound is b<=12*(extent+1)^3. The candidate superset can repeat a
layer when t=0; the proof needs only the original crossing list to be
duplicate-free. Endpoint spatial faces are retained, not deleted.

## What the next canonical-path join would have to establish

This is a reviewed paper calculation, NOT a new Lean theorem. Set R=U/ell,
let N be the number of updated links, and C the maximal crossing-face count
of their prefix cuts. At a path step j, the complementary configuration
rearrangement has cost R^(2c_j). Comparing the two actual single-link
conditional densities needs an additional R^(2d_j): one R^d_j from the
incident action factors, and one from their conditional normalizers.
The existing physical link-star bound d_j<=6 is
`BF4ExactSlabLinkStarGeometry.incidentIds_length_le_six`,
`lean/YMGap/Continuum/BF4ExactSlabLinkStarGeometry.lean:89`.

IF that cross-exterior conditional-density comparison and the exact
path-integral pin are proved for the SAME original law, the elementary
path telescope and Cauchy--Schwarz give the candidate

    Var_mu(f) <= N * R^(2C+12) * sum_j E_mu[ Var_j(f) ].

Two Sol reviews checked the normalization and exponent bookkeeping: the
1/2 in the variance identity cancels the conditional pair-variance factor
2; no Z, Z^2 or polynomial-degree multiplier remains in this calculation.
Neither of the two missing joins is supplied by the raw product certificate.
C may grow with cut area; even the candidate bound is therefore not a
proved useful spatial/scaling estimate. Do not present this increment as
improved coercivity, conditional-generator gap, OS decay or physical mass.
The next action is the actual conditional-normalizer/path comparison, not
another theorem assuming its desired conclusion.

In particular, `BF4ExactSlabStarNormalizer.normalizer_form_bounds`,
`lean/YMGap/Continuum/BF4ExactSlabStarNormalizer.lean:101`, provides
one-exterior Haar form bounds, not a pointwise ratio between two different
exteriors. The missing comparison must retain both actual normalizers,
their original incident factors and the shared updated link, then pass
through both conditional inverse pairings. Neither a star-deleted law nor
one-normalizer positivity is that bridge.

## Independent computational-route review

There already IS a general exact factorized Haar evaluator in Lean:
`SU2QuaternionFactorizedHaarContraction.quaternionHaar_factorizedHeadStep`
at `lean/YMGap/Continuum/SU2QuaternionFactorizedHaarContraction.lean:318`,
and `quaternionHaar_eq_compactFactorizedHaar` at `:438`. It integrates the
head-incident factors, retains independent factors and proves the result
equal to the original Haar product. It is not merely an untrusted Python
algorithm. `BF4ExactCutoffOneSurfaceFactorizedHaar.exactCorrectedSlabHaarCoefficient_eq_factorized`,
`lean/YMGap/Continuum/BF4ExactCutoffOneSurfaceFactorizedHaar.lean:96`,
already pins it to the actual corrected-slab spin coefficient at every
extent. Its existence alone supplies neither a resource bound nor the
six required original moments for the K>=627, 24-face proposed pilot.
The 24-face diagnostic core still needs its same-action/observable pin;
intermediate incident products can grow despite avoiding Cartesian label
enumeration. No large evaluation was launched. The cached feasibility screen remains
relevant to naive enumeration, not a lower bound on every compressed method.

## Verification record

Seven final focused module checks passed 49 printed gates within
{propext, Quot.sound}: PairSwap 3, CutFaceGeometry 5, CutLocality 8,
PairBounds 9, ChangedProductComparison 10, CutArea 4, CutComparison 10.
The initial finite-edge geometry proof was adjusted to remove
an unintended Classical.choice dependency before its successful check.
The comparison elaboration timeout was eliminated by avoiding unnecessary
unfolding at the certificate-product transport, without raising the worker
memory ceiling. Final successful checks have no sorryAx or Classical.choice.
No sorry or custom axiom was introduced, and no existing sorry discharged.

Logs under `/tmp/`: `ym-replica-pair-swap-20260930.log`,
`ym-cut-face-geometry-20260930.log`, `ym-replica-cut-locality-20260930.log`,
`ym-replica-pair-bounds-20260930.log`, `ym-changed-product-20260930.log`,
`ym-replica-cut-area-20260930.log`, `ym-replica-cut-comparison-20260930.log`.

All checks are serialized through the safe-build wrapper, one worker,
20 GiB ceiling, 12 GiB OS reserve and continuous dynamic safety telemetry.
Manual polling of a confirmed live job is spaced by about five minutes;
independent mathematical/source work continues while it runs. No full-root
build, global audit or frontier guard is claimed. Root imports are registered
without claiming a root compilation. Routine literature
scanning was not repeated within its twelve-hour cache interval.

Luna supplied time-layer geometry and the computational-route source review.
Sol supplied pair bounds, changed-product telescoping and the area count;
root supplied partial-exchange cancellation and the actual full-action
comparison. Independent Sol reviews checked its scope and the paper-level
conditional path budget. Lean verification remained serialized.

The canonical chart is unchanged. The useful original signed spatial/
scaling estimate, continuum survival, same-theory OS/physical-time passage,
full QFT axioms, finite physical mass and every-group construction remain
open.
