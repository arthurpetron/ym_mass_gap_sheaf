# One original spatial weight on a fixed slice carrier

Date: 2026-09-16. Classification: PROGRESS after `9706793`.

Whole-project goal: constructively build nontrivial continuum Yang--Mills
on R^4 with the required QFT axioms and a positive physical Hamiltonian gap
for each compact simple gauge group, with all clauses on the SAME theory.
This increment proves finite SU(2) identities, not that goal.

## Mathematical result

Let N be the number of boxed spatial links at time zero, retaining the
inclusive spatial fringe. Construct the original ordered plaquette words
on these N quaternion variables. Their complete finite heat product
`spatialWeight w K width` has no ambient-extent or time parameter.

Every contained placement sends it to the actual original spatial heat,
up to coefficient-sensitive zero padding. Its product-Haar pairing with
every supported source polynomial equals the corresponding original
ambient spatial-weighted pairing. This is stronger than merely having
carriers of equal size. It uses no positivity, division or coupling guard.

A second carrier explicitly orders the N variables at start followed by
the same N variables at start+1. Each lower and upper coordinate is pinned
to the original translated link. This is a coordinate input for the
kinetic factor, not yet a kinetic-factor or iteration theorem.

## Declaration evidence

Paths below are prefixed by `lean/YMGap/Continuum/`.

| Declaration | Module:line | Content |
|---|---|---|
| `face_edge_box` | `BF4ExactSlabFixedSpatialTwoLayerBoundary.lean:102` | Original face edges lie in the inclusive box; existing proof exposed. |
| `sliceLink_physical` | `BF4ExactSlabFixedSpatialBoundaryCarrier.lean:50` | Contained boxed spatial links are original physical links; existing proof exposed. |
| `baseLinks` | `BF4ExactSlabFixedSpatialSliceCarrier.lean:44` | Width-only spatial source enumeration. |
| `baseLinks_mem_iff` | `BF4ExactSlabFixedSpatialSliceCarrier.lean:47` | Exactly the entire boxed spatial slice. |
| `sliceLinks_length` | `BF4ExactSlabFixedSpatialSliceCarrier.lean:97` | Time translation keeps the same carrier size. |
| `embedding` | `BF4ExactSlabFixedSpatialSliceCarrier.lean:107` | Explicit physical injective placement. |
| `link_pin` | `BF4ExactSlabFixedSpatialSliceCarrier.lean:154` | Source coordinate is the original link quaternion. |
| `spatialFaces` | `BF4ExactSlabFixedSpatialFacePlacement.lean:31` | Width-only original spatial face list. |
| `temporalFaces` | `BF4ExactSlabFixedSpatialFacePlacement.lean:35` | Width-only original temporal face list. |
| `spatialFaces_shift_perm` | `BF4ExactSlabFixedSpatialFacePlacement.lean:189` | Exactly the original contained spatial faces with multiplicities preserved. |
| `temporalFaces_shift_perm` | `BF4ExactSlabFixedSpatialFacePlacement.lean:199` | Corresponding temporal-face identity. |
| `embedding` | `BF4ExactSlabFixedSpatialPairCarrier.lean:50` | Ordered lower N then upper N, disjoint by time. |
| `lower_block` | `BF4ExactSlabFixedSpatialPairCarrier.lean:103` | Head coordinates have the lower-slice order. |
| `upper_block` | `BF4ExactSlabFixedSpatialPairCarrier.lean:112` | Tail coordinates have the same upper-slice order. |
| `lower_link_pin` | `BF4ExactSlabFixedSpatialPairCarrier.lean:141` | Head original quaternion pin. |
| `upper_link_pin` | `BF4ExactSlabFixedSpatialPairCarrier.lean:158` | Tail original quaternion pin. |
| `plaquette` | `BF4ExactSlabFixedSpatialSliceHeat.lean:66` | Original oriented word, with noncommutative order retained. |
| `spatialWeight` | `BF4ExactSlabFixedSpatialSliceHeat.lean:70` | One polynomial depending only on w, K and width. |
| `plaquette_pin` | `BF4ExactSlabFixedSpatialSliceHeat.lean:117` | Ordered original plaquette reconstruction. |
| `heatFace_pin` | `BF4ExactSlabFixedSpatialSliceHeat.lean:156` | Every original finite heat-prefix term retained. |
| `spatialWeight_pin` | `BF4ExactSlabFixedSpatialSliceHeat.lean:168` | Actual spatialHeat identification, permitting scalar-factor permutation and padding. |
| `spatialWeight_supported` | `BF4ExactSlabFixedSpatialSliceHeat.lean:214` | No unsupported source exponent tail. |
| `spatialWeight_haar` | `BF4ExactSlabFixedSpatialSliceHeat.lean:224` | Weighted Haar identity for any supported source insertion. |

## Parameters, guards and remaining consumer

- The spatial-weight pin requires `width <= extent`, `time <= extent`.
  The pair placement requires `width <= extent`, `start+1 <= extent`.
  The face-list permutation alone needs only `width <= extent+1`.
  The stronger coordinate guard retains the whole box overcarrier, including
  unused fringe coordinates. No older statement is weakened.
- Nome w and cutoff K remain explicit. The identities hold at arbitrary
  rational w and finite K. They do not assert that these finite weights are
  positive, that any normalized law exists, or that a gap is uniform in w.
- `spatialWeight_haar` has insertion `embedding.polynomial p`, with source
  support supplied. It does not reduce an arbitrary spectator-coupled
  ambient insertion to N variables. The ambient coefficient identity can
  still be used there; reducing the full pairing needs a locality or
  marginal-integration argument.
- Actual next construction: the original kinetic polynomial on the N+N
  carrier, using its checked lower/upper link pins and the temporal-face
  permutation. Then finite Haar composition must integrate a full input
  slice, count each joining V once, and agree with the original action.
  These are not declarations proved by this increment.
- Finite weighted composition does not first require a stationary vacuum.
  Positivity, stationary normalization and the physical OS transfer pin
  remain distinct obligations. A quantitative original-Haar or signed-response
  estimate, cutoff-dependent insertion control, nome/volume/spacing limits,
  continuum QFT, physical mass calibration and all-group work remain open.

## Parallel work and independent review

Separate branches supplied single-slice coordinates, original face placement,
and ordered pair coordinates. The principal agent proved the spatial-weight
identity and alone ran the focused checks, serially. Independent read-only
review confirmed the exact original face set, ordered words, full spin sum
and insertion boundary; it found no mismatch or vacuity.

No new frontier bundle, analytic premise, literal hole or axiom was added.
No canonical atom was closed. The previously requested paper screening is
recorded separately in `RESEARCH-MATH-PH-2026-09-16.md`; no paper theorem
is a premise of the new Lean identities.

## Verification boundary

All six changed/new modules passed focused `scripts/safe_lean_build.py`
checks with one worker, a 20 GiB per-worker ceiling and individual `.olean`
outputs, following process/swap preflights. All 73 reported public gates
are subsets of {propext, Quot.sound}: 49 in the four new modules and 24
in the two rechecked existing modules, including two newly exposed helpers.

The initial face-placement check lacked a namespace import. Initial
spatial-heat elaboration needed heat-prefix imports and corrected notation;
the pair check needed explicit notation precedence. These failed runs were
not accepted. The final logs are clean apart from one harmless unused-variable
warning in the spatial-weight file. No new heartbeat, worker or memory
limit increase was required. Four root imports were added; the root/full
tree and full axiom audit were NOT run. CI remains manual-only.

Terminal log SHA-256 (logs are local `/tmp/` artifacts):

| Log | SHA-256 |
|---|---|
| `BF4ExactSlabFixedSpatialTwoLayerBoundary.log` | `143ff0b965c03e5ff26cb546c649a438f9b5d7ea6f71aa33ef009d5362845502` |
| `BF4ExactSlabFixedSpatialBoundaryCarrier.log` | `d04ab1107c7fa2e1cb756af334f99db35709fc8cd4761f9c1a379f18cd98485c` |
| `BF4ExactSlabFixedSpatialSliceCarrier.log` | `dcb64e336743241f4d81c6555fda1f7e6c916e81872b6ac441e733d1a5ce7a5f` |
| `BF4ExactSlabFixedSpatialFacePlacement.log` | `30be76b9414295ef9d6d5e5c074fc9d1f9b9d446eb892e4195c53023096d0856` |
| `BF4ExactSlabFixedSpatialSliceHeat.log` | `a59b3b2937fe404852c172cd76f3f0d753d4a25cc3155500716269300ff4b14a` |
| `BF4ExactSlabFixedSpatialPairCarrier.log` | `59d5fff617f884863410529930c991e59471313ce1fedd8fb62c7fdf156336b4` |
