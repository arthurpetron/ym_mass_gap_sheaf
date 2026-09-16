# Original response: distance exclusion and exact insertion activity

Date: 2026-09-16 (America/Los_Angeles). Base: `2319e53`.

PROGRESS: a literal three-mark connection gives a distance-to-core-size
floor, and the actual inserted SU(2) heat contributes one explicit w^3
factor. Both are integrated into the same signed response, with all
detached partition factors retained. OPEN: the remaining signed cofactor
has no useful spatially decaying bound here.

The whole-project goal remains constructive continuum Yang--Mills on R^4
with the required QFT axioms and a positive physical Hamiltonian gap for
every compact simple gauge group. No canonical frontier atom is closed.

## 1. Actual three-mark geometry

The old response filter tests p|(q,face), q|(p,face), and (p,q)|face.
The new argument treats the inserted plaquette as ONE ordinary face:

1. Any cut separating p from q after insertion places the inserted face
   on one side. Restricting that cut contradicts the corresponding first
   or second mark test.
2. The third test forces the inserted face into the ordinary common-root
   component. Every old path rooted at the union of all three marks can
   then use that actual face in place of its virtual insertion root.
3. The existing two-probe animal construction replaces the two remaining
   virtual roots by supplied connected carriers P and Q. No corridor
   between those carriers is added.

The resulting animal has at most |P|+|Q|+|anchor|+1 faces and contains
both carrier roots and the inserted face. The existing L-infinity animal
radius bound therefore yields

    max(d(P,Q), d(P,face), d(Q,face)) - |P| - |Q| <= |anchor|.

Subtraction is Nat subtraction. The inserted face's extra +1 cancels
the +1 in distance+1 <= animal size.

| Declaration | Source | Content |
|---|---|---|
| `BF4ExactSlabThreeMarkGeometry.keep_inserted` | `lean/YMGap/Continuum/BF4ExactSlabThreeMarkGeometry.lean:105` | First two tests force probe connection after adding the actual face. |
| `BF4ExactSlabThreeMarkGeometry.fixed_inserted` | `lean/YMGap/Continuum/BF4ExactSlabThreeMarkGeometry.lean:185` | The third test and old fixed-root condition transport the complete core. |
| `BF4ExactSlabThreeMarkGeometry.responseAnimal` | `lean/YMGap/Continuum/BF4ExactSlabThreeMarkGeometry.lean:213` | Type-valued actual animal and connecting paths. |
| `BF4ExactSlabThreeMarkGeometry.responseAnimal_size_le` | `lean/YMGap/Continuum/BF4ExactSlabThreeMarkGeometry.lean:219` | Two carrier sizes, old core size, and one inserted face. |
| `BF4ExactSlabThreeMarkGeometry.responseAnimal_inserted_mem` | `lean/YMGap/Continuum/BF4ExactSlabThreeMarkGeometry.lean:225` | The literal insertion belongs to that animal. |
| `BF4ExactSlabResponseDistanceActivity.response_anchor_size_floor` | `lean/YMGap/Continuum/BF4ExactSlabResponseDistanceActivity.lean:81` | Actual retained response anchors satisfy the marked-distance floor. |

The animal theorem requires connected probe carriers, a fixed rooted
anchor, physical face membership, duplicate-free anchor enumeration and
a fresh inserted id. The integrated theorem assumes id is absent from
the ambient list, which implies anchor freshness. The two graph lemmas
do not require freshness. No prior response statement was weakened.
For arbitrary disconnected probe supports, the old three tests alone
are still NOT a claim of one connected physical plaquette component.

## 2. Exact insertion activity, not a cofactor estimate

For a general affine insertion H=1+tR, let Z be the OLD partition, T3(R)
its partition-cubed third connected numerator, and C(p,R), C(q,R) its
partition-squared pair numerators. Exact rational algebra gives

    response = t * [ Z*T3(R) + t*(M(R)*T3(R)-C(p,R)*C(q,R)) ].

The linear third-moment term and quadratic correction both remain.
This is `RationalConnectedResponsePerturbation.affine_response`,
`lean/YMGap/Continuum/RationalConnectedResponsePerturbation.lean:35`;
the explicit cofactor is defined in that file:30, `cofactor`.

For the actual heat prefix, every positive spin s has c4(s)>=3.
`strippedHeat` sums dim(s)*w^(c4(s)-3)*chi_s over s=1,...,K. No inverse
of w is used, including at w=0. Thus the actual heat is 1+w^3*strippedHeat.

| Declaration | Source | Content |
|---|---|---|
| `BF4ExactSlabResponseInsertionActivity.strippedHeat` | `lean/YMGap/Continuum/BF4ExactSlabResponseInsertionActivity.lean:59` | Explicit division-free residual heat polynomial. |
| `BF4ExactSlabResponseInsertionActivity.faceHeat_affine` | `lean/YMGap/Continuum/BF4ExactSlabResponseInsertionActivity.lean:72` | Exact pin to the original full finite heat prefix. |
| `BF4ExactSlabResponseInsertionActivity.response_activity` | `lean/YMGap/Continuum/BF4ExactSlabResponseInsertionActivity.lean:157` | Original response equals w^3 times its constructed signed cofactor. |
| `BF4ExactSlabResponseInsertionActivity.responseCoefficient_activity` | `lean/YMGap/Continuum/BF4ExactSlabResponseInsertionActivity.lean:165` | Old-face finite differences preserve that SAME factor. |
| `BF4ExactSlabResponseDistanceActivity.responseAnchors_size_filter` | `lean/YMGap/Continuum/BF4ExactSlabResponseDistanceActivity.lean:104` | Removing too-short cores changes no retained anchor. |
| `BF4ExactSlabResponseDistanceActivity.distanceActivity` | `lean/YMGap/Continuum/BF4ExactSlabResponseDistanceActivity.lean:117` | Signed cofactor sum with each anchor's original detached Z^4. |
| `BF4ExactSlabResponseDistanceActivity.response_distance_activity` | `lean/YMGap/Continuum/BF4ExactSlabResponseDistanceActivity.lean:127` | Exact original response = w^3*distanceActivity. |

The combined identity is finite, at arbitrary rational w and cutoff K,
with the geometric guards above and original probe support/locality.
It assumes no quantitative coefficient bound. At w=0 it multiplies the
cofactor by zero; it neither divides by zero nor asserts that the cofactor
itself vanishes. The computed geometric filter is independent of w.

Actual consumer: the identity rewrites the finite response in
`BF4ExactSlabConnectedFaceResponse.covariance_response_bound_eventually`,
`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:224`.
The original denominator remains `responseDenominator` in that file:73,
Z_new^2*Z_old^2. No new limit or normalized surrogate is constructed.

## 3. Quantitative route constraint

Only ONE global insertion factor w^3 is proved here, not w^(3*|anchor|).
The distance floor therefore is not a spatial-decay theorem.

The existing all-nome cost is reciprocal to h^(4N+2), where
h=headFloor(w) and N=6*(markedLinks.length+4*anchor.length):
`BF4ExactSlabResponseCollarNormalization.collarFloor`,
`lean/YMGap/Continuum/BF4ExactSlabResponseCollarNormalization.lean:47`,
`collarCost`, same file:60, and `collarCount`, same file:156.
The checked floor obeys h<=1/32:
`BF4ExactSlabSharedWindowFloorBound.headFloor_le_oneThirtySecond`,
`lean/YMGap/Continuum/BF4ExactSlabSharedWindowFloorBound.lean:46`.

Arithmetic review, NOT a new Lean theorem: each additional anchor face
increases this coarse reciprocal budget by h^-96, at least 32^96.
Even a hypothetical w^(3*|anchor|) extraction would pair at w=1/1024
with per-face base w^3*32^96=2^450, before entropy. This diagnoses the
coarseness of that proposed majorant, not actual Yang--Mills behavior.

The sharper small-nome removal floor is already available:
`BF4ExactSlabRelativePartitionBound.removalFloor`,
`lean/YMGap/Continuum/BF4ExactSlabRelativePartitionBound.lean:33`, and
`relative_floor`, same file:50, use (1-heatRemainderBound(w))^count with
their explicit small-nome guards. The audit does not extend those guards
to weak coupling or prove a new response coefficient majorant.
Signed retained-interaction control with useful physical-scale dependence
remains missing. More counting alone would not supply that estimate.

## 4. Independent temporal-route source review

All-nome original interface windows already exist in
`BF4ExactSlabAllNomeSpatialHeatCertificate.interface_weighted_floor`,
`lean/YMGap/Continuum/BF4ExactSlabAllNomeSpatialHeatCertificate.lean:144`,
and `interface_weighted_upper`, same file:151. The original ONE-slab
boundary pairing is `BF4ExactSlabBoundaryMarginal.exact_bilinear_eq_boundaryHaar`,
`lean/YMGap/Continuum/BF4ExactSlabBoundaryMarginal.lean:100`.
`BF4ExactSlabSiteHeatAction.fullHeat_split`,
`lean/YMGap/Continuum/BF4ExactSlabSiteHeatAction.lean:143`, and
`fullAction_square`, same file:173, retain the shared-slice heat once
for site reflection. None of these statements is repeated time composition.

`Z4HalfTimeReflectionGeometry.boundaryCompleteSlabPlaquettes`,
`lean/YMGap/Continuum/Z4HalfTimeReflectionGeometry.lean:169`, uses
boxPlaquettes(extent+1). Time enlargement also changes the spatial box.
`BF4ExactSlabPlaquetteTimeEmbedding.translate`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteTimeEmbedding.lean:39`, changes
the finite carrier from half to half+n.

The existing stationarity-dependent consumer is
`BF4ExactSlabThermodynamicTimeBalance.formLimit_balance`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicTimeBalance.lean:61`,
using `BF4ExactSlabSpacetimeTimeInvariance.meanLimit_embed`,
`lean/YMGap/Continuum/BF4ExactSlabSpacetimeTimeInvariance.lean:40`.
Its construction uses the fixed nome guards in
`lean/YMGap/Continuum/BF4ExactSlabSpacetimeThermodynamicLimit.lean:34`,
`deltaGuard`, and the nome defined by
`BF4ExactSlabPlaquetteSmallNomeCertificate.nome`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeCertificate.lean:32`.

NOT FOUND in those boundary, site-action, time-embedding and time-balance
modules: an original adjacent-layer gluing theorem on a fixed spatial
carrier, retaining the intermediate spatial heat exactly once. That is
a proposed next mathematical target, not a proved declaration or an
assumed new field. Stationary-vacuum construction and identification with
the same original OS theory would still remain after that identity.

## 5. Verification and open boundary

Two agents supplied the geometry and heat-activity proofs independently;
the parent supplied scalar algebra, distance integration and serialized
verification. An independent read-only review checked all four modules,
freshness, all three mark tests, the distance offset, zero nome, signs,
and unchanged partitions.

All four new modules passed their FIRST focused checks through
`scripts/safe_lean_build.py`, one worker and the mandatory 20 GiB ceiling.
All 22 public gates are subsets of {propext, Quot.sound}; the scalar
definitions `third` and `cofactor` are axiom-free. Direct dependency
artifacts were newer than their sources; no dependency rebuild or raised
limit was needed. Four root imports were added. Root/full-tree compilation
and a full axiom audit were NOT run. No existing statement, canonical
field, axiom or literal hole changed. Final local log hashes:

- `/tmp/RationalConnectedResponsePerturbation.log`:
  `ec0e3fb8148a2ac5b168abb401ea558db6e984883912cf51def46f147b3b0221`.
- `/tmp/BF4ExactSlabThreeMarkGeometry.log`:
  `9ee1905ee1c5bf8158ae0d73bfbfd5bf5bfc43deaaee32e9d1dfef44fe0d655e`.
- `/tmp/BF4ExactSlabResponseInsertionActivity.log`:
  `f919750bffb72efc8816889ede8e55b55ba08dcb7654061874a53faf7c35805e`.
- `/tmp/BF4ExactSlabResponseDistanceActivity.log`:
  `21ac57c529887fcb7fc7b1d626780765c6615d494f2bebc460d207f542d60831`.

Spatial/cofactor estimates, all-nome stationary physical time, required
volume/spacing limits, continuum QFT/nontriviality, mass normalization and
all compact simple groups remain open. CI stays manual-only; the goal stays active.
