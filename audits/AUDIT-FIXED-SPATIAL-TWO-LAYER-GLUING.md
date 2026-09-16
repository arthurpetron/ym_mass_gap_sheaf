# Fixed-spatial two-layer gluing and parallel future-path checks

Date: 2026-09-16. Base: `3fc7c58`.

PROGRESS: kernel-checked original selected-window two-layer Haar gluing,
with fixed spatial width and exactly one middle spatial heat factor.
OPEN: repeated layers on one stationary original physical carrier and
the quantitative estimates needed for the continuum route.

The whole-project goal remains a constructive nontrivial continuum
Yang--Mills theory on R^4 with the required QFT axioms and a positive
physical Hamiltonian gap for every compact simple gauge group, all pinned
to the same theory. No canonical frontier atom is closed by finite gluing.

## 1. Work that could proceed independently

The user requested parallel work on future prerequisites. Three source
reviews ran independently: fixed-spatial geometry, the original physical
operator interface, and quantitative positivity/normalization. Geometry
and endpoint-factor support then became separate proof branches. The
parent integrated them using the existing common temporal sweep and
original-Haar conditional integration; all compilation remained serialized.

This split has a concrete join point: the geometry proves which original
factors occur, locality proves which variables the endpoints do not use,
and the integration proof must use BOTH on the same action. Separate
successful branches alone would not establish a physical transfer theorem.

## 2. Exact finite target and its scope

Write S_t for spatial faces at time t and T_t for temporal faces based at t.
Every list is filtered from the SAME ambient physical face-ID enumeration,
with an independently specified spatial BASE width. The two-layer window is

    S_t ++ T_t ++ S_(t+1) ++ T_(t+1) ++ S_(t+2).

The permutation to the literal boundary-complete window and duplicate-free
enumeration ensure every selected physical face occurs once. In particular,
the middle spatial slice is not counted twice. The complete, unclipped box
requires `width <= extent+1` and `start+2 <= extent`. The spatial cutoff uses
the repository's base-coordinate convention, not a newly asserted cubical
vertex-box boundary condition.

Let V0,V1,V2 be the ORIGINAL spatial heat products and K01,K12 the complete
finite relative-character heat products on the two temporal layers. A
single common sweep of the action AND endpoint observables gives the finite
Haar pairing with

    V0 * K01 * V1 * K12 * V2.

For arbitrary finite signed spatial endpoint face factors P, the proved
identity is

    Haar(P * originalWindowAction)
      = Haar((P * (V0 * V2)) * integrateMiddle(K01 * (V1 * K12))).

No positivity, inverse, asymptotic estimate or coupling restriction enters
this identity. All finite character terms and signs remain. P may contain
repeated faces and arbitrary signed character coefficients; every probe
face must be physical, spatial and on an endpoint slice. This is not yet a
statement for every vector of the original OS completion.

The selected window action is original heat action on that finite face
region. It is NOT the entire larger ambient slab action with its surrounding
interactions discarded. The ambient carrier supplies stable link indices;
the face region is specified explicitly. Algebra also works for clipped
windows, while the containment guards above certify the intended full box.

The integration schedule consists of original spatial-link blocks at the
middle time. Temporal links have disappeared only through the proved common
gauge change. Endpoint independence follows from actual polynomial locality,
not from treating an incident action factor as a spectator. No change of
coordinate numbering is made.

| New declaration | Source | Content |
|---|---|---|
| `BF4ExactSlabFixedSpatialTwoLayerGeometry.twoLayerIds_perm_window` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLayerGeometry.lean:171` | Exact five-family permutation of the original selected window. |
| `BF4ExactSlabFixedSpatialTwoLayerGeometry.twoLayerIds_nodup` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLayerGeometry.lean:206` | No repeated action face. |
| `BF4ExactSlabFixedSpatialTwoLayerGeometry.middle_spatial_mem` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLayerGeometry.lean:210` | Every selected middle spatial face is included. |
| `BF4ExactSlabFixedSpatialTwoLayerGeometry.windowFaces_mem_iff` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLayerGeometry.lean:217` | Complete raw-face window under explicit spatial/time containment. |
| `BF4ExactSlabSpatialSliceFactors.spatialFactors_swept_eq_zero` | `lean/YMGap/Continuum/BF4ExactSlabSpatialSliceFactors.lean:50` | Spatial endpoint factors remain literally unchanged at every sweep cut. |
| `BF4ExactSlabSpatialSliceFactors.endpointFactors_local` | `lean/YMGap/Continuum/BF4ExactSlabSpatialSliceFactors.lean:75` | Their actual monomials use only endpoint spatial links. |
| `BF4ExactSlabSpatialSliceFactors.heatFactors_zero` | `lean/YMGap/Continuum/BF4ExactSlabSpatialSliceFactors.lean:114` | Exact equality with the pre-existing original heat product. |
| `BF4ExactSlabFixedSpatialTwoLayerGluing.swept_window_factorization` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLayerGluing.lean:134` | Full finite heat products become V0*K01*V1*K12*V2. |
| `BF4ExactSlabFixedSpatialTwoLayerGluing.middle_haar_gluing` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLayerGluing.lean:165` | Only the middle spatial blocks are integrated. |
| `BF4ExactSlabFixedSpatialTwoLayerGluing.original_twoLayer_gluing` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLayerGluing.lean:188` | Same original action and signed endpoint insertions, including endpoint spatial weights. |

## 3. Reused proved inputs, not new wrappers

| Declaration | Source | Use |
|---|---|---|
| `BF4ExactSlabTemporalSweep.sweep_haar` | `lean/YMGap/Continuum/BF4ExactSlabTemporalSweep.lean:130` | One common ledger acts on a complete signed face-factor product. |
| `BF4ExactSlabConnectedTemporalSweep.sweep_product_haar` | `lean/YMGap/Continuum/BF4ExactSlabConnectedTemporalSweep.lean:61` | The same change of variables acts on probes and action together. |
| `BF4ExactSlabConnectedTemporalSweep.sweep_connected` | `lean/YMGap/Continuum/BF4ExactSlabConnectedTemporalSweep.lean:72` | Existing common pin for partition, both means and mixed moment. |
| `BF4ExactSlabTemporalGaugeFaces.crossing_face_word` | `lean/YMGap/Continuum/BF4ExactSlabTemporalGaugeFaces.lean:161` | Temporal-link cancellation follows the specified gauge assignment. |
| `SU2QuaternionOriginalHaarBlockMarginal.quaternionHaar_polyMul_eq_after_integratingBlocks_of_local` | `lean/YMGap/Continuum/SU2QuaternionOriginalHaarBlockMarginal.lean:173` | Original conditional Haar integration consumes proved spectator locality. |
| `BF4ExactSlabSiteHeatAction.fullHeat_split` | `lean/YMGap/Continuum/BF4ExactSlabSiteHeatAction.lean:143` | Existing site-reflection action counts shared spatial heat once; it was not already temporal iteration. |
| `BF4ExactSlabBoundaryMarginal.exact_bilinear_eq_boundaryHaar` | `lean/YMGap/Continuum/BF4ExactSlabBoundaryMarginal.lean:100` | Existing one-slab boundary pairing, not arbitrary adjacent-layer composition. |

## 4. Quantitative route check: a different carrier cannot be substituted

The original spatial interface has a certified weighted lower bound
`headFloor(w)^F` for `0<w<1` and `K>=headCutoff(w)`, and upper bound
`prefixCap(w)^F`. Here F is the actual crossing-face count and the background
is an arbitrary supplied square certificate, not an independent product.
The declarations are `interface_weighted_floor` and `interface_weighted_upper`
in `lean/YMGap/Continuum/BF4ExactSlabAllNomeSpatialHeatCertificate.lean:144`
and `lean/YMGap/Continuum/BF4ExactSlabAllNomeSpatialHeatCertificate.lean:151`.
Their same-original-bilinear pin is `exact_bilinear_eq_spatialGramHaar`,
`lean/YMGap/Continuum/BF4ExactSlabAllExtentTemporalHaarForm.lean:241`.

The computed nome-dependent constants already exist:

- `headFloor`, `headFloor_positive`, `headCutoff`:
  `lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:50`,
  `lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:52`,
  `lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:55`.
- `prefixCap`, `majorant_prefix_bound`:
  `lean/YMGap/Continuum/BF4ExactSlabAllNomeTailInterval.lean:117`,
  `lean/YMGap/Continuum/BF4ExactSlabAllNomeTailInterval.lean:125`.

There is already a finite-state terminal-message contraction theorem:
`BF4BoundaryMessageProjectiveRefresh.terminalProjectiveRefresh_l1_contraction`,
`lean/YMGap/Continuum/BF4BoundaryMessageProjectiveRefresh.lean:706`.
Its common mass is constructed as `1/spread^2` by `commonMass` at
`lean/YMGap/Continuum/BF4BoundaryMessageProjectiveRefresh.lean:260`.
It uses finite rational state lists and positive matrix entries; its
terminal normalization is `terminalNormalize` at
`lean/YMGap/Continuum/BF4BoundaryMessageProjectiveRefresh.lean:112`.

NOT FOUND in those modules: a bridge converting the actual original
quaternion-Haar certificate inequalities into that finite-state API.
Representation labels are not automatically positive configuration-kernel
entries. Finite-horizon terminal-message forgetting is a possible narrower
consumer than stationary Perron theory, but no original-Haar contraction is
claimed here. The actual Haar applicability proof remains open.

Nor is a physical stationary vacuum already supplied by a normalization
wrapper. `UniformNormalizedMatrix` ASSUMES row normalization and symmetry
(`lean/YMGap/Continuum/BF4NormalizedSameCarrierPerron.lean:199`), and
`PerronIdentification` SUPPLIES the dominant eigenmode
(`lean/YMGap/Continuum/BF4NormalizedSameCarrierPerron.lean:327`).
`vacuumCode_finite_norm` and `vacuumCode_limit_norm` normalize a boundary
code, not a stationary interacting vacuum
(`lean/YMGap/Continuum/BF4ExactSlabAllExtentVacuumNormalization.lean:141`,
`lean/YMGap/Continuum/BF4ExactSlabAllExtentVacuumNormalization.lean:150`).

## 5. Actual next consumers and remaining boundary

The new finite identity is a prerequisite for repeated original temporal
composition at fixed spatial volume. It does not itself construct a
one-carrier boundary operator, its stationary law or an OS identification.
The closest already completed physical iterate declarations are
`completedTime_moments` and `timeCovariance_operator_sum`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedTime.lean:153`
and `lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedTime.lean:191`.
Those use the existing stationary fixed-nome construction, not a new
all-nome stationary carrier furnished by this gluing theorem.
NOT FOUND in the reviewed time, boundary and Perron modules: a direct
all-nome same-carrier iterate consumer of the new selected-window identity.
Constructing that bridge is still required; this report does not assert it.

Cutoff convergence for FIXED original insertions exists as `finite_converges`,
`lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetExpectation.lean:78`.
It does not automatically permit cutoff-dependent intermediate boundary
functions. Likewise, dividing individual layers by unrelated partition
functions would not establish the normalized original cylinder law.

OPEN: original repeated-layer boundary composition/recoding, applicable
quantitative Haar contraction or signed spatial response control, physical
stationary vacuum and OS transfer identification, the required volume and
spacing estimates, continuum QFT/nontriviality and all compact simple groups.
The existing positive floor depends explicitly on nome and face count;
it is not a volume-uniform or physical-spacing-uniform gap.

## 6. Verification

All three new modules passed focused checks through `scripts/safe_lean_build.py`,
serialized with one worker and the mandatory 20 GiB memory ceiling. All 30
new public gates are within {propext, Quot.sound}; the classifier and finite
partition helper were also gated explicitly. No new literal hole, axiom,
named analytic assumption or canonical-field change was introduced.

The first geometry proof elaborated with an unwanted `Classical.choice`
dependency. It was NOT accepted: explicit conjunction/implication cases
and false elimination replaced the compound arithmetic shortcut. Namespace,
projection and syntax errors were also corrected in focused iterations.
The integrated factorization initially hit the elaboration budget; its
list algebra was proved on abstract lists before instantiating the physical
enumerations. One scoped heartbeat budget is 1,000,000. Memory/worker limits
were not raised and no dependency rebuild was required.

An independent source review checked the original action, common sweep,
exactly-once middle heat, endpoint locality, and remaining same-carrier
operator/limit boundary. Three semantic-root imports were added; the root,
full tree and full axiom audit were NOT compiled. CI remains manual-only.
The unchanged whole-project goal remains active.

Final focused log hashes:

- `/tmp/BF4ExactSlabFixedSpatialTwoLayerGeometry.log`:
  `2c5cf3e49300aa691418e3605cfa90260b244fb4fd1b40635d864bc7ebf0b7a6`.
- `/tmp/BF4ExactSlabSpatialSliceFactors.log`:
  `e1f788bd8b270ea78fde2fad183112ecbc4e3ef0db9799fe7a832fb6e96b636f`.
- `/tmp/BF4ExactSlabFixedSpatialTwoLayerGluing.log`:
  `ceb938c82313c92dc3c55979f68af71e280fc936be7c28ad461773888caa7b09`.
