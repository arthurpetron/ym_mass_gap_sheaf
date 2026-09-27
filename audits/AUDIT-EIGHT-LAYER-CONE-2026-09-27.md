# Checked physical eight-layer cone and separated pairing

## Outcome

The original completed conditional dynamics now have a computed schedule
which updates every physical link exactly once in eight commuting layers.
For an input localized on S, each layer can be replaced EXACTLY by the
updates in its current cone. One full sweep needs eight Ward-star
expansions, and n complete sweeps need 8*n expansions. The number of
expansions has no volume, heat-cutoff or coupling factor.

If the test support is disjoint from that enlarged cone, the original
interacting pairing is unchanged:

    B(sweep^n x, y) = B(x, y).

This is a finite-propagation identity, not a decay estimate. It provides a
direct spatial use for a future same-sweep contraction bound; a separate
Neumann inverse is not needed for this identity.

## Exact objects and evidence

The color is `(direction, coordinate-sum parity of the base vertex)` in
`Dir4 × Fin 2`. Parallel edges of a plaquette have opposite parity, while
perpendicular edges have distinct directions. This is proved against the
literal `edgesOf`, not an assumed coloring of a surrogate graph.

| Declaration | Source | Checked claim |
|---|---|---|
| `face_colors_nodup` | `lean/YMGap/Continuum/Z4LinkEightColor.lean:42` | All four boundary edges have different colors. |
| `same_color_on_face_eq` | `lean/YMGap/Continuum/Z4LinkEightColor.lean:88` | Same-colored edges on one face must be the same edge. |
| `colors_length`, `colors_nodup`, `color_mem_colors` | `lean/YMGap/Continuum/Z4LinkEightColor.lean:98`, `:100`, `:102` | The eight-color list is complete and duplicate-free. |
| `Family.sweep_filter` | `lean/YMGap/Continuum/GNSCommutingSweep.lean:34` | Delete initially fixing updates from a commuting schedule with exact completed-vector equality. |
| `schedule_covers` | `lean/YMGap/Continuum/BF4ExactSlabEightLayerCone.lean:65` | Every actual boundary-complete physical link is updated. |
| `schedule_nodup` | `lean/YMGap/Continuum/BF4ExactSlabEightLayerCone.lean:85` | Each physical link is updated only once per complete sweep. |
| `Localized` | `lean/YMGap/Continuum/BF4ExactSlabEightLayerCone.lean:131` | Operational support: every outside conditional update fixes the state. |
| `localized_embed` | `lean/YMGap/Continuum/BF4ExactSlabEightLayerCone.lean:134` | Literal polynomial support supplies operational support. |
| `same_color_commute` | `lean/YMGap/Continuum/BF4ExactSlabEightLayerCone.lean:141` | Actual original-action projections of the same color commute. |
| `layer_prune` | `lean/YMGap/Continuum/BF4ExactSlabEightLayerCone.lean:167` | Full layer equals the initially supported sublayer on the original input. |
| `layer_localized` | `lean/YMGap/Continuum/BF4ExactSlabEightLayerCone.lean:179` | At most one Ward-star expansion per layer. |
| `runLayers_eq_cone` | `lean/YMGap/Continuum/BF4ExactSlabEightLayerCone.lean:227` | Computed truncated cone gives the same completed vector as the full layers. |
| `eight_layer_cone_embed` | `lean/YMGap/Continuum/BF4ExactSlabEightLayerCone.lean:248` | Literal source instance of exact full/cone equality. |
| `runLayers_pairing` | `lean/YMGap/Continuum/BF4ExactSlabEightLayerCone.lean:271` | Pairing unchanged before cone/test contact. |
| `eight_layer_pairing_embed` | `lean/YMGap/Continuum/BF4ExactSlabEightLayerCone.lean:289` | Both inputs pinned to original supported polynomials. |
| `cycles_succ` | `lean/YMGap/Continuum/BF4ExactSlabEightLayerCone.lean:302` | The cycle enumeration really iterates the full physical sweep. |
| `cycles_localized` | `lean/YMGap/Continuum/BF4ExactSlabEightLayerCone.lean:311` | n complete sweeps require at most 8*n star expansions. |
| `cycles_pairing` | `lean/YMGap/Continuum/BF4ExactSlabEightLayerCone.lean:320` | Exact separated pairing under n complete sweeps. |

Every operator acts on the same `fullData hw0 hw1 K extent hK` as the
preceding sweep-loss theorem. The full original action and its unnormalized
weighted pairing are retained, for 0<w<1 and K>=headCutoff(w). These are
conditional L2 updates, not OS time translations.

## Why the completed support claim is honest

`Localized` asserts actual operator equalities. No converse from operational
support to a literal polynomial representative is claimed. The dense input
pin uses the existing `conditionalProjection_fix_local` in
`lean/YMGap/Continuum/BF4ExactSlabStarIndependentProbe.lean:138`.

The cone proof needs no such converse: all distant operators are deleted by
proved commutation and fixation equalities on the original completion.
Self-adjointness transfers the remaining operators to a separated test,
which they also fix. The output and pairings are therefore exact.

`expand` deduplicates the union of stars at each step. No exponentially
duplicated path list is retained. The theorem counts graph-neighborhood
expansions; it does not yet give a coordinate-distance or physical-length
bound. Empty supports and empty layers are allowed by the same proofs.

## Open analytic consumer and next work

The spatial obstruction of an arbitrary ordered sweep is removed for THIS
constructed eight-layer schedule. This does not provide a positive rate.
The next substantive estimate is contraction of this same sweep on the
correct interacting centered sector, with useful volume/coupling dependence
on a justified scaling family. An all-bare-coupling uniform constant is not
silently required or claimed.

Still missing are the bounded-degree final-residual energy estimate, its
useful original-action lower bound, and the identification placing centered
covariance vectors in the common-fixed-space orthogonal complement. The
normalized covariance pin must retain the actual partition; the present
pairing theorem is unnormalized. No assumption that all common fixed vectors
are constants has been inserted.

For a quantitative distance conversion, source review located
`edge_base_comp` and `natDist_triangle` in
`lean/YMGap/Continuum/SepLatticeZ4Linf.lean:104` and `:116`. They control
coordinates of links on a face and scalar coordinate distance. No direct
link-star-iteration to response-distance declaration was found in the
inspected `WardStarGeometry`, `StarConditionalLocality`, `SepLatticeZ4Linf`,
`CoreDistanceFloor` and `ResponseDistanceActivity` modules. The rooted response
uses plaquette rather than link distances. This is a remaining geometric
adapter, not the missing analytic lower bound.

No new canonical frontier field, assumed analytic interface or surrogate
closure is introduced. Physical spacing, nontrivial continuum survival,
mass calibration, full QFT axioms and every-group Clay closure remain open.

## Verification

Three focused monitored modules passed with one worker and a 20 GiB cap:
3 generic commuting-sweep gates, 5 coloring gates, and 18 physical cone/pairing
gates. All dependencies are within {propext, Quot.sound}. The final physical
check took 1.82 seconds and had no warnings or errors. No full-tree build or
axiom audit was run.

An initial check exposed a classical equality decision on the opaque physical
link subtype. Splitting on the explicit underlying lattice-link equality and
then using `Subtype.ext` removed that dependency without altering the theorem.
Other initial errors concerned finite-list simplification, a relation's type
annotation and recursive-parameter syntax. No `sorry`, new axiom, or classical
proof remains.

Sol implemented the finite coloring and independently reviewed the completed
cone, schedule coverage, separation, and iterated-pairing proofs. A separate
source task mapped the distance conversion while the physical check ran.
No math-ph listing refresh or chart-marker change was made.
