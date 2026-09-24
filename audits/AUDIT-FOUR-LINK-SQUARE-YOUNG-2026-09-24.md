# Four-link square heat image and explicit original Young cost

2026-09-24 UTC. Follows `f09b1b7`. The constructive continuum Yang--Mills
and Clay target remain OPEN. This increment closes the previously identified
finite four-link join and connects it to the original terminal-plaquette
energy; it does not close the interacting-variance comparison.

## Checked mathematical increment

For four distinct selected links, their original ordered plaquette character
f=chi_1(word), rational nome w and K>=2, the actual finite product heat obeys

    P(chi_2(word)) = w^32 * chi_2(word),
    P(f^2) = 1 + w^32 * chi_2(word).

These are `SupportedHaarEqv` statements: equality after pairing with EVERY
supported polynomial on the original carrier. They are not free coefficient
identities. The factor w^32 is the product of four checked w^8 transmissions;
label two is doubled spin, not physical spin two. Literal cyclic rotations
preserve word order up to trace cyclicity, rather than assuming commuting
quaternion factors. All other heat factors and the supported test remain.

The original spatial face now has both full-range images: P(f)=w^12*f and
P(f^2)=1+w^32*chi_2. A constructive witness selects its four distinct edge
indices from the full base-link range and pins the scalar word to the actual
plaquette. This uses no activity or interacting-transfer eigenstate premise.

Testing the images with q^2 and q^2*f gives the exact one-ended cost

    J = (1-w^32)*H[q^2] + (1+w^32-2*w^12)*H[q^2*f^2].

The first moment is written with an explicit multiplication by polyOne in
the collected Lean statement. The coefficient 1+w^32-2*w^12 is not claimed
nonnegative. The original-action consumer keeps

    4*E_original + D = 2*J,
    q = P_fringe(V*g_n),

where P_fringe is Haar projection, not fringe heat. It substitutes the actual
terminal message g_n and original spatial plaquette. Strict padding supplies
the required observable/fringe independence; source independence is NOT
assumed. Its checked right side is the equivalent three-channel moment form
`plaquetteChannelCost`. The favorable squared-source-increment correction D
is retained. Its existing positivity theorem requires the separate explicit
positive-heat cutoff guard; K>=2 alone is used for the exact image identities.

## Declaration map

All paths below are under `lean/YMGap/Continuum/`.

| Module:line | Declaration | Result |
| --- | --- | --- |
| `SU2QuaternionSpinTwoPlaquettePropagation.lean:125` | `fiveSlotSteps` | Computed physical five-slot chart. |
| `SU2QuaternionSpinTwoPlaquettePropagation.lean:253` | `spinTwoPlaquette_heat_pairing` | Actual arbitrary-link transmission with computed reverse-chart output. |
| `SU2QuaternionSpinTwoPlaquetteLiteral.lean:57` | `lift_word_character` | Character lift in common-padding coefficient equivalence. |
| `SU2QuaternionSpinTwoPlaquetteLiteral.lean:143` | `spinTwoPlaquette_literal_heat_pairing` | Literal retained-word output, factor w^8. |
| `SU2QuaternionProductHeatSpinTwoPlaquette.lean:195` | `productMap_spinTwoPlaquette_of_perm` | Full four-link w^32 image under supported Haar tests. |
| `SU2QuaternionProductHeatPlaquetteSquare.lean:49` | `productMap_plaquetteSquare_of_perm` | Actual square image. |
| `SU2QuaternionPlaquetteYoungCost.lean:95` | `singleEndedCost_plaquette_collected` | Exact two-moment J, arbitrary supported source. |
| `SU2QuaternionPlaquetteYoungCost.lean:201` | `four_mul_sourceEnergy_add_increment_eq_plaquette_collected` | Collected source-Young identity, D retained. |
| `BF4ExactSlabFixedSpatialPlaquetteSquare.lean:139` | `plaquette_fullRange` | Fundamental image on the original spatial face. |
| `BF4ExactSlabFixedSpatialPlaquetteSquare.lean:165` | `plaquetteSquare_fullRange` | Square image on the SAME original face. |
| `BF4ExactSlabFixedSpatialSourceYoungExplicit.lean:61` | `plaquette_singleEndedCost` | Actual face consumes both images. |
| `BF4ExactSlabFixedSpatialSourceYoungExplicit.lean:115` | `padded_terminal_plaquette_young_channels` | Original terminal energy and source, geometric independence constructed. |

## Remaining causal frontier

Raw H[q^2] and H[q^2*f^2] are not the SAME interacting centered variance.
The original projected marginal uses q*P(q), not q^2. Neither the new images
nor dropping D supplies the comparison. The next producer must control the
complete signed energy relative to that variance for ONE justified
changing-scale observable family, or directly prove the corresponding
sampled response. No such analytic comparison is introduced as an input here.

This is distinct from the EVERY-vector spatial/spacing gap task. SAME
continuum/OS/full QFT/Yang--Mills/UV identification, physical Hamiltonian and
finite positive mass, and construction for every compact simple group remain
open. The auxiliary product heat is not identified with the interacting
transfer or the physical Hamiltonian.

## Verification boundary

Seven final narrow checks passed 24 printed gates, all within
{propext, Quot.sound}. Accepted logs contain no error, warning, sorryAx,
Classical.choice or compiler-evaluation axiom.

| Target | Accepted log under `/tmp/` | Gates |
| --- | --- | --- |
| `SU2QuaternionSpinTwoPlaquettePropagation` | `ym-gap-spin-two-plaquette-propagation-check-2.log` | 7 |
| `SU2QuaternionSpinTwoPlaquetteLiteral` | `ym-gap-spin-two-plaquette-literal-check-1.log` | 4 |
| `SU2QuaternionProductHeatSpinTwoPlaquette` | `ym-gap-product-heat-spin-two-plaquette-check-5.log` | 2 |
| `SU2QuaternionProductHeatPlaquetteSquare` | `ym-gap-product-heat-plaquette-square-check-2.log` | 2 |
| `SU2QuaternionPlaquetteYoungCost` | `ym-gap-plaquette-young-cost-check-2.log` | 4 |
| `BF4ExactSlabFixedSpatialPlaquetteSquare` | `ym-gap-bf4-plaquette-square-check-1.log` | 2 |
| `BF4ExactSlabFixedSpatialSourceYoungExplicit` | `ym-gap-bf4-source-young-explicit-check-1.log` | 3 |

Checks were serialized through the monitored launcher with a 2 GiB worker
ceiling and unchanged OS reserve. No safety interruption. Namespace,
dependent-carrier, associativity and coefficient/scalar representation errors
were repaired; failing drafts are not evidence. A temporarily raised
elaboration-step budget was removed after the missing associativity step was
made explicit. The final leaves use the default elaboration budget.

No new source hole, axiom, analytic premise or canonical-field change.
Semantic imports are added; no full-root build, audit, guard or progress-metric
script was run. Parallel source review confirmed the supported-Haar and
source/marginal boundaries; root performed all Lean checks serially.
