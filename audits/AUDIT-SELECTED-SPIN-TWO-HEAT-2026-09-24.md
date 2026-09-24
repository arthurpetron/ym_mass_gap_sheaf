# Actual selected-link label-two heat transmission

2026-09-24 UTC. Follows `2028c8c`. The constructive continuum Yang--Mills
and Clay target remain OPEN. Here label two means the repository's doubled
spin label, with exponent 2*(2+2)=8, not physical spin two.

## Checked mathematical increment

Put the selected lower link in block 0, its retained heat partner in block 1,
and the three remaining ordered plaquette links in blocks 2,3,4. For every
orientation, rational w, cutoff K>=2, ambient carrier of at least five blocks,
and supported insertion r independent of block 0, the actual relative heat
factor now satisfies

    H[heat(0,1) * chi_2(word(0,2,3,4)) * r]
      = w^8 * H[chi_2(word(1,2,3,4)) * r].

The right word is represented by the literal liftHead of the canonical
four-block character. The insertion may depend on the retained partner and
every other in-carrier coordinate; no degree bound on spectators is assumed.
This is an exact finite-Haar identity, not a positivity or spectral estimate.

The proof transports the known harmonic solid through three head-fixing
tail transpositions. Reindexing introduces trailing-zero padding, so the
proof preserves prefix equality rather than falsely asserting equality of
raw coefficient lists. The actual retained substitution is computed
structurally. Finally, the four radii are removed using the existing SAME
Haar-carrier identities, including arbitrary-insertion lift transport.
The ordinary character itself is not asserted coefficientwise harmonic.

## Declaration map

All paths in this table are under `lean/YMGap/Continuum/`.

| Module:line | Declaration | Checked result |
| --- | --- | --- |
| `SU2QuaternionHeadHarmonicReindex.lean:26` | `headLaplacian_reindex` | Literal Laplacian commutes with a head-fixing involution. |
| `SU2QuaternionHeadHarmonicReindex.lean:54` | `harmonic_swapChain` | Harmonicity through the explicit tail chain. |
| `SU2QuaternionRetainedImagePrefix.lean:33` | `prefix_on_supported` | Supported prefix equality extends to arbitrary spectator carriers. |
| `SU2QuaternionRetainedImagePrefix.lean:103` | `retainedImage_prefix` | Actual retained substitution/reinsertion preserves prefix equality. |
| `SU2QuaternionSpinTwoHeatImage.lean:280` | `substituteRetained_selectedSolidTwo` | Computed selected-to-retained solid image. |
| `SU2QuaternionSpinTwoHeatImage.lean:310` | `retainedImage_selectedSolidTwo` | Same-carrier output coefficient pin. |
| `SU2QuaternionSpinTwoHeatTransmission.lean:275` | `selectedChartSolidTwo_harmonic` | Harmonic representative for the selected chart. |
| `SU2QuaternionSpinTwoHeatTransmission.lean:321` | `selectedSolidTwo_heat_pairing` | Actual selected solid heat pairing, arbitrary supported spectators. |
| `SU2QuaternionSpinTwoHeatTransmission.lean:372` | `selectedSolidTwo_eq_character` | Radius elimination in the SAME Haar carrier. |
| `SU2QuaternionSpinTwoHeatTransmission.lean:391` | `selectedCharacterTwo_heat_pairing` | Actual character transmission with factor w^8. |

## Actual consumer and remaining mathematical work

The existing consumer is
`BF4ExactSlabFixedSpatialSourceYoung.projected_young_moment_identity` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceYoung.lean:79`.
Its J uses the actual P(f^2). The new selected-link result does NOT yet give
the full product-map identity `P(f^2)=1+w^32*(f^2-1)`.

The remaining finite join is explicit: transport the five-slot chart to
arbitrary distinct physical indices, compose four selected-link removals,
use the original upper marginal, and combine chi_1^2=1+chi_2 with P(1)=1.
`SU2QuaternionProductHeatPlaquette.productMap_plaquette_of_perm` at
`lean/YMGap/Continuum/SU2QuaternionProductHeatPlaquette.lean:186` supplies
the already checked fundamental counterpart, only in SupportedHaarEqv sense.
Neither character image should be promoted to free coefficient equality.

Even the full square image would only simplify J. The original marginal
uses q*P(q), not raw q^2. Here q is the HAAR projection of V*g over fringe
coordinates (`projectedEndpointSource`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedSourceEnergy.lean:77`),
not fringe heat evolution. Useful signed-energy/SAME-variance control for
ONE justified changing-scale family, EVERY-vector spatial/spacing gap,
SAME continuum/QFT/YM/UV, physical Hamiltonian/mass and every group remain open.

## Parallel mathematical review (not a new Lean theorem)

An exact algebraic diagnostic is available at the unprojected original source.
Write a=V*g_n, T=transferStep, Z=H[a*T(g_n)], B=H[a*T(g_n)*f],
A=H[a*T(g_n)*f^2], F=Z*f-B, lambda=w^12, and
R_f=T(g_n*f)-lambda*f*T(g_n). Weighted symmetry gives

    Z*E(g_n,f) = (1-lambda)*(Z*A-B^2) - H[a*F*R_f].

The source definitions are `energy` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:63`
and `transferStep_weighted_symmetric` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSymmetry.lean:97`.
This prose calculation is NOT a checked new declaration or a sign theorem.
It requires no coefficientwise heat eigenrelation: R_f is defined using
the actual observed/unobserved responses. A useful signed lower bound for
the last pairing is still missing; no new wrapper assuming it was added.

## Verification boundary

Four final narrow checks passed 17 printed gates, all within
{propext, Quot.sound}; accepted logs contain no error, warning, sorryAx,
Classical.choice or compiler-evaluation axiom.

| Target | Accepted log under `/tmp/` | Gates |
| --- | --- | --- |
| `SU2QuaternionHeadHarmonicReindex` | `ym-gap-head-harmonic-reindex-check-2.log` | 3 |
| `SU2QuaternionRetainedImagePrefix` | `ym-gap-retained-image-prefix-check-5.log` | 5 |
| `SU2QuaternionSpinTwoHeatImage` | `ym-gap-spin-two-heat-image-check-7.log` | 4 |
| `SU2QuaternionSpinTwoHeatTransmission` | `ym-gap-spin-two-heat-transmission-check-5.log` | 5 |

Checks were serialized through the monitored launcher with a 2 GiB worker
ceiling. One attempted check was refused before startup at the unchanged
12 GiB reserve; source review continued, telemetry recovered, then the
narrow check resumed. No safety threshold was raised. Earlier proof errors
were repaired and are not counted as evidence. No new source hole, axiom,
analytic premise or canonical-field change. The semantic import is added;
no full-root build, audit, guard or progress-metric script was run.
