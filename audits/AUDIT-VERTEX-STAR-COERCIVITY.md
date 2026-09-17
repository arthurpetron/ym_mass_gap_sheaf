# Original vertex-star coercivity: proof scope and direction audit

Date: 2026-09-17 UTC. Parent checkpoint: `6746672`.

## Whole-project goal and decision

For every compact simple gauge group, construct a nontrivial continuum
Yang--Mills QFT on R^4 with the required QFT axioms and a positive physical
Hamiltonian mass gap, constructively in Lean within the repository's axiom
gate. The continuum, observable, reconstruction and Hamiltonian data must
belong to the same theory. This goal is unchanged and OPEN.

The current increment proves an original finite SU(2) vertex-odd sector
estimate. Its constants do not grow with volume or terminal depth. It does
not prove a physical-sector gap. The next priority is the signed interacting
estimate on the retained center-even plaquette sector, not an all-charge
compiler or another inverse wrapper.

## Actual objects and bound

Write `g_n = terminalMessage w K width n = T^n 1`, with the original
`T = transferStep = K V`. The unnormalized marginal is `nu=V*g_n*g_(n+1)`.
For a supported polynomial f odd under one full spatial vertex star,

```
H[nu*f] = 0,
headFloor(w)^6 * H[nu*f^2] <= prefixCap(w)^6 * energy(w,K,width,g_n,f).
```

Both statements use the original terminal messages, spatial action and
energy. See `terminal_starOdd_mean_zero`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialVertexStarEnergy.lean:156`,
and `terminal_starOdd_six_energy_floor`, same file `:234`.

The energy is the original marginal quadratic form minus its mixed
`transferStep` pairing (`energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:63`). It is
not the generator of a link-update/heat-bath dynamics. No completed-sector
spectral theorem or physical Hamiltonian calibration is claimed here.

## Checked causal chain

| Required fact | Declaration and source | Role |
|---|---|---|
| Full star, including fringe | `incident`, `blockSelector`, `starSign`; `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialVertexStar.lean:54`, `:60`, `:66` | Select all four components of every incident original retained link. |
| Original spatial action invariant | `plaquette_invariant`, `character_starSign`, `spatialWeight_starSign`; same file `:232`, `:313`, `:347` | Preserve the ordered noncommutative word, every spin and every spatial heat factor. |
| At most six affected kinetic factors | `activeStar_length_le_six`; same file `:380` | No factor proportional to spatial volume. |
| Actual partial Haar commutes with signs | `partialHaarHeads_sign`; `lean/YMGap/Continuum/SU2QuaternionProductHeatCenterSign.lean:224` | Raw coefficient equality, not merely tested-Haar equality. |
| Actual product map equivariant | `productMap_centerSign`; same file `:394` | Same selector on matching lower and upper links. |
| Original terminal symmetry produced | `transferStep_starSign`, `terminalMessage_starSign`, `endpointWeight_starSign`; `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialVertexStarTransfer.lean:49`, `:72`, `:83` | No assumed stationary law or replacement terminal sequence. |
| Erased factors alone pay floor/cap | `selected_floor`, `selected_cap`; `lean/YMGap/Continuum/SU2QuaternionWeightedProductBlockErasure.lean:74`, `:105` | Preserve the other heat factors and both complete endpoint weights. |
| Odd retained mixed term actually vanishes | `erased_cross_zero`; `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialVertexStarEnergy.lean:110` | Lower-only full star fixes the retained background and negates f. |
| Original factor list restored | `star_partition`; same file `:68` | Literal permutation of active-star and complement lists, with no omitted factors. |
| Correct original norm/energy normalization | `edge_diagonal_identity`, `energy_identity`; `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:181`, `:253` | Both carry the same factor two; cancel it only after the original equalities. |
| Common six-factor estimate | `terminal_starOdd_energy_floor`, `terminal_starOdd_six_energy_floor`; `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialVertexStarEnergy.lean:179`, `:234` | First exponent m=star size, then m<=6 with h<=1<=U. |

The geometric count embeds the nodup active star into a six-entry candidate
list. That target list is allowed to repeat or contain nonphysical boundary
candidates. Incoming-edge reconstruction uses `subE_addE` after an actual
endpoint equality, not its invalid converse at a Nat boundary. The source
review found no boundary omission or commutativity substitution.

## Parameter and group scope

- SU(2) quaternion carrier only. The finite proof uses the central sign
  action. It does not establish a result for every compact simple group.
- `0 < w < 1` and `headCutoff(w) <= K` are explicit hypotheses.
- `headFloor(w)` is positive and explicitly nome-dependent
  (`headFloor`, `headFloor_positive`,
  `lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:50`, `:52`).
- `prefixCap(w)` is explicitly nome-dependent (`prefixCap`,
  `lean/YMGap/Continuum/BF4ExactSlabAllNomeTailInterval.lean:117`). Its lower
  bound by one is `prefixCap_ge_one`,
  `lean/YMGap/Continuum/BF4ExactSlabStarRateObstruction.lean:32`.
- The six-factor theorem quantifies width, vertex, depth and admissible K.
  Its constants are independent of those parameters at fixed w. It claims
  no coupling-independent or spacing-independent positive physical rate.
- The finite block-erasure machinery admits empty and repeated lists. The
  physical star application supplies the actual partition of the original
  active list, not arbitrary duplicated factors.

## Consumer and stopping boundary

The existing `centered_extracted_energy_split`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFringeExtraction.lean:139`,
accepts arbitrary supported polynomials. Its active part is supported,
fringe-independent and marginally centered, not assumed gauge-invariant.
This is the stronger auxiliary route in which a parity decomposition can
isolate a controlled charged part. `evenPart`, `oddPart` and `decomposition`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialVertexStarParity.lean:50`, `:53`,
`:81`, construct these pieces. `parts_orthogonal` (`:135`) and
`marginal_norm_split` (`:152`) give exact original-marginal Pythagoras.
`oddPart_six_energy_floor` (`:179`) bounds the constructed odd part using
ITS OWN energy. No energy split or inequality E(oddPart f)<=E(f) is supplied;
norm splitting alone does not finish a coercivity reduction for general f.

The original physical `sourceProbe`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProbe.lean:52`, uses closed
plaquette characters. For spatial faces their center-even symmetry is
`character_starSign` above. A center-odd estimate does not bound that
center-even sector; nor does center-evenness alone imply gauge invariance.

The precise remaining signed-energy consumer is
`clearedDefect_diagonal_nonnegative_iff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:175`.
The existing `terminal_existing_fraction_nonnegative`, same file `:187`,
supplies only its width-dependent fraction. No improved physical fraction
is supplied by this increment. The revised work plan returns to this
estimate and keeps the original active-energy rejoin, physical scale,
same-theory QFT and all-group obligations open.

## Verification boundary

Focused, serialized checks use `scripts/safe_lean_build.py`, one worker and
the unchanged 20 GiB worker ceiling, after fresh process/swap preflights.
The six modules above pass their 65 displayed axiom gates, all within
`{propext, Quot.sound}` (two are axiom-free). Final logs contain no errors,
warnings or `sorryAx`. Independent source reviews cover block comparison,
star geometry, original-energy normalization and the restricted consumer.

No `sorry` was introduced or discharged; no analytic premise, canonical
frontier field, resource option or CI setting changed. No full-root build,
full audit, guard or progress script was run. The root import listing is
integration wiring, not a claim that the root itself was rebuilt.

Final logs (SHA-256):

- `/tmp/ym-weighted-product-block-erasure-20260917.log`:
  `5a5652951509764c19a934519d5e8b50784246094e987b7c3053339b7c98a8b3`
- `/tmp/ym-fixed-spatial-vertex-star-20260917.log`:
  `fe290c00b4d6dfe162e2934dcf5477f3ac30236cbd94015ae1639ea0c367eda8`
- `/tmp/ym-product-heat-center-sign-20260917.log`:
  `341db4b9e9883f2be91bfa12a6b8309df14ce72566bc4e664df512c15af60841`
- `/tmp/ym-fixed-spatial-vertex-star-transfer-20260917.log`:
  `86cedee2d283f930f2ba191979a5e2bf9a9e545a4bccc4f72a1253eb911c6887`
- `/tmp/ym-fixed-spatial-vertex-star-energy-20260917.log`:
  `cee4378efe20f33aee341eac7f7ae35c5993b2b5ef4598a5e9319c94747efd46`
- `/tmp/ym-fixed-spatial-vertex-star-parity-20260917.log`:
  `11e9d48e4799a14d7468b4e50367e2dbbdd52c76f135f409ac3f0384dec354fd`
