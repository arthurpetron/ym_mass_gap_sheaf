# Original chart plaquette means: spatial comparison without time-buffer loss

Date: 2026-09-16. PROGRESS after `6ea3deb`.

WHOLE-PROJECT GOAL: construct nontrivial continuum quantum Yang--Mills on
R^4 with the required QFT axioms and a positive physical Hamiltonian gap
for EVERY compact simple group, constructively and on the SAME theory.
That goal remains open.

## Mathematical result

For a base spatial face p, representation label spin and padding r, put
W_r=base+2*r+2. Use the original chart extent adjacentEvenExtent(W_r+t),
the original chainIds at width W_r, start W_r+1 and length 2*t, and the
literal character at shiftFace(r+1,W_r+1+t,p). Write F_r(k,t) for its
original normalized finite expectation at heat cutoff headCutoff(w)+k.

The new theorem proves, for every further padding d and every k,t,

    |F_(r+d)(k,t) - F_r(k,t)| <= A(w,spin) * rho(w)^(r+1).

The identical estimate holds after removing the heat cutoff at fixed t.
The coefficient has no base-width, face-position, cutoff, time-buffer or
outer-padding parameter. Its remaining dependence and hypotheses are:

- 0<w<1;
- heatRatio(w)<=1/2;
- hd: heatRemainderBound(w)<1;
- rho(w)=entropyRate(625,adjustedCoreRate(w,hd))<1;
- c(spin)=2*16^spin;
- A(w,spin)=(c+c)*singlePlaquetteAmplitude(w,hd,hs), where the latter is
  (probePrefactor(w,hd,4)*1250)/(1-rho(w)).

Every coupling guard is supplied in the existing w=1/1024 specialization.
No uniformity over w or lattice spacing is stated. This is a one-plaquette
mean comparison, not decay between two observables and not a mass gap.

## Causal argument and exact objects

1. A computed injective map translates the actual boundary-complete source
   link list, including fringe coordinates. Ordered plaquette multiplication
   and inverse-link orientations are preserved. Supported source polynomials
   retain their original quaternion-Haar integral.
2. Translate exactly the selected heat factors and the insertion. Both
   numerator and partition are pinned, so the original reciprocal is pinned
   too. This identifies the smaller law only with the translated selected
   target law, never with the full larger action.
3. The source-to-target displacement is d spatially and 2*d temporally.
   The two selected time windows coincide, including the last spatial slice
   and strict upper endpoint for temporal faces. Within the target chain,
   membership in the translated selection reduces to the three spatial
   base-coordinate intervals [d,W_r+d).
4. Any omitted target face lies at L-infinity distance at least r+1 from
   the recentered base face, independently of the root time. Omitted
   temporal plaquettes outside that spatial box are included, not discarded.
   A singleton carrier has one face and four links, so every active original
   core pays at least r+1 faces.
5. The actual character interval and locality certificate feed the existing
   signed mixed-numerator bound. This estimates N_outer*Z_inner -
   N_inner*Z_outer with the product Z_outer*Z_inner retained. Both positive
   ORIGINAL partitions cancel before the heat-cutoff limit.
6. The filtered target-chain order is proved to be a permutation of the
   translated smaller list. Exact action transport converts the normalized
   estimate into the displayed comparison of the actual two box measures.

## Declaration evidence

All paths below have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Role |
|---|---|---|
| `Placement.embedding`, `Placement.plaquette_pin`, `Placement.haar` | `BF4ExactSlabTranslatedHaarEmbedding.lean:94`, `:170`, `:190` | Actual computed carrier, ordered word and supported integral. |
| `numerator_pin`, `partition_pin`, `finiteValue_pin`, `expectation_pin_of_prefix` | `BF4ExactSlabTranslatedSelectedAction.lean:103`, `:119`, `:137`, `:170` | Selected-action transport with exact normalization. |
| `TranslatedWindow`, `translatedIds_mem_iff` | `BF4ExactSlabFixedSpatialTranslatedChain.lean:33`, `:139` | Actual spatial bounds and orientation-sensitive temporal endpoints. |
| `placement`, `translatedChartIds_mem_iff`, `omitted_separation` | `BF4ExactSlabFixedSpatialAlignedBoxes.lean:57`, `:101`, `:168` | Same-depth alignment and uniform omitted-face distance. |
| `insideIds_perm`, `finiteValue_pin`, `expectation_pin` | `BF4ExactSlabFixedSpatialAlignedAction.lean:80`, `:110`, `:133` | Exact filtered target law equals original source law. |
| `characterCap`, `characterAmplitude`, `placedCharacter_interval`, `active_core_size_floor` | `BF4ExactSlabFixedSpatialPlaquetteBoundary.lean:61`, `:63`, `:68`, `:82` | Explicit constants, actual insertion certificate and proved size floor. |
| `determinant_bound`, `finiteValue_bound`, `expectation_bound` | `BF4ExactSlabFixedSpatialPlaquetteBoundary.lean:96`, `:124`, `:145` | Signed original determinant, cancellation and fixed-observable cutoff passage. |
| `chartFace_physical`, `chartCharacter_translate` | `BF4ExactSlabFixedSpatialPlaquetteComparison.lean:51`, `:71` | Canonical physical placement and literal character transport. |
| `finiteMean_difference_bound`, `cutoffMean_difference_bound`, `existingNome_cutoffMean_difference_bound` | `BF4ExactSlabFixedSpatialPlaquetteComparison.lean:100`, `:118`, `:136` | Actual cross-width estimate, cutoff limit and fully supplied pilot. |

Existing quantitative producers are `mixedNumerator_tail_bound` in
`BF4ExactSlabUniformCoreBudget.lean:105`, `active_core_linf_floor` in
`BF4ExactSlabCoreDistanceFloor.lean:56`, `singlePlaquetteAmplitude` and
`singlePlaquetteBudget_factor` in `BF4ExactSlabInnerMarginBoundaryDecay.lean:53`
and `:68`, and the exact normalized consumer `finite_comparison_bound` in
`BF4ExactSlabAllNomeFaceSetComparison.lean:51`. The pilot rate is proved in
`BF4ExactSlabSummableCoreRate.lean:37`, `existingNome_entropyRate`.

## Remaining frontier

The new comparison concerns one character, not an arbitrary signed reflected
probe product. The existing local variance floor alone does not supply its
cross-width second moments or a common limiting vector. No spatial limit,
general observable state, or identification of separate completed carriers
has been constructed here.

The next consumer is the actual chartScalar reflected product. Its fixed
support needs actual interval/locality data with no growing ambient-volume
penalty. Spatial comparison must then be composed with the existing
fixed-width joint cutoff/time estimate, `chartJoint_rectangle` in
`BF4ExactSlabFixedSpatialChartJointCauchy.lean:102` and its explicit
`chartJointModulus` at line 70. The possible fixed-spatial-pivot argument
is a reviewed plan, NOT a new theorem: compare two large widths through
one fixed inner width, and use its joint temporal/cutoff modulus there.
This avoids demanding a width-uniform temporal modulus without proving the
needed spatial estimates first.

Unrestricted-nome signed response, width-independent connected decay,
full Hilbert/OS/QFT structure, spacing control, physical time/mass
calibration, continuum nontriviality and the all-group Clay target remain
open. No canonical frontier field or analytic premise was changed, and no
sorry or axiom was added or removed. No literature scan occurred.

## Verification boundary

Seven focused final module checks passed through the safe-build procedure,
serialized at one worker and 20 GiB with a fresh process/swap preflight for
each invocation. All 78 public printed gates use only subsets of
{propext, Quot.sound}. Development errors were hypothesis-name shadowing,
tuple-projection normalization, a missing namespace open and an omitted
section-variable inclusion; final successful logs contain no proof holes.
No worker/memory/safety limits were raised. Independent read-only review
checked the same action, exact partitions, endpoints and uniformities.

No root build, full-tree build or full axiom audit ran. Seven selective-root
imports were added; that root itself was not recompiled.

| Checked module | Gates | Final log SHA-256 |
|---|---:|---|
| `BF4ExactSlabTranslatedHaarEmbedding` | 17 | `089e8a40eb58b5a4261ef3d23669d1e6898f571c6e2b7e706005694407f3efe0` |
| `BF4ExactSlabTranslatedSelectedAction` | 10 | `c4407492cf8698642889e0d05894778378eddb38c071122aa67865aeb9b77679` |
| `BF4ExactSlabFixedSpatialTranslatedChain` | 8 | `05ca8c1a71f7cf7a6e8fd42c8be572d2dead5a8f762e0e8a056f332376374de7` |
| `BF4ExactSlabFixedSpatialAlignedBoxes` | 13 | `7fa0c9015b359aea86f0ff9adffa97c7c1987ab6fc800ad19d75c75ee9f6e5c4` |
| `BF4ExactSlabFixedSpatialAlignedAction` | 11 | `3a6f433c1ccec0fdef56bed6c134f4fa067ef4e3b879c52874adb9b1308b4fe9` |
| `BF4ExactSlabFixedSpatialPlaquetteBoundary` | 9 | `93899e53e15653bad9c763bcdaeac2e16271b87d0722f865956ba4b4ba766275` |
| `BF4ExactSlabFixedSpatialPlaquetteComparison` | 10 | `8195dd3765c4d562116d9a238fa7e02eff883597ff7009ab177c90f8436a3ccc` |

Local logs are `/tmp/ym-translated-haar-20260916.log`,
`/tmp/ym-translated-selected-action-20260916.log`,
`/tmp/ym-translated-chain-20260916.log`, `/tmp/ym-aligned-boxes-20260916.log`,
`/tmp/ym-aligned-action-20260916.log`,
`/tmp/ym-chart-plaquette-boundary-20260916.log` and
`/tmp/ym-chart-plaquette-comparison-20260916.log`.
