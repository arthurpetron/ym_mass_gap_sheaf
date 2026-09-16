# Original multi-time spatial probes and the same window limit

Date: 2026-09-16. Classification: PROGRESS after `68b9ba6`.

Whole-project goal: construct nontrivial continuum Yang--Mills on R^4 with
the required QFT axioms and a positive physical Hamiltonian gap for every
compact simple group, on the SAME theory, within the constructive axiom gate.
This increment identifies scheduled spatial probes for the fixed-nome/width/
cutoff SU(2) selected chain with the existing constructive window family.

## Literal geometry and original observables

Let N be the spatial source carrier size. A supported polynomial P on L+1
slices is shifted by m*N and embedded in the full m+L+n-transition chain.
The resulting literal polynomial equals P embedded as an L-transition window
at start+m. The block proof decomposes any window index into slice quotient
and intra-slice remainder and applies the existing middle_block twice. An
empty carrier cannot satisfy the supplied block bound, so there is no hidden
nonzero-carrier premise. All fringe blocks and their existing order remain.

BlockEmbedding.haar, the existing chain_pin and window_pairing then identify
the complete swept ambient numerator with ell(observedMessage(m,L,P)*u_n).
Every action factor and the final spatial V are retained.

For original gauge observables, the new schedule has type
List (Nat × List FaceFactor): each entry gives a time offset and an ordered
list of signed spatial face characters. Its source polynomial is the product
of lifted sourceProbe polynomials. Its original probe list is the literal
flattening of the lists placed at start+offset. No sorting, coefficient
change, repeated-factor removal or spin change occurs. Offset<=L proves
window support; actual source-face membership proves physical spatial
placement. The existing single-slice probe pin composes over this schedule
to a coefficient-sensitive whole-window pin.

Only this scheduled spatial-probe family is identified. Arbitrary supported
link-coordinate polynomials are not thereby original gauge observables, and
completeness of the gauge-observable realization is not proved.

## Same action and same normalization

The original_chain_pairing sweep applies to the produced physical spatial
probe list and the original selected action at the SAME retained cutoff.
Combining it with the complete window embedding gives the exact numerator.
The positive denominator is ell(u_(m+L)*u_n). terminalPair_total identifies
this with the compact partition for exactly m+L+n transitions; the existing
compactPartition_reciprocal pin identifies the ORIGINAL reciprocalTerm.
Both reciprocals therefore cancel the same z>0. The existing constructive
mul_left_cancel_of_pos proves they agree, without a new reciprocal choice
or a uniform lower bound on growing partitions.

The resulting theorem equates windowRatio with the original finiteValue
on chainIds extent width start (m+(L+n)). The chain has m+L+n transitions
and m+L+n+1 spatial weights, including final V exactly once.

## Original stream and returned limit

originalWindowScalar chooses the admissible ambient extent
width+(m+(L+n)), starts the selected chain at zero and places scheduled
probes at m+offset. Thus independently growing m,n recedes both boundaries
around one fixed relative schedule. The extra ambient links are encoding
coordinates; only the selected fixed-width chain carries action factors.
This is neither the full growing-box action nor its interacting marginal.

The exact scalar pin transfers the existing Type-level QCauchy witness with
the same windowTimeModulus. The original diagonal converges to the EXISTING
polynomialWindowLimit of windowProbe, not a separately chosen limit. The
rectangular theorem compares arbitrary m,n to its actual representative k
under s+1<=m,n,k with error

    q^s * (2*polynomialCap(windowProbe)*(kappa+1)).

The time modulus is independent of the late cutoff stage. Each convergence
statement fixes that stage; no comparison across cutoffs or cutoff removal
is asserted. Nome and spatial width still enter q and kappa.

## Declaration evidence

All paths in this table have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Content |
|---|---|---|
| `window_block`, `window_polynomial_pin` | `BF4ExactSlabFixedSpatialWindowEmbedding.lean:63`, `:100` | Literal full-window block and polynomial placement. |
| `swept_window_pairing` | `BF4ExactSlabFixedSpatialWindowEmbedding.lean:117` | Actual swept ambient numerator equals the complete window pairing. |
| `windowProbe`, `placeWindowProbes` | `BF4ExactSlabFixedSpatialWindowProbe.lean:49`, `:53` | Computed source polynomial and literal original signed schedule. |
| `windowProbe_supported` | `BF4ExactSlabFixedSpatialWindowProbe.lean:62` | Support from finite offset guards. |
| `placeWindowProbes_physical`, `placeWindowProbes_spatial` | `BF4ExactSlabFixedSpatialWindowProbe.lean:78`, `:90` | Original physical faces and spatial direction guards. |
| `windowProbe_pin` | `BF4ExactSlabFixedSpatialWindowProbe.lean:120` | Coefficient-sensitive original multi-time probe pin. |
| `original_window_pairing` | `BF4ExactSlabFixedSpatialOriginalWindow.lean:75` | Same original selected action and complete signed numerator. |
| `windowRatio_originalFiniteValue` | `BF4ExactSlabFixedSpatialOriginalWindow.lean:105` | Both normalizations have the identical positive partition. |
| `originalWindowScalar`, `originalWindowScalar_pin` | `BF4ExactSlabFixedSpatialOriginalWindow.lean:142`, `:149` | Actual growing-ambient original stream and exact window value. |
| `originalWindowCauchy`, `originalWindowCauchy_modulus` | `BF4ExactSlabFixedSpatialOriginalWindow.lean:164`, `:182` | Type-level Cauchy witness and explicit stored modulus. |
| `originalWindow_converges`, `originalWindow_approx_rectangular` | `BF4ExactSlabFixedSpatialOriginalWindow.lean:192`, `:209` | Same returned window limit and independent-boundary representative bound. |

## Next causal frontier: reflected positivity of this selected action

This section records a reviewed finite proof route, NOT a checked result.
Let c=radius+1, E=adjacentEvenExtent radius=2*c and start+depth=c.
Use exactly chainIds E width start (2*depth), with width<=E. Partition this
list into lower, fixed and upper face IDs at the site-reflection plane.
The central factor consists of spatial faces at c, once. Spatial reflection
sends base time t to E-t; temporal reflection sends it to E-(t+1). The
selected lower/upper ranges therefore have a candidate reflection bijection.

The actual missing lemmas are the selected-list reflection permutation,
the exact selected action split, lower one-sidedness, fixed-slice locality
and action dressing. Existing ingredients include `chainIds_mem_iff` and
`chainIds_nodup` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChainGeometry.lean:35` and `:91`,
and `faceHeat_reflection` in
`lean/YMGap/Continuum/BF4ExactSlabPolynomialReflectionInvariance.lean:66`.
The full-slab templates `lowerHeat_oneSided`, `fixedHeat_local` and
`fullAction_dressing` in `lean/YMGap/Continuum/BF4ExactSlabSiteHeatAction.lean:90`,
`:101` and `:155` do not automatically apply to the selected mask.

After proving those identities, the intended consumers are
`certified_weighted_nonnegative` in
`lean/YMGap/Continuum/BF4ExactSlabSiteWeightedSquare.lean:165` and the actual
central heat-product certificate `headProduct_certificate` in
`lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:101`.
This would dress a supported one-sided p by the lower action factor, without
requiring positivity of p. No substitution of the full-slab action is allowed.
The reflected spatial-probe schedule and time-limit pin would still need
proof before using finite positivity as a property of this window family.

The physical OS quotient/transfer/vacuum, same-operator connected correlations,
cutoff-limit power/moment compatibility, interior cutoff removal, spatial-width/
spacing-uniform estimates, continuum QFT and the all-group Clay target remain
open. No canonical field, old theorem or analytic premise changed.

## Verification boundary

Three focused serialized one-worker/20 GiB checks passed all 17 public gates
within {propext, Quot.sound}; placeWindowProbes is axiom-free. Initial checks
found two missing namespace opens and a dependent embedding-index rewrite.
The latter was repaired by exposing only polynomial/image indexing, preserving
the existing geometric identity. Only final axiom-clean outputs are claimed.
No new literal holes, axioms or classical input.

The safe-build skill kept checks narrow and serialized. Fresh process/swap
preflight preceded every check; no competing compiler/test was found and
observed swap remained 7077.19 MiB. No limits were raised. Independent
read-only review checked action count, final V, reciprocal normalization,
physical observable guards and the selected-action/full-box distinction.
Three selective-root imports were added; root/full-tree/full axiom audit
was NOT run. No new routine literature scan occurred.

Each check used `python3 scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check lean/YMGap/Continuum/<Module>.lean
--check-output lean/.lake/build/lib/lean/YMGap/Continuum/<Module>.olean
--log-file /tmp/<Module>.log`.

| Module / log basename | Gates | Final log SHA-256 |
|---|---:|---|
| BF4ExactSlabFixedSpatialWindowEmbedding | 3 | `c066862fca7d3c22d55ae13c5417f2032ab987d6709af298600c65a39891dc74` |
| BF4ExactSlabFixedSpatialWindowProbe | 6 | `0340162e67d6aa7b03437c77861a5063225a7ce08a2a0d20c4594c16077a18a4` |
| BF4ExactSlabFixedSpatialOriginalWindow | 8 | `8b78ed5d72a39314b978758066149df18eb8d4cc744436c86641de832280c50a` |
