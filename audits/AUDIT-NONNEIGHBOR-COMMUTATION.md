# Original non-neighbor conditional commutation

Date: 2026-09-15 (America/Los_Angeles). Base: `d52199a`.

PROGRESS: exact commutation on the existing original full-action completion,
not a spatial-decay estimate, OS transfer identification or mass gap.
No canonical frontier atom is closed. The whole-project goal remains a
constructive continuum Yang--Mills theory with the required QFT axioms and
positive physical Hamiltonian gap for every compact simple group.

## 1. Exact statement

For rational 0<w<1, finite extent, K>=headCutoff(w), and physical links i,j,
assume no original physical plaquette contains both links. Let C_i,C_j be
the existing `conditionalProjection` operators. Then on their entire COMMON
original full-action weighted completion:

    C_i C_j = C_j C_i,
    (C_i C_j)* = C_i C_j,
    (C_i C_j)^2 = C_i C_j,
    Fix(C_i C_j) = Fix(C_i) intersection Fix(C_j).

These are the operators from
`BF4ExactSlabStarConditionalProjection.conditionalProjection`,
`lean/YMGap/Continuum/BF4ExactSlabStarConditionalProjection.lean:220`, on
`BF4ExactSlabStarFullActionProbe.fullData`,
`lean/YMGap/Continuum/BF4ExactSlabStarFullActionProbe.lean:49`.
The latter uses the literal product over ALL physical face weights.
No product-reference operator or deleted-action update is substituted.

## 2. Causal proof map

| Declaration | Source | Mathematical role |
|---|---|---|
| `BF4ExactSlabStarIndependentProbe.independentExterior` | `lean/YMGap/Continuum/BF4ExactSlabStarIndependentProbe.lean:110` | Compute the exterior polynomial by reindexing and dropping the independent quaternion block. |
| `BF4ExactSlabStarIndependentProbe.independent_pair` | `lean/YMGap/Continuum/BF4ExactSlabStarIndependentProbe.lean:115` | Exact pairings retain the test polynomial times the COMPLETE original weight. |
| `BF4ExactSlabStarIndependentProbe.independent_embed` | `lean/YMGap/Continuum/BF4ExactSlabStarIndependentProbe.lean:128` | Realize the original input in the same completion, without false equality of padded coefficient lists. |
| `BF4ExactSlabStarIndependentProbe.conditionalProjection_fix_local` | `lean/YMGap/Continuum/BF4ExactSlabStarIndependentProbe.lean:138` | An update fixes a polynomial that omits its link. |
| `BF4ExactSlabStarIndependentProbe.probeMap_local` | `lean/YMGap/Continuum/BF4ExactSlabStarIndependentProbe.lean:149` | Every exterior probe omits that link. |
| `GNSDenseFixedPoint.fixed_of_cauchy_terms` | `lean/YMGap/Continuum/GNSDenseFixedPoint.lean:79` | Pass fixedness through the supplied original Cauchy sequence. |
| `GNSDenseFixedPoint.fixed_of_cauchy_images` | `lean/YMGap/Continuum/GNSDenseFixedPoint.lean:46` | Pass fixedness of operator images through that same sequence. |
| `GNSDenseFixedPoint.invariant_range_of_dense` | `lean/YMGap/Continuum/GNSDenseFixedPoint.lean:90` | Extend dense invariant range by self-adjointness and dense pairing tests. |
| `BF4ExactSlabStarNonneighborCommutation.nonneighbor_iff` | `lean/YMGap/Continuum/BF4ExactSlabStarNonneighborCommutation.lean:53` | Identify the exact no-common-physical-plaquette hypothesis. |
| `BF4ExactSlabStarNonneighborCommutation.conditionalProjection_preserves_omitted` | `lean/YMGap/Continuum/BF4ExactSlabStarNonneighborCommutation.lean:78` | Actual localized approximants cannot introduce the omitted non-neighbor link. |
| `BF4ExactSlabStarNonneighborCommutation.conditionalProjection_invariant_dense` | `lean/YMGap/Continuum/BF4ExactSlabStarNonneighborCommutation.lean:100` | Dense original outputs satisfy C_j C_i C_j = C_i C_j. |
| `BF4ExactSlabStarNonneighborCommutation.conditionalProjection_invariant` | `lean/YMGap/Continuum/BF4ExactSlabStarNonneighborCommutation.lean:121` | The invariant-range identity holds on every original completed vector. |
| `GNSProjectionCommutation.commute_of_invariant` | `lean/YMGap/Continuum/GNSProjectionCommutation.lean:21` | Transpose C_j C_i C_j = C_i C_j to obtain commutation. |
| `BF4ExactSlabStarNonneighborCommutation.conditionalProjection_commute` | `lean/YMGap/Continuum/BF4ExactSlabStarNonneighborCommutation.lean:131` | The original operator commutation theorem. |
| `BF4ExactSlabStarNonneighborCommutation.twoLink_update_selfAdjoint` | `lean/YMGap/Continuum/BF4ExactSlabStarNonneighborCommutation.lean:140` | Joint-update symmetry. |
| `BF4ExactSlabStarNonneighborCommutation.twoLink_update_idempotent` | `lean/YMGap/Continuum/BF4ExactSlabStarNonneighborCommutation.lean:147` | Joint-update idempotence. |
| `BF4ExactSlabStarNonneighborCommutation.twoLink_update_fixed_iff` | `lean/YMGap/Continuum/BF4ExactSlabStarNonneighborCommutation.lean:155` | Exact intersection of fixed spaces. |

The localized representatives are the existing
`BF4ExactSlabStarConditionalLocality.conditionalProjection_localRepresentative`,
`lean/YMGap/Continuum/BF4ExactSlabStarConditionalLocality.lean:141`.
No new completion, chosen quotient representative, inverse or modulus is
introduced by the generic passage lemmas. The three parallel helper tasks
have the concrete original-operator commutation theorem as their consumer.

## 3. What remains mathematically open

Zero non-neighbor commutators are NOT zero distant correlations. The result
locates where noncommutation can occur; it gives no small estimate there.
No spatial-decay theorem consuming this result is supplied in this increment.
The existing directional estimate
`BF4ExactSlabStarLocalInfluence.conditionalProjection_freeCentered_norm`,
`lean/YMGap/Continuum/BF4ExactSlabStarLocalInfluence.lean:123`, applies to
free-link centering in the deleted law, not to arbitrary centered inputs.
`BF4ExactSlabStarRateObstruction.inverseRate_ge_sixtyThreeSixtyFour`,
`lean/YMGap/Continuum/BF4ExactSlabStarRateObstruction.lean:56`, proves the
current coarse squared rate is at least 63/64. It is not a small cross-link
coefficient.

The separate response route still requires the supplied spatial bound in
`BF4ExactSlabConnectedFaceResponse.covariance_response_bound_eventually`,
`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:224`.
The retained interacting head cannot be treated as an independent baseline:
`BF4ExactSlabRetainedHeadCorrelation.connectedHead_eq`,
`lean/YMGap/Continuum/BF4ExactSlabRetainedHeadCorrelation.lean:62`, evaluates
its named original tube numerator as w^36. Neither observation was re-proved
here; these are source-reviewed boundaries on the next estimate.

The new theorem has no beta-uniform positive gap constant, no cutoff-removed
operator instance, no thermodynamic comparison, and no physical-time/spacing
calibration. Its operators are ordinary conditional projections, not the OS
transfer matrix or a physical Hamiltonian. Continuum QFT, nontriviality and
the all-compact-simple-group target remain open.

## 4. Verification

Five successful focused serialized checks: one per helper module and two
for the original commutation module (the second includes the joint-update
corollaries). Each used `scripts/safe_lean_build.py`, one worker and the
mandatory 20 GiB ceiling. All nineteen public gates report only subsets of
{propext, Quot.sound}; independentLinks is axiom-free. No limits raised,
dependency rebuild, new custom axiom or literal hole. Existing statements
and canonical frontier fields are unchanged. Four root imports were added;
root/full-tree compilation and a full axiom audit were NOT run.

Final local log SHA-256 values:

- `/tmp/ym-projection-commutation.log`:
  `bbe2e81f26d149f5a2f0905a9c5fc339b35a68e6b676f2a8489d2138079f6690`.
- `/tmp/ym-dense-fixed-point.log`:
  `c39e497e6d3f96d94de82956488b205b0d4942a6a521adc602c2679047350bb9`.
- `/tmp/ym-star-independent-probe.log`:
  `bab1067de4a9d61d07fe1f73b013689b2c91e892ecd2402842212db7dd988ac2`.
- `/tmp/ym-star-nonneighbor-commutation.log`:
  `70bb80882fb08569c157085fa5fdec1a4a34bbab5618dbbea419dd8bdee5411e`.

CI remains manual-only. The goal remains active.
