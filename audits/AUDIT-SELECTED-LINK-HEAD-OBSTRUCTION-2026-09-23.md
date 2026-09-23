# Selected-link/head-map obstruction

Date: 2026-09-23. Parent revision: `e6a4407`.

Whole-project goal: construct nontrivial continuum Yang--Mills on R^4 for
every compact simple group, with full same-theory QFT structure, isolated
vacuum and finite positive physical mass gap, constructively in Lean.
The goal remains OPEN. This increment refutes a proposed local proof route.

## The two different operators

`selectedHeatProjection`,
`lean/YMGap/Continuum/SU2QuaternionSelectedLinkHeadIdentification.lean:58`,
is `project selected (heatAt selected multiplier w K * polynomial)`.
It integrates the existing selected link against its existing partner.

`heatPair`, `lean/YMGap/Continuum/SU2QuaternionHeadHeatDiagonal.lean:52`,
introduces a fresh head through `copy` and `liftHead`; all old spectator
coordinates are shared. `headMap_pairing` at line 264 correctly pins that
pairing to `headMap`. It does not identify the existing-neighbor update.

`SelectedLinkExposedRelativePairing`,
`lean/YMGap/Continuum/SU2QuaternionSelectedLinkHeadIdentification.lean:195`,
asks for equality of these distinct pairings on every supported state/test.
The condition is false for admissible inputs.

## Exact finite counterexample

Use `tailBlocks=1`, selected pair `0,1`, `w=1/2`, `K=1`, state `polyVar 0`
and test `polyVar 4`. Both are supported on two quaternion blocks.

- `counterRelativePairing_value`,
  `lean/YMGap/Continuum/SU2QuaternionSelectedLinkHeadObstruction.lean:78`,
  proves the existing-neighbor side is `1/32`.
- `counterHeadPairing_value`, same file line 82, proves the proposed
  fresh-head side is zero.
- `selectedLinkExposedRelativePairing_uninhabited`, same file line 85,
  derives `False` from the specified certificate.

These are exact rational kernel checks, not floating-point evidence.

## The consumer guards do not repair it

Use the hybrid API's `n=2`, hence four blocks, selected pair `0,2`, and the
explicitly padded block-zero coordinate `hybridCoordinate` (same file line
100). For every w and K, its existing-neighbor self-pairing is zero:
`existingNeighbor_coordinate_pairing_zero` at line 114. This follows from
projection self-adjointness and its zero conditional mean; it does not
expand a large heat prefix.

Its norm is `1/4` (`hybridCoordinate_norm`, line 124), while its conjugated
fresh-head self-pairing is `w^3/4` for every `K>=1`
(`hybridCoordinate_conjugated_pairing`, line 153). The latter uses the
existing all-degree harmonic reproduction, not cutoff enumeration.

At `w=1/2`, the following certificates are therefore impossible at every
`K>=1` (all declarations in the same obstruction file):

- `hybrid_identification_uninhabited`, line 174;
- `hybrid_exposedHeadPairing_uninhabited`, line 187;
- `hybrid_relativePairing_uninhabited`, line 195;
- `hybrid_projectionPairing_uninhabited`, line 203.

`hybrid_guardedRelativePairing_uninhabited`, line 213, specializes to the
actual `sufficientCutoff counterNome`. This is not an example excluded by
the conditional local-bound consumer's cutoff guard.

The requested local bound itself fails, independently of those certificates:
`existingNeighbor_defect_bound_false`, line 221, proves at `w=3/4`, every K,

    H(p^2) - H(p * selectedHeatProjection(p)) = 1/4
        > (1-w) * H(blockAngularSquare 0 p) = 3/16.

The tested carrier is the admissible four-block polynomial API; this is not
a gauge-invariant Yang--Mills counterexample or a continuum theorem.

## What remains valid and where to work next

No existing theorem or certificate statement is weakened. In particular:

- `hybridMap_carrier`,
  `lean/YMGap/Continuum/SU2QuaternionProductHeatHybridSweep.lean:648`,
  still identifies the full sweep endpoint with the original `productMap`.
- `hybridMap_centered_square_bound`, same file line 688, remains the checked
  ordinary-Haar centered contraction. It does not use the refuted field.
- `hybridSweep_defect_cross_terms_eq_endpoint`, same file line 360,
  retains the signed cross terms; that exact telescope is unaffected.
- `head_update_eq`, same file line 702, applies to an explicitly copied
  input after dropping its cleared source coordinates, not to every
  doubled-carrier stage with unchanged coordinates.
- `energy_eq_bare_add_correction`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean:144`,
  retains the actual interacting source `V*g*f` and signed correction.
- `subunitCompletedSectorFormGap`,
  `lean/YMGap/Continuum/BF4PhysicalCubeSubunitCompletedGap.lean:155`,
  remains the separate proved BF4 completed-sector gap.

The next quantitative target is an endpoint bound on the original n-block
carrier, for the fully active product `ids=List.range n`:

    H(f^2) - H(f * productMap(f))
       <= (1-w) * sum_i H(blockAngularSquare i f).

The target retains `0 <= w < 1`, `sufficientCutoff w <= K`, and the
supported-input guard. It is not asserted here as a proved inequality.

`productMap_pairing`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:247`,
and `productMap_selected_expansion`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatHarmonicExpansion.lean:158`,
are existing exact producers. A joint positive harmonic decomposition, or
an equivalent proved same-carrier commuting-fold identity and product
inequality, remains to be constructed; this audit does not assert it.

For proper active subsets, `productMap` averages inactive links as well
(definition at `SU2QuaternionProductHeatMarginals.lean:56`). An active-only
angular bound cannot simply be asserted for all supported inputs: retain
the inactive projection residual or prove independence first. No estimate
here controls the interacting signed correction, spatial/spacing limits,
physical mass, full QFT axioms, or every group.

## Verification

The obstruction's focused check passed with all eighteen printed theorem
gates within `{propext, Quot.sound}`, no warnings or `sorryAx`:
`/tmp/ym-gap-selected-link-obstruction-final-check.log`. The preserved
identification/certificate module also passed its focused scope check:
`/tmp/ym-gap-selected-link-identification-scope-final-2.log`.

A dependency-complete target was attempted but STOPPED at the 12 GiB OS
reserve; it did not pass (`/tmp/ym-gap-selected-link-obstruction-final-build.log`).
The stop left the old reflection leaf's cache missing. Its monolithic
decision exceeded an 8 GiB recovery cap, so the unchanged theorem
`BF4ExactSlabVacuumReflectionFiniteCheck.faceSlice1_normal2` was split into
eight independently kernel-checked eight-term blocks. The repair passed
with only permitted axioms under that lower cap:
`/tmp/ym-gap-reflection-face2-chunked-check-1.log`, commit `6c5bf1c`.
Candidate literals came from untrusted evaluation and were checked against
the actual reflected source; no evaluator output is used as a proof oracle.
The temporary candidate-generation source was removed after use.

All successful final checks use one monitored worker capped at 8 GiB,
retaining the 12 GiB reserve. No safety threshold was raised. The large
dependency target was not restarted; root/full-tree audit/guard NOT run.
The historical progress-metric script was not run because it invokes a
repository-wide guard. CI is unchanged. The full hybrid consumer leaf also
passed: `/tmp/ym-gap-hybrid-sweep-scope-final-check.log`. All printed gates
in these final focused logs are within `{propext, Quot.sound}`; no errors,
warnings or `sorryAx` remain in the accepted logs.
