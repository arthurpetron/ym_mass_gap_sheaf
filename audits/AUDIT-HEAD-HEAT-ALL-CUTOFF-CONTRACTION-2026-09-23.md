# All-cutoff positive head map and original full-product norm control

Date: 2026-09-23. Parent revision: `0e6a0f3`.

Whole-project goal remains OPEN: nontrivial continuum Yang--Mills on R^4
for every compact simple group, with full same-theory QFT axioms, isolated
vacuum and finite positive physical Hamiltonian mass gap, in constructive Lean.

## Actual local operator, not an assumed form

In `lean/YMGap/Continuum/SU2QuaternionHeadHeatPositiveContraction.lean`:

- `heatPair_symm`, line 87, exchanges the two active head coordinates and
  keeps all spectators, using the original relative heat kernel symmetry.
- `headMap_symmetric`, line 118, identifies the resulting symmetry for the
  computed `headMap` under the original Haar pairing.
- `headMap_positive`, line 133, and `headMap_form_le_norm`, line 139,
  consume the already proved harmonic weights of that same map. For
  0<=w<=1 they give its form interval 0<=H<=I at every finite K.
- `headMap_square_le_pair`, line 149, applies the existing constructive
  `PositiveContractionOneStepForm.square_form_bound` to the literal map on
  the supported finite Haar GNS carrier. It proves

      Haar((headMap p)^2) <= Haar(p * headMap p).

- `headMap_square_contraction`, line 168, then bounds this by Haar(p^2).

The algebraic symmetry holds at all w,K. Positivity needs only w>=0; the
form ceiling and norm bound need 0<=w<=1. No strict nome inequality, cutoff
onset, pointwise kernel positivity or spectral theorem is assumed.
`spareSwap` and `copy_reindex_prefix` in `SU2QuaternionSpareHeadCopy.lean`
were made public with unchanged proof bodies so the symmetry proof can
reuse the already established copy/coordinate identity.

## Actual product consumer

In `lean/YMGap/Continuum/SU2QuaternionProductHeatCyclicContraction.lean`:

- `cycleStep_square_contraction`, line 45, uses the checked identity
  C=A headMap B and Haar norm invariance of A and B.
- `cycleIterate_square_contraction`, line 61, iterates this on the same
  supported n-block carrier, for every prefix length.
- `productMap_range_square_contraction`, line 74, consumes the original
  endpoint identity `productMap_range_cycle_carrier` to conclude

      Haar((productMap n w K (range n) p)^2) <= Haar(p^2).

This holds for n=tail+1>0, every supported p, every finite K, and rational
0<=w<=1. The uniform norm multiplier is 1, NOT a strict spectral rate.

This is distinct from the previous
`SU2QuaternionProductHeatTensorization.productMap_centered_square_bound`
(`lean/YMGap/Continuum/SU2QuaternionProductHeatTensorization.lean:113`),
which gives a strict nome-dependent rate under centering, 0<w<1 and its
computed heat-floor cutoff guard. That theorem and all its premises remain
unchanged; the new theorem does not remove the guard from the strict rate.

## Remaining causal frontier

Norm nonexpansion does not prove the desired endpoint angular defect

    Haar(p^2)-Haar(p * productMap(range n) p)
      <= (1-w) * sum_i Haar(blockAngularSquare i p).

The selected-update commutation/product-defect proof (or positive joint-mode
argument) is still open. Proper active subsets retain inactive projections.
The downstream interacting consumer remains `energy_eq_bare_add_correction`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean:144`,
with the original `V*g*f` source and signed correction. No original-action/
geometric-time, spatial/spacing, continuum survival, finite physical mass,
full QFT, every-group or Clay atom is closed by a multiplier-1 norm bound.

## Verification

Serialized focused checks, each terminal exit 0:

- `/tmp/ym-gap-spare-head-public-check-1.log`: eighteen public gates;
- `/tmp/ym-gap-head-heat-positive-contraction-check-2.log`: six public gates;
- `/tmp/ym-gap-product-heat-cyclic-contraction-check-1.log`: three public gates.

Each used `scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 8`
with named leaf/cache output and the 12 GiB OS reserve retained. All
twenty-seven gates are within `{propext, Quot.sound}`; accepted logs contain
no error, warning or `sorryAx`. The earlier failed local draft is not evidence.
A separate read-only review confirmed the guards and the distinction between
all-cutoff nonexpansion and the existing guarded strict centered rate.

No new `sorry`, axiom or changed frontier field. Root imports are registered,
but no full-root build/audit/progress guard or broad test suite was run.
CI is unchanged. An independently developed spectator-equivariance draft is
not part of this milestone's verification claim.
