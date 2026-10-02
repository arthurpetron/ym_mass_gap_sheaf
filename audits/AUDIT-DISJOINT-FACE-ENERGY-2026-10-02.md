# Mixed energy of disjoint original spatial faces

Literal link-disjointness now removes the first-order angular cross term
before integration. The full original temporal cross term is NOT zero: it
equals the mixed complete signed Taylor remainder. This isolates the remaining
cross-energy calculation without replacing the original density, normalizing
each singleton separately, or declaring interacting covariance zero.

## Exact argument and original consumer

Let f_p and f_q be the signed singleton spatial spans, and f_pq their sum.
All terms use the same w, cutoff K, width and original terminal depth n.
`LinkDisjoint` tests the actual four boundary links of each plaquette, not
statistical independence. Two incident witnesses with the same physical
`baseLinks width` index are the same link by
`BF4ExactSlabTemporalGaugeLedger.idxOf_injective_on_members`. Thus one face is
off the block row, and its angular derivative is coefficientwise zero by
`BF4ExactSlabFixedSpatialFamilyIncidence.blockRow_derivative_zero`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyIncidence.lean:116`).

Consequently, for each actual block b < length(baseLinks width),

```
Gamma_b(f_p,f_q) = 0
angularSquare_b(f_pq) = angularSquare_b(f_p) + angularSquare_b(f_q).
```

These are rational polynomial coefficient equivalences. Multiplying by ONE
arbitrary weight and integrating preserves the second identity. In particular
the original weight V*g_n*g_(n+1) stays intact, and all three normalized angular
terms use the same original odd partition. No positivity or factorization of
the weight is assumed for this algebraic step.

Under strict spatial padding and actual face membership, three applications of
`BF4ExactSlabFixedSpatialMarginalTaylor.padded_family_normalized_taylor`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMarginalTaylor.lean:127`) give

```
(E(f_pq) - E(f_p)) - E(f_q) = (R(f_pq) - R(f_p)) - R(f_q).
```

R is the EXISTING full `normalizedRemainder` (same module, line 102), including
the signed angular change-of-weight defect. Nothing asserts R is nonnegative,
small, or zero. The direct `finite_mixed_increment` consumer uses the existing
original squared-increment pin at K=headCutoff(w)+stage and identical endpoint
depths. Its mixed Wilson-window increment is TWO times this mixed remainder.
The interacting OWN covariance is untouched.

All new declarations below are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceEnergy.lean`, namespace
`YMGap.Continuum.BF4ExactSlabFixedSpatialDisjointFaceEnergy`.

| Declaration | Line | Exact role |
| --- | --- | --- |
| `LinkDisjoint`, `linkDisjoint`, `linkDisjoint_correct` | 61, 65, 68 | Literal edge condition and its computed finite test. |
| `blockRow_separate` | 78 | Same physical index cannot be incident to both faces. |
| `blockGamma_zero` | 104 | Mixed fundamental angular polynomial is zero on every physical block. |
| `blockAngularSquare_pair` | 153 | Exact blockwise split for arbitrary signed singleton coefficients. |
| `weightedAngular_pair` | 173 | Split under ONE arbitrary weight, with no independence assumption. |
| `marginalAngular_pair`, `normalizedAngular_pair` | 189, 197 | Original weight and common partition retained. |
| `padded_mixed_energy` | 218 | Entire normalized temporal cross equals full signed-remainder cross. |
| `finite_mixed_increment` | 270 | Direct original window consumer, with original schedule and factor two. |
| `exampleP`, `exampleQ`, `example_disjoint`, `example_spatial` | 314, 315, 317, 320 | Two parallel genuine spatial faces in base-two geometry. Not a favorable margin instance. |

## Verification and open input

The accepted focused command exited zero:

```
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceEnergy.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceEnergy.olean \
  --log-file /tmp/ym-disjoint-face-energy-20261002-third.log
```

All fifteen gates are empty or within {propext,Quot.sound}; `LinkDisjoint` and
the two face data definitions are axiom-free. The accepted log has no error,
warning, sorryAx or disallowed axiom. The two earlier draft checks failed on
elaboration/namespace errors and are not accepted evidence. Independent Sol
review passed the literal incidence proof, common density/partition and direct
window consumer. Independent Luna review passed the lines, gates, hashes,
documentation scope and byte-identical chart. The root agent alone compiled, with ONE 20-GiB worker and
unchanged 12-GiB OS reserve. Preflight found no competing compiler/runner/test
and zero swap; pressure-free memory was 86 percent before and 85 percent after.

| Artifact | SHA-256 |
| --- | --- |
| source | `edd9beb1cdb95a7c273e0acc4ad2c634ba2a19e7c18a9fa87619f6e054a0110e` |
| accepted log | `13d1227b73b2f62ca94c42f7c096da86252130107c9f9728e54f4ef7f31ab310` |

One semantic-root import is registered, not aggregate-checked. No broad build,
audit, guard, progress metric, literature scan or heavy moment evaluation ran.
No sorry, axiom, analytic premise, frontier weakening or machine/CI change.

NEXT: bound the retained original mixed remainder and OWN covariance with
useful signed slack on a justified changing family. Disjointness alone does
not control either quantity. Useful positive margin, spatial/spacing control,
EVERY-state decay, nonzero continuum survival, physical mass, full QFT, every
compact simple group and the Clay endpoint remain OPEN. The existing generic
`SU2QuaternionDisjointTemporalCrossTerm.energy_nonadditivity_value`
(`lean/YMGap/Continuum/SU2QuaternionDisjointTemporalCrossTerm.lean:211`) already
warns against mistaking angular cancellation for full energy additivity; it is
not an original Wilson numerical result. No displayed chart claim changed,
so its fenced blocks remain unchanged and no ASCII chart is reprinted.
