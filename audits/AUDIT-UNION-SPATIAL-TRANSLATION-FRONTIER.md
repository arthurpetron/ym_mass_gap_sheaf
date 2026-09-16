# Spatial translation frontier on the actual union carrier

2026-09-16. The parent-controlled focused Lean check of
`YMGap.Continuum.BF4SpatialUnionDiagonalTranslation` passed with terminal
exit code 0, no errors or warnings, and all 29 axiom gates reporting only
`propext` and `Quot.sound`. The final log is
`/tmp/ym-union-diagonal-translation-20260916.log`; its axiom output was
inspected for this report. No compiler was run by the parallel author.
This records that focused check, not a repository-wide build or audit.
The whole-project continuum/all-compact-simple-group Yang--Mills target
remains open.

## The short identity

The existing spatial limit recenters every original presentation by `r+1`
in each spatial coordinate, in width `b+2*r+2`:
`recenter`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialRecenter.lean:91`,
and `paddedWidth`, same file `:89`.

For a supplied natural `s`, translate the original face words diagonally by
`s` and enlarge their support base from `b` to `b+2*s`. Then

```
paddedWidth (b+2*s) r = paddedWidth b (r+s)
recenter r (translate s x) = recenter (r+s) x
```

The second displayed equality is between the literal underlying signed
presentations; the first reconciles their dependent support types. Thus the
translated joint-pairing sequence is exactly a cofinal shift of the original
one. No additional boundary-decay estimate, coupling guard or arbitrary
Hilbert-space identification is required.

## New module and exact consumers

All new declarations are in
`lean/YMGap/Continuum/BF4SpatialUnionDiagonalTranslation.lean`.

| Declaration | Line | Content |
| --- | --- | --- |
| `translate` | 43 | Original face-word translation, with support base `b+2*s`. |
| `translated_paddedWidth` | 57 | Exact common finite-box width. |
| `recenter_translate_val` | 62 | Exact original signed-presentation identity. |
| `jointPairing_recenter_translate` | 96 | Literal finite-width joint-pairing equality on the same width and same original presentations. |
| `spatialPairing_translate` | 105 | Actual spatial limiting reflected pairing is preserved. |
| `spatialDistSq_translate` | 116 | Actual spatial limiting squared distance is preserved. |
| `stageTranslate` | 129 | Support-safe operation on the current union `Stage`. |
| `stageTranslate_zero`, `stageTranslate_add` | 152, 155 | Literal natural-parameter semigroup laws. |
| `pairing_translate`, `distSq_translate` | 172, 185 | Common-base transport removes any requirement that the two input stages have the same base. |
| `translationNonexpansive` | 199 | Supplies the existing completion map interface with the proved SAME-distance bound. |
| `translation_cauchy_modulus` | 222 | Every supplied representative's modulus is retained exactly. |
| `completedTranslation_zero`, `completedTranslation_add` | 229, 233 | Natural-parameter semigroup on the existing union completion. |
| `completedTranslation_time` | 239 | Commutes with actual discrete physical time. |
| `completedTranslation_unit` | 261 | Fixes the actual completed unit. |
| `completedInner_translate` | 268 | Preserves the SAME completed inner product, not a substitute form. |

The old limiting inputs are `spatialPairing_converges`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialPairingLaws.lean:70`, and
`distSq_converges_spatial`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialSeminorm.lean:58`.
Completed descent uses the existing
`SquaredSeminorm.Nonexpansive.completionMap`,
`lean/YMGap/Continuum/CRealSeminormCompletion.lean:323`.

## Exact remaining scope

This is **positive diagonal translation**, `(x,y,z) -> (x+s,y+s,z+s)`.
The existing `shiftVertex`,
`lean/YMGap/Continuum/BF4ExactSlabBulkEmbeddingGeometry.lean:31`, has one
shared spatial-shift parameter. `Z4Vertex`,
`lean/YMGap/Continuum/ClusterCount4DProgress.lean:112`, uses four natural
coordinates; unguarded natural subtraction does not implement a signed
translation group.

Independent axis shifts cannot be obtained merely by replacing the single
`s` in this proof: its exact identity aligns all three coordinates at once.
For an axiswise or signed displacement, the current centered-box exhaustion
requires either a proved comparison with differently placed boxes or an
equivalent support-chart construction with translation-compatible limits.
No such full action on `UnionCompletion` is supplied by this module.

Specifically NOT FOUND in the inspected `BF4SpatialUnion*.lean`,
`BF4ExactSlabFixedSpatialSpatialRecenter.lean`,
`BF4ExactSlabFixedSpatialTranslatedProbe.lean`,
`BF4ExactSlabFixedSpatialBaseCoherence.lean`, and
`BF4ExactSlabBulkEmbeddingGeometry.lean`:

- completed inverses for the positive diagonal maps;
- independent signed actions of all three spatial coordinates;
- a spatial translation group with all group laws on the current completion;
- changing-coupling/spacing identification or continuum translation continuity.

No stronger nome bound, new analytic hypothesis, completed carrier,
canonical frontier field, `sorry`, axiom or classical principle was added.
The completed inner-product pin is the immediate consumer: it exposes an
actual spatial symmetry of the current original reflected theory while
keeping the full spatial and continuum obligations distinct.
