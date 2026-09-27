# Original-action deletion on reflection-fixed faces

Date: 2026-09-27. Base: `250a331`.

## Mathematical statement and original-object pin

For the central odd slab, retain the entire lower and upper bulk, and choose
any subset of its reflection-fixed crossing faces. The original unnormalized
reflected quadratic increases when that subset increases. At the unit
observable this is a comparison of the actual original partition integrals,
with comparison factor exactly one. The finite statement holds for every
rational nome w >= 0 and every representation cutoff K, including K=0.
It requires neither a pointwise positive heat prefix nor a late-head cutoff.

The proof does not replace the interacting action with independent factors.
`coeffW_zero_nome` (`:60`) makes every positive-spin coefficient vanish at nome zero;
`faceHeat_zero_nome` (`:68`) retains precisely the vacuum polynomial unit.
`masked_original_product` (`:137`) then identifies the full reflected profile with
the actual product on

    lower faces ++ kept fixed faces ++ upper faces.

`masked_original_quadratic` (`:149`) identifies its original Haar numerator,
including the reflected observable insertion. `original_quadratic_nested`
(`:156`) and `original_quadratic_deletion` (`:171`) apply coefficientwise Gram
positivity with unit comparison factors. `original_partition_nested` (`:199`)
and `original_partition_deletion` (`:207`) specialize the same numerator to the unit.
All are in
`lean/YMGap/Continuum/BF4ExactSlabReflectionFixedDeletion.lean`.

For 0 < w < 1, `original_quadratic_limit_nested` (`:214`),
`original_quadratic_limit_deletion` (`:227`), `original_partition_limit_nested`
(`:239`) and `original_partition_limit_deletion` (`:251`) in that module
pass the comparisons to the EXISTING `numeratorLimit`, `heatProductHaarLimit`
and `fullActionLimit`. Their explicit Cauchy moduli are reused, not assumed.
Volume, nome and observable remain fixed in this passage; physical spacing
does not vary. The multiplicative comparison constant is one for every such
parameter choice, but no spatial or spacing-uniform convergence modulus is
asserted.

## Relation to the current signed response frontier

This improves the original partition comparison for a restricted geometric
class. It does **not** replace the current arbitrary-collar normalization.

- `BF4ExactSlabDetachedFaceRegion.collarIds`,
  `lean/YMGap/Continuum/BF4ExactSlabDetachedFaceRegion.lean:26`, removes all
  ambient faces incident to the marked or core links. Its definition does
  not restrict removed faces to a reflection plane.
- `BF4ExactSlabRootedResponseResummation.markedLinks`,
  `lean/YMGap/Continuum/BF4ExactSlabRootedResponseResummation.lean:48`, includes
  both probes and the inserted face. Its `rootedResponse` (`:57`) sums over
  rooted cores in an arbitrary selected ambient face list.
- `BF4ExactSlabResponseCollarNormalization.detached_fourth_floor`,
  `lean/YMGap/Continuum/BF4ExactSlabResponseCollarNormalization.lean:106`,
  compares the detached action with the old and inserted endpoints. Neither
  endpoint is required to have the paired bulk used by the new theorem.
- `BF4ExactSlabRootedResponseResummation.covariance_response_bound_of_rooted`,
  `lean/YMGap/Continuum/BF4ExactSlabRootedResponseResummation.lean:118`, still
  requires its unsupplied quantitative estimate on the signed normalized sum.

An application of the new comparison needs an exact identification of those
endpoint products with a reflection-compatible action whose deleted faces
are fixed crossing faces. No such general identification is provided.
The new theorem changes no hypothesis of the existing response consumer.
Normalized-correlation monotonicity, spatial decay, physical-spacing control,
nontrivial continuum survival and the all-group Clay target remain open.

## Verification boundary

The final focused monitored check passed in 4.32 seconds with one worker
capped at 20 GiB. All 15 printed declarations are axiom-free or use only
`propext` / `{propext, Quot.sound}`. There is no `sorryAx` or classical
dependency. The initial check exposed missing namespace openings, a Boolean
filter rewrite and an ambiguous method lookup; these were corrected without
changing statements or increasing limits. The final check has no warning.

Sol's independent static review found no semantic defect in the original
product pin or stated scope, and confirmed the missing general-collar
application. No canonical field, analytic assumption, hole or chart marker
was changed. No full-tree build/audit was run or is implied.
