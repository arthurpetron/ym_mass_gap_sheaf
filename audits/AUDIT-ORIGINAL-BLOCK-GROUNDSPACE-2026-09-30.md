# Exact original block groundspaces

## Goal and result

The whole-project goal remains OPEN: constructive continuum Yang--Mills on
R^4 for every compact simple group, with SAME-theory QFT axioms, nontriviality
and a finite positive physical Hamiltonian gap.

For any finite list S of actual physical links, let Q_S be the EXISTING
original full-action block conditional projection and P_i the EXISTING
singleton conditional projection. This increment proves, for every state x
of the same completed carrier,

    Q_S x = x  iff  P_i x = x for every i in S.

For a list of physical-link indices, H_S=sum_{i in S}(I-P_i) and
E_S(x)=sum_{i in S}||(I-P_i)x||^2 are the existing residualSum and finalEnergy.
The same constructed Q_S therefore satisfies

    Q_S x = x  iff  H_S x = 0  iff  E_S(x) = 0.

Thus the already proved original orthogonal block projection is the exact
groundspace projection for the actual patch generator. Arbitrary exterior
dependence is retained. Empty lists and repeated indices are included; no
duplicate-free, small-nome, patch-gap or fixed-boundary premise is added.
The nome is rational with 0<w<1 and K>=headCutoff(w), as in the original
carrier. These are conditional-link weighted-L2 statements, not OS-time
or continuum spectral statements.

## Proof and declaration evidence

All paths below are relative to `lean/YMGap/Continuum/`.

| Declaration | File:line | What is proved |
| --- | --- | --- |
| `toBackgroundCauchy` | `BF4ExactSlabBlockCompletionComparison.lean:63` | Identity on polynomial sequences, explicit collar-rescaled modulus |
| `toFull_toBackground`, `toBackground_toFull` | `BF4ExactSlabBlockCompletionComparison.lean:113`, `:118` | Actual inverse completion maps, not assumed isometries |
| `completed_form_bounds` | `BF4ExactSlabBlockCompletionComparison.lean:124` | Explicit positive lower/upper collar constants for every original state |
| `family_square_contraction` | `SU2QuaternionWeightedHaarFamilyCompletion.lean:53` | Finite coordinate integration contracts the certified independent background |
| `familyProjection_fixed_of_singletons` | `SU2QuaternionWeightedHaarFamilyCompletion.lean:158` | Common coordinate fixedness implies family fixedness, with repetitions |
| `referenceCauchy`, `reference` | `BF4ExactSlabBlockReferenceProjection.lean:81`, `:89` | Actual transported reference with explicit representative and moduli |
| `conditional_reference` | `BF4ExactSlabBlockReferenceProjection.lean:140` | Original conditional fixes the raw reference range |
| `reference_conditional` | `BF4ExactSlabBlockReferenceProjection.lean:158` | Raw reference fixes the original conditional range |
| `fixed_iff_singletons` | `BF4ExactSlabBlockFixedSpace.lean:58` | Missing reverse implication, joined to the existing forward tower law |
| `union_fixed_iff` | `BF4ExactSlabBlockFixedSpace.lean:104` | Union-block fixed space equals intersection of the two fixed spaces |
| `finalEnergy_zero_iff_jointFixed` | `GNSProjectionGeneratorKernel.lean:86` | Nonnegative finite energy has exactly the joint fixed space as zero set |
| `residualSum_zero_iff_jointFixed` | `GNSProjectionGeneratorKernel.lean:109` | Same result for the actual residual sum, using its exact energy pairing |
| `fixed_iff_generator_zero`, `fixed_iff_energy_zero` | `BF4ExactSlabBlockFixedSpace.lean:149`, `:157` | Concrete original-action patch groundspace identification |

The reference has the form I M J: J and I compare the original completion
with the same-coordinate detached background, and M is raw family Haar
integration in that background. The maps change only explicit Cauchy moduli.
The original Q_S and the reference fix each other's ranges; they are NOT
identified as operators, and the reference is NOT claimed orthogonal in
the original interacting form. The forward singleton implication uses the
existing original tower law, not an unproved converse for the raw family.
The union fixed-space identity likewise does not assert Q_A Q_B=Q_(A union B)
or commutation for interacting blocks.

## Route decision and remaining analytic work

The initial source review tested a one-shared-face residual estimate.
`BF4ExactSlabSharedFaceComparison.shared_weighted_bounds` at
`lean/YMGap/Continuum/BF4ExactSlabSharedFaceComparison.lean:88` bounds forms, while
`BF4ExactSlabTwoLinkFourCopy.original_shared_four_copy_identity` at
`lean/YMGap/Continuum/BF4ExactSlabTwoLinkFourCopy.lean:255` and
`BF4ExactSlabTwoLinkNormalizerPin.interaction_covariance_normalizer_pair` at
`lean/YMGap/Continuum/BF4ExactSlabTwoLinkNormalizerPin.lean:152`
pin a signed union-covariance numerator. They do not supply a bound on the
pair of singleton residuals. A commuting reference retaining both one-sided
action factors and its quantitative comparison remain missing for that
route. The detached background used in THIS increment is not that missing
one-shared-face reference.

The completed patch groundspace identification was an independent prerequisite
for a same-object subsystem/overlap argument, recorded as missing in
`RESEARCH-DEFECT-RETAINING-COLLECTIVE-ROUTE-2026-09-30.md`. It is now proved.
It supplies the actual kernel to preserve in a prospective finite certificate;
it supplies no useful lower bound on its orthogonal complement.

NEXT: a quantitative original-action patch or overlap estimate, retaining
the exterior action and its actual conditional groundspace, with a budget
that can pass a justified local-to-global criterion along a scaling family.
The earlier local-support coefficient is not an all-state patch estimate.
Positive finite collar comparisons and the new kernel identity do not
repair its known inadequate scaling dependence. Do not replace an infinite-
degree estimate by a principal finite matrix or delete exterior ground states.

OS/physical-time identification, useful spatial/spacing control, nontrivial
continuum survival, finite physical mass, full QFT and every group remain
open. No canonical chart node changed; no ASCII chart was reprinted.

## Verification boundary

Five final focused checks passed all 41 printed gates within
{propext, Quot.sound}; `testLinks` is axiom-free. Verification used the
safe-build skill: one serialized worker, 20 GiB hard ceiling, 12 GiB OS reserve,
continuous safety telemetry and 300-second status cadence. All checks finished
in their initial calls, so there was no live-build polling loop. No full-root
build, full-tree audit or guard run was performed. Root imports are registered,
not claimed broadly rebuilt. One harmless unused-hypothesis warning remains
in the norm comparison's deliberately uniform physical-block API.

Final logs: `/tmp/ym-block-completion-comparison-20260930.log`,
`/tmp/ym-weighted-haar-family-completion-20260930.log`,
`/tmp/ym-block-reference-projection-20260930.log`,
`/tmp/ym-projection-generator-kernel-20260930.log`, and
`/tmp/ym-block-fixed-space-20260930.log`.
No new sorry, custom axiom, classical reasoning, native decision oracle,
analytic assumption or frontier weakening. No old sorry was discharged.
Independent source review confirmed the all-nome/list scope, the original
carrier and operator pins, and the distinction between range intersection
and operator commutation. No issue was found in that bounded review.
