# Shared-factor comparison and the block neighbor budget

Date: 2026-09-27 UTC. Starting commit: `f5ba614`.
The whole-project target remains constructive nontrivial continuum Yang--Mills
on R^4 for every compact simple group, with same-theory QFT structure and a
positive physical Hamiltonian gap. This increment does not close that target
or the changing-spacing signed estimate.

## New checked result: only shared factors pay the form-comparison cost

For finite link lists A,B, the computed shared region contains exactly the
physical faces touching both lists; all other faces remain in the reference.
No disjointness, physical-membership, nonempty or nodup assumption on the
supplied lists is needed for this finite face partition.

Declarations in `lean/YMGap/Continuum/BF4ExactSlabSharedFaceRegion.lean`:

| Declaration | Line | Result |
| --- | --- | --- |
| `sharedTest`, `sharedIds`, `retainedIds`, `sharedCount` | 25, 29, 34, 37 | Explicit Boolean partition and face-count data. |
| `shared_partition` | 42 | Shared followed by retained faces is a permutation of all physical faces. |
| `retained_not_touches_both` | 57 | Every retained face avoids at least one selected list. |
| `sharedCount_le_left`, `sharedCount_le_right` | 88, 95 | At most six times either selected-list length. |
| `sharedIds_singleton` | 104 | Literal equality with the existing two-link shared-face list. |
| `sharedCount_singleton_le_one` | 115 | Reuses the older at-most-one-face theorem for distinct singleton links. |

The singleton geometry was ALREADY present in
`BF4ExactSlabSharedFaceGeometry.heatProduct_shared_partition` and
`retainedHeat_partition`, at
`lean/YMGap/Continuum/BF4ExactSlabSharedFaceGeometry.lean:99` and `:145`.
`sharedIds_length_le_one` at
`lean/YMGap/Continuum/BF4ExactSlabSharedFaceUniqueness.lean:24` was also
already proved. This increment generalizes to block lists and explicitly
joins back to those declarations; it does not claim to discover their facts.

Declarations in `lean/YMGap/Continuum/BF4ExactSlabSharedFaceComparison.lean`:

| Declaration | Line | Result |
| --- | --- | --- |
| `sharedHeat`, `retainedHeat` | 49, 52 | Actual original face-factor products on the unchanged coordinate algebra. |
| `sharedLower`, `sharedUpper` | 55, 58 | L=headFloor(w)^s and U=prefixCap(w)^s, with s the actual shared count. |
| `sharedLower_positive` | 61 | Positive L at every rational 0<w<1. |
| `fullWeight_split` | 66 | Original full weight equals retained times shared, coefficientwise. |
| `retainedHeat_certificate` | 73 | Positivity witness for the retained weight at K>=headCutoff(w). |
| `shared_weighted_bounds` | 88 | L H[q retained] <= H[q full] <= U H[q retained] for every certified positive q. |
| `shared_weighted_bounds_by_left` | 108 | Coarser cost controlled by the left block's length, not ambient volume. |
| `shared_signed_pair` | 127 | Two-sided signed mixed-form comparison for EVERY supported polynomial pair. |

For B_R the retained form and B_F the original full form, the last theorem is

```
-(U-L)*(B_R(p,p)+B_R(q,q))
    <= 4*B_F(p,q)-2*(L+U)*B_R(p,q)
    <= (U-L)*(B_R(p,p)+B_R(q,q)).
```

It follows by the existing `QuaternionHaarSignedFormComparison.centered_polarization`
at `lean/YMGap/Continuum/QuaternionHaarSignedFormComparison.lean:114`.
Tests may depend on every spectator link. There is no sampled-observable,
bounded-degree or independent-face premise. The target uses the original
full action; the explicitly compared reference omits shared factors and is
NOT silently identified with that action or its conditional projections.

The constants depend on nome and shared-face count. The coarser comparison
depends on nome and selected-list size, not extent or late heat cutoff.
These are form comparisons, not useful scaling-uniform conditional angles.

## Checked route obstruction: the current floor cannot close this degree budget

The old `headFloor_le_oneThirtySecond` at
`lean/YMGap/Continuum/BF4ExactSlabSharedWindowFloorBound.lean:46` and
`BF4ExactSlabStarRateObstruction.prefixCap_ge_one` supply the scalar facts.
The older finite two-state counterexample is recorded in
`audits/AUDIT-SHARED-WINDOW-INFLUENCE.md`; it is not re-proved or presented as new.

New declarations in
`lean/YMGap/Continuum/BF4ExactSlabSharedFloorBudgetObstruction.lean`:

| Declaration | Line | Result |
| --- | --- | --- |
| `sharedFloorRatio` | 44 | The actual ratio delta=headFloor(w)^s/prefixCap(w)^s with positive denominator. |
| `sharedFloorRatio_le_oneThirtySecond` | 53 | s>=1 implies delta<=1/32 at every rational 0<w<1. |
| `degreeBudget` | 84 | D*(1-delta), the scalar 2*D*eta for eta=(1-delta)/2. |
| `not_degreeBudget_lt_one` | 90 | s>=1 and D>=2 imply that this budget is NOT less than one. |

Thus even the proposed improved pair coefficient `(1-delta)/2` cannot feed
these particular constants into a positive uniform degree-two-or-higher
neighbor margin. This is not a bound on the ACTUAL conditional influence.
It excludes this scalar estimate combined with this summation budget, not
all block methods, sharper original-action estimates, signed aggregate
methods retaining positive terms, or Yang--Mills itself. A positive
dimensionless uniform margin is sufficient for one route, not a necessary
condition for the physical Clay conclusion.

## Reviewed two-block argument, NOT a newly checked analytic producer

For disjoint blocks, a reference retaining only A-only, B-only and exterior
factors is conditionally a product after exterior coordinates are fixed.
If its actual one-block and joint-exterior projections were constructed on
identified completions with the same omission ranges, the two-sided form
comparison and product variance inequality would give

```
E_full >= L*E_ref >= L*V_ref >= (L/U)*V_full.
```

Here E is the sum of the two conditional residual energies, and V the joint
exterior residual energy. This prose argument requires genuine reference
projections and range identifications; the new signed form comparison alone
does not supply them. No field assuming them is introduced.

There is a constructive, zero-safe last step: on the original joint-exterior
complement put H=R_A+R_B, E=<Hy,y>, delta=L/U. From delta*||y||^2<=E and
`0<=||Hy-delta*y||^2`, obtain `||Hy||^2>=delta*E`, hence
`<R_A y,R_B y> >= -(1-delta)*E/2`. No division by an unknown CReal energy or
excluded-middle split on whether that energy vanishes is needed.
This algebra was independently reviewed by Sol; it is not claimed as a new
Lean theorem in this increment.

Absolute correlation of residual ranges is the wrong target: already in a
product law, an interaction mode can belong to both ranges. The required
bound is SIGNED. Centered prediction-space correlation or a product variance
comparison must preserve the common exterior mode explicitly.

## Targeted research and route decision

This was a targeted source review, not another routine math-ph listing scan.

- Caputo--Parisi's block factorization theorem starts from strong spatial
  mixing of the underlying spin system; it does not supply that hypothesis
  for the original SU(2) action. See [the primary paper](https://arxiv.org/abs/2004.10574),
  Definition 2.1 and Theorem 2.3.
- Chen's separator/block-factorization approach includes strong-spatial-mixing
  results in its discrete-spin setting. This does not establish the missing
  SU(2) input. See [the primary paper](https://arxiv.org/abs/2307.08212),
  Definition 5.2 and Lemma 5.5.
- Peyre tensorizes supplied maximal-correlation controls under the relevant
  dependence hypotheses. It is not a producer of the present action-specific
  correlation estimate. See [the primary paper](https://arxiv.org/abs/1004.1602),
  Definition 3.1.2 and section 3.3.

Do NOT construct a retained-reference completion solely to insert the above
coarse all-nome window into the uniform neighbor budget: its scalar failure
is already checked. Retain the exact block shared-factor comparison for a
sharper estimate, but seek original-action signed cancellation or an aggregate
bound that preserves positive contributions. Do not replace either with a
new assumed-angle certificate or infer an all-vector estimate from finite
source tests. The existing ordered-pair consumer is `neighboringCross_lower`
at `lean/YMGap/Continuum/GNSProjectionNeighborLowerBound.lean:142`;
`energy_contract` at `lean/YMGap/Continuum/GNSResidualGeneratorDescent.lean:112`
needs a genuine generator-square lower bound.

Physical scaling, nontrivial survival, selected-face thermodynamic control,
same-theory reflected OS/QFT and physical mass, and every-group construction
remain open. No canonical chart marker changes.

## Next bounded mathematical producer

Prioritize an exact signed four-copy covariance determinant with the exterior
variables shared, before taking absolute values. For disjoint blocks let nu
be the A-only times B-only reference, integrating selected coordinates ONLY;
the exterior coordinates are still polynomial variables. Put K=sharedHeat,
Z=nu(K), N_f=nu(K f), and likewise N_g,N_fg, for an A-only test f and B-only
test g. The proposed identity is

```
4*(Z*N_fg-N_f*N_g)
  = nu_A^2 nu_B^2 [(f_a-f_a')*(g_b-g_b')
      *(K_ab*K_a'b' - K_ab'*K_a'b)].
```

All A-only/B-only weights are duplicated with their corresponding block.
The common exterior weight is inserted ONCE after this polynomial-valued
identity; the statement must not multiply separately exterior-integrated
expectations. Prove equality under every exterior insertion. The determinant
vanishes for a separating K and so retains information the positive window
does not measure. This is a proposed proof task, not a checked theorem here.

Reuse `replica_identity` at
`lean/YMGap/Continuum/SU2QuaternionConditionalVarianceReplica.lean:126`
and `varianceNumerator_replica` at
`lean/YMGap/Continuum/BF4ExactSlabStarVarianceReplica.lean:104`
for coordinate-copy/partial-Haar techniques, and the new `fullWeight_split`
for the actual action. The targeted search found no signed four-copy identity
in those replica modules or `SU2QuaternionWeightedProductTwoLinkDual.lean`.
The single-link `conditionalGenerator_square` at
`lean/YMGap/Continuum/BF4ExactSlabSignedNeighborEnergy.lean:68` displays the
downstream signed sum with its positive remote remainder. A block consumer
still requires actual schedule geometry and an analytic estimate, not only
this identity. A rate for the original heat determinant with arbitrary
retained spectator weights and its completed prediction-space join are open.

## Verification boundary

Three focused targets passed all 28 printed axiom gates within
`{propext, Quot.sound}`. The geometry was rechecked after adding its singleton
pin, and its signed-comparison consumer was then refreshed. All checks ran
serially through the monitored launcher, one worker, 20 GiB ceiling. No
competing Lean/CI process was present at the preflight check. Sol/Luna supplied
bounded proof and review work in parallel; no compiler was delegated.
No new sorry, axiom, analytic bundle, weakened field or classical shortcut.
No full/root build, full audit/guard, progress-metric run, or CI was run.
