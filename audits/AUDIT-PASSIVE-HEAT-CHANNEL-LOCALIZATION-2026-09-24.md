# Exact passive-heat channel localization

Date: 2026-09-24 UTC. This records checked finite mathematical progress, not
continuum or Clay closure. The whole-project target remains constructive
nontrivial continuum Yang--Mills on R^4 for every compact simple group,
with SAME-theory QFT/local YM/UV structure, isolated vacuum and finite
positive physical Hamiltonian mass gap.

## Mathematical change

The previous Taylor estimate expanded the complete projected source
q=P_fringe(V*g), including its modes on links untouched by the observable.
The new construction retains those links' heat factors exactly.

Let A be the observable blocks and S their complement. The actual spectator
kernel has a computed finite expansion

    K_S(x,y) = sum_c lambda_c h_c(x) h_c(y),    lambda_c >= 0,

where equality is on the original doubled Haar carrier with ARBITRARY later
polynomial insertions, not just a bare integral identity. The coefficients
come from the original heat packet and positive inverse basis weights.
The polynomials are real/imaginary representation-column tensor leaves;
Cartesian products construct the whole selected kernel's channel list.

Set b_c=P_S(q*h_c). Endpoint pairing first dresses BOTH copies of q;
the already checked inactive-source identity then proves

    E_original = sum_c lambda_c E_full(b_c,f),
    M_original(p) = sum_c lambda_c M_full(b_c,p).

The moment identity applies to spectator-independent insertions p; the
original slab consumer also retains its fringe-independence guard. It
therefore preserves the same partition normalization and, for the allowed f and f^2, the same
raw moments used in centering. Every b_c is spectator-independent.
The resulting upper estimate is

    E_original <= sum_c lambda_c *
      [eps * sum_i H[b_c^2 Gamma_i(f)]
       + eps^2 * pairBudget(b_c,b_c*f^2)],    eps=1-w.

The literal plaquette supplies the A/S partition and independence.
Strict spatial padding supplies the separate original fringe guard.
The action, terminal message, cutoff guard and original transfer are retained.

## Declarations

Paths in this section are under `lean/YMGap/Continuum/`.

- `SU2QuaternionProductHeatGramChannels.lean:96`: `productChannels`;
  `:180`: `productChannels_supported`; `:213`: `productChannels_nonnegative`;
  `:435`: `productHeat_gram_carrier` construct and certify the actual channel list.
- `SU2QuaternionProductHeatPassiveChannels.lean:185`:
  `sourceMoment_passive_channels`; `:199`: `sourceEnergy_passive_channels`;
  `:224`: `channelSource_independent`; `:231`: `sourceMoment_projected_channels`;
  `:252`: `sourceEnergy_projected_channels`;
  `:275`: `sourceEnergy_le_projected_channel_budgets` preserve and bound the same form.
- `BF4ExactSlabFixedSpatialPlaquetteChannelPartition.lean:59`:
  `spectator_observable_cover`; `:66`: `plaquette_spectator_independent` construct
  the actual observable partition, without assuming the source is local.
- `BF4ExactSlabFixedSpatialPassiveChannels.lean:73`:
  `oddMoment_eq_plaquette_channels`; `:91`: `padded_plaquette_energy_eq_channels`;
  `:115`: `padded_plaquette_energy_le_channel_budgets` are the original-action consumers.

## Separate sharp ordinary-heat consequence

`SU2QuaternionProductHeatSharpAngularDefect.lean:137` proves
`pairCasimir_diagonal_eq_angular`; `:164` proves `productMap_full_defect_le_angular`.
The already checked diagonal remainder positivity removes the factor two
from the ordinary full-product angular estimate. The constant-source Casimir
calculation uses padding-safe carrier equality, not false literal polynomial
equality. The existing sufficient-cutoff guard is retained; no cutoff
dominating the entire source degree is added.

This is an ordinary finite kinetic estimate, not an interacting variance
comparison or a spectral/physical mass identification.

## Rejected shortcuts and remaining input

- Omitting a heat factor in `productMap` integrates that coordinate; it does
  NOT act as the identity there. Directly writing the partially diagonal
  angular term as a pairing of q^2 and Gamma(f) on independent active
  endpoints is wrong. The exact Gram/source projection avoids that error.
- lambda_c are unnormalized positive weights, not probabilities. Individual
  b_c and their moments may be signed. No individual channel probability law
  or channelwise recentering is asserted.
- No width-independent channel count, total coefficient bound, mixed-budget
  estimate, or scaling-sufficient variance comparison has been proved here.
  The source, channel list and weights retain nome, cutoff, spatial-width,
  terminal-depth and observable dependence.
- The next analytic input is useful control of the COMPLETE weighted budget
  against SAME centered variance on ONE justified changing-scale observable
  family, or direct sampled-response control. The independent EVERY-vector
  spatial/spacing gap, SAME-theory continuum/QFT/local YM/UV, physical mass and
  every compact simple group remain open. No canonical field was changed.

## Verification and review

Five final serialized checks used `scripts/safe_lean_build.py --jobs 1`,
`--check`, explicit `.olean` output, and a 4 GiB worker cap. Each completed
with terminal exit 0:

- `/tmp/ym-gap-sharp-angular-defect-check-6.log`: two gates;
- `/tmp/ym-gap-product-gram-channels-check-5.log`: five gates;
- `/tmp/ym-gap-plaquette-channel-partition-check-2.log`: five gates;
- `/tmp/ym-gap-passive-channel-energy-check-2.log`: six gates;
- `/tmp/ym-gap-original-passive-channel-energy-check-1.log`: four gates.

All twenty-two printed gates are within {propext, Quot.sound}; accepted logs
contain no error/warning/sorryAx. Failed drafts are not verification evidence.
Sharp-estimate attempts 3 and 5 were stopped by the memory monitor (exit 75)
when available memory reached 11.4 GiB, below the 12 GiB reserve. Verification
resumed only after memory recovery; no reserve, swap threshold or worker cap
was weakened, and no unrelated process was killed.

Sol implemented the Gram producer and sharp-estimate draft; Luna implemented
the bounded plaquette partition. The main agent implemented the exact
moment/energy consumer and original-action specialization and completed
verification repairs. Independent source review checked both-endpoint
dressing, common normalization, signed channels and the absence of a
uniformity claim. Semantic imports were added for the actual consumers.
No new hole/axiom, classical input or canonical-field change was introduced.
No full-root build, full-tree audit, guard or progress-metric run was performed.
CI remains unchanged (disabled).

## One-link conditional Bessel follow-up

Checked 2026-09-24 UTC. This proves the first norm estimate on the computed
channels, not the full spectator-family budget or a continuum conclusion.

For the actual list `heatChannels 0 w K`, the exact identity and bound are

    sum_c lambda_c H[(P_0(q*h_c))^2]
      = H[q*headMap(w,K,q)] <= H[q^2].

The untouched coordinates are SHARED: on (x,y,z), `copy q` is q(x,z) and
`liftHead q` is q(y,z). Their two copies of z are not integrated independently.
The two-link Gram carrier extends to arbitrary shared-spectator insertions;
exact head Fubini then produces the conditional square. The existing
`headMap_form_le_norm` supplies the coefficient-one inequality.

For a head-independent insertion r, absorbing r into the source yields

    sum_c lambda_c H[(P_0(q*h_c))^2*r^2] <= H[q^2*r^2].

The coefficient is one for every finite K and 0<=w<=1, with no pointwise
heat-floor guard. The source, insertion and channel list may still depend on
parameters. The right side is the raw Haar source square, NOT the original
interacting partition or centered variance. No channel probability law is
asserted; signed q and r are allowed.

### Exact declarations

Paths are under `lean/YMGap/Continuum/`.

- `SU2QuaternionProductHeatGramLocality.lean:162`:
  `heatChannels_independent`; `:172`: `productChannels_independent`;
  `:192`: `project_productChannel_fixed`; `:199`:
  `familyProject_productChannel_fixed`. These concern the computed channels,
  not locality of q.
- `SU2QuaternionSharedHeadGramPairing.lean:84`: `copy_mul_carrier`;
  `:109`: `copy_lift_pair_eq_project_square`; `:141`:
  `sharedHead_channel_pairing` preserve the shared spectator carrier.
- `SU2QuaternionHeadHeatGramBessel.lean:91`:
  `heatChannels_project_square_eq_pair`; `:115`:
  `heatChannels_project_square_le`; `:135`:
  `heatChannels_project_weighted_square_le` are the exact recombination,
  norm bound and weighted consumer.
- `SU2QuaternionProductHeatGramChannels.lean:171`:
  `heatChannels_supported`; `:350`: `heatChannels_carrier` are existing
  one-link producer proofs made public, with their own printed axiom gates.

### Remaining causal join and rejected repetitions

The arbitrary selected-block and whole spectator-list Bessel inequalities
are NOT yet proved. Their precise next construction is supported channel
transport through a head/block swap, followed by finite-list composition.
Transport must preserve weights, multiplicities and original normalization;
raw polynomial equality is inappropriate when reindexing adds zero padding.
Only after that join may the six angular squares be summed into the full
angular channel cost consumed by `sourceEnergy_le_projected_channel_budgets`.

Even that angular contraction would not control the remaining mixed budget
or compare it with SAME centered variance along changing scales. Arbitrary
raw source norms cannot be identified with attenuated physical moments:
`SU2QuaternionHeadHeatDiagonal.harmonic_pair` explicitly retains the cutoff
attenuation, including zero above cutoff. Source review also found that
merely renaming the existing input-dependent Taylor tree as an active-block
tree supplies no new quantitative inequality.

The existing completed plaquette increment and affine-floor quotient must
not be repackaged as a new survival route:
`BF4AllNomeCompletedPlaquetteIncrement` already supplies the 192*n*(1-w)
increment, while `BF4ExactSlabPlaquetteAffineCalibrationObstruction.computedLossRatio_ge`
proves the corresponding available-budget ratio is at least 115200. This
concerns those certificate numbers, not a counterexample to Yang--Mills.

### Follow-up verification

Final serialized monitored 4 GiB checks completed with exit 0:

- `/tmp/ym-gap-gram-locality-check-3.log`: four gates;
- `/tmp/ym-gap-gram-public-pairing-check-1.log`: seven gates, five pre-existing;
- `/tmp/ym-gap-shared-head-gram-check-4.log`: three gates;
- `/tmp/ym-gap-head-gram-bessel-check-2.log`: three gates.

All seventeen printed gates are within {propext, Quot.sound}; accepted logs
contain no error, warning or sorryAx. Failed draft logs are not evidence of
proof. Pairing check 3 was refused before launch when available memory reached
the 12 GiB reserve. Read-only memory telemetry confirmed recovery before the
unchanged check resumed; no threshold was weakened or unrelated process killed.

Sol supplied the locality and pairing drafts and independently reviewed the
mathematical scope. Root implemented the Gram recombination/Bessel consumer,
repaired the drafts and performed all serialized checks. No new hole, axiom,
analytic premise or canonical-field change was introduced. Semantic imports
were added; no full-root build, full-tree audit, guard or progress-metric run
was performed. CI remains disabled. Whole-project Clay target remains OPEN.
