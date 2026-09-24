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
