# Collective original face-patch energy and a stronger certified margin

## Goal and scope

The whole-project goal remains OPEN: constructive continuum Yang--Mills on
R^4 for every compact simple group, with SAME-theory QFT axioms, nontriviality
and a finite positive physical Hamiltonian gap. The operators in this report
are conditional-link projections on ordinary original-action weighted L2,
not OS time translations. No continuum/scaling conclusion is asserted.

## Mathematical improvement

Let R_i be the EXISTING original full-action completed conditional residuals,
H=sum_i R_i, E(x)=sum_i ||R_i x||^2, and
A_f=sum_{i on face f} R_i. Let d_i count the original physical faces containing
i. The actual slab geometry gives d_i<=6; it is not identically six at the
boundary. Two distinct neighboring links share exactly one physical face,
and nonneighbors share none. Consequently the following is an exact signed
identity on EVERY completed state:

    sum_f ||A_f x||^2 = sum_i d_i ||R_i x||^2 + C_near(x).

C_near is the pre-existing ORDERED signed neighboring Gram sum; both pair
orientations occur, with no missing factor two. The global square is
E+C_near+R_remote, and the unchanged commutation proof gives R_remote>=0.
This proves the unconditional comparison

    sum_f ||A_f x||^2 <= ||H x||^2 + 5 E(x).

More importantly, if the actual collective patch square is at least gamma
times its actual incidence-weighted energy, with gamma<=1, then

    ||H x||^2 >= (6*gamma-5) E(x).

The consumer permits a collective estimate, not only a separate bound on
each face. A lower coefficient for an isolated/free-boundary plaquette
cannot be substituted: A_f uses the SAME full-action conditional projections,
with every exterior interaction retained. A coefficient above 5/6 is an
analytic obligation, not a consequence of geometry or positivity.

The existing proved small-nome pair coefficient e supplies the actual local
coefficient gamma=1-6e: each of four face links has at most three other face
links, and both endpoint costs are retained. The global margin is therefore
1-36e, improving the previous coarse count 1-50e without adding an analytic
hypothesis. At the EXACT rational nome 1/40, the new margin is positive and
the old one negative; both signs and the original scalar guards are checked
by Lean. Negativity of the old certificate is not negativity of a true gap.

The new margin also yields the actual completed centered inequality

    ((1-36e)/2) ||x||^2 <= E(x),

uniform in spatial extent and late heat cutoff. Constructive descent uses
the previous positive chronological area coefficient only to remove its
norm tail; that volume-dependent coefficient is absent from the final
bound. No spectral theorem is used. The new reverse-energy coefficient
c=2+(2/625)*(1-36e)/2 applies to the SAME balanced conditional sweep and the
actual order-n Chebyshev auxiliary constructed with that same c.

## Declaration evidence

Paths in this table are relative to `lean/YMGap/Continuum/`.

| Declaration | File:line | Role |
| --- | --- | --- |
| `patchSquareSum_expansion` | `GNSProjectionPatchEnergy.lean:161` | Exact joint-incidence weighted Gram expansion |
| `patchEnergySum_expansion` | `GNSProjectionPatchEnergy.lean:187` | Exact variable diagonal incidence |
| `patchSquareSum_eq_energy_add_cross` | `GNSProjectionPatchEnergy.lean:253` | Signed neighboring terms retained without absolute values |
| `jointCount_self_le_six` | `BF4ExactSlabFacePatchIncidence.lean:65` | Boundary-safe diagonal cap |
| `jointCount_distinct_near_eq_one` | `BF4ExactSlabFacePatchIncidence.lean:77` | Exactly one actual shared face |
| `jointCount_nonNear_eq_zero` | `BF4ExactSlabFacePatchIncidence.lean:92` | No shared patch for nonneighbors |
| `facePatch_other_length_le_three` | `BF4ExactSlabFacePatchSize.lean:61` | Actual patch has at most three other links |
| `generator_lower` | `RCCollectivePatchBudget.lean:76` | Cancellation of the SAME signed cross sum |
| `face_square_signed_identity` | `BF4ExactSlabFacePatchEnergy.lean:86` | Original completed operator identity |
| `faceSquareSum_le_generator_plus_five` | `BF4ExactSlabFacePatchEnergy.lean:100` | Unconditional patch-to-global comparison |
| `generator_square_lower_of_collective_patch` | `BF4ExactSlabFacePatchEnergy.lean:115` | Conditional collective margin consumer |
| `actual_face_lower` | `BF4ExactSlabFacePatchSmallNome.lean:69` | Actual small-nome local producer, no patch-gap premise |
| `margin_pin` | `BF4ExactSlabFacePatchGeneratorBound.lean:38` | Exactly 1-36e |
| `old_margin_le` | `BF4ExactSlabFacePatchGeneratorBound.lean:48` | New margin dominates the old one |
| `generator_square_lower` | `BF4ExactSlabFacePatchGeneratorBound.lean:57` | New estimate on every original completed state |
| `expandedNome_margin_separation` | `BF4ExactSlabFacePatchGeneratorBound.lean:80` | Exact positive-new/negative-old witness at 1/40 |
| `expandedNome_generator_square_lower` | `BF4ExactSlabFacePatchGeneratorBound.lean:87` | Actual positive bound, all extents and late cutoffs |
| `coefficient` | `BF4ExactSlabFacePatchUniformCoercivity.lean:39` | Explicit (1-36e)/2, no extent or cutoff argument |
| `volume_uniform_centered_coercivity` | `BF4ExactSlabFacePatchUniformCoercivity.lean:129` | EVERY original completed centered input |
| `expandedNome_centered_coercivity` | `BF4ExactSlabFacePatchUniformCoercivity.lean:161` | Fully supplied positive instance at 1/40 |
| `volume_uniform_reverse_energy` | `BF4ExactSlabFacePatchUniformCoercivity.lean:191` | Same balanced original conditional sweep |
| `coupled_auxiliary_reverse_energy` | `BF4ExactSlabFacePatchUniformCoercivity.lean:205` | Actual c-dependent auxiliary at every order |

The existing coefficient-parametric covariance consumer is
`BF4ExactSlabChebyshevCovarianceBound.finiteCovariance_sq_bound` at
`lean/YMGap/Continuum/BF4ExactSlabChebyshevCovarianceBound.lean:102`.
It additionally requires supported original observables, grow(16*n)
separation, c>=0 and positive Chebyshev denominator. Its legacy fixed-coefficient
wrapper has not been changed; this report does not claim it automatically
uses the improved coefficient.

## Why the search changed direction

Source review, not a new theorem: support-local original coercivity and its
application to actual growing Chebyshev auxiliaries already exist in
`BF4ExactSlabLocalSupportCoercivity.dense_local_coercivity`,
`BF4ExactSlabCompletedLocalSupportCoercivity.completed_local_coercivity` and
`BF4ExactSlabLocalAuxiliaryCoercivity.auxiliary_coercivity`. Their whole-cone
cost is not useful asymptotically: the checked
`BF4ExactSlabLocalChebyshevObstruction.factor_approaches_one` at
`lean/YMGap/Continuum/BF4ExactSlabLocalChebyshevObstruction.lean:203`
records the loss. Another support-local wrapper would not fix this.

Also, `GNSChebyshevEnergy.state` at
`lean/YMGap/Continuum/GNSChebyshevEnergy.lean:76` starts from (x,0), and its
first auxiliary is x. Restricting a reverse-energy claim to all auxiliary
orders but allowing every source is not automatically a smaller problem.
The present work instead proves a previously missing collective face-patch
join and supplies it with an actual, quantitatively stronger producer.

## Open analytic input and boundaries

The conditional consumer `generator_square_lower_of_collective_patch`
requires an actual same-action aggregate lower bound; it does not produce
one outside the checked small-nome regime. A useful such bound on a justified
scaling family, or a justified larger-patch alternative, remains open. Neither
the new counting constant nor a succession of larger fixed small nomes is a
continuum trajectory. Shared-face form comparisons alone do not supply the
required conditional operator estimate.

This local-to-global machinery is group-agnostic; the supplied pair estimate
and finite instance use the original SU(2) construction and explicitly
nome-dependent guards. No beta-uniform physical mass bound is claimed.
OS/physical-time comparison, nontrivial continuum survival, finite mass,
full QFT and every compact simple group remain open. No canonical chart
node has changed, and no ASCII chart was reprinted.

## Verification boundary

Eight final focused checks passed, serialized through the safe launcher with
one worker, 20 GiB hard ceiling, 12 GiB operating-system reserve and automatic
pressure/swap monitoring. Each completed within its initial tool call; no
live-build polling loop was needed. All 53 printed axiom gates stay within
{propext, Quot.sound}; some are axiom-free. No new sorry, native decision
oracle, custom axiom or analytic premise was introduced, and no old sorry or
canonical frontier field was discharged or weakened.

The final logs are `/tmp/ym-collective-patch-budget-20260930.log`,
`/tmp/ym-gns-patch-energy-20260930.log`, and
`/tmp/ym-face-patch-{incidence,size,energy,small-nome,generator-bound,uniform-coercivity}-20260930.log`.
These are focused file checks with dependency artifacts, not a current full
root build, full-tree audit or guard run. Root imports were registered;
no broad verification is claimed. Independent source review covered signed
pair counting, original-action scope, the covariance consumer and the
noncircular use of chronological coercivity solely for descent-tail removal.
