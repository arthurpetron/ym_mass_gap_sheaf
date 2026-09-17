# Exact active spatial action and original temporal energy

Date: 2026-09-17 UTC. Parent checkpoint: `0b76bcb`.

Whole-project goal: for every compact simple group, constructive nontrivial
continuum Yang--Mills on R^4 with same-theory QFT axioms, isolated vacuum
and a strictly positive finite physical Hamiltonian mass gap. This remains
OPEN. The present result is a finite, exact action/transfer/energy identity.

## What is proved

Let F be the inactive fringe coordinates of the existing slice carrier,
V its complete spatial heat product, and V_A the SAME finite heat product
restricted to faces whose four links all have active kinetic indices.
The original face order and each retained heat factor are unchanged.

For every supported fringe-independent q,

    H[V*q] = H[V_A*q].

For every supported q, without fringe independence,

    H[(P_F V)*q] = H[V_A*q].

These are Haar-tested identities. No raw free-polynomial equality is
claimed. The proof first constructs a free original link for each removed
face: the link is fringe and belongs to no other spatial face. All positive
spins cancel at that link against the entire other factor product, leaving
the normalized spin-zero factor one. A finite induction retains every
other face and the insertion throughout the removal.

Let P be the original kinetic product map, T=P V and T_A=P V_A. For
supported f,p with f fringe-independent,

    H[p*T(f)] = H[p*T_A(f)].

The test p need not be fringe-independent. The proof uses the symmetry of
the literal original kinetic kernel: P(p) is fringe-independent, so the
full spectator f*P(p) is eligible for spatial cancellation. It does not
replace the original transfer by link-variable heat-bath dynamics.

Finally retain the ORIGINAL messages g_n=T^n1 and t=g_(n+1). For supported
fringe-independent b,c the new identities give

    H[nu*b] = H[V_A*g_n*t*b],
    <b,c>_nu = H[V_A*g_n*t*b*c],
    E_gn(b) = H[V_A*g_n*t*b^2] - H[V_A*(g_n*b)*T_A(g_n*b)].

There is no new reduced-message sequence, stationary normalization or
limit argument. This is the explicit interacting energy left by the
previously proved centered fringe decomposition.

## Checked declaration map

All paths below start at `lean/YMGap/Continuum/`.

| Result | Declaration and source |
| --- | --- |
| Active indices are exactly spatial links at strictly interior bases | `active_index_iff`, `BF4ExactSlabFixedSpatialFringeFaceGeometry.lean:54` |
| Decidable full-face activity | `FullyActive`, `BF4ExactSlabFixedSpatialFringeFaceGeometry.lean:82` |
| Any inactive incident link belongs to no other spatial face | `inactive_incident_unique`, `BF4ExactSlabFixedSpatialFringeFaceGeometry.lean:129` |
| Actual Type-level free-link witness by finite edge search | `fringeFaceLeaf`, `BF4ExactSlabFixedSpatialFringeFaceGeometry.lean:165` |
| Complete heat prefix has no dependence on a link absent from its face | `heatFace_independent`, `BF4ExactSlabFixedSpatialFaceIndependence.lean:138` |
| Complete ordered spectator product retains that independence | `heatProduct_independent`, `BF4ExactSlabFixedSpatialFaceIndependence.lean:168` |
| Actual fixed-slice ordered plaquette is pinned to four distinct coordinate blocks | `plaquette_fourWord`, `BF4ExactSlabFixedSpatialFaceSelection.lean:61` |
| Any selected edge cancels every positive spin against an independent supported spectator | `character_haar_zero`, `BF4ExactSlabFixedSpatialFaceSelection.lean:91` |
| Full finite heat factor removes exactly to one | `heatFace_haar_remove`, `BF4ExactSlabFixedSpatialFaceSelection.lean:155` |
| The retained face list and unchanged product | `activeSpatialFaces`, `activeSpatialWeight`, `BF4ExactSlabFixedSpatialActiveSpatialWeight.lean:58`, `:62` |
| Exact whole-product cancellation | `spatialWeight_haar_active`, `BF4ExactSlabFixedSpatialActiveSpatialWeight.lean:130` |
| Existing conditional mass, tested against arbitrary supported q | `spatialFringeMass_haar_active`, `BF4ExactSlabFixedSpatialActiveSpatialWeight.lean:140` |
| Same kinetic map with the exactly integrated spatial action | `activeTransfer`, `BF4ExactSlabFixedSpatialActiveTransfer.lean:55` |
| Literal kinetic map is Haar symmetric | `kineticMap_symmetric`, `BF4ExactSlabFixedSpatialActiveTransfer.lean:72` |
| Tested ORIGINAL transfer equality on the active subspace | `original_transfer_haar_active`, `BF4ExactSlabFixedSpatialActiveTransfer.lean:87` |
| Original marginal mean and pairing with both original terminal messages | `marginal_mean_active`, `marginal_pair_active`, `BF4ExactSlabFixedSpatialActiveEnergy.lean:69`, `:93` |
| Original active energy, not an auxiliary dynamics | `energy_active`, `BF4ExactSlabFixedSpatialActiveEnergy.lean:129` |

The finite-selection proof uses the existing all-spin theorem
`any_slot_zero`, `lean/YMGap/Continuum/SU2QuaternionOrientedWordSelection.lean:128`.
Distinctness of the four original coordinates and their ordered quaternion
word are proved in the new fixed-slice module, not presumed from a different
ambient carrier. Product peeling consumes the original spatial face list's
`spatialFaces_nodup`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFacePlacement.lean:172`.

## Parameter and proof-status boundary

All rational nomes, every finite cutoff, width and terminal depth are
admitted by these identities. Positivity is unnecessary for cancellation;
this does not assert a positive heat weight for arbitrary nome/cutoff.
The positivity guards on the earlier norm/energy inequalities are unchanged.
All-nome identities are NOT coupling-uniform lower bounds.

Spatial locality of V_A is established for this particular geometry. It
does not establish locality, clustering or small influence of T^n1.
The arbitrary Haar-test clause for P_F(V) is not raw coefficient equality;
the transfer clause requires a supported fringe-independent input.
No completed projection, reconstructed operator, physical mass calibration,
continuum limit or new group realization is inferred.

## The next mathematical obstruction

A parallel coordinate review derives the following from `active_index_iff`,
the actual face membership criterion `spatialFaces_mem_iff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFacePlacement.lean:98`, and
the literal `edgesOf` definition,
`lean/YMGap/Continuum/ClusterCount4DProgress.lean:147`:
under spatial-face membership, full activity additionally requires
x+1<width,y+1<width for p01; x+1<width,z+1<width for p02; and
y+1<width,z+1<width for p12. Thus the retained faces form the cubical core;
width two already retains the six faces of a cube. This coordinate
characterization and the no-further-free-link conclusion are source-review
deductions, NOT additional newly checked declarations in this checkpoint.

The existing cubical incidence result is
`unitCubeFaceIncidenceCount_two_of_mem`,
`lean/YMGap/Continuum/Z4UnitCubeHaarSectorBridge.lean:90`.
The planned route does not assert that repeatedly applying the new fringe
lemma will remove this interacting core.

The quantitative target remains a lower bound on the exact active energy
above in its same centered norm. One existing route is
`actualResidual_corrected_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:294`, which gives

    h*<b,S>_nu^2 <= E_gn(b)*(h*||S||_nu^2 + D + 2hR)

for its actual ORIGINAL-marginal weighted residuals and finite correction
degrees. A controlled construction with S approximating b and a signed
budget D+2hR<=C(w)*||b||_nu^2, with the width/depth/cofinal-cutoff control
needed by the route, is still OPEN. Nome dependence must remain explicit.
The signed determinant is `messageDeterminant`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLinkDual.lean:141`;
its actual weighted pairing is `determinantCross`, same file:171.
No per-link centering, active-only approximation budget or determinant
estimate is supplied merely by this action reduction.

An isolated cube integral does not bound its full terminal-dependent
spectator. The existing whole-product floor cannot be declared spatially
uniform: `mixFraction_le_width_power` and `no_width_uniform_computed_rate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRateWidthObstruction.lean:74`,
`:132`, record that particular rate's width obstruction. This does not
refute a stronger signed estimate. Do not add a new assumed coercivity
interface in place of proving that estimate or a valid alternative.

## Verification

Six final focused serialized checks passed through the monitored launcher,
one worker, unchanged 20 GiB ceiling and fresh process/swap preflight.
All 31 gates stay within {propext, Quot.sound}; one is axiom-free. Final
logs have no warnings, errors, sorryAx or classical dependencies.
An intermediate geometric omega proof brought in Classical.choice through
a negated conjunction. It was replaced by explicit decidable coordinate
cases, and the final gates pass. This was not accepted as a constructive
proof. Minor namespace/congruence-call corrections were also rechecked.

Independent read-only review passed the complete-spectator peeling,
tested conditional-mass equality, original kinetic adjoint argument,
parameter scope and surviving active obstruction. The final same-energy
consumer was additionally kernel-checked. Six semantic-root imports were
added; root/full-tree/full-audit/guard NOT run. No sorry introduced or
discharged, canonical frontier changed, CI enabled or safety limit raised.

Final local logs (not repository artifacts):

| Log under `/tmp/` | Gates | SHA-256 |
| --- | ---: | --- |
| ym-fringe-face-geometry-20260917.log | 6 | `0255c20016d7f8f083b995d72afd1dd7f2afad2fea36349cb8350842472638af` |
| ym-face-independence-20260917.log | 6 | `7e6adcb34cefdeadf013cc7f823fd9a952254b110baaa44f1cb12cc47b2764ec` |
| ym-face-selection-20260917.log | 4 | `33ae283cbcd9b32b823aa4355d0eeb18e943171f626920e1eb5454f2ea42bf14` |
| ym-active-spatial-weight-20260917.log | 7 | `c6125b9ed9b8a1df88098f44af9251ead995f894f720d6c5f091e03eb764fb72` |
| ym-active-transfer-20260917.log | 4 | `32f55fb12446f7d46902361892b43d9ee86992446d4f7318c2b3924d7bf5639f` |
| ym-active-energy-20260917.log | 4 | `6c4d39df87bde486ff5242df77c165bfa0652d77bad068ccdd72c47d3b826de8` |
