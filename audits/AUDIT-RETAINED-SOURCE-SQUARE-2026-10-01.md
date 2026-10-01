# Retained source square in the original plaquette energy bound

Date: 2026-10-01 UTC. The original Young energy estimate now keeps an
explicit source-dependent lower bound for its favorable discarded term.
The complete projected terminal source, heat kernel and original odd
partition are unchanged. This is an unconditional finite estimate with
its cutoff guards, not the missing relative energy/variance scaling bound.

## Mathematical estimate

Let f be the actual fundamental plaquette character, q the complete
projected endpoint source, and P the full product heat. Write H for product
quaternion Haar integration and Delta for the difference between two slices.
The existing source-Young identity is

    4*E + D = 2*C,
    D = H_xy[K(x,y) (Delta q * Delta f)^2].

The product heat has total mass one. Its exact plaquette action is
P f = w^12 f in supported Haar pairings. Hence

    H_xy[K * Delta q * Delta f] = 2*(1-w^12)*H[q*f] = J.

Cauchy--Schwarz against the constant function gives D>=J^2 and therefore

    4*E + J^2 <= 2*C.

The final theorem divides all terms by the SAME positive original odd
partition Z. It neither replaces q*Pq by q^2 nor erases the terminal factors.

## Checked declarations

`SU2QuaternionProductHeatJumpMean.productHeat_mass_one`
(`lean/YMGap/Continuum/SU2QuaternionProductHeatJumpMean.lean:54`)
and `jump_mean` (line 72) prove the generic finite identities. Their
algebraic statements require a valid duplicate-free heat-index list, but
no nome positivity assumption.

`BF4ExactSlabFixedSpatialSourceYoungCancellation.sourceResponse`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceYoungCancellation.lean:64`)
is the actual rational J, not a supplied witness for a desired estimate.
`plaquette_jump_mean` (line 68) pins it using the original w^12 image.
`sourceIncrement_ge_response_square` (line 93) proves J^2<=D from the
constructed positive heat certificate. The guards are 0<w<1,
headCutoff(w)<=K, K>=1 and literal spatial-face membership.

`padded_terminal_energy_retained_square` (line 123) supplies the actual
projected terminal source and strict spatial padding, with K>=2 for the
existing explicit channel cost. `padded_terminal_normalized_retained_square`
(line 145) retains the original Z and normalizedEnergy.

## What remains open

J^2 is nonnegative but is not proved positive for the complete terminal
source. Thus strict improvement over the previous raw Young ceiling is
not asserted for that source. H[q*f] is a ONE-copy Haar moment, not the
interacting mean or variance under q*Pq. The known positive centered
two-endpoint response is a different quantity and cannot fill this gap.

No comparison bounds the remaining channel cost minus this square by
physical time times the SAME interacting variance. In particular, the
explicit factor (1-w^12)^2 does not alone establish the size of J^2/Z,
because q and Z depend on the parameters. Cutoff, depth, spatial and physical
spacing control remain separate; continuum survival and Clay remain open.

Read-only trial-source review also found no supplied low-energy producer
from temporal averaging or widening coefficients alone. Their existing
norm/energy estimates do not establish a vanishing energy/variance ratio.
This review is not a new impossibility theorem for either family.

At this checkpoint, the next reviewed, NOT kernel-checked candidate used the test
(q_x+q_y)*(f_x+f_y). The product with Delta q*Delta f is
Delta(q^2)*Delta(f^2). With A=H[q^2] and F=H[q^2*f^2], the exact
label-two heat image suggests mean 2*(1-w^32)*(F-A); the existing
character square cap gives a route to test norm at most 64*A. This would
yield 64*A*E+(1-w^32)^2*(F-A)^2<=32*A*C, without any response reciprocal.
The linear and quadratic test squares may NOT be added without proving
their joint Gram/orthogonalization estimate. This candidate still requires
the separate SAME interacting variance comparison.

Subsequent checkpoint: this quadratic test and its normalized energy
consumer are now checked. See
`audits/AUDIT-QUADRATIC-SOURCE-CANCELLATION-2026-10-01.md` for the exact
declarations and remaining source-moment input.

## Verification boundary

Two final focused checks passed six printed gates, all exactly
{propext, Quot.sound}. No sorry, new axiom, Classical dependency,
native_decide, noncomputable declaration or canonical field was introduced.
The main agent alone compiled; a parallel reviewer checked the identity,
complete-source normalization and limits of the inferred improvement.

The safe-build procedure used one worker, a 20 GiB worker ceiling, 12 GiB
OS reserve and dynamic pressure monitoring. Preflight found no competing
compiler/runner and reported 89% memory free. No full root build, tree
audit or guard was run. Root imports were registered but not compiled
as an aggregate. No canonical chart state changed or was reprinted.

Final log SHA-256 values, under `/tmp/`:

- `ym-product-heat-jump-mean-20261001.log`:
  `f12746438e664b39c3e41883a81914d6b045b61e58ff6bccae6b39dc707a43fc`.
- `ym-source-young-cancellation-20261001.log`:
  `6a7a7fc7be7c776c77a78a1d333ca6255ee8c31049691b8f7283fc26eac0617d`.
