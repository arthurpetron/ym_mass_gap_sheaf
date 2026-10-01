# Original signed-family energy versus interacting variance

Date: 2026-09-30. Scope: finite-cutoff, finite-width, finite-terminal-depth
SU(2), the complete signed plaquette family and the existing Wilson window.
This is an exact identity, NOT a relative estimate or continuum theorem.

## Actual geometric input

`blockCasimir_linear`,
`lean/YMGap/Continuum/SU2QuaternionBlockLinearCasimir.lean:39`, transports
the degree-one angular Laplacian eigenvalue -3 to any supported original
block, under arbitrary Haar insertions. For a genuine spatial plaquette,
exactly four distinct incident blocks contribute, and every spectator block
contributes zero. Thus the positive total Casimir is 12:
`plaquette_casimir`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCasimir.lean:141`.
`spatialSpan_casimir`, same file, line 292, extends it by coefficient
linearity to arbitrary signed coefficients and repeated faces. No bare
heat-eigenvalue identity is differentiated or substituted for this geometry.

## Complete-weight Ward identity and normalization

Let H be the original product-Haar functional, W=V*g_n*g_(n+1),
Z=H(W)=oddMass, f the whole signed family, and c=H(W*f)/Z. Write

    A = sum_(block,plane) H[W*(X f)^2]
    B = sum_(block,plane) H[(f-c)*(X W)*(X f)].

Every spatial factor and both terminal messages are differentiated in B.
Integration by parts and the actual Casimir action give

    A + B = 12*Z*Var_W(f).

Generic evidence: `block_ward`, `complete_ward_raw`, and
`complete_ward_own_mean`, respectively
`lean/YMGap/Continuum/SU2QuaternionWeightedCasimirWard.lean:186`, `:235`,
and `:257`. The generic eigenpin is supplied by the geometric theorem above
in the actual family consumer, not left as an analytic hypothesis there.

The original mass, mean and variance pins are `marginalMass_pin`,
`marginalMoment_pin`, and `marginalVariance_pin`, respectively
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceWard.lean:48`,
`:64`, and `:93`. `oddVariance`, line 87, is precisely the existing
middleRatio(n+1,n,f^2)-middleRatio(n+1,n,f)^2. No new density or partition.
`wardResidual`, line 105, retains the computed actual mean; its normalization
is line 111. `family_ward` and `family_normalized_ward`, lines 124 and 144,
apply the actual Casimir-12 producer without an additional spectral premise.

## Joined original temporal identity

For h=1-w, retain the previously proved angular-weight defect
D=sum_i H[q*(Pq-q)*Gamma_i(f)], q=P_fringe(V*g_n). The original Taylor
identity has E=h*A+R_mixed-R_diagonal-h*D. Therefore

    E/Z = 12*h*Var_W(f) + C,
    C = [R_mixed-R_diagonal-h*(D+B)]/Z.

`varianceRemainder` and `varianceRemainder_raw`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceTaylor.lean:42`
and `:49`, expose this complete signed correction. The energy identity is
`padded_family_energy_variance`, line 67. Strict padding supplies the required
fringe independence; the Ward identity itself does not require padding.
`finite_family_increment_variance`, line 101, pins twice this expression to
the EXISTING originalWindowScalar squared increment, at the unchanged
cutoff headCutoff(w)+stage and terminal depth. This is twice the transfer
Dirichlet energy, not the norm square of f-Tf.

All w, cutoff, width, terminal-depth, source and coefficient dependence
remains explicit in these functions. Only the geometric eigenvalue 12 is
constant. There is NO parameter-uniform estimate on C. The identity does
not prove C is small, nonnegative, or O(h^2). In particular XW includes
action/message derivatives and need not be a perturbatively small error.

## Verification boundary

Five final focused checks exited 0 through the monitored launcher, one
worker, 20 GiB worker cap, 12 GiB OS reserve, live memory telemetry and
300-second status setting. Preflight found no competing compiler/test/runner
and zero swap use. No safety limit changed. Two Sol agents supplied and
reviewed the independent generic/geometric arguments; main serialized all
compiler runs and constructed the original-marginal consumers. Independent
review confirmed the signs, exact normalization and the remaining upper-bound
direction for one-excitation survival.

All 20 printed gates report exactly {propext, Quot.sound}. No new sorry,
axiom, classical dependency, native_decide or frontier weakening. No full
tree/root build, audit or guard was run. Root imports were registered after
targeted verification; the large root file was not recompiled.

| Final log in `/tmp/` | SHA-256 |
| --- | --- |
| `ym-block-linear-casimir-20260930.log` | `eb8d6a3ad46dc84ddcc5db876aeba16550afb5d1cb40f17ca5785cb54f522434` |
| `ym-weighted-casimir-ward-20260930.log` | `3c236dedb7e56f4ffcc2f8dbdbc0c92bd1384f549b381c6413d9a66055955902` |
| `ym-family-casimir-20260930.log` | `8267f47ee6d12db7d68b8a290b7e98fbefc5f4b1b4d0029ad1a888b7be50fbe8` |
| `ym-family-variance-ward-20260930.log` | `b9140b2ae286e46c4c0a28a0827e1bb2974d06da46a8ddbf167b5fe7ec74b227` |
| `ym-family-variance-taylor-20260930.log` | `ffbd8782ecde16a00a72b0bb00352169790fe749acfe7f5219fd13c93f5c4e76` |

## Remaining mathematical input and consumer

This branch needs a useful UPPER bound on the actual energy relative to the
SAME interacting variance on one justified scaling family. The new exact
formula exposes its combined signed correction; it does not prove that
upper bound. A lower coercivity estimate belongs to the every-state gap
branch and does not replace the survival input.

The immediate checked consumer is the existing finite Wilson window above.
After valid limit/scaling control, the existing conditional source/domain
transfer uses an upper relative energy bound: `relative_norm_retention`
and `relative_derivative_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomeSectorSourceTransfer.lean:104` and
`:116`. Their hypotheses are not supplied by this milestone. No additional
equivalent survival wrapper is needed.

Physical spacing/time calibration, scaling survival, uniform every-state
decay, physical reflected OS identification, continuum QFT and every compact
simple group remain OPEN. No canonical displayed node changed; no ASCII
chart is reprinted.
