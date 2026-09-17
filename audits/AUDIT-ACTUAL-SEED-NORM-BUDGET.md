# Actual finite-degree seed norm budget — 2026-09-17 UTC

## Whole-project goal and scope

The goal remains constructive continuum Yang--Mills on R^4 for every compact
simple gauge group, with the required same-theory QFT structure, nontrivial
state space, isolated vacuum and finite positive physical mass gap. This
checkpoint is a finite-regulator SU(2) estimate on the original Haar carrier.
It does not establish the regulator-uniform signed cost or close a Clay node.

The new estimate is

    ell * sum_i ||q_i||_nu^2 <= H[(nu*Phi)^2] <= u*||Phi||_nu^2,
    ell * D <= (U-h) * (u*||Phi||_nu^2).

Here nu is the original odd marginal; Phi=H[nu]*f-H[nu*f]; ell,u are
the existing finite density window; q_i are the actual produced tests;
D is the diagonal remainder of the existing temporal-energy inequality.
The bounds have no coordinate-count or approximation-degree factor.
The density contrast u/ell still depends on nome, cutoff, width and depth.

## Exact objects and audit-driven plan correction

- Original density and pairing: `marginalWeight`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualMarginalDual.lean:75`,
  and `marginalPair`, same file `:78`.
- Partition-cleared target/source: `centeredObservable`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredHaarTelescope.lean:57`,
  `source`, same file `:62`; `piece`, same file `:66`.
- Actual finite inverse/seed/test: `inverse`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualSeed.lean:68`,
  `seed`, same file `:109`, and `test`, same file `:116`.
- Exact family and coordinate multiplicities: `familyTests`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeedFamily.lean:115`,
  and `labels_perm_range`, same file `:57`.
- Explicit window: `lower`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualMarginalWindow.lean:85`,
  and `upper`, same file `:127`.

These seeds use FULL nu, including on fringe-independent inputs. The
active-action equality `energy_active`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveEnergy.lean:129`, does
not identify these source-dependent polynomials with a family rebuilt from
the reduced action. `activeSeeds` and `correctedSum_active`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveSeeds.lean:45`, `:127`,
do not assert approximation after deleting inactive entries. No such
substitution is made in the new proof.

## Kernel-checked argument

Write m=P_i(nu), z=J_k*tau, M=P_i(nu*z), and q=m*z-M.

1. Exact integrated conditional Pythagoras gives
   H[nu*(m*z)^2]=H[nu*q^2]+H[m*M^2]. The last term is nonnegative by
   a constructed certificate. See `weightedResidual_pythagoras`,
   `lean/YMGap/Continuum/SU2QuaternionWeightedResidualNorm.lean:81`, and
   `weightedResidual_square_le`, same file `:95`.
2. The actual seed inverse has the sharp multiplier certificate
   1-(nu*m*J_k)^2. See `inverseMultiplierCertificate`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualSeedNorm.lean:60`.
   The certificate identity

       tau^2-ell*nu*(m*J_k*tau)^2
       = (1-(nu*m*J_k)^2)*tau^2 + nu*(nu-ell)*(m*J_k*tau)^2

   proves the scaled-input estimate; integrated centering then gives
   ell*H[nu*q^2]<=H[tau^2]. See `scaledSeedCertificate`, same file `:78`,
   and `test_norm_le`, same file `:114`. The latter needs no conditional
   zero-mean hypothesis on tau. No pointwise contraction of q is asserted.
3. The original ordinary-Haar terms obey exact Pythagoras, retaining the
   final projection square. See `telescope_pythagoras`,
   `lean/YMGap/Continuum/SU2QuaternionHaarBlockTelescopeNorm.lean:49`.
   Dropping only that certified nonnegative square gives
   `full_term_square_sum_le`, same file `:98`. This is not weighted
   orthogonality of inverse-density-conjugated residuals.
4. Sum the actual tests with their proved label permutation, then use
   the certificate nu*(u-nu)*Phi^2. See `family_norm_le_source`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeedNormBudget.lean:106`,
   `source_norm_le`, same file `:127`, and `family_norm_budget`, `:149`.
5. The second-stage multiplier d_i*G_i has square bound one; it therefore
   contracts each original-nu norm. Fringe entries are unchanged. See
   `corrected_norm_le`, same file `:160`, and
   `corrected_family_norm_budget`, `:186`. This holds for arbitrary finite
   component correction degrees, not just one common degree.
6. The existing diagonal remainder obeys D<=(U-h)*sum_i||corrected_i||^2;
   fringe coefficients 1-h are bounded using 1<=U. See
   `diagonal_norm_sum_le`, same file `:206`, and the resulting
   `diagonal_family_norm_budget`, `:247`.

The consumer is the SAME original temporal-energy inequality:
`actualResidual_corrected_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:294`, and its
actual-family specialization `approximant_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFamilyApproximation.lean:129`.
No link-update generator has been substituted for this energy.

## Exact next frontier

The approximation schedule is already constructed by `approximationDegrees`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFamilyApproximation.lean:86`,
with `approximation_bound`, same file `:94`. The required next estimate is
on the JOINT signed cost D+2hR along a sufficient constructed schedule,
relative to ||Phi||_nu^2 with an explicit vanishing approximation remainder
and the width/depth/cofinal-cutoff control needed by the chosen route.

Separate uniformity of the crude u/ell bound is not asserted or made a new
mandatory hypothesis. Bounding all determinant terms absolutely can discard
needed cancellation and introduce a family-size factor. Nor must a sufficient
joint estimate hold at every finite approximation degree. The existing
approximants converge to Phi, not f: retain their partition normalization
when connecting to an active observable. These corrections change execution
priorities, not the Clay target or a canonical frontier field.

The reviewer's reduced-cube coefficient-one obstruction remains an unchecked
candidate; it is not used as a theorem or a refutation of this estimate.

## Verification boundary

Four focused serialized checks used `scripts/safe_lean_build.py`, one worker
with a 20 GiB limit, and a fresh process/swap preflight before every invocation.
All 15 new gates report only `{propext, Quot.sound}`. Final logs have no
errors, warnings, `sorryAx` or classical dependency. No `sorry` was introduced
or discharged and no new analytic premise was added. Independent mathematical
and source review passed; its normalization/cancellation advice is reflected
in the live plan above.

The four modules are registered in `lean/YMGap.lean`. Root/full-tree build,
full axiom audit and guard were NOT run. CI, safety limits and canonical
frontier fields are unchanged. Logs:

- `/tmp/ym-weighted-residual-norm-20260917.log`
- `/tmp/ym-haar-telescope-norm-20260917.log`
- `/tmp/ym-actual-seed-norm-20260917.log`
- `/tmp/ym-seed-norm-budget-20260917.log`

Final log SHA-256, in the same order:

```text
cc644635714806b2d61194c27b8da73321ca3a715705d8c5c944ada3b4136b1d
3588c58778fd05f4d214f185d600ea48f74cd6b598d1ee3ef83e885f4267c5dd
6ba3a853da15408aeb457d469bc339cc2e76b9fe8d860f6dafd2cf1dee25b03a
7ad9201968537ec918ddf62ce0e8c47763efbeb2b7d8f188a79a8257f9e84f8d
```
