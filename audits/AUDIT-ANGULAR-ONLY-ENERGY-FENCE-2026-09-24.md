# Positive-source fence against discarding the signed remainder

2026-09-24 UTC. Follows `ef4d3d7`. The continuum Yang--Mills / Clay target
remains OPEN. This is a checked counterexample to a proposed generic finite
estimate, NOT a Yang--Mills counterexample.

## Actual data and exact calculation

In `lean/YMGap/Continuum/SU2QuaternionAngularOnlyEnergyFence.lean`, let
f be the literal fundamental character of quaternion block 0 and let
a=1+2*f^2. Use the ORIGINAL `sourceEnergy 1 w K [0] a f` and
`weightedAngularEnergy 0 a f`, at w=1/2 and K=3.

The source is one plus a nonnegative square with a positive coefficient;
`positiveSourceCertificate` supplies the explicit certificate. Both support
proofs and `sufficientCutoff half<=3` are checked. Exact kernel reductions give

    energy       = 97727/8192
    angular cost = 23
    (1-w)*cost   = 23/2 = 94208/8192.

Thus the energy exceeds the angular-only budget by 3519/8192>0.
`angular_only_energy_bound_false` proves the negation of the proposed bound
using those actual quantities, not detached scalar placeholders. In character
notation a=3*chi_0+2*chi_2; the corresponding arithmetic is
E=15+14*w^8-25*w^3-4*w^15. This explanation is not used as a proof oracle.

## What this changes -- and what it does not

The generic implication from the exact signed Taylor identity to
`E<=(1-w)*angularCost` is false, even with this positive source. Neither
positivity of the remainder form nor positivity of the source fixes the sign
of `R(a,a*f^2)-R(a*f,a*f)`. The checked bounds RETAINING remainder costs are
unchanged. This does not claim the chosen source is an interacting terminal
source or that the one-link observable is a 4D physical excitation.

The counterexample rules out coefficient one only. It does not prove any
larger uniform constant, and numerical finite searches do not establish one.

Source review also confirmed the existing independent absolute-loss route:
`BF4AllNomeCompletedPlaquetteIncrement.completed_loss_nome_bound`,
`lean/YMGap/Continuum/BF4AllNomeCompletedPlaquetteIncrement.lean:83`, bounds
loss on the SAME completed plaquette excitation by 192*n*(1-w).
The existing `family_joint_variance_floor`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilyVariance.lean:136`,
is width/face-count uniform at FIXED nome. Its weak changing-nome behavior
cannot be silently used for survival:
`sixHundred_floor_le_defect_power` at
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteAffineCalibrationObstruction.lean:75`
and `computedLossRatio_ge` at line 102 prove that the displayed certificate
ratio is at least 115200. `computedLossRatio_no_linear_scaling` at line 139
already blocks that certificate's proposed linear-spacing use. These are
existing results, not new checks or counterexamples to actual survival.

The next candidate is the actual positive-kernel Young identity
4E=2J-D, with J the one-end squared-source increment cost and D the
nonnegative squared source-increment correction. Its formalization and the
literal observable heat-image calculation are separate unfinished work at
this checkpoint. Useful SAME-variance control, ONE surviving excitation,
EVERY-vector scaling, SAME continuum/QFT/YM/UV, physical Hamiltonian mass and
every compact simple group remain OPEN.

## Verification boundary

Accepted check: `/tmp/ym-gap-angular-only-energy-fence-check-3.log`, through
`scripts/safe_lean_build.py --jobs 1 --check`, matching `.olean` output and
one 4 GiB worker. All seven gates stay within {propext, Quot.sound}; the
cutoff guard has no axioms. No errors, warnings or sorryAx in the accepted
log. No source sorry, native_decide, new axiom or analytic premise.

Two finite evaluations use scoped `maxRecDepth` 4096 and 8192. Memory limits,
OS reserve and worker count are unchanged; no safety interruption occurred.
Failed draft checks are not evidence. Semantic import added and a stale
second-moment status comment corrected. No full-root build/audit/guard or
canonical-field change. Independent Sol arithmetic review agreed with the
exact values before kernel verification.
