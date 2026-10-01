# Original source test norm and interacting variance

Date: 2026-10-01 UTC. The actual symmetric source-test norm now has an
exact reduction to the SAME original interacting variance and an explicit
signed source defect. The whole signed plaquette family supplies its heat
eigenimage geometrically. This is a finite-cutoff, finite-width and
finite-terminal-depth identity with an original energy consumer, not a
variance-relative scaling estimate or continuum theorem.

## Exact norm and original centering

Let H be one-slice Haar, P the full product heat, and
q=P_fringe(V*g_depth) the complete original projected terminal source.
The original odd weight is W=V*g_depth*g_(depth+1), with partition Z.
For a supported fringe-independent f, compute c=H[W*f]/Z and psi=f-c.
Use the original two-slice heat pairing and write

    r=(q_x-q_y)*(f_x-f_y),  s=(q_x+q_y)*(psi_x+psi_y),
    D=<r,r>,  J=<r,1>,  M=<s,1>,  X=<r,s>-J*M,
    U=H[q^2*psi*Ppsi],  S=<s,s>.

`SU2QuaternionProductHeatSumNorm.sumTest_norm_pin`
(`lean/YMGap/Continuum/SU2QuaternionProductHeatSumNorm.lean:123`)
reduces the generic norm using both heat marginals and symmetry.
`SU2QuaternionProductHeatSourceCentering.sourceIncrementCost_shifted`
(`lean/YMGap/Continuum/SU2QuaternionProductHeatSourceCentering.lean:82`)
proves that subtracting c leaves D unchanged. Its padded two-slice jump
pin is `jump_shifted`, same file, line 45.

`BF4ExactSlabFixedSpatialSourceVarianceGram.centered_source_square`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceVarianceGram.lean:89`)
identifies the source moment of psi^2 with Z*Var_odd(f), using the original
partition, mean and marginal pins. `centered_sum_norm`, same file, line 145,
therefore proves

    S = D + 8*U + 8*Z*Var_odd(f).

This is not a raw q^2 variance or a new source law. The actual center is
`oddCentered`, same file, line 69; it is not assumed to center H[q^2*f].

## Whole signed family and retained defect

If Pf=lambda*f in supported Haar equivalence, define

    C_psi = H[q*psi^2*(Pq-q)],  R_psi=H[q^2*psi],
    delta = lambda*C_psi + (1-lambda)*c*R_psi.

`SU2QuaternionProductHeatCenteredMixed.centered_mixed_pin`
(`lean/YMGap/Continuum/SU2QuaternionProductHeatCenteredMixed.lean:107`)
retains both terms. `BF4ExactSlabFixedSpatialSourceVarianceDefect.sourceNormDefect`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceVarianceDefect.lean:79`)
is this explicit delta, and `centered_mixed_defect_pin`, same file, line 91,
proves U=lambda*Z*Var_odd(f)-delta.

`BF4ExactSlabFixedSpatialFamilyHeatEigen.spatialSpan_fullRange`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyHeatEigen.lean:42`)
supplies lambda=w^12 for the actual complete signed plaquette family,
including repeated faces and arbitrary signed coefficients, at K>=1.
Strict padding supplies fringe independence in the concrete consumer
`padded_family_test_norm_defect`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceVarianceDefect.lean:170`):

    S = D + 8*(1+w^12)*Z*Var_odd(f) - 8*delta.

All family cross terms remain inside the literal norm and variance.
Cutoff, width, terminal depth, nome, faces and coefficients remain explicit.
No sign, smallness, stationary-source or variance-floor premise is added.

## Original energy consumer and remaining input

`original_centered_energy_budget`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceVarianceGram.lean:208`)
applies the existing exact source-Young identity and centered joint Gram
inequality. `padded_family_energy_defect_budget`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceVarianceDefect.lean:194`)
supplies the geometric family pin and proves, with K=S-M^2,

    4*K*E + K*J^2 + X^2 <= 2*K*C.

E is the original temporal energy and C the original single-ended cost.
`centered_denominator_nonnegative`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceVarianceGram.lean:175`)
proves K>=0. Neither K nor a source norm is inverted. K need not be positive,
and X and J need not supply a strict improvement. The complete defect,
responses and cost still need estimates relative to the SAME interacting
variance on a justified physical scaling family. The exact norm identity
alone does not provide those estimates.

## Source review and next mathematical direction

This paragraph records source review, not additional kernel-checked theorems.
`oddMoment_eq_active_plaquette_channels`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChannelActiveMoments.lean:146`)
retains spectator heat in actual one-plaquette moments. By contrast,
`channelSourceMass_le_raw`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChannelGeometricContraction.lean:261`)
is only a one-sided contraction to the raw q^2 norm, not its equality with
the interacting channel norm. Those declarations do not identify the raw
q^2 terms in delta with spectator-heat-preserving channel terms.

The next estimate must retain that difference, or use the already supplied
spectator-preserving energy budget and its appropriate tests. A four-link
single-face channel theorem does not cover cross terms of an arbitrary
signed family: their active links must be retained too. No stationary
terminal-source replacement or volume-uniform raw-norm/partition ratio is
supplied by this milestone. Do not rebuild the existing channel decomposition
or add another equivalent conditional survival wrapper.

Physical spacing/time calibration, nontrivial continuum survival, uniform
every-state physical decay, canonical limiting OS/observable identification,
full QFT and every compact simple group remain OPEN. No displayed canonical
node changed, and the unchanged ASCII chart is not reprinted.

## Verification boundary

Six final focused checks passed all 20 printed gates, each exactly
{propext, Quot.sound}. The monitored launcher used one worker, a 20 GiB
worker ceiling, a 12 GiB OS reserve and dynamic pressure telemetry.
Preflight found no competing compiler/test/runner and 91 percent memory free.
The centered-mixed check has one unused-argument warning, not a proof hole.
Intermediate namespace and elaboration errors were corrected before the
accepted final checks. Sol supplied the generic arguments and family
eigenpin; main constructed the original variance and energy consumers.
Independent Sol and Luna reviews checked the mathematical scope.

No new sorry, axiom, Classical dependency, native_decide, noncomputable
declaration, canonical field or chart change. No full root/tree build,
axiom audit or guard was run. Root imports were registered after the
targeted checks and were not compiled as an aggregate.

| Final log under /tmp | SHA-256 |
| --- | --- |
| ym-product-heat-sum-norm-final-20261001.log | 8792c4d81cbbf27a69dc035049b8990cbb62fcd437459a48d90488c57cff5ccc |
| ym-product-heat-source-centering-final-20261001.log | bb22b303754037933653669de01540731ea21f32615256cb1c628aa7adfcc008 |
| ym-original-source-variance-gram-final-20261001.log | 35be749214a8f2acab453eef467162b3f0721056742708cf37256a902f1d56ec |
| ym-product-heat-centered-mixed-final-20261001.log | d722f3a59fccf3fe95f9666d0173af9c81cffbcf671fd63693fe985c1f437ed9 |
| ym-family-heat-eigen-20261001.log | 9b58df5c721bfbd24553dfd44479c2e587be8f64da06519c733aba0e46ed85d4 |
| ym-original-source-variance-defect-20261001.log | ce8f33a8c91cf0dc8a0d15eb263c58b6634e58d01f485cd09e2b0d893d9a6f34 |
