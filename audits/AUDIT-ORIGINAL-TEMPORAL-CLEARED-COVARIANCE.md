# The original temporal defect is a full-weight conditional covariance

Date: 2026-09-17 UTC. Base revision: `ed5d1f3`.

Whole-project goal: nontrivial continuum Yang--Mills on R^4 for every
compact simple gauge group, with same-theory QFT and a positive physical
Hamiltonian mass gap, constructively within {propext, Quot.sound}. OPEN.

## Exact mathematical result

Write m(f)=H[V*f], g=T^n1, p=g*Tg and Z=m(p), using the existing original
spatial weight, transfer and terminal message. For signed probes r,s set

    N(r,s)=m(p*r*s),  J(r,s)=m((g*r)*T(g*s)),  B(r)=m(p*r),
    C_delta(r,s)=Z*(N(r,s)-J(r,s))-delta*(Z*N(r,s)-B(r)*B(s)).

`clearedDefect`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:62`,
defines this quantity without a bound or centering hypothesis.
`combinedTest`, same file:71, constructs

    F_s=Z*(1-delta)*(Tg)*s-Z*T(g*s)+delta*B(s)*(Tg).

`clearedDefect_pairing`, same file:96, proves

    C_delta(r,s)=H[(V*g)*r*F_s].

The algebra retains the negative transfer term and the marginal-mean
correction. Neither positivity nor support nor transfer symmetry is needed
for this identity. In particular, conditional weighted centering does not
silently become centering against the odd temporal marginal.

The actual residual is `terminalResidual`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalDirichletCoercivity.lean:104`:
with a=V*T^n1 it is R_i=P_i(a)*f-P_i(a*f).
`terminalResidual_clearedDefect`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:158`,
proves the full original-action pin

    C_delta(R_i,s)=H[P_i(a)*P_i(a*f*F_s)-P_i(a*f)*P_i(a*F_s)].

The only integration premise is i<N, where N is the actual base-link carrier
length. The proof reuses `weightedResidual_pairing`,
`lean/YMGap/Continuum/SU2QuaternionWeightedBlockCentering.lean:77`, and
`project_mean`,
`lean/YMGap/Continuum/SU2QuaternionHaarBlockProjection.lean:204`.
It adds the formerly missing original temporal-form identification, not a
replacement generic response identity. No source-dependent factor is removed.

## Exact existing consumer

`clearedDefect_diagonal_nonnegative_iff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:175`,
proves that C_delta(f,f)>=0 is exactly

    delta*(Z*N(f,f)-B(f)^2) <= Z*energy(g,f).

Here `energy` is the original definition in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:63`.
The equivalence needs no positive-Z assumption because no division occurs.
`terminal_existing_fraction_nonnegative`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:187`,
recovers the known instance from `terminal_energy_variance_floor`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletCoercivity.lean:242`.
It retains all of that theorem's support, late-cutoff and nome hypotheses.
The fraction is still `mixFraction`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferMixingRate.lean:81`,
with its width dependence. No improved rate has been produced.

## What this changes about the next proof

The analytic target is now a checked conditional HAAR determinant with full
weight Vg and full polynomial F_s. It is not a covariance of two fundamental
traces under an isolated relative heat kernel.
`adjacent_shared_defect`,
`lean/YMGap/Continuum/SU2QuaternionAdjacentPlaquetteHeat.lean:326`,
cannot be substituted directly: its quadratic source insertion and retained
test have different dependence from F_s, which contains T(g*s) and Tg.
Using those shared-heat channels still requires a further action-specific
reduction retaining every source/output dependence.

The quantitative signed estimate, the weighted global decomposition and
a spatially uniform summation budget remain OPEN. The new equalities do
not certify a smaller full-source remainder, a nonnegative cross term,
transfer invariance of a sector, or a completed/scaling gap. Physical mass
calibration, continuum QFT and the every-group quantifier remain open.

## Verification

The final focused source check passed through `scripts/safe_lean_build.py`,
one worker and 20 GiB, after a fresh process/swap preflight. No competing
compiler/runner was observed; swap was unchanged at 6669.00 MiB. All six
printed declarations depend only on {propext, Quot.sound}. The final log
contains no error, warning or sorryAx. Initial parser and namespace mistakes
were repaired without changing the theorem statements or raising limits.
Independent mathematical and source reviews confirmed the normalization,
mean term, integration hypotheses and exact diagonal consumer.

No sorry, new axiom, canonical frontier field or analytic guard was changed.
Root import added; root/full-tree/full-audit/guard NOT run. CI remains
manual-only. No literature scan occurred.

Log: `/tmp/ym-fixed-spatial-cleared-covariance-20260917.log`.
SHA-256: `747b2ea85d21cfa571c90d599112bcb041fd92ff82dfa1290b2ea05fcb042601`.
