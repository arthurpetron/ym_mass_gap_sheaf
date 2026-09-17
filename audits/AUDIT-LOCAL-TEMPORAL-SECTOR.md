# One-factor local coercivity in the original temporal norm

Date: 2026-09-17 UTC. Base revision: `6b09535`.

Whole-project goal: construct nontrivial continuum Yang--Mills on R^4 for
every compact simple gauge group, with the required same-theory QFT structure
and positive physical Hamiltonian gap, within {propext, Quot.sound}. OPEN.

## Mathematical change

The previous all-observable comparison has a computed fraction at most
32^(-width): `mixFraction_le_width_power`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRateWidthObstruction.lean:74`.
The new estimate avoids that product loss on a stated conditional sector.
It does NOT upgrade the old all-observable fraction.

Let P_i be the existing conditional Haar projection. The polynomial

    R = P_i(a)*f - P_i(a*f)

is constructed by `weightedResidual`,
`lean/YMGap/Continuum/SU2QuaternionWeightedBlockCentering.lean:33`.
`project_weightedResidual_zero`, same file `:57`, proves P_i(a*R)=0
coefficientwise without support, positivity or inverse premises.
`weightedResidual_pairing` at `:77` and `weightedResidual_quadratic` at
`:99` prove the exact conditional covariance identities; in particular

    P_i(a*R^2) = P_i(a) * (P_i(a)*P_i(a*f^2) - P_i(a*f)^2).

The extra mass P_i(a) is retained. R is a scaled residual, not an asserted
normalized conditional projection.

## Cancellation and one-factor comparison

Use the full product heat K_i*K_rest, complete endpoint weights a_0,a_1,
and e=K_i*K_rest*a_0*a_1. Write e'=K_rest*a_0*a_1. For P_i(a*f)=0,
`erased_cross_zero`,
`lean/YMGap/Continuum/SU2QuaternionWeightedProductLocalGap.lean:98`, proves
H[e'*f_0*f_1]=0. Every other heat factor and both endpoint weights remain.
The remaining factors must omit the selected lower slot.
`erased_jump_eq_diagonal`, same file `:137`, gives

    H[e'*(f_0-f_1)^2] = H[e'*(f_0^2+f_1^2)].

The positive certificates for K_i-headFloor and prefixCap-K_i, multiplied
by the entire certified remaining density and actual squares, prove

    headFloor(w)*H[e*(f_0^2+f_1^2)]
      <= prefixCap(w)*H[e*(f_0-f_1)^2].

This is `local_energy_floor`, same file `:220`.
`local_energy_floor_of_mem` at `:310` proves it for a selected member of
the unchanged original list. Constructive Nat-list selection, permutation
of the polynomial product and Nodup ensure exactly one factor is erased;
no classical selection is used.

## Same original action and terminal message

`local_sector_coercivity`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalDirichletCoercivity.lean:77`,
sets a=V*g and uses the ACTUAL activeBlocks factorization. Its premise
i in activeBlocks excludes invented heat factors at fringe coordinates.
The original edge diagonal identity is `edge_diagonal_identity`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:181`;
the squared-jump identity is `energy_identity`, same file `:253`.
They identify the two integrals above with twice the original marginal
quadratic form and twice the original energy, respectively. Cancelling 2:

    headFloor(w)*m(g*Tg*f^2) <= prefixCap(w)*energy(g,f),
    provided P_i(V*g*f)=0.

Here T=K V, m(p)=H[V*p], and
energy(g,f)=m(g*Tg*f^2)-m((g*f)*T(g*f)). Neither the measure nor the
temporal operator has been replaced by a link-update Markov generator.
There is no new stationary state, denominator or square-root weight.

`terminalResidual`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalDirichletCoercivity.lean:104`,
constructs R_i using the actual a=V*T^n1. Its support is supplied by
`terminalResidual_supported` at `:107`; `terminalResidual_coercivity`
at `:116` supplies weighted centering and actual terminal positivity.
There is no unsupplied centering or message-certificate premise in this
terminal theorem. It holds for every supported polynomial f and selected
active i, 0<w<1, all widths/depths, and K>=headCutoff(w).

Both constants depend explicitly on w. They do not contain width, n or K.
The residual DOES depend on all these parameters. No beta/spacing-uniform
bound or statement for another gauge group is asserted.

## Remaining mathematical join

The existing global consumer is `terminal_normalized_energy_variance_floor`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletCoercivity.lean:284`.
It concerns arbitrary observables and the SAME original odd-chain variance;
its current fraction is still width-dependent.

The new modules do not prove a stable weighted decomposition or cross-energy
estimate that upgrades this fraction. In particular:

- P_i(a*R_i)=0 is not a claim that R_i has zero mean under V*g*Tg.
- The residuals are not proved mutually orthogonal or nonzero.
- No conditional-sector transfer-invariance is proved. The local form
  inequality alone is therefore not an iterated temporal-decay theorem.
- V*T^n1 is not proved local merely from the locality of V.
- The K/n-dependent residual cannot be passed through a fixed-observable
  limit without further control and compatibility.
- No dimension-free sum-of-sectors estimate or interacting version of
  the pure-Haar tensorization is supplied.

Next work must prove the actual weighted join, or rule out a proposed join
on explicit finite data, before introducing another analytic interface.
The unchanged alternatives are signed-response estimates retaining the
original action and partition factors. Same-object completed OS/scaling,
physical-time/mass calibration, nontrivial continuum survival, full QFT
and every compact simple group remain OPEN. No canonical Clay atom closes.

## Verification

Four final focused checks passed through the monitored launcher, serialized
with one worker and the mandatory 20 GiB ceiling after fresh process/swap
preflights. All 24 public gates (15 new) lie within {propext, Quot.sound};
the final logs have no warnings/errors. Missing namespace/import references
and a coefficient-lemma name were repaired without changing statements or
resource limits. Independent read-only mathematical review checked both
the general weighted argument and the actual terminal specialization.

Root imports added; root/full-tree/full audit/guard NOT run. CI remains
manual-only. No sorry, new axiom, classical shortcut, old guard, canonical
frontier statement or safety limit changes. Preflight swap remained
6781.19 MiB; no competing compiler/runner was observed.

Final log paths and SHA-256:

- `/tmp/ym-weighted-block-centering-20260917.log`:
  `acfd3fb8a29fce7de3d088096d03e83ead7c1ed515bc2919d056823fa357cbcf`
- `/tmp/ym-dirichlet-form-diagonal-20260917.log`:
  `7fdfca9db98ab533c1d44496b3316def541e01a945098dfe9e0fe86f155114f3`
- `/tmp/ym-weighted-product-local-gap-20260917.log`:
  `f1a146f23cc4adaf3b980a3d6f7c757929dd87e2458a8aa59baae27c629de342`
- `/tmp/ym-local-dirichlet-coercivity-20260917.log`:
  `88ad05f00c5956130d51ad1d85d7bc722014c619ed745c8b0df7efeab8590d91`
