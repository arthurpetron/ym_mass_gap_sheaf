# Same odd-chain coercivity and actual positive plaquette energy

Date: 2026-09-17 UTC. Base revision: `4d7bc5e`.

Whole-project goal: construct nontrivial continuum Yang--Mills on R^4 for
every compact simple gauge group, with the required same-theory QFT structure
and positive physical Hamiltonian gap, within {propext, Quot.sound}. OPEN.

## Constructed fraction, not an assumed coercivity field

Use the original finite transfer T=K V, m(p)=H[V p], and a supported
certified nonnegative g with M=m(g)>0. Define

    b=m(g*f), C=m(g*f^2), D=M*C-b^2,
    p=g*Tg, Z=m(p), A=m(p*f^2), B=m(p*f),
    E=A-m((g*f)*T(g*f)).

`energy_floor`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletFloor.lean:174`,
proves E>=L*D, where L is the actual kineticFloor(w,width). The residual
K-L is multiplied by BOTH full endpoint Vg weights and the squared jump.
`independent_jump_identity`, same file `:119`, identifies the removed
constant-kernel term with 2D. Only the positive scalar 2 is cancelled.
No original spatial weight or signed cross term is discarded.

For the upper comparison use the explicit polynomial F=M*f-b, with no
reciprocal or selected minimizer. `centered_test_decomposition`,
`lean/YMGap/Continuum/RationalVarianceCapComparison.lean:29`, proves

    M^2*(Z*A-B^2) + (M*B-Z*b)^2
      = Z*(M^2*A - 2*M*b*B + b^2*Z).

`variance_cap_of_centered_test`, same file `:63`, discards the displayed
nonnegative correction square and cancels M^2>0. It needs only Z>=0 and
the supplied centered-test comparison; there is no sign premise on the
first or second moments or cap U.

`marginal_variance_cap`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletCoercivity.lean:174`,
supplies that test comparison using the ACTUAL transferStepUpperCertificate:
Tg<=U*M, with U=kineticCap(w,width). It concludes

    Z*A-B^2 <= U*Z*D.

The constructed positive fraction r=mixFraction=L/U gives

    r*(Z*A-B^2) <= Z*E.

This is `energy_variance_floor`, same file `:222`. It loses ONE floor/cap
factor, not its square. It is not claimed to be an optimal estimate.
All K/V certificates are supplied; the conclusion is not an input field.
The generic theorem explicitly requires positive M. Its terminal consumer
constructs this premise rather than inferring it from g>=0 alone.

## Exact original finite-chain and normalized consumers

`terminal_energy_variance_floor`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletCoercivity.lean:242`,
sets g=T^n1 and constructs its support, certificate and positive mass.
It holds for every width, every n, every rational 0<w<1 and every
K>=headCutoff(w), for all supported polynomial tests f.

`terminal_normalized_energy_variance_floor`, same file `:284`, proves

    mixFraction(w,width) * Var_middleRatio(n+1,n)(f)
      <= normalizedEnergy(n,f).

It multiplies the cleared theorem by the SAME oddMass reciprocal squared,
using Z*rZ=1, and invokes the existing marginal_middleRatio pin. This
denominator is the original 2*n+1-transition chain partition, not a new
stationary law. No even-chain density or other observable is substituted.
The fraction is independent of boundary depth and late representation
cutoff, but explicitly depends on nome AND spatial width.

## Parallel nonconstant observable, in this SAME marginal

`odd_variance_floor`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOddLocalVariance.lean:161`,
directly applies the existing selected local-star comparison to the original
chain with unequal depths (n+1,n). First and second moments of the literal
fundamental character chi_1 of any valid spatial plaquette are pinned via
the singleton/double source probe and OriginalMiddle's exact finiteValue
identity. They retain the same selected action, cutoff and partition.
The floor is starRatio(w)>0, independent of width, n and late K.

`odd_marginal_variance_floor`, same file `:174`, transfers that exact floor
to the literal V*T^n1*T^(n+1)1 marginal, with the existing oddMass reciprocal.
It does not invoke the mismatched even-chain centralVariance theorem.

`plaquette_energy_floor` and `plaquette_energy_positive`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletCoercivity.lean:314`
and `:329`, combine these results on the SAME measure:

    normalizedEnergy(n,chi_1)
      >= mixFraction(w,width)*starRatio(w) > 0.

The actual spatial-face membership premise is retained. General coercivity
permits width zero; this nonconstant-observable claim does not invent a
face when there is none. It is finite nontriviality and positive temporal
energy, not proof of nontrivial continuum survival or a Hamiltonian energy.

## Surviving obstruction and next mathematical target

The existing `mixFraction_le_width_power`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRateWidthObstruction.lean:74`,
bounds this computed fraction above by 32^(-width). Thus its positive
fixed-width value cannot provide a common spatially positive fraction.
This obstructs THIS comparison, not the actual optimal energy or gap.
The new local variance floor is width-independent; the energy lower bound
is not. Replacing mixFraction by starRatio would be an unproved step.

Next: construct a stronger fraction for the SAME odd-marginal inequality
with the spatial, cutoff and depth control needed at nomes along the scaling
route. Seek a cancellation-preserving local comparison or signed-response
estimate that avoids the full product floor/cap loss. Further normalization
wrappers or re-proving existing fixed-width completed results do not remove
this estimate. The pure-Haar product contraction cannot simply be applied
to the interacting marginal.

The present operator is the actual finite one-step temporal transfer,
not a link-update heat-bath generator. Same-object temporal/completed OS
and growing-volume/scaling joins, the actual physical-time and mass
calibration, continuum QFT and every compact simple gauge group remain open.
The fixed-spacing small-nome completed branch and its proved AF obstruction
are unchanged. No canonical frontier field, old guard or Clay atom changes.

## Verification

Four final focused serialized checks pass through the monitored launcher,
one worker and the mandatory 20 GiB ceiling after fresh process/swap checks.
All 12 public axiom gates are within {propext, Quot.sound}. Final logs have
no errors or warnings. Independent mathematical source review checked the
full residual, correction square, single ratio loss, shared normalization,
actual face and parameter scope. A missing namespace opening was repaired
without increasing heartbeat or memory limits.

Root imports added; root/full-tree/full audit/guard NOT run. CI remains
manual-only. No sorry, new axiom, classical shortcut or safety relaxation.
No competing compiler/runner was observed; preflight swap stayed at
6781.19 MiB throughout these checks.

Final log SHA-256:

- `/tmp/ym-variance-cap-comparison-20260917.log`:
  `c6a800273ee8a69687369fc74dc469be3663e25b7269d6177374d2be0c0abe4c`.
- `/tmp/ym-dirichlet-floor-20260917.log`:
  `573399dcd93ccbf6ac16b32798a630f661687782bbfba4b9c5d3d5e0b690ed7d`.
- `/tmp/ym-odd-local-variance-20260917.log`:
  `b7ae346ad3b488f77acd65e5a4e07c0569250a61b56ba70b96399ae4a5834f38`.
- `/tmp/ym-dirichlet-coercivity-20260917.log`:
  `f6dce01f481d2fb0a62dc57341cd8e3dd31e740bb88c3ab9f5f49d80bd5b691a`.
