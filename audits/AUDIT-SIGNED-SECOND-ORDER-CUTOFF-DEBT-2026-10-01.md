# Signed second order and original cutoff payment

Date: 2026-10-01 UTC. The complete signed-family original energy now has
an explicit second-order upper estimate inside its SAME interacting
variance formula. Quadratic cancellation remains signed before cubic and
cutoff errors are bounded. This is a finite estimate, not a useful uniform
scaling bound, continuum construction or physical mass-gap theorem.

## Scalar cubic remainder and the actual cutoff

Let h=1-w and S be the sum of d*(d+2) on an actual finite degree path.
`SU2HeatRetainedCubicTaylor.cubicRemainder` and `cubicBudget`
(`lean/YMGap/Continuum/SU2HeatRetainedCubicTaylor.lean:48`, `:54`)
compute r=w^S-1+S*h-S*(S-1)*h^2/2 and a recursive B(S).
`cubicRemainder_nonpositive` and `cubicRemainder_budget_lower`
(same module, lines 181 and 206) prove -B(S)*h^3<=r<=0 for 0<=w<=1.
The recurrence r_(S+1)=w*r_S-S*(S-1)*h^3/2 supplies the short invariant
r_S+B(S)*h^3>=0. No closed binomial or S^3 budget theorem is claimed.

`SU2HeatProductCutoffDebt.retained`
(`lean/YMGap/Continuum/SU2HeatProductCutoffDebt.lean:41`)
requires EVERY coordinate degree to be at most K. `omittedDebt`, line 71,
is zero for retained paths and w^S otherwise. `productAttenuation_debt`,
line 74, identifies the ORIGINAL attenuation as w^S-omittedDebt.
These reference powers are finite scalar coefficients, not a replacement
heat operator. `omittedDebt_le_tail`, line 111, proves the explicit cap
w^((K+1)*(K+3)). The actual cutoff remains coordinatewise, not on S.

`productRemainder_secondOrder`, line 127, proves on EVERY path:

    originalRemainder = (h^2/2)*(C^2-C) + r - omittedDebt.

Signed pairing coefficients still have to be paid; the scalar tail alone
is not a bound relative to interacting variance.

## Mixed quadratic cancellation before absolute estimates

`SU2QuaternionCyclicCasimirMixed.full_mixedSecondMoment_eq_literal`
(`lean/YMGap/Continuum/SU2QuaternionCyclicCasimirMixed.lean:64`)
identifies the complete mixed Casimir-square leaf sum with H[(Cp)*(Ct)].
The original ragged tree and arbitrary supported test remain intact.

All declarations below are in
`lean/YMGap/Continuum/SU2QuaternionCyclicSecondOrder.lean`.
`sourceSecondMoment_literal`, line 228, retains

    D2 = H[(Cq)*C(q*f^2)] - H[(C(q*f))^2].

`sourceRemainder_secondOrder`, line 197, has coefficient D2+A, NOT D2-A.
`sourceEnergy_secondOrder`, line 246, identifies the actual energy as

    E = h*A + (h^2/2)*(D2+A) + sourceCubic - sourceOmitted.

`pairCubic_bounds`, line 123, pays computed absolute leaf sums weighted
by B(S), times h^3. `pairOmitted_bounds`, line 111, pays the actual
omitted coefficients; `pairOmitted_tail_bounds`, line 164, alternatively
pays the scalar tail times the complete absolute leaf coefficient budget.
`sourceErrorBudget`, line 265, adds the mixed and diagonal payments.
`sourceError_bound`, line 275, bounds sourceCubic-sourceOmitted above by
that budget. `sourceEnergy_le_secondOrder`, line 303, keeps D2 signed.
Pointwise nonnegative cutoff debt does not give its source difference a
favorable sign. No cross term or source derivative is discarded.

## Original marginal and same variance consumer

`BF4ExactSlabFixedSpatialFamilySecondOrder.varianceRemainder_secondOrder`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilySecondOrder.lean:73`)
equals the EXISTING signed correction. `padded_family_energy_secondOrder`,
line 90, joins it to the original normalized energy and oddVariance:

    E/Z = 12*h*Var_odd +
      [(h^2/2)*(D2+A) + sourceCubic - sourceOmitted
        - h*angularWeightDefect - h*wardResidual]/Z.

The source is the existing projectedEndpointSource of terminalMessage at
depth n. It is not the separate unprojected depth n+1 source used by the
latest local-band theorem. The original oddMass, mean and both complete
interacting derivative corrections remain. `secondOrderVarianceCeiling`,
line 105, replaces ONLY sourceCubic-sourceOmitted by sourceErrorBudget.
`padded_family_energy_le_secondOrder`, line 138, proves the resulting
upper bound for the WHOLE signed padded family, including repeated faces.
Only the existing explicitly positive partition is divided by; no source
or variance inverse is formed.

## Remaining analytic input

Nothing here controls that ceiling relative to SAME variance along a
justified physical scaling family. The cubic/tree coefficient budget and
cutoff-tail coefficient norm can depend on the changing terminal source,
width, cutoff and observable. A scalar h^3 factor is not uniformity in
those changing inputs. The complete Ward residual includes original
action and terminal derivatives and is not proved small.

The next candidate argument is to localize the signed D2 cancellation
by the actual Casimir product rule and Haar integration by parts. No such
new local identity is claimed in this checkpoint. Nonzero continuum
survival, spatial/spacing-uniform decay, physical time/mass calibration,
full same-theory continuum QFT and every compact simple group remain open.
No canonical frontier field or displayed chart marker changes.

## Verification boundary

Six final focused checks passed 58 printed gates within
{propext, Quot.sound}; several computed definitions are axiom-free.
Five existing finite-leaf algebra helpers were made public without proof
changes to avoid duplicating recursion. Independent Sol and Luna reviews
checked source depths, cutoff semantics, signs and the remaining scope.
No sorry, new axiom, Classical dependency, native_decide or noncomputable
declaration was introduced. The documentation skill kept the finite
estimate distinct from its unavailable scaling input.

Checks were serialized by the safe launcher with one worker, 20 GiB worker
ceiling, 12 GiB OS reserve and dynamic telemetry. No limits were raised.
Final logs have no errors or warnings. Root imports were registered but
the aggregate root was not checked. No full tree build, audit or guard
was run. CI remains manual-only. No unchanged ASCII chart was reprinted.

Final logs under `/tmp/`, with SHA-256:

- `ym-cyclic-leaf-public-20261001.log`:
  `ba044c1eefd3da08112367e77460f090b0d886e5a94498315c9cf7c89a9426c1`.
- `ym-retained-cubic-final-20261001.log`:
  `a915d6584ea862e59098bed8a9352dfbe2255a165762a95229c2adac3ae25377`.
- `ym-product-cutoff-debt-accepted-20261001.log`:
  `e01c4a84a82e0d7e2477e59e655ea93a86f9a38069e5220ad58408eaa471209f`.
- `ym-casimir-mixed-final-20261001.log`:
  `2d07aa741338bb14f53089df4785416cc4b2da0e09e4b45f2a8fcd1bb65fde4b`.
- `ym-cyclic-second-order-bound-20261001.log`:
  `ad929dacef90a49da0a70870296315d0e57fa5d304d6578a88c3922babdf07e3`.
- `ym-family-second-order-bound-20261001.log`:
  `1a6e0e35550dcda7dbe176489f12dd3012668a033df5bf46e8336f48bc5a5535`.
