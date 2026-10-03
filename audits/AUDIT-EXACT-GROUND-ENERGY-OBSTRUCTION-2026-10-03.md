# Exact ground pins do not supply small OWN-relative energy

## Result and scope

PROGRESS after `db1b56d`: a generic shortcut is now refuted even after adding
an exact positive interacting ground pin and uniformly bounded positive
action. Two focused checks passed 22 permitted axiom gates. This is an
explicit two-state diagnostic, NOT a BF4 terminal source, gauge theory or
Yang--Mills counterexample. No continuum-survival or physical-gap input is
discharged. The constructive whole-project Clay target remains OPEN.

## Constructed family and SAME law

For rational 0 < e < 1/2, the actual data are

    K_e = [[1-e,e],[e,1-e]],       V = (1-e+e^2, 2-e),
    T h = K_e(V*h),               g = (e*(2-e), 1-e+e^2),
    lambda = (2-e)*(1-e+e^2),      f = (1,0),
    ell(h) = sum_i V_i*h_i.

`lean/YMGap/Continuum/PositiveHeatGroundEnergyObstruction.lean:44` `heat`,
`:47` `action`, `:48` `transfer`, `:49` `ground`, `:50` `groundEigenvalue`,
`:51` `weightedMass` and `:52` `source` define these objects directly.

- `:97` `heat_unit`, `:107` `heat_symmetric`, `:120` `heat_nonnegative` and
  `:132` `heat_psd` prove unit preservation, symmetry, positivity preservation
  and positive semidefiniteness for the SAME heat.
- `:157` `heat_bare_defect` proves, for EVERY signed h,
  `<h,h>-<h,K_e h> = e*(h_0-h_1)^2`.
- `:169` `action_bounds` proves 1/2 <= V_i <= 2, uniformly in e.
- `:197` `weightedGround_pin`, `:206` `transferGround_pin` and `:230`
  `ground_positive` construct V*g=lambda*(e,1), T*g=lambda*g and strict
  positivity of g and lambda. No eigenrelation is supplied as a hypothesis.
- `:256` `excitation_transfer_pin` and `:273`
  `excitation_ground_orthogonal` give the literal excitation (1,-e), its
  T-eigenvalue 1-2e, and its orthogonality to g in the SAME V pairing.

The original edge law is V*g*Tg, not V*g^2 with a silently changed transfer.
Set Z=ell(g*Tg), M1=ell(g*Tg*f), M2=ell(g*Tg*f^2),
Det=Z*M2-M1^2 and E=M2-ell[(g*f)*T(g*f)]. These are the literal definitions
`:55` `edgePartition`, `:58` `sourceMomentOne`, `:61` `sourceMomentTwo`,
`:66` `determinantVariance` and `:69` `groundEnergy`.

Writing mu0=e^2*(2-e), mu1=1-e+e^2, the checked pins are

    Z = lambda^2*(mu0+mu1),   M1 = M2 = lambda^2*mu0,
    Det = lambda^4*mu0*mu1,   E = lambda^2*e^2.

Evidence: `:280` `moment_pins`, `:340` `determinant_pin`, `:356` `energy_pin`.
`:401` `edgePartition_positive` and `:408` `determinant_positive` establish
the nonzero original partition and variance determinant. The decisive
`:417` `energy_relative_obstruction` proves

    Det < 2*Z*E,

using the strictly positive difference
lambda^4*e^3*(2*e*(2-e)+mu1). In normalized variables this says that the
energy/OWN-variance ratio is greater than one half, not small with e.

## Constructed failure of every proposed O(e) coefficient

The witness e=1/[4*(C+1)] for each rational C>=0 is reused from
`lean/YMGap/Continuum/PositiveSourceHeatModeScalingObstruction.lean:379`
`counterStep`; `:404` `counterStep_bounds` proves 0<e<=1/4 and C*e<=1/4.
That older obstruction explicitly lacks an interacting eigenpin (`:155`
`heat_probe`). The new family supplies it rather than assuming it.

In `lean/YMGap/Continuum/PositiveHeatGroundEnergyNoUniformRate.lean`:

- `:40` `counterStep_ground_bound_false` proves NOT Z*E <= C*e*Det.
- `:66` `normalizedMean`, `:71` `normalizedVariance`, and `:76`
  `normalizedEnergy` use ONLY the positive SAME edge partition reciprocal.
- `:81` `normalizedVariance_cleared` proves Z^2*Var=Det; `:111`
  `normalizedVariance_positive` establishes genuine nonconstancy in that law.
- `:153` `counterStep_normalized_ground_bound_false` refutes
  E/Z <= C*e*Var, and `:166` `counterexample` returns the heat step,
  admissibility, positive OWN variance and failed bound as Type-level data.

No source norm or variance determinant is inverted. e=0 is excluded; its
ground coordinate and variance would degenerate. The action does NOT tend
to a scalar action. Consequently this does not refute a theorem requiring
that additional behavior, actual Wilson geometry, or action-specific signed
cancellation. No abstract normalized-transfer contraction or continuum
spectral theorem is asserted as a new checked declaration.

## Bidirectional route decision

An initial-energy alternative ALREADY has its SAME-carrier consumers:

1. `lean/YMGap/Continuum/BF4WilsonAllNomeTemporalEnergyLimit.lean:218`
   `energyLimit_completed_pin` identifies the actual original energy limit
   with the completed one-step time loss delta0.
2. `lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:123`
   `completed_reference_ratio` propagates ONE late-cutoff, original reference
   estimate `finiteEnergy <= c*finiteVariance`, with explicit coefficient
   c*(1+comparisonEta(w,width,s))^2. The estimate itself remains an input.
3. `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyKineticUpper.lean:233`
   `time_loss_linear_bound` applies to EVERY state on this SAME completion:
   C0-C_L <= L*delta0. Thus a reference coefficient D satisfying
   4*u*D <= 1-kappa would suffice for C_(4u) >= kappa*C0.

This alternative avoids producing a separate dynamic-ratio estimate at
each lag; it does NOT avoid the missing action-specific analytic producer.
The exact forward source identity is
`lean/YMGap/Continuum/BF4DyadicWilsonSquareVarianceTaylor.lean:257`
`paddedSquare_energy_variance`:

    original energy = 12*side*(1-w)*OWN variance + varianceRemainder.

Its COMPLETE signed remainder is not bounded here. Another available
source bound is
`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelMomentBalance.lean:331`
`paddedSquare_energy_channel_moment_bound`, retaining the Ward residual,
angular-weight defect and channel/Sobolev debt TOGETHER. The new obstruction
rules out paying this debt from generic heat/action/ground positivity alone.

Retain two alternatives, not two mandatory branches: the action-specific
initial-energy remainder/reserve, or the actual aggregate signed-window
estimate consumed by
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`
`original_window_budget_macro_ratio`. BOTH require the original variance,
explicit terminal factors and a justified changing family. Nontrivial
continuum survival, physical calibration, full QFT structure and every
compact simple group remain OPEN. No extra assumed-budget wrapper or
duplicate heat-coefficient module was introduced.

## Verification boundary

Accepted focused logs (both terminal exit 0, no errors/warnings/sorryAx):

- `/tmp/ym-positive-heat-ground-obstruction-20261003-3.log`: 17 gates;
  SHA-256 `a1348b5633df0a08a30118040b248ced17af3a434e134821c4b36f204f5b3b97`.
- `/tmp/ym-positive-heat-ground-no-rate-20261003-1.log`: 5 gates;
  SHA-256 `7d40b6dcd82522a422befc9f35a075c92791829ffe7e8b78667c5fa8bc7a4567`.

All dependencies are within {propext, Quot.sound}; independent Sol semantic
and Luna source/log reviews passed. Earlier failed attempts are NOT proof
evidence. No new sorry, axiom, Classical shortcut, field weakening or CI
change. Root imports registered; full root/tree build, full audit, guard and
metrics runs were NOT performed.

Checks were serialized with one compiler, the 20 GiB worker ceiling and
12 GiB OS reserve after fresh capacity preflights. Swap was 0 throughout
the preflights; pressure-free capacity was 76--77%. No limit was increased.
Exact canonical chart claims are unchanged; no ASCII chart is reprinted.
