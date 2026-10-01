# Actual terminal first order and joint signed variance control

Date: 2026-10-01 UTC. The actual positive-depth projected terminal source now
has a first-order angular-energy bound against the SAME original centered
interacting variance. Its coefficient is independent of late cutoff and
terminal depth at fixed nome and full width. The original energy consumer
combines both signed first-order corrections before estimating them, leaving
curvature and Taylor debt explicit. This is not a physical scaling estimate.

## Original objects and constructed comparison

Write d=n+1, f=spatialSpan(width,c,qs), q=projectedEndpointSource(w,K,width,T_d),
W=V*T_d*T_(d+1), Z=oddMass(w,K,width,d), and Var=oddVariance(f) at that SAME
depth and original mean. Coefficients c are arbitrary rational numbers;
faces may repeat. For the source comparison each face belongs to the full
spatial slice. The energy consumer additionally requires strict padding and
faces from the smaller slice, which supply the actual fringe independence.

Let m=H[V*T_n]>0, v_-=spatialFloor(w,width), v_+=spatialCeiling(w,width),
k_-=kineticFloor(w,width), and k_+=kineticCap(w,width). Define
L0=v_-^2*k_-^3 and U0=v_+^2*k_+^2. Existing transfer floors/caps and the
actual fringe projection construct certificates for

    q <= v_+*k_+*m,     W >= L0*m^2.

These are positive-polynomial certificates under arbitrary Haar insertions,
not assumed pointwise inequalities or a replacement law. Evidence:
`BF4ExactSlabFixedSpatialTerminalSourceBounds.projectedSource_upperCertificate`
at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalSourceBounds.lean:130`,
and `marginalWeight_lowerCertificate` in the same file at line 196.

The complete signed physical family has H[f]=0 and H[Gamma(f,f)]=12*H[f^2].
Its bare squared norm is no larger than H[(f-center)^2] for ANY rational
center, including the unchanged original W-mean. The declarations are
`family_haar_zero`, `family_gamma_square`, and `family_shifted_square_ge`
at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyBareHaar.lean:124`,
`:149`, and `:172`. `family_sourceFirstOrder_gamma` at line 94 identifies
A=sourceFirstOrder with H[q^2*Gamma(f,f)], retaining all signed cross terms.

The resulting inequalities are A<=12*U0*m^2*H[f^2] and
L0*m^2*H[f^2]<=Z*Var. Scaled substitution, without dividing by m or Var,
gives L0*A<=12*U0*Z*Var. Evidence:
`BF4ExactSlabFixedSpatialFamilySourceVarianceBound.family_firstOrder_variance_cleared`
at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilySourceVarianceBound.lean:252`.
`marginal_centered_square` at line 150 pins the centered insertion to the
original Z*Var without an extra fringe restriction.

`firstOrderVarianceConstant` at line 281 computes U=12*U0/L0; its positivity
is proved at line 286. `family_firstOrder_variance_bound` at line 293 gives
A<=U*Z*Var. Only the explicit positive scalar L0 is inverted.

## Joint signed energy consumer

Put h=1-w, alpha=h^2/2, Delta=angularWeightDefect, and R=wardResidual.
The actual marginal Ward and source-weight identities give

    A + Delta + R = 12*Z*Var.
    alpha*A - h*Delta - h*R <= ((h+alpha)*U - 12*h)*Z*Var.

Both terms remain signed until this exact combination. Source, mean,
normalization and terminal depth are unchanged. Evidence:
`BF4ExactSlabFixedSpatialFamilyJointCorrection.family_firstOrder_defect_ward`
at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyJointCorrection.lean:77`,
and `jointRaw_le_variance` in the same file at line 149.

Let debt=alpha*(-curvatureMoment-48*projectedObservableSquare)+sourceErrorBudget.
`jointDebt` at line 132 retains the signed whole-family curvature, the actual
negative source square, and the original cubic and omitted-mode cutoff
budgets. `padded_family_energy_le_jointVariance` at line 293 proves

    normalizedEnergy <= (h+alpha)*U*Var + debt/Z.

The original leading 12*h*Var cancels algebraically against the corresponding
joint correction; no separate helpful sign is assigned to Delta or R.

## Parameter dependence and remaining frontier

All statements retain 0<w<1 and K>=headCutoff(w). The source and variance
are at positive depth n+1. U names only w and width, not K, n, coefficients
or family-list size. In terms of S=number of spatial faces and T=number of
temporal faces, its defining factors are

    U = 12*prefixCap(w)^(2*S+2*T) / headFloor(w)^(2*S+3*T).

This expansion is algebra from the defining factors, not a separate new
Lean power identity. See `spatialFloor` and `spatialCeiling` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCentralDensity.lean:72` and `:75`,
and `kineticFloor` and `kineticCap` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSandwich.lean:57` and `:61`.
There is no width-uniform or coupling-uniform assertion, no beta/spacing
calibration, and no proved scaling-small coefficient or debt/variance bound.

The next required input remains useful control of the COMPLETE signed cost
against SAME variance on a justified physical family. The new first-order
producer removes a finite comparison gap; it does not supply that scaling
input. Physical decay across scales, nonzero continuum survival, mass
calibration, full same-theory QFT and every compact simple group remain OPEN.
No canonical frontier field or displayed chart marker changes.

## Verification

Four final focused file checks exited zero; all 35 printed gates stay within
{propext, Quot.sound}, with three axiom-free step definitions. No sorry, new
axiom, Classical dependency, native_decide or noncomputable declaration.
Independent Sol and Luna reviews checked the coefficients, original center,
depths, zero cases and signed consumer. Initial namespace, rational-setoid
chaining, reflection syntax and unfolding errors were repaired without
changing the mathematical hypotheses or raising heartbeat/memory limits.

Only main compiled, serially through the monitored launcher with one worker,
20 GiB ceiling and 12 GiB OS reserve. Preflight found no competing
Lean/Lake/test/runner process, 83 percent pressure-free capacity and zero
swap. Root imports were registered but not checked in aggregate. No full
root/tree build, audit or guard ran. CI remains manual-only. The documentation
skill kept finite parameter control separate from its open physical consumer;
the unchanged canonical ASCII chart was not reprinted.

Final logs under `/tmp/`, with SHA-256:

- `ym-terminal-source-bounds-final-20261001.log`:
  `1ad3bfb86edc486236e790d69ca57841c71cca817e0f4ea8665b2e7465730b8f`.
- `ym-family-bare-haar-final-20261001.log`:
  `0af9d2e65d7bb87cd6a9e1e5e9eea2544ee3cc6c84885008b15fd60f14758a98`.
- `ym-family-source-variance-final-20261001.log`:
  `ae9fb6efe9f5f502c34adfc62f83481879d4f0b47402319e46397f3500b1deb7`.
- `ym-family-joint-correction-accepted-20261001.log`:
  `740034386772b96df5342bfa25d967afb9b0bfc92cc7ac882147bc10a500a4a9`.
