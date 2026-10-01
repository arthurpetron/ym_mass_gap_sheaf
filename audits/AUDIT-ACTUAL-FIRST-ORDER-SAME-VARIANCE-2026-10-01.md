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

## Addendum: two-sided fixed-source heat-step and moment limits

The actual fixed-source zero-step calculations now have quantitative joins
to the ORIGINAL finite-cutoff energy and moments. These are constructed
moduli, not new assumed analytic fields. They do not control a changing
terminal source along a physical scaling trajectory.

### Original energy slope

The declarations below are in
`lean/YMGap/Continuum/SU2QuaternionProductHeatSourceSlope.lean`.
`sourceEnergy_ge_firstOrder_sub_quadratic` at line 36 supplies the lower
companion to the existing upper Taylor estimate, retaining BOTH signed
pair-remainder bounds. `slopeCap` at line 65 computes

    cap = 1 + abs(sourceTaylorBudget(tail,a,f)),
    radius = e / cap,  h = 1-w,
    h*(A-e) <= E_original <= h*(A+e).

`sourceEnergy_slope_interval` at line 98 proves the interval whenever
0<=w<1, h<=radius and K>=sufficientCutoff(w). Here A is exactly the
existing weightedAngularEnergy(tail,a,f), and E_original is the full
List.range(tail+1) original product-heat energy of the SAME supported
source and observable. `slopeRadius` at line 80 and `slopeCertificate`
at line 145 return the positive radius and the all-guarded-cutoff proof
as Type-level data. Neither h nor a variance is inverted in the inequality.

### Original signed moment endpoint

The declarations below are in
`lean/YMGap/Continuum/SU2QuaternionProductHeatSourceMomentLimit.lean`.
`zeroStepMoment` at line 31 is H[(a*p)*a], not a replacement positive-step
interacting variance. `momentCap` at line 35 computes

    cap = 1 + abs(pairCasimir(tail,a,a*p)) + abs(pairBudget(tail,a,a*p)).

`sourceMoment_endpoint_interval` at line 64 proves
M0-h*cap<=H[(a*p)*P(a)]<=M0+h*cap for 0<=w<1 and EVERY
K>=sufficientCutoff(w). The h^2<=h reduction explicitly uses w>=0.
`momentRadius` at line 44 and `momentCertificate` at line 124 return
e/cap and its two-sided e-precision bound. The insertion p may be signed;
only a has a supported-source premise. The actual cutoff and heat operator
are retained throughout.

### Consumer, scope and verification

These certificates allow a concrete FIXED-source Haar/Ward endpoint
calculation to be tested at genuine positive heat steps. The source is
fixed BEFORE w varies. Applying the theorem separately to parameter-dependent
terminal sources does not produce a common radius. The required useful
SAME-interacting-variance bound for the actual terminal/channel source on a
justified physical family remains OPEN, as do scaling survival, physical
mass, full continuum QFT and every compact simple group.

Both final focused checks exited zero, with 13 printed gates within
{propext, Quot.sound}. Independent read-only reviews checked the signs,
cutoff quantifiers, signed insertion and returned witness scope. No new
sorry, axiom, Classical dependency, native_decide or noncomputable
declaration. One unused-binder warning in slopeCertificate is harmless.
Only main compiled with the monitored one-worker 20 GiB ceiling and 12 GiB
OS reserve. The safe-build skill confined verification to the exact targets.
No aggregate/root/tree build, broad audit or guard ran; CI stays manual-only.
No canonical chart marker changed, so no chart was reprinted.

Accepted logs and SHA-256:

- `/tmp/ym-source-slope-first-20261001.log`:
  `4aa12a9f0e66c67c3080cf12d8bdfb893d1d3e1e2cd1e76791d8ae95f1237fa3`.
- `/tmp/ym-source-moment-limit-accepted-20261001.log`:
  `52532fc6f2ac2b3851856fd3e0616e57a91f581f401fc79e9aa7dc49dd2b7149`.
