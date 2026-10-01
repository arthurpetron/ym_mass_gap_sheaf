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

## Addendum: concentrated-source Ward obstruction on actual heat

This supplies the preceding fixed-source certificates' concrete consumer.
For each requested nonnegative coefficient C, actual source/nome witnesses
defeat E<=C*(1-w)*B, where E and B are ORIGINAL finite-step energy and
uncentered second moment. This is not an actual terminal-family claim.

### Exact one-link source and Ward identities

Declarations in
`lean/YMGap/Continuum/SU2QuaternionConcentratedSourceWard.lean`:

- `sourceCertificate`, line 87, constructs the NONNEGATIVITY certificate
  of q_N=(x1^2+x2^2+x3^2)^N. This is not pointwise strict positivity.
- `radial_carrier`, line 98, pins radial+chi_1^2/4=1 on the SAME unit
  quaternion Haar carrier under arbitrary insertions.
- `fundamental_casimir`, line 112, pins C f=3f under every original Haar
  insertion. It does not equate padded and unpadded raw monomial keys.
- `fundamental_sourceSquare_gamma`, line 192, proves the exact coefficient
  identity Gamma(f,q_N^2)=-4N*f*q_N^2.
- `sourceSquare_moment`, line 382, proves Z=(N+1)*J, with Z=H[q_N^2]
  and J=H[q_N^2*f^2]. `sourceSquare_angular`, line 390, proves A=(4N+3)*J.

Declarations in
`lean/YMGap/Continuum/SU2QuaternionConcentratedSourceMoments.lean`:
`radialMass_step`, line 243, proves (2k+4)*Z_(k+1)=(2k+3)*Z_k for
Z_k=H[radial^k]. `radialMass_pos`, line 251, inducts from Z_0=1.
`source_power_add`, line 277, identifies the actual source square with
the double radial power. `mass_pos`, line 288, and `secondMoment_pos`,
line 294, supply Z>0 and J>0 without assumed nondegeneracy.
`firstMoment_zero`, line 306, follows directly from Ward and positive
coefficient cancellation, without a parity or high-degree expansion.

### Computed original positive-step witnesses

All declarations below are in
`lean/YMGap/Continuum/SU2QuaternionConcentratedSourceHeatFence.lean`.
`escapeExponent`, line 47, returns N=C.num.toNat; its coefficient proof
at line 49 gives 2C<4N+2 for C>=0. `step`, line 77, computes

    h = min(1/2, slopeRadius(0,q_N,f,J), momentRadius(0,q_N,f^2,J)),
    w = 1-h,  0<w<1.

`zeroStep_square_pin`, line 66, identifies H[(q_N*f^2)*q_N] with J.
The slope error J gives E>=h*(4N+2)*J; the signed moment error J gives
B=H[(q_N*f^2)*P(q_N)]<=2J. Since h,J>0, their exact combination proves

    E > C*h*B

in `energy_gt_same_secondMoment`, line 120, for EVERY
K>=sufficientCutoff(w). `obstruction`, line 183, returns N,w and this
all-guarded-cutoff proof as Type-level data. No endpoint replaces a
positive-step heat expression; no interacting variance is inverted.

### Scope and next actual-source input

The finite-step B is UNCENTERED. The proved zero first moment belongs to
the bare Haar endpoint, not an asserted positive-step centering identity.
These q_N are nonnegative certified sources, not pointwise-strict sources
or identified BF4 terminal messages. Consequently this refutes only a
nonnegativity-only source-independent comparison. It refutes no actual
terminal-source theorem, scaling trajectory, continuum theory or mass gap.

The stronger existing actual-source input is
`BF4ExactSlabFixedSpatialEndpointRelativeBound.projectedEndpointRelativeBound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointRelativeBound.lean:96`.
Its original same-channel consumer is
`projectedEndpoint_familyChannelDerivative_le`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointChannelRegularity.lean:61`,
and `padded_plaquetteChannel_firstMoment_le`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointChannelFirstMoment.lean:136`.
Their cap-squared cost is still not useful scaling control. The original
positive-depth heat-recursion pin is `terminal_cons_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalJacobiAngularBound.lean:53`.
An improved integrated heat-score estimate from that recursion is a next
candidate to investigate, not a proved estimate or an assumed new field.
Read-only search found no existing one-sided heat-relative Casimir bound
with useful O(1/(1-w)) cost. The alternative candidate is the integrated
spectral inequality (1-w)*lambda*w^(2*lambda)<=w^lambda and its actual
source-pairing/derivative join. The relevant original grouping declaration
is `polynomial_grouped_heat_pairing` in
`lean/YMGap/Continuum/SU2QuaternionGroupedHeatComparison.lean`; source
grouping alone does not justify arbitrary spectator-weight orthogonality.
This candidate has not been formalized in this checkpoint and supplies
no new terminal or scaling estimate.
The actual complete signed SAME-variance scaling bound, survival, physical
mass, full QFT and every-group construction remain OPEN.

### Focused verification

Three final focused target checks exited zero with 30 printed gates within
{propext, Quot.sound}; the exponent definition is axiom-free. Independent
Sol/Luna reviews passed on the Ward signs, strict-moment producer, original
finite-step joins, all-cutoff quantifier and nonnegative/uncentered scope.
Initial namespace, scalar-parenthesis and rational simplification errors
were repaired. A false raw-key Casimir statement was replaced by its actual
arbitrary-insertion Haar equality; no canonical field was weakened.
There is no new sorry, axiom, Classical, native_decide or noncomputable
declaration in the accepted sources.

Main alone compiled, serially under the monitored one-worker 20 GiB cap
and 12 GiB OS reserve. Preflight found 84 percent pressure-free memory,
zero swap and no competing compiler/test/runner. No limit was raised.
The safe-build skill confined verification to these targets. No full
root/tree build, broad audit or guard ran. CI remains manual-only; the
unchanged canonical chart was not reprinted.

Accepted logs and SHA-256:

- `/tmp/ym-concentrated-source-ward-accepted-20261001.log`:
  `b22411972470d0523786b746e39421f0de0145cfb0a3c326f31aa31fef4d9485`.
- `/tmp/ym-concentrated-source-moments-accepted-final-20261001.log`:
  `1f23bf2af13a48af52088d6e650cd767d8b1ad6bd7a77c55fcf8dbc7d4e16324`.
- `/tmp/ym-concentrated-source-heat-fence-accepted-20261001.log`:
  `9e755e1ad176d98c6b6359037831fd1b66ab11c23a8701c82794ee9b63752b07`.
