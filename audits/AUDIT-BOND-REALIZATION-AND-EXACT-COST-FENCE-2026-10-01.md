# Original bond form realization and exact cost fence

Date: 2026-10-01 UTC. Two results advance the unchanged constructive
Yang--Mills route. The original fixed-width bond-reflection form now has a
dense witnessed realization in the existing time-continuity sector. On the
analytic side, exact signed Young coefficients still cannot repair the
current coarse endpoint-floor certificate into a subunit loss estimate.
Neither result supplies physical scaling or closes the continuum Clay goal.

## Physical form and original objects

For signed intrinsic Wilson sources x,y, put R=max(x.radius,y.radius).
`crossOdd` is their actual reflected product in a common chart, with the
second source advanced by one original time step. The product fits the
balanced odd window of extent 2R+1. The original joint-limit padding theorem
removes one exterior slice from the displayed chart; no finite-depth
symmetric-padding equality is assumed.

The resulting original reflected joint limit equals B(embed x,T(1)embed y).
This physical functional is defined before identifying it with a Gram form.
On the diagonal the source is exactly the already established `oddPair`.
The declarations are `crossOdd`, `crossOdd_within`, `crossOdd_pin`,
`crossOdd_self` and `completed_crossOdd_pin` in
`lean/YMGap/Continuum/BF4WilsonAllNomeBondReflectedForm.lean:42`,
`lean/YMGap/Continuum/BF4WilsonAllNomeBondReflectedForm.lean:50`,
`lean/YMGap/Continuum/BF4WilsonAllNomeBondReflectedForm.lean:66`,
`lean/YMGap/Continuum/BF4WilsonAllNomeBondReflectedForm.lean:93` and
`lean/YMGap/Continuum/BF4WilsonAllNomeBondReflectedForm.lean:98`.

Let root_1 be the already constructed positive square root of the ORIGINAL
T(1). Map x to root_1(embed x), retaining its computed original range
witness. The square-root pairing law then gives

    B(image x,image y) = original bondForm(x,y).

The norm of image(x)-image(y) is exactly the physical bond form on x-y.
Thus two images agree precisely for the physical null relation. A dense
source is bond-null exactly when T(1)embed x=0, NOT when its original
ambient norm is zero. The ambient carrier, including its actual nonzero
boundary time-kernel states, is unchanged.

The declarations `bondForm`, `image`, `image_pairing`, `image_distance`,
`image_eq_iff_bond_null` and `bond_null_iff_time_kernel` are in
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSRealization.lean:63`,
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSRealization.lean:69`,
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSRealization.lean:74`,
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSRealization.lean:81`,
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSRealization.lean:91` and
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSRealization.lean:99`.
`image_advance` and `image_unit`, lines 113 and 120 in that module, preserve
the same one-step transfer and normalized vacuum.

## Constructed density with explicit moduli

For an existing witnessed sector state z and squared error epsilon:

1. Its supplied range witness computes X with T(1)X within epsilon/4 of z.
2. The computed representative of root_1(X) supplies a finite Wilson
   expression e within epsilon/4 of root_1(X).
3. Root contraction and root_1 squared=T(1) show image(e) is within epsilon
   of z, using the squared-distance triangle budget.

No quotient representative is selected and no uniform norm bound on the
preimages is assumed. Sampling at epsilon_n=1/(n+1) gives an actual
state-valued Cauchy sequence. Its computed limit equals z in the original
completion. These are `denseExpression`, `denseExpression_bound`,
`denseSequence_bound`, `denseRows` and `dense_limit` in
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSRealization.lean:128`,
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSRealization.lean:136`,
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSRealization.lean:165`,
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSRealization.lean:174` and
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSRealization.lean:190`.

This proves a dense witnessed realization of the physical bond null
relation, recovering every existing sector state by an explicit limit. It
does not introduce a separate completed quotient datatype or a theorem
identifying that datatype isometrically with the sector. It does not
instantiate the canonical continuum `PositiveTimeOSRoot`: canonical
limiting support/approximation, observable actions, spatial/spacing control
and physical spectral identification remain open. In particular, it does
not override the proved obstruction to restricting time-zero multipliers.

## Exact coefficients do not repair the coarse analytic certificate

For the actual plaquette f and any supported channel source q, set
A=H[q^2] and F=H[q^2 f^2]. Existing square certificates give 0<=F<=4A.
The existing exact channel cost is

    C = (1-w^32)A + beta*F,   beta = 1+w^32-2*w^12.

The new result retains that sign and proves C<=kappa*A, where

    kappa = (1-w^32) + 4*max(beta,0).

This uses an explicit decidable rational branch, not a new opaque constant.
For the EXISTING endpoint heat floor rho, the proved inequalities are

    2*rho <= 1-w <= kappa;
    kappa <= 2*rho*c  implies  1 <= c.

Consequently replacing the coarse quadratic remainder coefficient by this
exact scalar ceiling cannot certify a subunit loss using the same endpoint
floor. This is a bound on the CERTIFICATE'S coefficient, not an actual
energy lower bound, a failure of the signed identity or a YM counterexample.
The definitions and results are `squareCoefficient`, `exactChannelCeiling`,
`plaquetteChannelCost_le_exactCeiling`, `gap_le_exactChannelCeiling`,
`two_endpointFloor_le_exactChannelCeiling` and
`normalizedExactCeiling_not_subunit` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointExactCoefficientFence.lean:40`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointExactCoefficientFence.lean:45`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointExactCoefficientFence.lean:81`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointExactCoefficientFence.lean:123`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointExactCoefficientFence.lean:147` and
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointExactCoefficientFence.lean:165`.

Source review found that spectator-preserving Young was already implemented:
`padded_terminal_plaquette_passive_signed_geometric_budget`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPassiveGeometricBudget.lean:164`.
The next useful analytic input must retain quantitative source-increment
cancellation or control the actual inserted response against the SAME
interacting variance. `terminalMessage_next`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:57`,
is an uninserted recursion, not a Perron equation for the projected source.
The missing inserted response is visible in `sourceEnergy`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatProjectedSourceEnergy.lean:52`.
No useful physical scaling bound for it was proved here.

## Verification

Three final focused checks exited 0, with 23 printed gates: two axiom-free,
21 depending only on {propext, Quot.sound}. No new sorry, axiom, classical
shortcut, native_decide, frontier weakening or surrogate substitution.
Sol agents worked independently on the mixed physical pin and the exact-cost
fence; the main agent constructed the density realization and alone ran Lean.
A separate read-only review confirmed the physical-source, null-relation,
modulus, vacuum and time scope. The cost proof's initial namespace and scalar
cancellation errors were repaired before its final successful check.

Checks used the monitored launcher, one worker, 20 GiB worker ceiling,
12 GiB OS reserve and dynamic memory telemetry. Preflight found zero swap
and no competing compiler/runner/test process. No safety limits changed.
No broad build/audit/guard or root rebuild was run. Three root imports were
registered after the focused checks. Canonical chart and frontier fields
are unchanged; CI remains off.

| Final log in `/tmp/` | SHA-256 |
| --- | --- |
| `ym-bond-reflected-form-20261001.log` | `43bb2351cfddedf96bc1e6c4ec7746ea853190720ff236033986f1b9dcde626e` |
| `ym-bond-os-realization-20261001.log` | `0c7c4991cbac7fcf27de9e264c435effc328d66b8680347cbc005fcfdd8010b9` |
| `ym-endpoint-exact-coefficient-fence-20261001.log` | `3d9dc4eab1f6b61c9eff91f6cf9b59fdf1b38ec5e625f622a17a317a86689d41` |
