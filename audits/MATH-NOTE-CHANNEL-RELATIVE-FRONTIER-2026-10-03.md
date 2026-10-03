# Original channel relative frontier — mathematical review, 2026-10-03

Scope: source-reviewed reasoning; the finite comparison below was subsequently
kernel-checked in the explicitly cited OWN-variance increment module.
The unchanged goal is the SAME continuum Yang–Mills theory and physical mass
gap for every compact simple group. Changing-family survival, physical
calibration, the canonical OS/QFT realization and the Clay target remain OPEN.

## Exact nonperturbative alternative to the Taylor ceiling

Let f be the original padded-square fundamental trace, g=terminalMessage_n,
Z=oddMass_n, s=side(scale), a=w^(12s), d=w^(32s). Let M and F be the actual
passive-channel raw mass and f² moment, with all original channel weights,
and let I be the complete channel source-increment cost. The checked identity is

    4 E + I = 2 B,   B=(1-d)M+(1+d-2a)F,
    E/Z = B/(2Z) - I/(4Z).

`paddedSquare_terminal_channel_cost` is at
`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelCost.lean:135`;
the normalized identity and ceiling retaining computed response squares R<=I
are `paddedSquare_energy_exactChannel_increment` and
`paddedSquare_energy_exactChannel_response_bound` at
`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelExactResponse.lean:217,237`.
The normalized consumer keeps 0<w<1, headCutoff(w)<=K, K>=2 and s<width.
There are no cubic/omitted-mode debts here, and no sign is assigned to 1+d-2a.
Passive projection retains conditional active sources, not a source-free law:
`sourceEnergy_projected_channels`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatPassiveChannels.lean:252`.

The checked OWN join is A<=2Z*OWNVar+16L, with A the raw OWN-centered channel
square and L=M-Z>=0, not a paid relative bound on L:
`paddedSquare_channel_square_linear_bound`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceLoss.lean:591`.

## Constant-one finite comparison — now kernel-checked, with retained mean square

With the actual OWN center c_n and psi=f-c_n, the first centered energy term
is Z*OWNVar; the subtracted term ell[(g_n psi) T(g_n psi)] is nonnegative.
The actual selected-product Gram floor is stronger than nonnegativity:
ell(h*T h)>=ell(h)^2. Thus, with L=ell(g_n*psi), the checked identities give

    I+4Z*OWNVar = 2B+4*ell((g_n*psi)*T(g_n*psi)),
    2B+4L^2 <= I+4Z*OWNVar.

The original OWN center does NOT imply L=0. All three statements are checked
in `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelOwnVariance.lean`:
`transferStep_quadratic_ge_mean_square`:65,
`paddedSquare_channel_ownVariance_identity`:103, and
`paddedSquare_channel_ownVariance_lower`:128. Verification:
`audits/AUDIT-ORIGINAL-CHANNEL-OWN-VARIANCE-2026-10-03.md`.
The previously derived E/Z<=OWNVar is now backed by this stronger actual
estimate, but it remains a unit-coefficient ceiling, not the needed rate.
Ingredients: `centered_source_square` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceVarianceGram.lean:89`,
`transferStep_quadratic_nonnegative` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferPositive.lean:67`, and
`energy_shifted` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyBandResponse.lean:130`.
Analytically Q_n f=T(g_n f)/g_(n+1) is reversible for the ORIGINAL odd law
V*g_n*g_(n+1); its symmetric edge is K*(Vg_n)_x*(Vg_n)_y.
No polynomial reciprocal or constructed Markov kernel is asserted here.
Coefficient one is PSD response, not the required O(1/s) filtered rate.

## Perron caution and remaining producer

Since T=P M_V, Tg=lambda*g gives P(Vg)=lambda*g, NOT lambda*Vg.
Perron stationarity alone does not remove `energy_eq_bare_add_correction`'s correction:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean:60,144`.
A non-BF4, non-kernel-checked diagnostic is P_h=[[1-h,h],[h,1-h]], V=diag(2,1),
0<h<1/2. Its positive reversible transfer has lambda_+>=2(1-h),
lambda_-<=1-h, so its centered Doob mode has relative loss >=1/2 as h->0.
Perron normalization and near-identity bare heat alone do not produce a rate.

The unpaid original target remains s*D<=C*Z1*ell(b²), with A=g_(n+t),
b=T^t(g_n*(f-c_n)), Z0=ell(A²), Z1=ell(A*TA), and
D=Z1*ell(b²)-Z0*ell(b*Tb), on a JUSTIFIED changing family.
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:136,157`
pins ell(b²)/Z0 and D/(Z0Z1) to the SAME norm-cleared response and drop.
Neither the channel formula nor the checked constant-one comparison supplies
the action-specific combined signed cost bound against the filtered norm.
Once that relative bound exists, the existing macro consumer does not
require an additional absolute lower floor on the shrinking response:
`response_anchor_bridge` in
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedAnchorContinuity.lean:175`
handles start=m=side>=4C directly. This is a source-reviewed existing
implication, not a new physical instance or kernel check in this note.
