# Original temporal energy controls erased-marginal dual tests

Date: 2026-09-17 UTC. Base revision: `e941bcd`.

Follow-up: the reciprocal/actual-marginal join labelled open in this dated
checkpoint is now proved in `AUDIT-ACTUAL-MARGINAL-DUAL-ENERGY.md`.
The collective spatial and continuum/physical-gap obligations remain open.

Whole-project goal: nontrivial continuum Yang--Mills on R^4 for every compact
simple gauge group, with the same-theory QFT and positive physical Hamiltonian
gap, constructively within {propext, Quot.sound}. OPEN.

## Proved mathematical increment

Let g=T^n1 and a=Vg. Remove ONLY kinetic factor i, retaining the entire a at
both endpoints and all other kinetic factors. Let d_i be the resulting
message and nu'=a*d_i. For supported f,r with P_i(a*r)=0, the new theorem is

    headFloor(w) * H[nu'*f*r]^2
        <= energy(g,f) * H[nu'*r^2].

Here f is arbitrary. This bounds its original temporal energy, unlike the
previous local-sector estimate applied to energy(r) or to a multiplied f.
Neither V nor the propagated message is made into an independent spectator.

| Declaration | Exact source | Content |
|---|---|---|
| `productHeat_swap` | `lean/YMGap/Continuum/SU2QuaternionWeightedProductDualEnergy.lean:76` | Actual slice swap for any selected list, including the erased list. |
| `marginalPair` | `lean/YMGap/Continuum/SU2QuaternionWeightedProductDualEnergy.lean:115` | H[(a*K_remaining(a))*f*r], with full endpoint weight. |
| `erased_jump_pairing` | `lean/YMGap/Continuum/SU2QuaternionWeightedProductDualEnergy.lean:242` | Both mixed terms vanish; jump pairing equals twice that marginal pairing. |
| `one_factor_dual_bound` | `lean/YMGap/Continuum/SU2QuaternionWeightedProductDualEnergy.lean:263` | Supported positive-weight CS plus one heat floor; no list-length power. |
| `erasedPair` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDualDirichlet.lean:58` | Literal a*d_i pairing for a=V*T^n1. |
| `terminal_dual_energy` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDualDirichlet.lean:75` | Displayed bound in the original finite temporal energy of arbitrary f. |
| `terminalResidual_dual_energy` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDualDirichlet.lean:107` | Actual polynomial residuals supply the dual-test centering. |

The proof retains the factors of two: writing L=H[nu'*f*r], R=H[nu'*r^2],
the erased cross jump is 2L and the test jump square is 2R. CS gives
4L^2<=2J_erased*R. The heat floor gives h*J_erased<=J_full, hence
2hL^2<=J_full*R. The original `energy_identity`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:253`,
identifies J_full=2*energy(g,f), yielding the stated constant without loss.

Three shared helpers were exposed without changing their statements/bodies:
`kernel_pairing_swap`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSymmetry.lean:52`;
`certified_floor` and `factor_pairing`,
`lean/YMGap/Continuum/SU2QuaternionWeightedProductLocalGap.lean:173` and `:195`.
They are reused proofs, not new mathematical results.

## Parameter and same-object boundary

The coefficient is h=headFloor(w), explicitly nome-dependent. The statement
requires 0<w<1, K>=headCutoff(w), and an actual active link. The coefficient
has no width, boundary-depth or late-cutoff power; the action, observable,
dual test and erased marginal retain all those parameters. It is a finite
SU(2) result, not an every-group estimate or physical mass calibration.

The reference nu'=a*d_i is NOT the original odd marginal nu=a*Tg. The
actual d_i is `conditionalMessage`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialConditionalMessage.lean:58`.
Its independence is proved by `conditionalMessage_independent`, same file:71.
Only this erased message is independent of i, not g or Tg.

## Next mathematical join -- not yet a Lean theorem

For a polynomial q conditionally centered in the actual marginal, with
`RatPolyCoeffEqv (project i (polyMul nu q)) polyZero`, construct i-independent polynomial
approximants G_k to 1/d_i and use r_k=(Tg)*q*G_k. A complete argument must
prove exact P_i(a*r_k)=0, convergence of H[nu'*f*r_k] to H[nu*f*q], and
the norm budget using Tg<=U*d_i. The latter comparison is already
`conditionalMessage_capCertificate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialConditionalMessage.lean:117`.
The intended resulting local statement is

    h * H[nu*f*q]^2 <= U * energy(g,f) * H[nu*q^2].

This statement is OPEN. Formal division is not a RatPoly construction.
Finite width/depth-dependent inverse bounds may supply the approximation
modulus; they must not enter as an unreported spatial loss in the final rate.

The source-reviewed construction prescription, still UNFORMALIZED, is:
write t=Tg, M=m(g)>0, L=kineticFloor(w,width)*M and
B=kineticCap(w,width)*M. Set ell=L/U and C=B/h+ell+1. Then

    d_i-ell = U^(-1)*[(U*d_i-t)+(t-L)],
    C-d_i   = h^(-1)*[(B-t)+(t-h*d_i)]+(ell+1).

The scalar reciprocals are positive-rational operations, not function
reciprocals. The two transfer bounds are `transferStepLowerCertificate` and
`transferStepUpperCertificate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSandwich.lean:197`
and `:223`; positivity of M is `terminalMessage_mass_positive`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalBracket.lean:131`.
The existing message comparisons provide the other two certificate terms.

With alpha=1/C, rho=1-alpha*ell, R=alpha*d_i-1, set
G_k=alpha*corrector(R,k), eps_k=residual(R,k). The exact algebra is
`cancellation`, `lean/YMGap/Continuum/QuaternionHaarPolynomialGeometricInverse.lean:67`;
`residualInterval`, same file:88, does not require radius <=1/2.
Do NOT infer eps_k>=0 from that interval: construct it separately by
induction from the certificate of -R=alpha*(C-d_i). Together with
eps_k<=rho^k<=1 this gives a certificate for 1-eps_k, hence for

    1-(d_i*G_k)^2 = eps_k*(2-eps_k).

For r_k=t*q*G_k, multiply U*d_i-t by the certified background
a*d_i*t*q^2*G_k^2, then use this square cap, to obtain

    H[a*d_i*r_k^2] <= U*H[nu*q^2*(d_i*G_k)^2] <= U*H[nu*q^2].

Positivity of q or G_k is not required; their squares are used. Positivity
of a,d_i,t IS required. The independent reciprocal construction, these
certificates and the pairing limit remain work to do, not proved results
of the present checkpoint. This prescription records where only one U
enters and where an unjustified positivity shortcut must be avoided.

The full-slab star projection is not a direct substitute: `fullData`,
`lean/YMGap/Continuum/BF4ExactSlabStarFullActionProbe.lean:49`, is fixed to
the all-face slab law. Its `conditionalUpdate_pairing`,
`lean/YMGap/Continuum/BF4ExactSlabStarConditionalProjection.lean:144`, does
not identify the odd marginal's conditional projection.

Even a proved local actual-marginal bound is not a global gap. Combining
individual-link bounds with ordinary approximate tensorization incurs the
number of active links. A collective weighted decomposition/cross-energy
budget remains necessary toward `clearedDefect_diagonal_nonnegative_iff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:175`.
The full temporal mean correction, spatial/scaling control, physical mass,
continuum QFT and every-group joins remain open. No canonical atom closes.

## Verification

Four final focused checks passed, serialized through the monitored launcher
with one worker, mandatory 20 GiB ceiling and fresh process/swap preflights.
Swap stayed at 6669.00 MiB; no competing compiler/runner was observed.
The two new modules print 4+3 gates; the two shared modules print 3+12.
All final dependencies are within {propext, Quot.sound}, or empty. Final
logs have no errors/warnings/sorryAx. Initial namespace/syntax, index-bound
and equality-orientation repairs changed no mathematical claim or limit.
Independent source review checked both mixed cancellations, support, positive
weights, factors of two, original energy and the erased/actual distinction.

No sorry, new axiom, analytic guard or canonical frontier statement changed.
Two root imports added; root/full-tree/full-audit/guard NOT run. CI remains
manual-only. No literature scan occurred.

| Log under `/tmp/` | SHA-256 |
|---|---|
| `ym-transfer-symmetry-shared-api-20260917.log` | `497df12af80a740ac07e03cda693ab4bf72b0b5edbf967fa68f86ff400fb4f1d` |
| `ym-product-local-gap-shared-api-20260917.log` | `2eba26266617079328698add06eff31aa859e0237cb040c6e38a7421370850b8` |
| `ym-weighted-product-dual-energy-20260917.log` | `fa1513720584645a51dde555f1a942d1f767a014e9d3d3922ff8b429d31d3f29` |
| `ym-fixed-spatial-dual-dirichlet-20260917.log` | `6c6dda3745c53be33a36bd899e3ff5e821e8de29b7ae0b40d4aa22806e43682c` |
