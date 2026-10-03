# Normalized survival and continuity from a macroscopic ratio

The existing original positive-time excitation now needs only one supplied
macroscopic response comparison to obtain normalized survival and continuity.
An adjacent-response budget is a sufficient alternative, not a mandatory
intermediate input. This reduction does not produce the comparison on a
justified scaling family or establish any continuum endpoint.

## Exact input and unchanged objects

Let s=side(scale), u be the existing dyadic unit excitation, R(j) its SAME
original completed-transfer response, N=R(2*s) and alpha the already
constructed inverse square root of N. The normalized state remains
z=alpha*T(s)u, with its original bond-range and vacuum-complement witnesses.
No new carrier, observable state, normalizer or frontier structure is added.

The sole analytic comparison is

    kappa*R(s) <= R(2*s),   kappa>0 rational.

There is no start, microscopic lag budget, raw R(1) reserve or uniform lower
bound on N. A family-uniform conclusion requires the SAME positive kappa
at every family index and a proved ratio for those actual parameters.

## Proved consequences

All declarations below are in
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean`.

`halfAnchorPreimage_norm_cleared:115` uses the existing
y=alpha*T(s/2)u, s>=2, to prove kappa*B(y,y)<=1 directly from the ratio.
The proof multiplies by alpha twice and uses alpha^2*R(2*s)=1; it does
not divide an absolute modulus by a collapsing raw norm.

`normalizedAnchorResponse_block_floor:132` proves, for every natural j,

    B(z,T(j*s)z) = R((j+2)*s)/R(2*s) >= kappa^j.

The displayed quotient is descriptive notation. The declaration itself
uses the constructed CReal representative, multiplication and exact
normalization, without assuming division. This result does not need s>=2.
It first propagates the s-to-2*s ratio to 2*s-to-3*s using the original
positive time form, then applies the checked block-response induction.

`normalizedMesh_increment_bound:184` controls every actual dyadic increment
by half^k/kappa when its time is at most (s/2)*half^k, s>=2.
`macroGeometricRadius:204` computes the positive rational radius

    delta(kappa,epsilon) = (1/4)*2^(-(epsilon*kappa).den).

`macroGeometricRadius_positive:207` proves its positivity.
`normalizedBond_geometric_real_increment:300` and
`normalizedBond_geometric_real_forward_increment:322` transport the estimate
to ALL represented positive real bond times and forward orbit increments:
if spacing(scale)*t<=delta, the squared distance is at most epsilon>0.
The radius depends only on kappa and epsilon, not nome, width, scale or N.

Spacing here is the existing assigned geometric 1/s. Neither this statement
nor the block floor identifies that assignment with physical Yang--Mills
time or supplies a cross-scale/local-field comparison. The original u and
normalized positive-time z are not silently identified.

## Forward and backward meeting input

The immediate forward target is now a family-wide macroscopic ratio for
the SAME interacting transfer, rather than necessarily an adjacent 1/s
defect estimate. The prior signed-gain, local-covariance and radial-cost
results remain available tools; they do not yet produce either input.

The backward cross-scale seam still requires BOTH-order normalized scalar
comparisons, not merely additive comparisons of raw responses. For
N_k=R_k(2*s_k), matched samples t_k require, with effective moduli,

    R_k(t_k)*N_l <= R_l(t_l)*N_k + epsilon*N_k*N_l,

and the reverse inequality. No such family comparison is proved here.
Full QFT, nontrivial continuum survival, physical mass calibration and the
every-group Clay endpoint remain OPEN. No canonical field has been weakened.

## Focused verification

Final second focused check passed all seven printed gates within
{propext, Quot.sound}; the radius definition is axiom-free. Independent
source/log review confirmed the SAME objects, guards, formulas and hashes.
No new sorry, axiom or classical shortcut. Root import registered, NOT
aggregate-checked; no full build/audit claimed. CI and chart fence unchanged.

The safe launcher used one worker, a 20-GiB worker cap and a 12-GiB reserve.
Fresh preflight found no competing compiler, 85% memory-pressure-free and
zero swap. Accepted log: `/tmp/ym-normalized-macro-ratio-20261003-second.log`.
SHA256 source/log pair:

    e67bff288126c8822641c6711e62fc20e4cf517d052d8e3bada8cd8a4c1898cc
    44ac2ee5871a84f567bbb5cbddc3399eb19c763c615d314ada3b9a9645e95134

The rejected first draft had missing namespace names and downstream sorryAx
outputs. Only the corrected final source and second log are accepted evidence.
