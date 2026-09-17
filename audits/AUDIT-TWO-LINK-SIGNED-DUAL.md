# Signed two-link control on the original temporal energy

Date: 2026-09-17 UTC. Base revision: `2dc9443eafa2003c798959159b92bf455797591d`.

Whole-project goal: for every compact simple G, construct nontrivial continuum
Yang--Mills on R^4 with same-theory QFT axioms, isolated vacuum, and a positive
finite physical Hamiltonian mass gap, within the constructive axiom gate.
That goal remains OPEN. This checkpoint is an actual finite SU(2) estimate.

## Proved mathematical increment

Write g=T^n1, a=Vg, t=Tg, nu=a*t, h=headFloor(w), U=prefixCap(w). Erase
only kinetic factor i to get d_i, only j to get d_j, and both to get d_ij.
For distinct active i,j and supported f,r,s with P_i(a*r)=P_j(a*s)=0,

    h * (H[a*d_i*f*r] + H[a*d_j*f*s])^2
      <= energy(g,f) * (H[a*d_i*r^2] + H[a*d_j*s^2] + 2*h*H[a*d_ij*r*s]).

This is `terminal_two_link_dual_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLinkDual.lean:78`.
The energy observable f is arbitrary. The signed cross term is retained;
no smallness, orthogonality, absolute-value bound, or factor-two separate-test
estimate is assumed. All endpoint and remaining kinetic factors stay present.

The existing consumer still requiring collective control is
`clearedDefect_diagonal_nonnegative_iff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:175`.
It has the original marginal mean correction and partition factors. The new
two-link result does NOT prove its diagonal nonnegative at an improved rate.

## Four positive cells and exact normalization

With remaining edge weight mu, heat factors A,B, and jumps z,x,y, use

    weights = [mu*(A-h)*(B-h), mu*h*(B-h), mu*h*(A-h), mu*h*h]
    u       = [z, z, z, z]
    v       = [0, x, y, x+y].

The constructed positive form satisfies

    B(u,u) = J = H[mu*A*B*z^2]
    B(u,v) = h*L,  L = H[mu*B*z*x] + H[mu*A*z*y]
    B(v,v) = h*Q,  Q = H[mu*B*x^2] + H[mu*A*y^2] + 2*h*H[mu*x*y].

All four weight certificates are constructed from the original certificates.
Cauchy--Schwarz and h>0 give h*L^2<=J*Q. This is `two_factor_dual`,
`lean/YMGap/Continuum/QuaternionHaarTwoFactorDual.lean:85`.
The positivity of Q comes from this form, not from imposing a sign on the
cross term. No inverse heat factor or square root is constructed.

`erased_jump_pairing`,
`lean/YMGap/Continuum/SU2QuaternionWeightedProductDualEnergy.lean:242`,
already supplies the one- and two-erasure jump identities. Its arbitrary
remaining list can miss both selected links; one centered input suffices.
`two_link_dual_bound`,
`lean/YMGap/Continuum/SU2QuaternionWeightedProductTwoLinkDual.lean:68`,
specializes the four cells to actual SU(2) heat factors. Actual list
permutations retain every other factor exactly once. With
L=2*(L_i+L_j), Q=2*(R_i+R_j+2*h*C_ij), and J=2*energy(g,f),
the two-link statement above has exactly h on its left, not 2*h or h/2.
The original normalization is `energy_identity`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:253`.

## Actual marginal and determinant: no hidden cross hypothesis

The physical module constructs the following declarations, all under
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLinkDual.lean`:

| Declaration | Line | Meaning |
|---|---:|---|
| `twiceErasedMessage` | 60 | d_ij from the full V*T^n1 source and twice-erased actual list. |
| `twiceErasedMessage_supported` | 64 | Original finite slice support. |
| `crossPair` | 71 | H[a*d_ij*r*s], signed. |
| `messageDeterminant` | 141 | Delta_ij=t*d_ij-d_i*d_j, with no sign premise. |
| `messageDeterminant_supported` | 146 | Support of that actual polynomial. |
| `correctedCross` | 162 | H[nu*q_i*q_j*(d_i*G_i,k)*(d_j*G_j,l)]. |
| `determinantCross` | 171 | H[nu*Delta_ij*q_i*q_j*G_i,k*G_j,l]. |
| `dualTest_cross_pin` | 179 | Exact split of the twice-erased pairing into the previous two rows. |
| `actual_signed_two_link_bound` | 200 | Two-link estimate with diagonals paid by U times actual nu-norms. |

Here G_i,k and G_j,l are the already constructed independent polynomial
reciprocal approximants, and r=t*q_i*G_i,k, s=t*q_j*G_j,l. Thus exactly

    H[a*d_ij*r*s] = correctedCross + determinantCross.

There is no factor two in this identity; the energy estimate multiplies
its entire right side by 2*h. Actual centering P_i(nu*q_i)=P_j(nu*q_j)=0
supplies the required a-centerings through `dualTest_centered`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualMarginalDual.lean:111`.
`dualTest_norm_bound` in the same file:164 supplies each one-U diagonal
budget. Consequently the final right-hand budget is

    U*(H[nu*q_i^2]+H[nu*q_j^2]) + 2*h*(correctedCross+determinantCross).

The left-hand pairings still use the finite approximating tests r,s.
No collective k,l limit or determinant summability has been proved here.

## Audit-driven execution decisions and remaining inputs

1. **Target the determinant correction, not raw off-diagonal smallness.**
   The ordinary corrected nu-pairing remains in `dualTest_cross_pin`:179.
   The signed remainder is the source-dependent Delta_ij. A controlled
   finite-family energy estimate and its summed determinant budget remain
   open. Adding all two-link inequalities does not supply these without
   multiplicity losses. No locality of the integrated terminal message or
   nonneighbor determinant vanishing is claimed.
2. **Keep complete coverage, including averaged fringe coordinates.**
   `step`, `lean/YMGap/Continuum/SU2QuaternionHeadChainComposition.lean:75`,
   integrates all lower blocks, not only the active heat factors.
   `productMap_independent_of_not_mem`,
   `lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:306`, records
   disappearance of inactive output coordinates. Inactive is not frozen.
   `terminal_energy_variance_floor`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletCoercivity.lean:242`,
   already gives a width-dependent positive fraction for all supported f.
   Active-only residuals still require a fringe remainder or a proved
   sufficient domain reduction. The next coverage target is a controlled
   approximation of the actual centered observable Z*f-H[nu*f], Z=H[nu],
   in the SAME nu-norm, with explicit modulus and total signed cost.
   This is a planning target, not a supplied decomposition declaration.
3. **Do not identify support with gauge invariance.**
   `invariant_original_chain_pairing`,
   `lean/YMGap/Continuum/BF4ExactSlabTemporalInvariantSweep.lean:94`, requires
   temporal gauge invariance explicitly. Wilson tests provide it through
   `placed_ledger_invariant`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindow.lean:232`.
4. **Keep the scaling and whole-project boundaries.**
   Theorems explicitly take 0<w<1, K>=headCutoff(w), width/depth, and
   distinct active links. h and U depend on w; d_ij and the determinant
   depend on the original source and parameters. Reciprocal degrees k,l
   are finite and explicit. No beta-uniform positive margin is claimed.
   The four-cell argument itself supplies no non-abelian mass-generation
   mechanism. Spatial/scaling control, full same-theory QFT and Hamiltonian
   calibration, positive finite physical mass, and every compact simple
   group remain OPEN. No canonical frontier type or guard is changed.

## Verification boundary

Three final focused Lean checks passed, serialized through the monitored
launcher with one worker and the mandatory 20 GiB ceiling. Fresh safety
preflights found no competing compiler/runner; swap stayed 6669.00 MiB.
All 1+2+10 printed axiom gates use only {propext, Quot.sound}. Final logs
contain no errors, warnings or sorryAx. Initial namespace-reference repairs
changed no mathematical statement. Two independent read-only mathematical
reviews passed, checking factors, erasures, actual marginal, guards, and scope.

No sorry, axiom, classical shortcut, canonical atom closure, CI setting or
resource-limit change. Three root imports added. Root/full-tree/full-audit/
guard checks were NOT run; this is focused verification only. No literature
scan occurred.

| Log under `/tmp/` | SHA-256 |
|---|---|
| `ym-two-factor-dual-20260917.log` | `d62dd3beaec7153258ee07d943181b76ccfd4060c178cc7fda47f46ac2487f4e` |
| `ym-product-two-link-dual-20260917.log` | `a5cc510e4a0f843dd0b6ab8e3b78287c03dcdc15a28daed25cb5b58bac56f57c` |
| `ym-physical-two-link-dual-20260917.log` | `27f644956c3efd4d783d5c71a71f24c070999ca0ebd5b9ad79abbd092c2a84d6` |
