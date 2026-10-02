# Centered original energy and channel heat loss

## Result and scope

The complete original growing Wilson-square energy now has an exact signed
polarization at its OWN interacting mean, and a separate sufficient ceiling
using its actual channel heat loss. Both are kernel checked. The loss-only
ceiling is optional: it does not replace the cancellation-preserving route
or establish the missing physical-scale estimate.

Let f be the original fundamental character of paddedSquare, psi=f-mu
with mu its OWN interacting mean, g the original terminal message at depth n,
and Z the SAME oddMass. Use the existing signed passive sources b_c and their
original nonnegative weights. Define

    a = w^(12*side(scale)), s = 1-a > 0,
    A = sum_c weight_c * H[b_c^2*psi^2],
    J = sum_c weight_c * H[b_c^2*psi],
    L = M-Z, D = A-Z*OWNVar,
    T = (1/2) sum_c weight_c * integral_product_heat
        [psi(x)*psi(y)*(b_c(x)-b_c(y))^2].

T and D are SIGNED; neither is asserted nonnegative. For 0<w<1,
headCutoff(w)<=K, the SEPARATE guard 2<=K, and side(scale)<width,
at EVERY terminal depth, the complete ORIGINAL energy satisfies

    E = s*(A+mu*J) + T-D,
    E/Z <= 4*s*OWNVar + (16+34*s+8/s)*(L/Z).

The first identity remains available when T-D cancellation is useful.
There is no assertion that small L is necessary, or that the second
ceiling dominates earlier ceilings numerically. All centers, sources,
partitions, channels and energies are the original ones.

## Mathematical argument

Centering changes the bare heat eigenpin into an affine identity:

    P(psi) = a*psi-(1-a)*mu.

It does NOT give P(psi)=a*psi. Symmetry and the product-heat marginals give
the exact polarization on each actual channel. Weighted aggregation joins
its interacting centered moment to Z*OWNVar and yields the displayed
complete energy identity, with both signed terms retained.

The centered cap sixteen supplies an explicit square certificate for

    16-psi(x)*psi(y)
      = (1/2)*[(16-psi(x)^2)+(16-psi(y)^2)+(psi(x)-psi(y))^2].

Testing it against the positive original product heat times the source jump
square proves T<=16L. The appended original-moment results additionally give

    sum_c weight_c * sourceMoment(b_c,psi) = 0,
    A >= 0, J^2 <= L*A, A <= 2*Z*OWNVar+16*L.

These need no extra label-two guard. Together with the already checked
D^2<=16L*A, mu^2<=4 and L>=0, root-free rational Young estimates give

    -D <= (s/2)*A+(8/s)*L,
    s*mu*J <= (s/2)*A+2*s*L,
    E <= 2*s*A+(16+2*s+8/s)*L.

Insert the linear A bound and normalize by the SAME positive Z. No square
root, variance inverse, nonzero-variance premise, source-sign premise,
active independence of the original source, or new analytic hypothesis is
used. The only inverses are the explicitly positive s and original Z.

## Declaration evidence

| Declaration | Source | Content |
| --- | --- | --- |
| `le_add_of_square_le_four_mul` | `lean/YMGap/Continuum/RationalSquareLossYoung.lean:28` | Signed root-free Young inequality |
| `square_loss_young` | `lean/YMGap/Continuum/RationalSquareLossYoung.lean:69` | Explicit epsilon-dependent rational ceiling |
| `sourceHeatCross_pin` | `lean/YMGap/Continuum/SU2QuaternionProductHeatCenteredEnergyLoss.lean:77` | Signed cross term on the original product heat |
| `productMap_shifted_affine` | `lean/YMGap/Continuum/SU2QuaternionProductHeatCenteredEnergyLoss.lean:133` | Correct affine centered heat image |
| `sourceEnergy_centered_polarization` | `lean/YMGap/Continuum/SU2QuaternionProductHeatCenteredEnergyLoss.lean:173` | Entire generic centered energy identity |
| `sourceHeatCross_le_cap_loss` | `lean/YMGap/Continuum/SU2QuaternionProductHeatCenteredEnergyLoss.lean:219` | Constructed cap certificate gives the cross upper bound |
| `centeredChannelFirstMoment` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceLoss.lean:432` | Actual raw first moment at OWN center |
| `paddedSquare_channel_centered_heat_firstMoment_zero` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceLoss.lean:471` | Original centered interacting moment vanishes |
| `centeredChannelSquare_nonnegative` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceLoss.lean:497` | A>=0 |
| `paddedSquare_channel_firstMoment_loss_bound` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceLoss.lean:523` | J^2<=L*A |
| `paddedSquare_channel_square_linear_bound` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceLoss.lean:591` | A<=2*Z*OWNVar+16L |
| `paddedSquare_channel_heatLoss_pin` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceLoss.lean:620` | Actual source loss equals M-Z |
| `squareOwnMean` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCenteredEnergyLoss.lean:101` | SAME original mean |
| `squareHeatGap_positive` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCenteredEnergyLoss.lean:111` | Witnessed positive denominator s |
| `squareCenteredHeatCross` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCenteredEnergyLoss.lean:121` | T on actual channels |
| `squareCenteredMomentDefect` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCenteredEnergyLoss.lean:131` | Signed D at OWN variance |
| `paddedSquare_energy_centered_loss_identity` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCenteredEnergyLoss.lean:144` | Exact original signed identity |
| `paddedSquare_centered_cross_le_loss` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCenteredEnergyLoss.lean:246` | Actual T<=16L |
| `half_gap_young` (private) | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCenteredEnergyLoss.lean:270` | Explicit half-gap absorption |
| `complete_scalar_bound` (private) | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCenteredEnergyLoss.lean:293` | Complete scalar ceiling |
| `paddedSquare_energy_centered_loss_bound` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCenteredEnergyLoss.lean:356` | Original normalized energy bound |

## Remaining physical input

OPEN: a useful bound on this SAME complete energy relative to OWN variance
on a physically justified changing family. The exact signed T-D route and
the optional L-only ceiling are alternatives, not cumulative prerequisites.
The explicit coefficient 8/s is singular as s approaches zero; no useful
bound on L/Z relative to OWNVar and physical spacing is supplied here.
Parameter-free numerical constants do not make these original moments or
their ratios uniform in coupling, width, cutoff, depth or spacing.

The existing completed consumer
`response_ge_fraction_of_relative_energy` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointEnergySurvival.lean:97`
requires a relative temporal-energy estimate for its SAME completed state.
The finite scalar theorem above does not by itself supply that state join
or the required useful changing-family budget. The related
`marginRate_le_of_relative_energy` at the same path, line 167, is a necessary
rate constraint from a supplied state and spacing, not an all-vector gap
producer or physical calibration theorem.

Nonzero continuum survival, physical mass calibration, full SAME-theory QFT,
every actual compact simple group and the Clay result remain OPEN. No
canonical field is weakened or discharged. Exact chart claims are unchanged.
The requested papers supply methods, not these missing inputs; their cached
screen is in `RESEARCH-REQUESTED-FIFTEEN-PAPERS-2026-10-02.md`.

## Verification boundary

Four serialized focused checks passed, each with one worker and explicit
20-GiB ceiling under fresh capacity checks. Their 3+10+6+12 printed outputs
remain within {propext,Quot.sound}; quarter, qpow_rg and squareHeatGap are
axiom-free. The accepted variance-loss log has ten unchanged unused-variable
warnings. The other three accepted logs have no warnings or errors.
Rejected drafts are NOT evidence: the first variance append, first two generic
polarization checks and first three concrete consumer checks were repaired
without changing the mathematical statements, guards or resource limits.

The variance-loss change appends 246 lines, preserving its original 385-line
HEAD prefix byte-for-byte (prefix SHA-256
`209d1284159bc4d921abdada2d29cdf86f1a5c58cfdbef96e95677aa6ddc5d26`).
Independent Sol mathematical review and Luna read-only evidence review passed.
No sorry, new axiom, classical shortcut or compiler-trusted decision was added.
One root import exposes the final consumer and its new dependencies. Root/tree
builds, broad audit/guard and progress metric were NOT run. CI stays unchanged.

| Source or accepted log | SHA-256 |
| --- | --- |
| `lean/YMGap/Continuum/RationalSquareLossYoung.lean` | `4a2d1cb64c23ebd8e94b68df02baa5222a4a5fbf35322dc7b18c1e7c942648bc` |
| `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceLoss.lean` | `9131421d5920110c67667e2fd3a64e7a54939ff771573b36b89044adfd7566ba` |
| `lean/YMGap/Continuum/SU2QuaternionProductHeatCenteredEnergyLoss.lean` | `adfaf78252a0d25a5d281a5584a07f8349133031941bc5be05ca8a069e9f12f4` |
| `lean/YMGap/Continuum/BF4DyadicWilsonSquareCenteredEnergyLoss.lean` | `4b7fd0ee389b69733ff30263b2741145d87b247e0d3869249fb01836bdf61a2c` |
| `/tmp/ym-rational-square-loss-young-20261002-first.log` | `771e14a1520213a4bea48285242de7e54841c3a33f892de5797cd5daf753902b` |
| `/tmp/ym-centered-channel-first-linear-loss-20261002-second.log` | `696e2e08d0f8a01af8b08a7964b5ad3c57ff4811709ee0012397b652248e1666` |
| `/tmp/ym-centered-heat-polarization-20261002-third.log` | `504b0c48df19005acc565511ad4029844187b8bf4befa9bc6a4c49721a455dc8` |
| `/tmp/ym-original-centered-energy-loss-20261002-fourth.log` | `761a9418304e534c3eb7b41cddd419425f678700d3fc7c04d7fd0070210d08d8` |
