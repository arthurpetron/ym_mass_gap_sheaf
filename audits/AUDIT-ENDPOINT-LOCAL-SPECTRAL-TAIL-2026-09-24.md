# Original endpoint regularity and computed one-link harmonic tail

2026-09-24 UTC. Checked original-source refinement after `39c9463`.
All five leaves passed narrow serialized checks. A03 and the continuum
Clay target remain OPEN.

## Mathematical input: the complete original source

Use q=P_fringe(V*g_n), the existing `projectedEndpointSource` with the
original `spatialWeight` and `terminalMessage`. No action factor or terminal
history is removed. Define

    B_d(w) = relativeCap w d = d*JacobiShiftedRelativeSlope.budget(w)+1,
    C(w) = endpointRelativeCap w = 6*B_4096(w)+B_32(w),
    K_reg(w) = max(relativeCutoff w 4096, relativeCutoff w 32).

For 0<w<1 and K>=K_reg(w), each angular derivative D at an original active
link has constructed positive-cone certificates for C*q-Dq and C*q+Dq.
The six incident-face upper bound follows from the actual 4D link/plaquette
incidence list. The face scalar derivative cap 4096 is conservative finite
polynomial algebra, not a claimed sharp constant. The terminal bound includes
n=0 explicitly; positive depths use the existing output-heat bound. Actual
fringe Haar integration preserves both relative certificates because the
active differentiated link is absent from the integration schedule.

Multiplication of the two certificates, followed by any certified positive
polynomial background R, gives

    H[R*(Dq)^2] <= C(w)^2 H[R*q^2],
    H[R*angularSquare_link(q)] <= 6*C(w)^2 H[R*q^2].

R may share variables with q. This estimate does not divide by q or require
strict positivity of its value. Its constants and cutoff depend on w, not on
width, terminal depth, selected active link, or K above that cutoff.

## Computed tail and its actual consumer

The tail construction groups the existing Fischer expansion by harmonic
degree and retains degrees strictly above L, including every cross term
within a degree. Weighted orthogonality of distinct degrees and Casimir
eigenvalues give the threshold lambda_L=(L+1)*(L+3). The general theorem
retains a certified head-independent background. Reindexing an actual link
to the head and back gives the ORIGINAL source consumer with R=1:

    lambda_L * H[high_L(q)^2] <= 6*C(w)^2 * H[q^2].

`endpointTailDegree w epsilon he` is the natural numerator of the explicit
positive-denominator quotient 6*C(w)^2/epsilon. It is a coarse computable
upper bound, not the minimal threshold. For every L at least that value,

    H[high_L(q)^2] <= epsilon * H[q^2].

The cutoff K and harmonic threshold L are distinct parameters. The source
can have arbitrarily high polynomial degree as width/depth/K change; the
bound does not assume its degree is at most K or L. No lower bound on its
raw norm is assumed. No coupling- or spacing-uniformity is asserted.

## Declaration map

| Declaration | Source | Role |
|---|---|---|
| `familyProjectRelativeBound` | `lean/YMGap/Continuum/SU2QuaternionHaarFamilyRelativeBound.lean:65` | Preserve the relative cone through the actual fringe schedule. |
| `relativeWeightedSquare` | `lean/YMGap/Continuum/SU2QuaternionHaarFamilyRelativeBound.lean:125` | Square consequence with an arbitrary certified positive background. |
| `spatialIncidentFaces_length_le_six` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalRelativeBound.lean:70` | Width-independent local incidence count. |
| `plaquetteScalarAngularInterval` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalRelativeBound.lean:213` | Explicit conservative face derivative certificate. |
| `spatialWeightRelativeBound` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalRelativeBound.lean:301` | Complete spatial action, including independent complementary factors. |
| `endpointRelativeCap`, `endpointRelativeCutoff` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointRelativeBound.lean:59`, `:63` | Explicit fixed-nome data. |
| `projectedEndpointRelativeBound` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointRelativeBound.lean:96` | COMPLETE original projected source, every terminal depth. |
| `projectedEndpointAngularSquare_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointRelativeBound.lean:130` | Six-plane selected-link bound. |
| `spectralHighPart` | `lean/YMGap/Continuum/SU2QuaternionGroupedHarmonicTail.lean:57` | Computed high-degree polynomial, with within-degree sums retained. |
| `spectralHighPart_threshold_le_energy` | `lean/YMGap/Continuum/SU2QuaternionGroupedHarmonicTail.lean:543` | Weighted tail paid by the ORIGINAL input's angular energy. |
| `selectedSpectralHighPart_threshold_le_energy` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointSpectralTail.lean:70` | Actual selected-link recoding back to the original carrier. |
| `projectedEndpoint_highTail_bound` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointSpectralTail.lean:111` | Original projected terminal source, fixed-nome uniform local tail. |
| `endpointTailDegree`, `endpointTailDegree_sufficient` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointSpectralTail.lean:139`, `:142` | Executable threshold and its inequality. |
| `projectedEndpoint_highTail_small` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointSpectralTail.lean:164` | Explicit epsilon-small tail on the SAME raw source norm. |

## Causal residue and rejected identifications

This is a one-link RAW HAAR tail estimate, not a spectator-smoothed quadratic,
joint four-link truncation, positive interacting variance, or scaling theorem.
The next required join retains the actual `familyChannelQuadratic` instead
of replacing it by raw H[q^2]. Its sources are signed Gram channels; positivity
of the channel coefficients does not make those sources positive polynomials.

A proposed equality with H[q*productMap(spectators,q)] was rejected by source
review. `SU2QuaternionProductHeatMarginals.productMap_nil`
(`lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:84`) is global
Haar averaging, whereas `familyProject []` is identity and the empty-family
channel quadratic is H[q^2]. Thus the proposed general equality has the wrong
operator even before any estimate. This is a source/mathematical diagnostic,
not a new Lean counterexample theorem.

The precise missing producer is conditional mixed positivity

    sum_c lambda_c H[P_F(u*c)*P_F(v*c)] >= 0

for supported certified nonnegative u,v, with the active coordinates shared.
The existing one-head square identity is
`SU2QuaternionSharedHeadGramPairing.copy_lift_pair_eq_project_square`
(`lean/YMGap/Continuum/SU2QuaternionSharedHeadGramPairing.lean:109`).
The generic selected-set mixed identity is not supplied by this milestone.
The reviewed candidate construction swaps only spectator coordinates between
two copies; existing certificate extension and reindexing preserve positivity.
Its conditional Fubini/Gram identification still needs a proof. No new named
analytic hypothesis is introduced in place of that proof.

An earlier smallness shortcut 24*(1-w)*C(w)^2<1 was also rejected by elementary
source-level algebra, not by a new kernel-checked refutation. Here
C(w)=24608*budget(w)+7 and budget(w)=2w/((1-w)^2*(1-w^2)) on 0<w<1.
For w<=1/2 the proposed left side is at least 588; for w>=1/2,
budget(w)>=(1-w)^(-2) also excludes the condition. The adjustable harmonic
threshold avoids that assumption; it does not repair the missing conditional
quadratic, retained four-link heat floor, or SAME centered-variance comparison.

## Verification record

Five accepted narrow checks passed 28 printed gates, all within
{propext, Quot.sound}, each serialized with a 2 GiB worker cap:

- `/tmp/ym-gap-family-relative-bound-check-3.log`: four permitted gates.
- `/tmp/ym-gap-local-relative-bound-check-3.log`: three permitted gates.
- `/tmp/ym-gap-endpoint-relative-bound-check-1.log`: six permitted gates.
- `/tmp/ym-gap-grouped-harmonic-tail-check-6.log`: eight permitted gates.
- `/tmp/ym-gap-endpoint-spectral-tail-check-1.log`: seven permitted gates.

The final logs have no errors or warnings. Draft namespace, coefficient
association, empty-list and weighted-IBP transport errors were repaired.
A local 800000-heartbeat trial still timed out; correcting the association
directions and using typed intermediates resolved it at the DEFAULT limit.
That override was removed. No memory ceiling or reserve was raised/lowered,
and no safety interruption occurred in these checks. An independent read-only
review confirmed the actual-source, parameter and norm boundaries.

No new hole, axiom, analytic premise or canonical-field change. The semantic
root imports the endpoint consumer and therefore all five new leaves.
No full-root build, full-tree audit, guard or progress script has been run.
The 12 GiB reserve is unchanged. Canonical chart schema 1 is unchanged;
snapshot 5 records partial A03 evidence only. No goal-node status changes.
