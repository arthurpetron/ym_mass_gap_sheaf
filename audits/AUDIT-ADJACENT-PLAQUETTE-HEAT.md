# Shared-link SU(2) heat channels and signed adjacent-plaquette defect

Date: 2026-09-17 UTC. Base revision: `7953a70`.

Whole-project goal: nontrivial continuum Yang--Mills on R^4 for every
compact simple gauge group, with same-theory QFT structure and a positive
physical Hamiltonian gap, constructively within {propext, Quot.sound}. OPEN.

## Mathematical result and exact scope

The original relative heat prefix, with cutoff K>=2, acts on a product of
two functions linear in its shared source quaternion through two channels:
trace-free quadratic transmission w^8 and the retained scalar contraction.
The new calculation keeps both, including their signed difference from the
product of the two degree-one multipliers. It is not another normalization
comparison and does not replace the complete interacting input by Haar.

For the literal adjacent fundamental plaquette traces P,Q, and the trace R
of their outer rectangle, the shared-link result is

    heat_shared(PQ) = w^8*PQ + (1-w^8)*R/2,
    shared defect  = (w^8-w^6)*PQ + (1-w^8)*R/2.

These are equalities after pairing with an arbitrary retained polynomial.
They integrate the shared source link only. No extra w^18 from the six
outer links is claimed. The signed defect is not the global connected
correlation or the full terminal C_delta. The literal plaquette words have
not yet been placed into the complete fixed-spatial action by a new physical
embedding theorem in this checkpoint.

## From harmonic transmission to the literal word calculation

The previously proved ingredients are
`quadratic_heat_transmission`,
`lean/YMGap/Continuum/SU2QuaternionQuadraticHeatTransmission.lean:183`,
and `shared_link_contraction`,
`lean/YMGap/Continuum/SU2QuaternionAdjacentPlaquetteGluing.lean:194`.
The latter is Haar elimination; it does not by itself retain the shared
heat factor. The former transmits the trace-free quadratic, not its trace.

`coordinatePair_transmission`,
`lean/YMGap/Continuum/SU2QuaternionQuadraticHeatProduct.lean:122`, recombines
the trace and trace-free contributions. In coordinate notation its output is

    w^8*y_i*y_j + (1-w^8)*delta_ij/4.

The sphere radius is replaced by one only inside the original Haar pairing.
No false free-polynomial equality is used. `retainedLinear` and
`linearProductImage`, same file:152 and :157, construct the finite-list
output. `linear_product_transmission`, same file:262, proves its pairing
identity. Each coefficient polynomial may depend on the target quaternion
and on other retained coefficients; it may not depend on the eliminated
source. No support or target-independence assumption is hidden in this step.

`path_heat_transmission`,
`lean/YMGap/Continuum/SU2QuaternionAdjacentPlaquetteHeat.lean:166`, turns
that calculation into an ordered quaternion-path identity, retaining the
Schur factor 1/2 for fundamental characters. It does not commute quaternion
factors: the existing associative/cyclic trace identities supply the recoding.

`sourceAdjacentProduct`, same file:187, is literally

    plaquette(2,0,6,7) * plaquette(3,4,5,0).

The source is block 0, its heat target is block 1, and the six outer links
are blocks 2..7. After source integration the target is block 0 and the
outer links are 1..6. `adjacentImage`, same file:192, uses the existing
`adjacentProduct` and `liftHead rectangle` in those coordinates.
`adjacent_heat_transmission`, same file:269, proves the displayed two-channel
formula with `tailBlocks>=7`, arbitrary rational w and K>=2.

The full relative prefix is retained. K>=2 ensures inclusion of the
quadratic mode and suffices for the exact identities; it is NOT a proof
that this finite prefix is positive for every w. No late-cutoff positivity
guard was weakened.

## Signed coefficients and cancellation bounds

`sharedDefectImage`,
`lean/YMGap/Continuum/SU2QuaternionAdjacentPlaquetteHeat.lean:288`, is
parametrized by the explicit rates

    b = 1-w^8,
    a = 1+3*w^8-4*w^6,
    sharedDefectImage = ((a-b)/4)*PQ + (b/2)*R.

`sharedDefectImage_channels`, same file:294, identifies this with the
two-channel image minus w^6*PQ. `adjacent_shared_defect`, same file:326,
proves the signed subtraction on the SAME retained Haar pairing. In
particular, no separate absolute estimate removes the negative coefficient
w^8-w^6 when 0<w<1. A signed test or two different plaquettes do not acquire
a nonnegative scalar pairing merely from the following rate inequalities.

All rate assertions have their actual nome dependence explicit:

| Result | Declaration and source |
|---|---|
| b=1-w^8 | `transverseRate`, `lean/YMGap/Continuum/SU2QuaternionHeatCovarianceRates.lean:28` |
| a=1+3w^8-4w^6 | `radialRate`, same file:30 |
| a=(1-w^2)^2(1+2w^2+3w^4) | `radialRate_factorization`, same file:34 |
| b-a=4w^6(1-w^2) | `transverseRate_sub_radialRate`, same file:46 |
| 0<=a<=b | `radialRate_nonnegative` and `radialRate_le_transverseRate`, same file:64 and :73 |
| 0<=b<=8(1-w) | `transverseRate_nonnegative` and `transverseRate_le_eight_linear`, same file:83 and :89 |
| a<=24(1-w)^2 | `radialRate_le_twentyFour_quadratic`, same file:111 |

The inequalities require 0<w<1; the identities allow any rational w.
They are scalar bounds, not an already proved pointwise covariance-matrix
norm theorem or a beta-uniform mass gap. Their SU(2) values come from the
quaternion character channels w^3, w^8 and Schur factors 1/4, 1/2; no
arbitrary compact-group instance is asserted.

## Remaining actual-action join

The full original transfer is `transferStep`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferStep.lean:51`,
with spatial potential `spatialWeight`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSliceHeat.lean:70`, and actual
iterate `terminalMessage`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalBracket.lean:118`.
Other incident plaquettes and that terminal message generally use the
shared source. They CANNOT be silently put into the retained test r of
the new identity. A complete-star expansion/comparison and a quantitative
signed remainder estimate are still required.

The intended global consumer is still
`terminal_normalized_energy_variance_floor`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletCoercivity.lean:284`.
The new selected-word calculation does not supply an improved fraction
for it. Its existing rate remains width-dependent. The actual weighted
decomposition, signed cross budget, full OS/scaling passage, physical-mass
calibration, continuum nontriviality, QFT axioms and all-group realization
remain OPEN. No canonical Clay atom is closed.

## Verification and independent review

Four final focused checks passed through the monitored launcher, serialized
with one worker and 20 GiB per worker after fresh process/swap preflights.
Swap remained 6669.00 MiB; no competing compiler/runner was observed.
All 48 public printed gates (27 new-module, 21 shared-algebra) use only
{propext, Quot.sound}, or no axioms. Final logs have no errors/warnings.
Namespace and symbolic polynomial-normalization repairs did not change the
statements or resource limits. An elaboration timeout disappeared after
removing the malformed scalar expression; no limit was raised.

Eight formerly private helpers in `SU2QuaternionAdjacentPlaquetteGluing`
were exposed with unchanged bodies/statements and included in the shared
module's axiom check. They are reused algebra, not eight new results.
Independent source review covered radius replacement, target-dependent
coefficients, source/target indexing, both channels, signed subtraction,
scalar bounds and the absent full-action join.

Root imports added; root/full-tree/full audit/guard NOT run. No sorry,
new axiom, frontier statement, analytic guard or safety limit change.
CI remains manual-only. No literature scan occurred.

| Focused log under `/tmp/` | SHA-256 |
|---|---|
| `ym-quadratic-heat-product-20260917.log` | `10b68297828bd170ae81f62f134316052e2f9bcf6f9183d68b73440abe43ff91` |
| `ym-heat-covariance-rates-20260917.log` | `dbfeafaf8daf794c8ee3f07c9069ef26379015fb7cd7bd4ea7dce4f326f3d559` |
| `ym-adjacent-gluing-shared-api-20260917.log` | `62d50a50bbb7ab53b1ac10775aa909a2697458c49c57f0147c8a558e5ea6b6ea` |
| `ym-adjacent-plaquette-heat-20260917.log` | `f3d2b18fcb5b4a6be4564d852c2b8e638606776721f1677a8bbae34b930b847d` |
