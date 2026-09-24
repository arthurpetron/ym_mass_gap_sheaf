# Positive-source variance comparison: finite diagnostic

2026-09-24 UTC. This is a test of a proposed generic estimate, not a
counterexample to the original four-dimensional Yang--Mills construction.

## Mathematical question

Let P be the actual one-link product heat at nome w=1/2 and cutoff K=3,
f its fundamental character, and q=1+(1+f)^2. Use the existing definitions
`sourceMoment` and `sourceEnergy` in
`lean/YMGap/Continuum/SU2QuaternionProductHeatProjectedSourceEnergy.lean:49`.
Write Z=H[q P(q)], B=H[q f P(q)], A=H[q f^2 P(q)],
E=A-H[q f P(q f)], and V=Z*A-B^2. The tested normalized comparison is

    E/Z <= (1-w^3) * V/Z^2,

or, after clearing the positive mass, Z*E <= (1-w^3)*V.
The right side uses the SAME interacting centered variance, not H[q^2].

The finite source has representation coefficients 3,2,1 at labels 0,1,2.
It is represented compactly in code as 2+2f+f^2; the explicit square
certificate identifies it with 1+(1+f)^2.

## Exact certificate data

| Quantity | Exact rational value |
|---|---|
| Z | 2433/256 |
| B | 897/128 |
| A | 3333/256 |
| E | 229503/32768 |
| V | 4890753/65536 > 0 |
| (1-w^3)*V-Z*E | -10616463/8388608 < 0 |

These quantities are named and evaluated in
`lean/YMGap/Continuum/SU2QuaternionPositiveSourceVarianceFence.lean`:
`mass_value`, `firstMoment_value`, `secondMoment_value`, `energy_value`,
`varianceNumerator_value`, and `clearedResidual_value`.
`bare_loss_variance_bound_false` states the failed cleared inequality itself.
The residual here is DEFINED as that algebraic comparison deficit; this
module does not additionally identify it with a separately defined Haar
integral of a transmission residual.

Positivity is not being assumed for an indefinite truncated kernel.
`SU2QuaternionHalfHeatThreeCertificate.heatAt_half_three_quarterFloor`
in `lean/YMGap/Continuum/SU2QuaternionHalfHeatThreeCertificate.lean:79`
constructs a `Certificate 2` for the actual relative heat minus 1/4.
The sharp dimension-weighted non-vacuum cap is 1097/2048. The kernel and
source positivity witnesses live in Type and retain polynomial-square data.

## Consequence and remaining task

The checked diagnostic proves that source positivity and positive product
heat alone cannot supply this proposed bare-rate variance comparison.
The test source is NOT identified with the physical projected terminal source
P_fringe(V*g_n). Nothing here refutes a source-specific estimate, the
four-dimensional interacting route, or continuum survival.

The active analytic task remains a useful signed-energy/SAME-variance estimate
for ONE justified changing-scale original observable, or its direct sampled
response. The independent EVERY-vector spatial/spacing bound, SAME continuum
and full Hilbert/OS/QFT/YM/UV construction, physical Hamiltonian/mass, and
every compact simple group remain open. No canonical field is changed.

## Verification boundary

The kernel certificate passed a serialized 2 GiB check with three permitted
axiom gates in `/tmp/ym-gap-half-heat-three-certificate-check-3.log`.
The diagnostic's whole-file check passed with thirteen permitted axiom gates
in `/tmp/ym-gap-positive-source-variance-fence-check-5.log`. Both final logs
are free of errors, warnings and forbidden axioms. The two leaves together
passed sixteen gates within {propext, Quot.sound}.

Earlier drafts encountered an explicit compiler memory ceiling and two
host-reserve stops across the diagnostic and parallel complex-CS tasks.
Limits and the 12 GiB reserve were not weakened. Large rational expansions
were replaced by compact source algebra and opaque theorem reuse. Earlier
namespace/setoid errors were repaired before the accepted checks. Semantic
root import added; no full-root build/audit/guard was run. No new source
`sorry`, axiom, analytic premise, or canonical-field change is involved.
