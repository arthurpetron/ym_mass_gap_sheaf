# Radial Wilson increments and the quartic correction

Date: 2026-10-01 UTC. The constructive continuum Yang--Mills goal is
unchanged and open. This checkpoint tests a proposed radial replacement
for the existing absolute temporal-loss bound and constructs a corrected
inequality under the original edge measure. It does not supply the
missing energy-to-variance estimate on a justified scaling family.

## What the source review established

The absolute, floor-free link displacement estimate was already proved in
`SU2QuaternionProductHeatExactAlignment.product_displacement_nome_bound`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatExactAlignment.lean:141`.
Its original Wilson-word consumers were also present. Reconstructing heat
alignment or its known absolute plaquette loss would not advance the
relative-energy frontier.

The existing `BF4ExactSlabFixedSpatialEnergyNormBound.energy_le_norm`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEnergyNormBound.lean:85`)
uses positivity of the original transfer. The existing projected-source
energy and moment pins retain the odd marginal:
`BF4ExactSlabFixedSpatialProjectedSourceEnergy.energy_projected_source`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedSourceEnergy.lean:102`)
and `oddMoment_projected_source` in that module at line 117. These facts do not by
themselves yield a useful strict energy-to-centered-variance ratio.

## A finite radial replacement fails

In the original one-link polynomial Haar carrier, take the fundamental
character f, source q=1+f^8=1+(f^4)^2, nome w=1/2 and heat cutoff K=3.
The source has an explicit square certificate. The existing cutoff-three
heat kernel has a certificate placing it above 1/4; neither source nor
kernel positivity is an assumed numerical observation.

With Z=H[q Pq], M2=H[q f^2 Pq], R=H[q(4-f^2)Pq], the checked values are

    Z  = 3649/16
    M2 = 41917/64
    R  = 16467/64
    E  = 54241/128
    E - 3*(1-w)*R = 605/16 > 0.

`SU2QuaternionRadialMarginalEnergyFence.radial_marginal_bound_three_false`
(`lean/YMGap/Continuum/SU2QuaternionRadialMarginalEnergyFence.lean:99`)
therefore refutes the proposed universal coefficient-three bound using
the SAME marginal, not a bare Haar surrogate. Its `radialMoment1` is the
actual inserted source moment, rather than an unrelated scalar definition.

This is not the Yang--Mills terminal source. It neither refutes a larger
finite coefficient nor excludes an estimate using additional properties
of the actual source. It is not a Yang--Mills or continuum counterexample.

## Corrected kinematics

For unit polynomial quaternions p,q, write f=2*p.scalar, g=2*q.scalar and
r=|p-q|^2. The corrected inequality is

    (f-g)^2 <= 2*r*(4-f^2) + 2*r^2.

The last term cannot be dropped at opposite center values: f=2 and g=-2
have zero radial defects but a nonzero trace increment. The new bound
retains the mixed radial/chordal term and the fourth-order displacement.

The explicit certificate uses z=q*conj(p), d=1-z.scalar, a=p.scalar,
b=vec(p), v=vec(z), and s=v dot b. Under the two unit-norm equations,
the right side minus the left side is

    4*(a*d-s)^2
      + 8*sum_{i<j}(v_i*b_j-v_j*b_i)^2
      + 16*sum_i(d*b_i)^2.

`QuaternionHaarRadialChordalIncrement.radialCertificate` constructs these
seven supported squares
(`lean/YMGap/Continuum/QuaternionHaarRadialChordalIncrement.lean:159`).
The finite ring identity includes explicit
multiples of norm(p)-1 and norm(q)-1 before using the Haar-unit relations.
Lean's polynomial normalizer checks that identity; an external symbolic
calculation is not a proof oracle. Unit relations are used only as
equalities under arbitrary Haar insertions. `radialBudget_pin` exposes
the displayed polynomial, and `weighted_radial_bound` keeps any supplied
certified positive weight in both moments.

## Original Wilson energy consumer

`BF4ExactSlabFixedSpatialWilsonRadialIncrement` uses the actual ordered
lower and upper words of a `SourceLoop`, their proved Haar-unit norms,
and `BF4ExactSlabFixedSpatialWilsonKineticIncrement.upper_character_lift`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonKineticIncrement.lean:205`).
The existing `BF4ExactSlabFixedSpatialDirichletForm.energy_identity`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:253`)
identifies the trace-increment square with twice the original temporal energy.

`wilson_energy_radial_cleared` retains the entire original `edgeDensity`,
including both spatial factors and both terminal messages. Its normalized
version divides by the existing positive `oddMass`. No active-link premise
is required for this purely kinematic inequality, because no smallness of
the remaining displacement moments is asserted.

Equivalently, with Z the original odd partition, this bounds

    E/Z <= H[W*r*(4-f^2)]/Z + H[W*r^2]/Z.

Here f is the lower fundamental Wilson trace and r is the full-word
displacement. The consumer is for one `SourceLoop`; it does not assert
an estimate for arbitrary signed families or discard their cross terms.

The next analytic producer must estimate the mixed radial-displacement and
quartic terms, or retain equivalent signed source-response cancellation,
relative to the SAME centered variance on a justified physical trajectory.
No independence or product-of-expectations replacement is justified here.
Neither term has been proved uniformly quadratic in the nome defect.

## New declaration map

All paths below are under `lean/YMGap/Continuum/`; declaration namespaces
are the corresponding module basenames.

| Declaration | Module:line | Scope |
|---|---|---|
| `positiveSourceCertificate` | `SU2QuaternionRadialMarginalEnergyFence.lean:73` | Explicit one-plus-square source |
| `kernelQuarterFloor` | `SU2QuaternionRadialMarginalEnergyFence.lean:77` | Existing strictly positive K=3 heat certificate |
| `mass1_value`, `secondMoment1_value`, `radialMoment1_value`, `sourceEnergy1_value` | `SU2QuaternionRadialMarginalEnergyFence.lean:85`, `:88`, `:91`, `:94` | Exact original one-link moments |
| `radial_marginal_bound_three_false` | `SU2QuaternionRadialMarginalEnergyFence.lean:99` | Failure of coefficient three only |
| `radialBudget_pin` | `QuaternionHaarRadialChordalIncrement.lean:89` | Literal mixed and quartic polynomial |
| `radialCertificate` | `QuaternionHaarRadialChordalIncrement.lean:159` | Seven-square constructive witness |
| `weighted_radial_bound` | `QuaternionHaarRadialChordalIncrement.lean:185` | Arbitrary certified positive insertion retained |
| `wilson_energy_radial_cleared` | `BF4ExactSlabFixedSpatialWilsonRadialIncrement.lean:117` | Twice actual energy under full original edge density |
| `wilson_energy_radial_normalized` | `BF4ExactSlabFixedSpatialWilsonRadialIncrement.lean:154` | Same positive odd partition |

## Verification

Three final focused checks exited 0. All 18 printed gates passed: two are
axiom-free, 16 use only {propext, Quot.sound}. Initial parenthesis,
namespace and proof-composition errors were corrected before the final
successful checks. No new sorry, axiom, classical shortcut, native_decide,
surrogate measure, or weakened frontier field was introduced. The root
import list was updated, but no full root build or broad audit was run.

Sol agents supplied the finite counterexample and independent arithmetic
review; a separate read-only review checked the seven-square identity's
scope and its full-weight physical application. The main agent built the
generic certificate and original consumer and alone ran Lean.

The safe launcher serialized one worker with a 20 GiB ceiling, 12 GiB OS
reserve and dynamic safety telemetry. Preflight found no competing Lean,
Lake, pytest or runner process; macOS reported 91% memory free before the
final generic check. No broad or parallel compilation was used.

Final logs (local `/tmp` artifacts) and SHA-256:

| Log | SHA-256 |
|---|---|
| `/tmp/ym-radial-marginal-fence-20261001.log` | `01dbe9a62a4a51d922de2f127f2210ceb65a6453a25efce16dfa624474a711ad` |
| `/tmp/ym-radial-chordal-20261001.log` | `6ada60bd52ce5ead1b77db70ed98cd10abdf24a91b7b8f62c5d9b86e158bfffc` |
| `/tmp/ym-wilson-radial-increment-20261001.log` | `ad88a1eb0551fe9bcb4b66cc540761610efb467bc169910ce3be5be01d6987b0` |

The canonical chart is unchanged. SAME-variance scaling control, one
nonzero continuum excitation, physical mass calibration, full QFT axioms
and the all-groups Clay target remain open.
