# Grouped harmonic norm, original heat pairing and cutoff/Casimir budget

Date: 2026-09-21 UTC. WHOLE-PROJECT GOAL remains OPEN: constructive,
nontrivial continuum Yang--Mills on R^4 for every compact simple group,
with the same theory's full QFT axioms, isolated vacuum and finite positive
physical mass gap. This checkpoint is finite SU(2) polynomial mathematics.

## The mathematical obstruction removed

Fischer decomposition may return several signed summands with the same
harmonic degree. Cross-degree orthogonality does not permit dropping their
cross terms. The new construction first forms the complete polynomial h_d
at each harmonic degree d, THEN takes its square. It proves

    H[p^2] = sum_d H[h_d^2]

for the actual original supported input p, using its previously constructed
Haar-carrier reassembly. At the stronger partial-Haar level, the equality
retains every surviving tail coefficient. This is not an orthogonality
claim about each individual Fischer summand.

The same computed groups enter the original heat-packet pairing:

    H[(relativeHeat(w,K)*p)*r]
      = sum_d a_K(d)*H[retainedImage(h_d)*r],

where r is any head-independent polynomial on the same original carrier,
and a_K(d) is w^(d(d+2)) for d<=K and zero otherwise. No replacement
kernel, propagation assumption or discarded insertion is used.

## Quantitative estimate, with its parameter domain

For 0<=w<=1 and

    1 <= (1-w)*(K+1)*(K+3),

the checked scalar estimate is

    1-a_K(d) <= (1-w)*d*(d+2)       for EVERY degree d.

For d<=K this is the existing constructive Bernoulli bound. For d>K,
the defect is exactly one, and monotonicity of d(d+2) applies the guard.
In particular no condition degree(p)<=K is needed. This matters for a
changing weighted source whose degree can grow with K.

For every strict rational nome w<1, `sufficientCutoff w := (1-w).den`
returns a sufficient cutoff as Nat data. A positive rational has numerator
at least one; its denominator therefore supplies an elementary sufficient
bound. `cutoff_guard_of_le` proves the guard for every K above this witness.
The resulting `grouped_defect_le_angular_of_cutoff` does not require the
caller to supply the scalar guard separately. The witness depends on the
rational presentation of w and is not claimed asymptotically sharp.

Each H[h_d^2] is nonnegative by the original supported Haar square
certificate. Multiplying and summing therefore proves

    sum_d (1-a_K(d))*H[h_d^2]
      <= (1-w)*sum_d d(d+2)*H[h_d^2]
       = (1-w)*sum_d H[angularSquare(h_d)].

The last equality uses all six angular planes and the exact harmonic
Casimir, not an assumed energy estimate. Its stronger retained form allows
any head-independent background r, without a positivity premise on r.

## Source map

All paths in this table are under `lean/YMGap/Continuum/`.

| Declaration | Source | Content |
| --- | --- | --- |
| `grouped_filter` | `SU2QuaternionGroupedHarmonicNorm.lean:61` | Complete equal-degree signed group. |
| `harmonic_cross_degree` | `SU2QuaternionGroupedHarmonicNorm.lean:92` | Partial-Haar annihilation only for unequal degrees. |
| `partial_norm_sum` | `SU2QuaternionGroupedHarmonicNorm.lean:119` | Polynomial-valued Pythagoras on distinct degrees. |
| `polynomial_norm` | `SU2QuaternionGroupedHarmonicNorm.lean:171` | Square norm of arbitrary supported original input. |
| `grouped_norm_nonnegative` | `SU2QuaternionGroupedHarmonicNorm.lean:186` | Original grouped square positivity. |
| `one_sub_attenuation_le` | `SU2HeatCutoffCasimirBound.lean:54` | All-degree defect bound with explicit cutoff guard. |
| `sufficientCutoff` / `sufficientCutoff_guard` | `SU2HeatCutoffCasimirBound.lean:84` / `:110` | Computed cutoff and proved guard at every strict nome. |
| `cutoff_guard_of_le` | `SU2HeatCutoffCasimirBound.lean:125` | Guard for every larger cutoff. |
| `retained_harmonic_energy` | `QuaternionHaarHarmonicAngularEnergy.lean:76` | All-degree retained six-plane energy/Casimir identity. |
| `polynomial_grouped_heat_pairing` | `SU2QuaternionGroupedHeatComparison.lean:76` | Original packet consumes the complete groups. |
| `grouped_defect_le_casimir` | `SU2QuaternionGroupedHeatComparison.lean:96` | Positivity-weighted finite sum bound. |
| `grouped_casimir_energy` | `SU2QuaternionGroupedHeatComparison.lean:112` | Actual angular square of each complete group. |
| `grouped_defect_le_angular` | `SU2QuaternionGroupedHeatComparison.lean:137` | Quantitative grouped angular-energy budget. |
| `grouped_defect_le_angular_of_cutoff` | `SU2QuaternionGroupedHeatComparison.lean:149` | Consumes the computed cutoff guard. |

## What has NOT been inferred

The grouped attenuation sum has not yet been identified with the bare
quadratic form of the full original product operator. The original-packet
formula has a retained substitution and an independent insertion; the
norm formula by itself does not identify those expressions with one
another. Iterated-factor substitution/support compatibility and the
total angular-cost reassembly must be proved on the actual carrier.

Even after that join, the original weighted energy contains the signed
endpoint correction from
`BF4ExactSlabFixedSpatialGroundStateEnergy.energy_eq_bare_add_correction`.
It is not discarded by a bare kinetic estimate. The checked differential
cancellation is not automatically its finite-time analogue. The SAME-
variance small rate, spatial and scaling control, nontrivial survival,
finite physical mass, full QFT and all compact simple groups remain open.

The nome w and cutoff K are explicit. There is no claim of uniformity in
the bare coupling, spacing or volume, and no claim of a physical gap.
No canonical field, hypothesis bundle or frontier statement was changed;
no `sorry` or axiom was introduced or discharged.

## Verification boundary

Verification uses the monitored launcher with ONE 20 GiB worker, a 12 GiB
OS reserve and the existing swap/pressure guards. Sol supplied the bounded
scalar and angular-energy modules; main supplied grouping, norms and the
actual-packet/estimate consumers and serialized verification.
Sol's independent read-only review passed, including same-degree cross
terms, original support/carrier reassembly, retained tail factors, and the
explicit boundary between this grouped budget and a product-transfer bound.

Focused check logs:

- `/tmp/ym-gap-cutoff-casimir-check.log`
- `/tmp/ym-gap-grouped-harmonic-norm-check.log`
- `/tmp/ym-gap-harmonic-angular-energy-check.log`
- `/tmp/ym-gap-grouped-heat-comparison-check.log`

The four focused checks passed all 22 printed axiom gates within
`{propext, Quot.sound}`, with no warning, error, `sorryAx`, classical axiom
or native-decider dependency. The dependency-complete consumer target
`+YMGap.Continuum.SU2QuaternionGroupedHeatComparison:olean` also passed
(quiet successful log: `/tmp/ym-gap-grouped-heat-comparison-build.log`).
It imports all four new modules; the root import list is updated but the
full root was not checked in this increment.

No full-root build, full axiom audit or frontier guard is claimed.
