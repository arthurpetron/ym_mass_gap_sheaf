# Original real-time continuity sector and represented real-linear graph

Date: 2026-09-30 UTC. Classification: PROGRESS, four checked constructive
modules on the original fixed-nome/width Wilson completion. Clay remains OPEN.

## Next mathematical input removed

The preceding checkpoint identified the witnessed closure of ran(T(1))
with the root/dyadic zero-continuity sector and proved its represented
closedness. This checkpoint extends continuity to EVERY sufficiently small
positive real time, proves positive-time invariance and real-linear closure
of the witnessed sector, and constructs real scaling of represented
derivative graphs. No legacy time operator or carrier is substituted.

If k(epsilon) is the already computed dyadic continuity depth of the supplied
range witness, the real radius is exactly 2^(-k(epsilon)-1). A supplied real
time below it has dyadic approximants eventually below 2^(-k(epsilon)).
Their original squared-distance bound passes through the existing represented
pairing limit. The radius remains explicit data; the eventual index extracted
from the Prop-valued real inequality is used only inside that order proof,
not to construct an output representative or modulus.

Conversely, supplied real-continuity radii r(epsilon) give the explicit root
depth r(epsilon).den. Exact recovery of the original dyadic operator then
constructs the range witness. Thus the mathematical real-zero-continuity
sector is also characterized, in the explicit-modulus/represented sense.

Every positive mesh has a final root, so it has an explicit original range
witness. Positive-real-time images are the already constructed limits of
such meshes, and range closedness applies. For sector inputs, their range
witness computes the input representative, so no further representative
premise is needed for invariance.

Subtraction uses rows of actual time images and their existing difference
limit. Real scaling uses rational scalar rows on the representative computed
from the range witness, then range closedness. Finally, the bounded
derivative-on-preimages A is real-linear by symmetry of the original pairing.
The equation Au=T(1)v is stable under that same scalar action. The existing
two-coordinate graph criterion therefore constructs the scaled graph, with
source representatives given by explicit finite inverse sums. No new graph
norm estimate, preimage cap, resolvent or log-series identity is assumed.

## Checked source map

| Declaration | Source | Exact result |
|---|---|---|
| `incrementRows`, `incrementRows_pin`, `incrementRows_limit` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeRangeRealContinuity.lean:68`, `:74`, `:82` | Original increment rows and exact dyadic/real limit pins, from a representative computed from the range witness. |
| `realRadius`, `realRadius_positive`, `real_smallTime` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeRangeRealContinuity.lean:90`, `:93`, `:99` | Computed positive radius bounds EVERY small positive real increment in the original squared norm. |
| `realContinuityCertificate`, `rangeOfRealContinuity` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeRangeRealContinuity.lean:133`, `:143` | Both real-continuity/range directions preserve explicit data. |
| `meshAction_range`, `dyadicAction_range` | `lean/YMGap/Continuum/BF4WilsonAllNomePositiveTimeRangeClosure.lean:52`, `:69` | Every supplied positive mesh image has an original T(1)-range witness. |
| `positiveAction_range`, `positiveAction_preservesRange` | `lean/YMGap/Continuum/BF4WilsonAllNomePositiveTimeRangeClosure.lean:78`, `:90` | Positive-real-time images lie in the range sector; an existing sector witness needs no extra input representative. |
| `rationalSmul`, `zero`, `subtract`, `negate`, `add`, `realSmul` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeRangeLinear.lean:53`, `:71`, `:80`, `:101`, `:117`, `:126` | Original real-linear operations return actual preimage streams and range moduli. |
| `derivativeAction_realSmul`, `realScale_equation` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraphRealLinear.lean:55`, `:63` | Original real homogeneity of A and stability of the actual graph equation. |
| `realScale`, `realScale_source_pin`, `representedRealScale` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraphRealLinear.lean:69`, `:77`, `:90` | Scaled graph with explicit inverse-sum source representatives; the original graph's source representatives remain an input. |

## Remaining consumer and scope

The represented sector is now closed, real-linear, invariant under positive
time, and continuous at zero for the actual positive-real-time action.
The existing positive semigroup laws, original integer-time pin, graph
Taylor differentiation and scoped weak-adjoint criterion retain their
original objects and hypotheses. This checkpoint supplies prerequisites
for the subsequent intrinsic real presented-sector adjoint construction,
now checked in `audits/AUDIT-ORIGINAL-SECTOR-ADJOINT-2026-09-30.md`.
The full physical/complex Hilbert identification is not supplied.

In particular, `DerivativeGraphRealLinear.representedRealScale` operates on
represented graphs. It does NOT redefine the old quotient `Domain`, select
representatives from arbitrary quotient-valued source sequences, or silently
equip that whole quotient with a new scalar operation. The follow-on
preserves the source witnesses and original equality in a presented sector.

Identifying this mathematical sector with the physical OS Hilbert space
remains OPEN. So do physical-time/mass calibration, spatial/scaling control,
nontrivial continuum survival, full continuum QFT/Yang--Mills field content,
and every compact simple group. The independent primary analytic input is
still the SAME-source signed temporal-energy/variance comparison on a
justified scaling trajectory. This checkpoint supplies no such estimate.
Equality A=regularizedLog is not assumed; the actual derivative construction
does not require that historical identification here. Ambient boundary
states are retained, and whole-carrier zero continuity is not asserted.

## Verification

Four final serialized focused checks passed 23 printed gates (eight real
continuity, four positive-time range, six range linearity, five represented
graph real linearity), each with exactly {propext, Quot.sound}. The first
real-continuity check required replacing two `decide` terms on dependent
mesh projections by `Nat.succ_pos 0`; its final check is clean. Before its
first check, the positive-range draft's Type-returning declarations were
corrected from `theorem` to `def` and its root pin made explicit. The final
sector-invariance consequence was then added and rechecked. All final
logs have no warnings. No new sorry/axiom, classical dependency, frontier
weakening or canonical chart change.

The safe-build skill kept all checks narrow and serialized: one worker,
20 GiB ceiling, 12 GiB OS reserve, process preflight and automatic telemetry.
All finished within their initial check calls. No safety stop, raised limit,
full root/tree build, audit or guard. Added root imports are NOT a root check.
Sol drafted range linearity; Luna drafted positive-time membership; main
finalized those, proved real continuity and graph real scaling, and ran every
check. Sol independently reviewed the latter two modules' witness flow.

Final logs and SHA-256:

- `/tmp/ym-wilson-time-range-real-continuity-20260930.log`:
  `37802a41dff4e9cd6b5d65fa46a80e70d8cee856051191fdaee418e8789ced6a`
- `/tmp/ym-wilson-positive-time-range-closure-20260930.log`:
  `032b09949db07a3aff60757178f915482bdb46258f9efd68e9275c9873b0c7ac`
- `/tmp/ym-wilson-time-range-linear-20260930.log`:
  `2e03b33402ce16c42db1390295dd8ae7202aa2be56ffdd944bf3d3be46e366b7`
- `/tmp/ym-wilson-derivative-graph-real-linear-20260930.log`:
  `5839ec2e318765d5f8950da70fdf2e09c5bf0450c5d0d7f3b3bef5008202a5b1`
