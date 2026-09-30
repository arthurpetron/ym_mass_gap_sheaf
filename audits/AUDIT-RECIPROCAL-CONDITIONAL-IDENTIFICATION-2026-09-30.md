# Original reciprocal identification and replica path bound

## Whole-project goal and scope

The unchanged goal remains OPEN: constructive continuum Yang--Mills on
R^4 for every compact simple group, with SAME-theory QFT axioms,
nontriviality and a finite positive physical Hamiltonian gap.

This checkpoint identifies the new finite reciprocal polynomials with
the EXISTING conditional update on the original full-action weighted
completion. These are ordinary weighted L2 spaces, not reflected OS
spaces. The hypotheses are rational nome 0<w<1, K>=headCutoff(w), and
membership of the selected physical link in the original slab.
No new analytic hypothesis is supplied or assumed.

## Constructive inverse identification

Let D be the actual integrated incident star in head coordinates, B the
entire complementary action, and G_k(D) the finite positive reciprocal
polynomial from the preceding comparison. The star window is
ell=headFloor(w)^d, U=prefixCap(w)^d, rho=1-ell/U, where d is the
actual number of incident faces. The new estimate is

    ||r - D (r G_k(D))||_B^2 <= rho^(2k) ||r||_B^2.

The proof integrates the certified error square against the certified
nonnegative weight B*r^2. It does not substitute a product-face law for
the original interacting action. Existing normalizer coercivity then
converts residual control into a Cauchy modulus for r G_k(D), and a
cross-sequence null modulus against the existing inverse iteration.

Write L=lowerFactor(w), the existing positive coarse normalizer floor.
The Cauchy cutoff evaluates the geometric residual cutoff at L^2*epsilon/4.
The cross-sequence cutoff is the maximum of that new cutoff and the old
inverse-iteration cutoff, at the SAME tolerance. The squared triangle
inequality costs 2+2, and coercivity cancels L^2. No root extraction,
choice of quotient representative, or uniqueness assumption is needed.

All paths in the tables below start at `lean/YMGap/Continuum/`.

| Declaration | File:line | Proved content |
| --- | --- | --- |
| `headLowerCertificate`, `headUpperCertificate` | `BF4ExactSlabHeadNormalizerBand.lean:133`, `:156` | The actual head normalizer retains the incident-count window |
| `headErrorInterval` | `BF4ExactSlabHeadNormalizerBand.lean:189` | Error of the finite head reciprocal has explicit geometric interval |
| `reciprocal_weighted_error_le` | `QuaternionHaarReciprocalWeightedError.lean:60` | Certified weighted squared-residual estimate for any supported input |
| `reciprocal_residual_norm` | `BF4ExactSlabStarReciprocalInverse.lean:72` | Original complementary-action instance, with rho^(2k) error |
| `residualCutoff`, `reciprocalCauchy` | `BF4ExactSlabStarReciprocalInverse.lean:105`, `:133` | Explicit tolerance cutoff and same-carrier Cauchy data |
| `inverseNullModulus` | `BF4ExactSlabStarReciprocalInverse.lean:150` | Computed comparison with the EXISTING inverse sequence |
| `reciprocal_limit_eq_inverseState` | `BF4ExactSlabStarReciprocalInverse.lean:171` | Equality to that original completed inverse |
| `conditionalNullModulus`, `reciprocal_limit_eq_conditionalUpdate` | `BF4ExactSlabStarReciprocalInverse.lean:178`, `:186` | Existing full-action probe transports the explicit comparison to the original conditional update |

The geometric residual estimate is weakened to rho^k only to reuse the
existing geometric cutoff without a square-root tolerance. This is not
a claimed physical decay rate. Nome dependence remains explicit; no
beta-, volume- or spacing-uniform inverse norm is asserted.

## Literal original-coordinate realization

For the unchanged physical slot j, let A be the original incident star.
The literal polynomial approximant is

    project_j(p*A) * G_k(project_j A).

The actual head swap transports its numerator and reciprocal separately.
The equalities are Haar-carrier equalities under arbitrary polynomial
insertions, not equality of polynomial coefficient lists. Consequently
they preserve the entire original-action squared distance. The same-k
coordinate change has a zero null modulus; composing it with the inverse
comparison gives an explicit null modulus to the existing conditional map.

| Declaration | File:line | Proved content |
| --- | --- | --- |
| `inPlace_headReciprocal_carrier` | `BF4ExactSlabStarReciprocalTransport.lean:163` | Actual finite reciprocal commutes with the original head-coordinate transport under Haar insertions |
| `inPlaceNumerator`, `numerator_head_pin` | `BF4ExactSlabInPlaceReciprocalConditional.lean:67`, `:75` | Actual selected-coordinate numerator and exact head pin |
| `inPlaceApproximation`, `approximation_head_pin` | `BF4ExactSlabInPlaceReciprocalConditional.lean:84`, `:95` | Literal product and its full original-coordinate identification |
| `inPlaceCauchy`, `headNullModulus` | `BF4ExactSlabInPlaceReciprocalConditional.lean:121`, `:134` | Explicit original-action convergence and exact coordinate-change null data |
| `conditionalNull`, `inPlace_limit_eq_conditionalUpdate` | `BF4ExactSlabInPlaceReciprocalConditional.lean:147`, `:153` | SAME original completed conditional update, not a replacement inverse |

Luna independently reviewed these pins and the null-modulus composition;
no same-object or scope defect was found. This result does not yet
identify the limiting joint two-copy edge-flow pairing with residual energy.

## Parallel coordinate-path algebra

For n original quaternion blocks, p_j is the original observable with
the first j coordinates exchanged between the two copies. Its adjacent
differences telescope exactly. The finite Cauchy certificate gives

    (f(x)-f(y))^2 <= n * sum_j (p_(j+1)-p_j)^2.

`SU2QuaternionReplicaPathTelescope.increments_telescope` at
`lean/YMGap/Continuum/SU2QuaternionReplicaPathTelescope.lean:71` proves
the polynomial telescope. `path_cauchy_certificate` at `:90` supplies
the length-times-sum-of-squares certificate without an exponential
triangle-inequality loss. `replica_path_cauchy_certificate` at `:152`
pins the endpoints to the original two-copy observable square.

`BF4ExactSlabReplicaPathVariance.original_path_variance_bound` at
`lean/YMGap/Continuum/BF4ExactSlabReplicaPathVariance.lean:72` multiplies
this certificate by BOTH copies of the original full action W and uses
the preceding exact variance identity to prove

    2*(H[W] H[W f^2] - H[W f]^2)
      <= n * H_2n[W(x)W(y) * sum_j (p_(j+1)-p_j)^2].

`fullWeight_certificate` at `:59` constructs positivity of the actual
whole weight. No partition division or conditional-energy comparison
is used. This is the unnormalized global variance determinant, not an
already normalized Poincare inequality.

The coordinate prefix is a literal index order. It is NOT yet identified
with the time-layer order required by the previously proved area estimate.
The path certificate alone does not identify any increment with a local
conditional energy.

## Remaining mathematical join

The single-copy reciprocal limit is now identified. Still OPEN is the
joint two-copy pairing identity needed to use the finite two-normalizer
comparison as an inequality for the original local residual energies.
The original replica-cut comparison must then be joined to the weighted
path bound with all action factors and normalizations retained. The
time-layer order also requires an actual coordinate-order pin before
its crossing-face area bound can be used in that joined estimate.

The next local consumer is the existing `GNSProjectionSweep.Family.single_loss`
at `lean/YMGap/Continuum/GNSProjectionSweep.lean:79`, instantiated by
`BF4ExactSlabConditionalSweep.projections` at
`lean/YMGap/Continuum/BF4ExactSlabConditionalSweep.lean:56`.
`conditionalProjection_embed` at
`lean/YMGap/Continuum/BF4ExactSlabStarConditionalProjection.lean:225`
ties this operator to the dense conditional update identified above.
The next finite pairing pin to prove is

    B_F(p,p) - B_F(p,A_k p)
      = H_exterior[(N(p^2) - N(p)^2 G_k) * B],

where A_k is the literal conditional approximant. The existing ingredients
are `full_insertion_pin` at
`lean/YMGap/Continuum/BF4ExactSlabStarNormalizer.lean:86` and `probeMap_test`
at `lean/YMGap/Continuum/BF4ExactSlabStarFullActionProbe.lean:105`.
The algebraic residual split to formalize is

    N(p^2) - N(p)^2 G_k
      = varianceNumerator(p) * G_k + (1-D G_k) * N(p^2).

These displayed next-step pins are a source-reviewed proof plan, NOT new
kernel-checked declarations. In particular, `polynomialResidual_variance_pair`
at `lean/YMGap/Continuum/BF4ExactSlabStarPolynomialResidual.lean:115`
retains the unnormalized numerator; it is not the normalized conditional
residual energy. Also, `varianceNumerator_replica` at
`lean/YMGap/Continuum/BF4ExactSlabStarVarianceReplica.lean:104` duplicates
the HEAD with shared exterior, whereas the preceding cross-exterior
comparison duplicates the EXTERIOR with a shared updated link. An exact
path/insertion identity connecting those geometries is still required.

The candidate N*(prefixCap/headFloor)^(2C+12) is still not a Lean Poincare
theorem. Even such a theorem would retain area-dependent loss and would
not itself supply useful signed spatial/scaling control, an OS-transfer
gap, or a physical Hamiltonian gap. Continuum survival, same-theory
reconstruction, full QFT, physical-time calibration and the every-group
construction remain open. Canonical chart states are unchanged.

## Verification and parallel work

Seven final focused module checks passed all 45 printed gates within
{propext, Quot.sound}: HeadNormalizerBand 5, ReciprocalWeightedError 3,
StarReciprocalInverse 10, StarReciprocalTransport 1,
InPlaceReciprocalConditional 9, ReplicaPathTelescope 12,
ReplicaPathVariance 5. No new sorry, custom axiom or analytic assumption
was introduced; no existing sorry was discharged or frontier weakened.

Every check used the safe-build skill's monitored narrow-check procedure,
serialized with one worker, 20 GiB ceiling, 12 GiB OS reserve and
continuous safety telemetry. These short checks completed within their
initial calls, so there was no live heavy compiler to poll. No full-root
build, global audit, broad test or frontier guard was run. Root imports
are registered without claiming root compilation. The existing research
cache was reused; no routine listing scan was repeated.

Final logs under `/tmp/`: `ym-head-normalizer-band-20260930.log`,
`ym-reciprocal-weighted-error-20260930.log`,
`ym-star-reciprocal-inverse-20260930.log`,
`ym-star-reciprocal-transport-20260930.log`,
`ym-in-place-reciprocal-conditional-20260930.log`,
`ym-replica-path-telescope-20260930.log`, and
`ym-replica-path-variance-20260930.log`.

Sol constructed the head window, coordinate reciprocal transport and
replica-path bounds; Luna proved the weighted error helper and independently
reviewed the inverse and literal-coordinate identification. Root constructed
the inverse comparison and original-coordinate convergence, integrated the
proofs and ran serialized checks. Mathematical work ran in parallel without
parallel compiler processes.
