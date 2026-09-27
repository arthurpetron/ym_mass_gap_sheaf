# Original weighted conditional variance and polynomial kernel tests

## Mathematical target and normalization

Fix a finite original slab, one physical link, rational `0<w<1`, and
`K>=headCutoff(w)`. After the existing selected-link reindexing write
`W(x,z)` for the complete incident heat product, `B(z)` for the untouched
complementary action, and `A` for normalized Haar integration in x only.
The actual normalizer and inserted numerator are

    D(z)=A(W)(z),       N(p)(z)=A(W*p)(z).

The new signed polynomial is

    Phi(p)=D*N(p^2)-N(p)^2.

It is not the Haar variance `A(W^2)-A(W)^2` of the heat weight. In ordinary
conditional-law notation, `Phi=D^2*Var_(W/D)(p)`. Accordingly the original
unnormalized residual energy is `integral B*Phi/D`, NOT `integral B*Phi`
or `integral B*Phi/D^2`. This normalization explanation is mathematical
notation; no pointwise reciprocal or new normalized measure is constructed
by the replica modules. The completed conditional operator remains the
one already constructed in `BF4ExactSlabStarConditionalProjection.lean`.

## Exact replica construction

Only x is copied. The spectator variables z are shared:

    A_x A_y [W(x,z) W(y,z) (p(x,z)-p(y,z))^2] = 2*Phi(p)(z).

The formal equality is `HaarCarrierEqv` on the retained carrier, meaning
equality under EVERY remaining polynomial insertion, not merely equality
of total Haar values or a coefficientwise positivity assertion. The
polynomial algebra pins preceding that equality are coefficientwise.
Given an existing weight certificate, the proof constructs a certificate
for the replica square, integrates its two heads, and multiplies by 1/2
to obtain the variance-determinant certificate. No independent-spectator
hypothesis is introduced.

| Declaration | Source | Content |
| --- | --- | --- |
| `replica_product` | `lean/YMGap/Continuum/SU2QuaternionConditionalVarianceReplica.lean:76` | Exact double partial Haar product, retaining common tails. |
| `replica_identity` | `lean/YMGap/Continuum/SU2QuaternionConditionalVarianceReplica.lean:126` | Two-copy square equals the doubled weighted variance determinant under every retained insertion. |
| `replica_certificate` | `lean/YMGap/Continuum/SU2QuaternionConditionalVarianceReplica.lean:163` | Constructed positive certificate for the actual weighted replica square. |
| `determinant_certificate` | `lean/YMGap/Continuum/SU2QuaternionConditionalVarianceReplica.lean:180` | Witness-bearing determinant positivity on the retained carrier. |
| `spectator_nonnegative` | `lean/YMGap/Continuum/SU2QuaternionConditionalVarianceReplica.lean:192` | Retains any positive spectator certificate. |
| `varianceNumerator` | `lean/YMGap/Continuum/BF4ExactSlabStarVarianceReplica.lean:63` | Actual `D*N(p^2)-N(p)^2`, with the original incident factors. |
| `varianceNumerator_pin` | `lean/YMGap/Continuum/BF4ExactSlabStarVarianceReplica.lean:77` | Coefficient pin to the generic determinant after the physical link reindexing. |
| `varianceNumerator_replica` | `lean/YMGap/Continuum/BF4ExactSlabStarVarianceReplica.lean:104` | Exact physical-star two-copy identity. |
| `headWeight_certificate` | `lean/YMGap/Continuum/BF4ExactSlabStarVarianceReplica.lean:138` | Constructs positivity from all original incident face factors. |
| `exterior_certificate` | `lean/YMGap/Continuum/BF4ExactSlabStarVarianceReplica.lean:146` | Constructs positivity for the untouched complementary action after removing its unused head. |
| `varianceNumerator_certificate` | `lean/YMGap/Continuum/BF4ExactSlabStarVarianceReplica.lean:158` | Actual physical-star variance certificate. |
| `retained_variance_nonnegative` | `lean/YMGap/Continuum/BF4ExactSlabStarVarianceReplica.lean:167` | Nonnegativity with the SAME original exterior action retained. |

## Parallel original-kernel construction

The accompanying task constructs the literal original polynomial

    t_i(p)=J_i(D_i)*p-J_i(N_i(p)),

and proves its membership in the kernel of the actual completed conditional
projection. This is different from the free-Haar-centered input whose
preservation by neighboring updates was refuted. Its direct consumer is
the lower bound

    ||R_i f||^2 >= 2*<f,t_i(p)>-||t_i(p)||^2,

with every norm and pairing in the existing ORIGINAL full-action completion.
This bound does not divide by a possibly null norm or substitute the
coarse lower factor for D. It retains the original unnormalized full form.
The cross-pairing `<p,t_i(p)>` equals `integral B*Phi(p)`; it is NOT the
conditional-residual squared norm or the squared norm of t itself.

| Declaration | Source | Content |
| --- | --- | --- |
| `polynomialResidual` | `lean/YMGap/Continuum/BF4ExactSlabStarPolynomialResidual.lean:71` | Literal supported original polynomial `D*p-J(Np)`. |
| `polynomialResidual_probe_zero` | `lean/YMGap/Continuum/BF4ExactSlabStarPolynomialResidual.lean:76` | Every exterior probe pairs to zero in the original full form. |
| `polynomialResidual_variance_pair` | `lean/YMGap/Continuum/BF4ExactSlabStarPolynomialResidual.lean:115` | Cross-pair with p equals the retained-exterior variance numerator. |
| `polynomialResidual_projection_zero` | `lean/YMGap/Continuum/BF4ExactSlabStarPolynomialResidual.lean:187` | The ACTUAL completed conditional projection annihilates the computed test. |
| `polynomialResidual_dual_lower` | `lean/YMGap/Continuum/BF4ExactSlabStarPolynomialResidual.lean:246` | The floor-free dual lower bound on the actual completed residual energy. |
| `dualValue` | `lean/YMGap/Continuum/BF4ExactSlabStarPolynomialResidual.lean:277` | Finite rational test value `2*B(f,t)-B(t,t)`. |
| `dualValue_lower` | `lean/YMGap/Continuum/BF4ExactSlabStarPolynomialResidual.lean:296` | Embeds that rational test value into the completed lower bound. |

An arbitrary test may give a negative or zero value. Constructing tests
that give a useful positive summed bound remains mathematical work; no
nonzero excitation, all-degree estimate or scaling uniformity follows
from the existence of this rational evaluator.

## Analytic residue and next action

Neither determinant positivity nor a conditional-kernel test supplies
strict global coercivity. The missing task is to choose and control the
polynomial tests (or directly estimate the signed weighted determinant)
so their summed dual lower energy dominates the ORIGINAL globally centered
norm, with useful cutoff, volume and changing-coupling dependence.
That lower estimate is the consumer needed alongside
`BF4ExactSlabConditionalSweepEnergy.eight_layer_energy_le_625_loss`
(`lean/YMGap/Continuum/BF4ExactSlabConditionalSweepEnergy.lean:84`).
No new interface assuming that estimate is added here.

A separate backward task was identified by the targeted primary-source
review in `audits/AUDIT-SWEEP-ACCELERATION-2026-09-27.md`: constructive
Chebyshev acceleration on the SAME completed carrier could improve the
conditional-gap-to-spatial-rate conversion. That task neither assumes
the missing Yang--Mills estimate has been proved nor replaces its producer.

The bare-Haar small-variance shortcut is not used. Its relevant limitation
is already proved in `BF4ExactSlabHeatHaarVarianceObstruction`:
`remainderVariance_lower` (`lean/YMGap/Continuum/BF4ExactSlabHeatHaarVarianceObstruction.lean:134`)
and `no_eventual_small_variance` (`:170`) apply to one original face at all
later cutoffs, not to the full weighted conditional determinant. They do
not refute this signed route or Yang--Mills theory.

No completed global gap, same-theory physical Hamiltonian, spacing-uniform
estimate, continuum construction or every-group Clay closure follows from
this increment. Canonical chart markers remain unchanged.

## Verification boundary

All three modules passed serialized focused monitored one-worker checks
capped at 20 GiB. Their five, six and seven printed gates, respectively,
were `{propext, Quot.sound}`; no warnings or holes remained in those checks.
Independent Sol review found no carrier/normalization mismatch and confirmed
the test-selection limitation. The root import list was updated but not
compiled as a root target.
No full-tree build/audit, CI change, canonical-field change, new analytic
field or routine literature-listing refresh is part of this work.
