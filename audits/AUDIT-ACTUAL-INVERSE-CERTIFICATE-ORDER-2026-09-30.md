# Positive certificates through the actual conditional inverse

Date: 2026-09-30 UTC. Focused verification passed; independent Sol review passed.

## Proved mathematical result

The existing inverse of the ORIGINAL block normalizer preserves the
nonnegativity certified by the existing polynomial sum-of-squares syntax.
This is an order theorem and a sufficient certificate consumer. It neither
constructs a useful correlation coefficient nor proves completeness of the
certificate syntax for positive polynomials or integrated inequalities.

Write E for the detached action, D for the actual conditional normalizer,
M for multiplication by D on the E-background completion, and I for its
already constructed dense inverse. The original background and multiplier
are `backgroundData` and `normalizerMap` at
`lean/YMGap/Continuum/BF4ExactSlabBlockNormalizerMap.lean:43` and `:55`.
Their lower form bound is `normalizerMap_form_bounds` at `:81`.

The proof is short:

1. Pass positivity of M to its existing explicit completion.
2. Use M(Ir)=r to obtain `<Ir,r>_E = <Ir,M(Ir)>_E >= 0`.
3. Use the already proved inverse/product identity to obtain
   `<I(r*r),1>_E = <Ir,r>_E >= 0`.
4. Extend by sums, nonnegative rational multiples and Haar-carrier transport.

The right-inverse identity is `normalizer_inverseState` at
`lean/YMGap/Continuum/BF4ExactSlabBlockCompletedInverse.lean:205`;
the product identity is `inverseState_product_pair` at
`lean/YMGap/Continuum/BF4ExactSlabBlockCovarianceNormalizer.lean:76`.
The new declarations in
`lean/YMGap/Continuum/BF4ExactSlabBlockInversePositive.lean` are:

| Declaration | Line | Exact role |
| --- | --- | --- |
| `normalizerCompletion_positive` | 58 | Positivity on every completed background vector. |
| `inverseState_positive` | 75 | Nonnegative quadratic pairing of the actual inverse. |
| `inverseMean` | 82 | Linear functional `<I(1),r>_E`. |
| `inverseMean_pin` | 88 | Equality with `<I(r),1>_E`. |
| `inverseMean_add`, `inverseMean_sub`, `inverseMean_smul` | 96, 101, 107 | Exact linearity. |
| `inverseMean_carrier` | 120 | Respects arbitrary-insertion Haar-carrier equality. |
| `inverseMean_square_nonnegative` | 132 | Positivity on supported polynomial squares. |
| `inverseMean_certificate` | 186 | Consumes any supplied existing certificate. |
| `inverseMean_mono` | 201 | A certificate for t-r implies mean(r)<=mean(t). |

The existing certificate's transport constructor need not preserve literal
polynomial support. `Certificate.supportedRepresentative` at
`lean/YMGap/Continuum/QuaternionHaarCertificateSupportedRepresentative.lean:36`
recursively constructs a supported Haar-equivalent polynomial. The proof
therefore never treats an unsupported intermediate as a GNS vector.
Haar-carrier equality is NOT claimed to be pointwise equality; transport
is tested against the actual inverse approximants with E retained.

## Exact covariance consumer

Let N(p,q)=D*N_pq-N_p*N_q be the EXISTING `covarianceVector`, defined at
`lean/YMGap/Continuum/BF4ExactSlabBlockCovarianceNormalizer.lean:90`.
`covarianceBudget` at
`lean/YMGap/Continuum/BF4ExactSlabBlockCovarianceCertificate.lean:47`
is the supported polynomial

```
rho * (N(p,p) + N(q,q)) - 2 * N(p,q).
```

`inverse_covariance_bound` in that module at `:58` proves that a certificate
for this polynomial yields the same inequality after applying the actual
inverse functional. `inverse_covariance_sequence_bound` at `:70` applies
it to the existing dense sequences. There is no loss in rho, replacement
of D by a scalar floor, extra copy of E, or global partition normalization.

`residual_pair_lower_of_certificates` at `:83` requires a certificate at
EVERY index of the actual block-prediction approximants of the supplied
Cauchy state, with `0<=rho<=1`. It yields the SAME completed residual bound

```
<R_A x,R_B x> >= -(rho/2) * (||R_A x||^2 + ||R_B x||^2).
```

The proof calls `residual_pair_lower_of_dense_covariance_bound` at
`lean/YMGap/Continuum/BF4ExactSlabBlockPredictionAngle.lean:116`.
The existing neighbor-sum consumer is `neighboringCross_lower` at
`lean/YMGap/Continuum/GNSProjectionNeighborLowerBound.lean:142`.
Its separate geometric degree hypotheses still have to be supplied.

## Remaining mathematical work and route limits

No certificates for a useful rho are constructed here. A finite list of
successful test certificates would not fill the quantified input above or
establish its cutoff, volume or scaling control. The next producer must
retain the original one-sided action weights, exterior variables and D.
The existing shared-interaction feature expansion is available for that
analysis, but gives no norm bound by itself.

This is a sufficient pairwise route, not a necessary condition for physical
mass. Collective signed bounds, or bounds only along the required auxiliary
recurrence, are not excluded. No new analytic assumption bundle, canonical
frontier or fixed dimensionless gap requirement is introduced.

The order argument uses positivity and inverse algebra; it introduces no
new load-bearing noncommutative estimate. It supplies no beta-uniform gap.
These are ordinary full-action conditional projections, NOT an OS transfer.
Useful signed scaling-family control, block geometry, nontrivial survival,
thermodynamic passage, same-theory OS/QFT/physical Hamiltonian mass and every
compact simple group remain open. No canonical chart claim changes.

Parallel source review also found that action invariance alone is not the
missing gauge-sector preservation theorem: `Invariant` and
`heatProduct_invariant` at
`lean/YMGap/Continuum/BF4ExactSlabVertexGaugeAction.lean:60` and `:234`
use auxiliary gauge variables; `slabGauge_haar` at
`lean/YMGap/Continuum/BF4ExactSlabAuxiliaryVertexGauge.lean:106` supplies
an auxiliary Haar identity. The required original completed block-projection
equivariance was NOT FOUND in those modules or in
`BF4ExactSlabBlockConditionalProjection.lean`,
`BF4ExactSlabBlockCompletedInverse.lean`, and `GNSChebyshevEnergy.lean`.
`state_mem` in the last module at `:137` consumes sector closure; it does
not prove this missing closure for the gauge sector. No gauge-restricted
small-correlation estimate is inferred.

## Verification boundary

All three new modules passed focused checks, serialized with one worker and
a 20 GiB ceiling through `scripts/safe_lean_build.py`; checked `.olean`
outputs were supplied to the downstream checks. All 16 printed declaration
gates were within `{propext, Quot.sound}`. No new sorry, axiom, classical
input or weakened frontier. Sol independently reviewed the original weights,
actual inverse, support-sensitive certificate transport and limit joins.

No full-root or full-tree build, audit, guard, broad test suite or progress
metric was run. Root imports are added without claiming a root integration
check. No Rust computation or external positivity solver was used.
