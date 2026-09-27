# Constructive polynomial approximation of the original conditional residual

## The mathematical join

For the actual original slab action, let C_i be its already constructed
conditional projection, R_i=I-C_i, D its local conditional normalizer,
N its inserted numerator, B the retained complementary heat product, and
J the exterior probe map. The original polynomial kernel test is
t(p)=J(D)*p-J(Np). All these objects are unchanged.

Take the existing explicit reciprocal iteration a_n=A(1,n) and e_n=1-D*a_n.
The useful identity is

    R_i p - t(J(a_n)*p) = R_i(J(e_n)*p)

in the SAME completed full-action carrier. The exterior numerator term
J(a_n*Np) is killed by R_i; it is not discarded by a norm estimate.
Projection contractivity then reduces the squared approximation error to

    ||J(e_n)*p||_F^2 = H[B*N(p^2)*e_n^2].

The weight B*N(p^2) has an explicitly constructed square certificate. The
original normalizer interval L<=D<=U, stated under every supported square
test, extends by induction to EVERY existing positive certificate. This
includes both B*N(p^2) and the earlier B*Phi_p variance weight. No pointwise
normalizer order is assumed, and every shared exterior variable is retained.

Consequently the same polynomial iteration has geometric defect in the
required weight, with q(w)=1-L(w)/U(w):

    ||R_i p - t(J(a_n)*p)||_F^2 <= q(w)^(2n) * ||p||_F^2.

This is approximation TO the fixed residual R_i p, not decay OF that
residual, a sweep-mixing estimate, or a physical mass gap. The relative
rate is independent of K>=headCutoff(w), extent and link position at fixed
w. Polynomial size and runtime are not asserted independent of these
parameters. There is no uniformity claim as w approaches one.

## Source map

- `Certificate.form_interval` in
  `lean/YMGap/Continuum/QuaternionHaarCertificateFormBounds.lean:58` transfers
  square-test bounds through square/add/nonnegative-scalar/transport
  constructors. Arbitrary-insertion equivalence justifies the transport case.
- `certified_residual_norm` and `certified_error_le` in
  `lean/YMGap/Continuum/BF4ExactSlabStarCertifiedApproximation.lean:134`
  and `:165` estimate
  the EXISTING polynomial iteration in the certified weight.
  `variance_residual_norm` (`:187`) supplies the actual B*Phi instance without a
  positivity premise.
- `tailSquare_certificate`, `original_norm_pin`, `exteriorSeed_norm_pin`
  and `exteriorSeed_one_completed` in
  `lean/YMGap/Continuum/BF4ExactSlabStarExteriorSeedNorm.lean:97`, `:106`,
  `:120` and `:155` construct the
  B*N(p^2) certificate and exact original norm identities. The padded
  exterior unit is identified in the completion, not coefficientwise.
- `residual_error_identity`, `residual_approximation_norm`,
  `residualCutoff` and `residual_approximation_error_le` in
  `lean/YMGap/Continuum/BF4ExactSlabStarResidualApproximation.lean:142`,
  `:177`, `:221` and `:225` implement
  the direct same-carrier join and its absolute squared-distance tolerance.
- `residual_dual_error_identity` and `residual_energy_bracket` in
  `lean/YMGap/Continuum/BF4ExactSlabStarVariationalApproximation.lean:84`
  and `:137` are the
  finite-test variational consumer: the exact error equals residual energy
  minus the signed rational dual value. `approximationValue` (`:130`) retains the
  chosen iteration and finite value as data, without a supremum or choice.

## Relative tolerance and actual finite values

`relativeCutoff` in
`lean/YMGap/Continuum/BF4ExactSlabStarResidualApproximation.lean:241` takes
ONLY w and epsilon. `residual_relative_error_le` (`:247`) bounds squared
distance by epsilon times the original squared norm at every later index.
Unlike the absolute-tolerance cutoff, its index does not depend on the
input norm or on volume/cutoff/link position. No division by a possibly
zero input norm occurs.

`relativeValue` and `residual_relative_bracket` in
`lean/YMGap/Continuum/BF4ExactSlabStarVariationalApproximation.lean:148`
and `:156` compute v and prove

    v <= ||R_i p||_F^2 <= v + epsilon*||p||_F^2.

All comparisons embed the rational endpoints into the existing constructive
real quotient. The absolute variant has interval width epsilon instead.
These are unnormalized original-form energies of a supplied original
polynomial, not yet an interval algorithm for arbitrary completed inputs
and not normalized physical Hamiltonian energies. Local variational
completeness means precisely these checked finite-test brackets.

## Boundary and verification

All five new modules passed focused checks, serialized through
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check ...`.
All 29 printed public gates lie within `{propext, Quot.sound}`; the relative
cutoff itself is axiom-free. Sol contributed the certificate/norm/variational
lemmas and independently reviewed the same-object error estimate. The one
check that outlasted its initial tool call was polled about five minutes
later; independent proof work continued meanwhile. No new sorry, axiom,
classical input or analytic field. Root imports were added, but no root/
full-tree build, audit or guard was run.

The local approximation does not supply a useful uniform lower bound on
the sum of residual energies against the original centered norm. That
analytic estimate, or the smaller observable-generated estimate actually
consumed by the spatial argument, remains the next missing producer. Local
variational completeness cannot substitute for it. The rescaled operator/
cone join, physical scaling, same-theory OS/Hamiltonian and continuum QFT,
nontrivial survival, every-group estimates and the Clay target remain open.
No canonical field or chart marker is changed by this work.
