# The auxiliary condition is order-specific, not an automatic bootstrap

This checkpoint tests the proposed use of the smaller, observable-generated
auxiliary condition. It neither abandons that route nor establishes its
missing useful uniform estimate. The whole-project constructive continuum
Yang--Mills/Clay target remains open.

## Exact original-carrier identity

Write W for the original conditional sweep, B=W*W for its balanced sweep,
X=cB-I, and (t_n,u_n) for its actual coupled Chebyshev state. Then

    ||t_n||^2 + c M_n = ||x||^2,
    M_n = 2||W u_n||^2 - c||B u_n||^2.

`BF4ExactSlabChebyshevRescale.coupled_norm_add_margin` in
`lean/YMGap/Continuum/BF4ExactSlabChebyshevRescale.lean:210` proves this
identity on the SAME original full-action completion, with no centering,
coercivity or sign hypothesis. It combines the existing invariant
`GNSChebyshevEnergy.state_energy` in
`lean/YMGap/Continuum/GNSChebyshevEnergy.lean:113` with the original affine
norm expansion, preserving the signed terms.

For c>0, `coupled_first_norm_iff_reverse_energy` in
`lean/YMGap/Continuum/BF4ExactSlabChebyshevRescale.lean:256` gives exactly

    ||t_n||^2 <= ||x||^2  iff  c||B u_n||^2 <= 2||W u_n||^2.

Only the positive rational c is inverted. No vector norm is inverted and
no representative is chosen. This is an equivalence to the UNNORMALIZED
first-component norm bound at this order, not an equivalence to covariance
decay: the subsequent Cauchy--Schwarz inequality can be strict.

## A finite two-projection counterexample to propagation

`lean/YMGap/Continuum/RationalChebyshevAuxiliaryObstruction.lean` uses the
Euclidean rational coordinate space Q^4. Its matrices are

    P = diag(1,0,1,0),
    Q = diag([[9,12],[12,16]], [[16,12],[12,9]]) / 25,
    W = QP,  B = PQP = diag(9/25,0,16/25,0).

`P_symmetric`, `P_idempotent`, `Q_symmetric`, `Q_idempotent`
(`lean/YMGap/Continuum/RationalChebyshevAuxiliaryObstruction.lean:65`)
certify the finite coefficient identities. `balanced_matrix_pin` (`:79`)
computes B and `balanced_is_gram` (`:82`) checks B=W*W. These are coefficient-level rational
matrix certificates, not a newly constructed GNS completion.

Take c=4 and x=(1,0,1/2,0). The actual finite recurrence is

    (t_0,u_0) = (x,0),
    u_(n+1) = t_n + X u_n,
    t_(n+1) = X u_(n+1) - u_n.

`first_auxiliary_value` (`:107`) and `second_auxiliary_value` (`:109`)
compute u_1=x and u_2=(22/25,0,39/25,0). `first_reverse_margin` (`:115`)
and `second_reverse_margin` (`:118`) give

    M_1 = 14/125 > 0,
    M_2 = -55944/78125 < 0.

`first_pass_later_failure` (`:127`) states the two actual sweep-norm
comparisons, and `no_first_to_second_bootstrap` (`:134`) refutes their
implication. `first_component_norm_tests` (`:141`) checks the corresponding
success and failure of the actual first-component norm comparisons. The failure
is at the SAME c and SAME seed. Orthogonal-projection geometry plus a
successful initial test therefore does not propagate the required sign.
This is NOT an original Yang--Mills action, a centered physical-carrier
counterexample, or a counterexample to a physical mass gap.

## Consequence for the next proof

The original consumer
`BF4ExactSlabChebyshevCovarianceBound.finiteCovariance_sq_bound` in
`lean/YMGap/Continuum/BF4ExactSlabChebyshevCovarianceBound.lean:102`
requires M_n>=0 at the actual order n, together with its grow(16*n)
separation. Its statement is unchanged. The existing finite checker
`BF4ExactSlabChebyshevFiniteTest.reverse_energy_of_finite_test` in
`lean/YMGap/Continuum/BF4ExactSlabChebyshevFiniteTest.lean:115` also
certifies only its supplied order. Do not extrapolate one success.

The existing all-order producer
`BF4ExactSlabFiniteVolumeReverseEnergy.coupled_auxiliary_reverse_energy`
in `lean/YMGap/Continuum/BF4ExactSlabFiniteVolumeReverseEnergy.lean:200`
uses separately proved centered coercivity, with a volume-dependent
coefficient. This checkpoint does not improve that coefficient.

Keep the actual-auxiliary route as a sufficient alternative to all-state
coercivity, but require a genuine estimate over every order and parameter
range consumed. Alternatively bound the original signed covariance
directly. Neither recasting the norm target as reverse energy nor testing
one order supplies that estimate. No additional recurrence compiler or
assumption bundle is warranted by this diagnostic.

## Quantitative target, without an unnecessarily strong spacing requirement

The checked scalar result `ChebyshevSqrtRate.rate_deficit_sq_lower` in
`lean/YMGap/Continuum/ChebyshevSqrtRate.lean:131` gives

    (1-s)^2 >= d / (4*(2+d)),  where c=2+d and d>0.

`reciprocal_T_le` in
`lean/YMGap/Continuum/ChebyshevSqrtRate.lean:174` bounds the reciprocal
Chebyshev factor by 2*s^n. Its existing original finite-action join is
`BF4ExactSlabFiniteVolumeChebyshevRate.finiteCovariance_sq_rate_bound` in
`lean/YMGap/Continuum/BF4ExactSlabFiniteVolumeChebyshevRate.lean:102`.

The following is a paper-level budget deduction, NOT a new checked scaling
family or physical-mass theorem. For 0<a<=a0, d(a)>=C*a^2 with C>0 gives

    (1-s)^2 >= C*a^2 / (4*(2+C*a0^2)).

This follows by monotonicity of d/(2+d), then a<=a0. Any explicit positive
rational kappa with 4*kappa^2*(2+C*a0^2)<=C gives 1-s>=kappa*a.
Thus the needed relative spatial coefficient can tolerate quadratic
vanishing of the excess. With suitable separated observable geometry,
16*n lattice steps represent physical distance 16*n*a. A spacing-independent
positive lower bound for d is not necessary for this mechanism.

The original-action producer of d(a)>=C*a^2 is missing. Uniform diagonal
variance control and an actual separated observable/scaling family are also
needed for an absolute continuum correlation claim. No identification with
OS physical time, no Hamiltonian gap, and no lattice spacing law is supplied
by the scalar inequalities above.

## Verification

Both focused final checks passed, serialized with one worker, a 20 GiB
worker ceiling, 12 GiB OS reserve and continuous safety telemetry:

- `BF4ExactSlabChebyshevRescale.lean`: seven printed gates, all exactly
  `{propext, Quot.sound}`; log `/tmp/ym-chebyshev-margin-final-20260930.log`.
- `RationalChebyshevAuxiliaryObstruction.lean`: fifteen printed gates,
  two axiom-free and thirteen with only `propext`; log
  `/tmp/ym-chebyshev-auxiliary-obstruction-20260930.log`.

The first original-carrier attempt found a local-notation/name collision;
the final check above follows its correction. No full-root, full-tree,
audit or guard run was performed. `git diff --check` passed. No new `sorry`,
custom axiom, classical principle, frontier-field change or chart-state change.
No existing `sorry` or genuinely open analytic estimate was discharged.
Luna supplied the finite example; root supplied the original-carrier identity
and equivalence; Sol independently reviewed both arguments.
