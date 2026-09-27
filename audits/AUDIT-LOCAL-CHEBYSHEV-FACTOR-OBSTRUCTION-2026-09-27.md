# Checked obstruction to the current local Chebyshev factor

## Conclusion and exact scope

For every rational nome 0<w<1, nonempty seed-support list of size s, and
degree d=n+1, the ACTUAL factor constructed at checkpoint `b338a25` satisfies

    1 - 2^(-d) <= factor(w,s,n) <= 1,
    factor(w,s,n)^2 >= 1/4.

For every positive rational epsilon, the returned modulus
`factorModulus(epsilon)=epsilon.den` ensures
`1-epsilon <= factor(w,s,n) <= 1` whenever n>=factorModulus(epsilon).
The modulus is independent of nome and nonempty seed size. Consequently this
factor returns to ONE, not zero, even if nome and seed size vary with degree.

The old upper covariance bound remains valid. This result rules out obtaining
long-distance decay merely by sending its degree to infinity. A lower bound
on its upper-bound MULTIPLIER is not a lower bound on the actual covariance.
It refutes neither covariance decay nor Yang--Mills. The old covariance
theorem also requires degree-dependent support separation: the scalar limit
does not assert applicability to a fixed pair on a fixed finite extent for
all degrees. Empty support is excluded explicitly by `1 <= size`.

## Declaration-level proof chain

1. `covarianceFactor`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalChebyshevCovariance.lean:53`,
   is the reciprocal of T_(n+1)(c_n-1), with
   c_n=2+(2/625)*supportRatio(w,25^(16*(n+1))*s).
   `finiteCovariance_sq_bound` in that file at line 69 uses its SQUARE
   times BOTH original diagonal variances. No surrogate factor is introduced.
2. `headFloor_le_oneThirtySecond`,
   `lean/YMGap/Continuum/BF4ExactSlabSharedWindowFloorBound.lean:46`,
   and `prefixCap_ge_one`,
   `lean/YMGap/Continuum/BF4ExactSlabStarRateObstruction.lean:32`,
   bound the actual collar ratio. `supportRatio_le_eighth_pow`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalChebyshevObstruction.lean:81`,
   proves supportRatio(w,b)<=(1/8)^d whenever d<=6*b.
   This is a deliberately weaker ceiling sufficient for the obstruction.
3. `degree_le_coneBudget`,
   `lean/YMGap/Continuum/BF4ExactSlabConeBudgetDegree.lean:32`,
   proves n+1<=25^(16*(n+1))*s for s>=1.
   `excess_le_eighth_pow`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalChebyshevObstruction.lean:94`,
   therefore bounds c_n-2 by (1/8)^(n+1).
4. `T_near_one_upper`,
   `lean/YMGap/Continuum/ChebyshevNearOneUpper.lean:156`,
   proves T_k(1+e)<=1+e*4^k for 0<=e<=1/2, by the rational recurrence.
   `T_congr` in that file at line 21 preserves rational equivalence of
   the actual coefficient argument. `denominator_bounds`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalChebyshevObstruction.lean:121`,
   yields 1<=T_(n+1)(c_n-1)<=1+2^(-(n+1)).
5. `factor_bounds`, `factor_ge_half`, and `factor_square_ge_quarter`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalChebyshevObstruction.lean:168`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalChebyshevObstruction.lean:179`, and
   `lean/YMGap/Continuum/BF4ExactSlabLocalChebyshevObstruction.lean:190`,
   give the displayed bounds on the existing reciprocal factor.
   `factorModulus` and `factor_approaches_one`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalChebyshevObstruction.lean:200` and
   `lean/YMGap/Continuum/BF4ExactSlabLocalChebyshevObstruction.lean:203`,
   supply the explicit tolerance-to-degree data and its proof.

## Redirected mathematical priority

Retain the existing local and finite-volume estimates as checked baselines;
do not continue treating this degree-dependent factor as a decay candidate.
The next target is a stronger collective SAME-original-action lower bound
on the actual auxiliary's conditional residual energy, with useful
degree/coupling dependence and signed cross terms retained.

The existing local finite rational input is `relativeValue`,
`lean/YMGap/Continuum/BF4ExactSlabStarVariationalApproximation.lean:148`;
`residual_relative_bracket` in that file at line 156 sandwiches each actual
residual energy between this value and this value plus epsilon times the
original input norm squared. This is approximation, not a collective lower
bound. `cross_link_kernel_test`,
`lean/YMGap/Continuum/BF4ExactSlabStarMixedPolynomialCost.lean:130`,
retains the mixed signed numerator and original exterior action; it does not
assert neighboring conditional kernels are preserved by exterior multiplication.

The actual downstream consumer is `reverse_energy_of_coercivity_at_balanced`,
`lean/YMGap/Continuum/BF4ExactSlabFiniteVolumeReverseEnergy.lean:156`.
Its needed lower bound is not supplied by `final_energy_le_625_loss`,
`lean/YMGap/Continuum/BF4ExactSlabConditionalSweepEnergy.lean:71`, which is
an UPPER comparison of residual energy with sweep loss. No new assumed
analytic certificate is added in this increment.

Parallel source review also rejects simply multiplying a fixed-degree factor
across spatial blocks. The cited `finiteCovariance_sq_bound` controls one
unconditional pairing of literal local tests. Its statement does not provide
a spatial cut/factorization through boundary observables, nor an operator
contraction uniform over the intervening boundary conditions and test class.
Those are additional obligations for such an iteration, not consequences of
a one-shot factor below one. This is a scope review, not a new Lean no-go
theorem about all possible finite-size methods.

These are original finite SU(2) conditional-link operators in ordinary GNS,
not identified physical OS-time operators. A03's justified scaling-family
estimate, same-theory thermodynamic/scaling/OS/QFT passage, nontrivial continuum
survival, physical Hamiltonian mass, every compact simple group and the Clay
target remain open. No canonical displayed claim or chart marker changes.

## Verification

Three focused checks passed, serialized through `scripts/safe_lean_build.py`
with one worker and a 20 GiB cap: ConeBudgetDegree (1 printed gate),
ChebyshevNearOneUpper (3), and LocalChebyshevObstruction (10). All 14 gates
stay within {propext, Quot.sound}; `factorModulus` is axiom-free. Each check
finished in its initial call; there was no live job requiring manual polling.

Sol supplied the scalar bound and independently reviewed the actual-factor
scope. Luna supplied the elementary cone-budget bound. The main agent
proved the actual-factor estimates and modulus and ran the serialized checks.
No new sorry, axiom, classical input, noncomputable declaration or canonical
frontier field. Root imports are registered; no root/full-tree build, full
audit, guard, progress-metric script, routine literature scan or CI run.
