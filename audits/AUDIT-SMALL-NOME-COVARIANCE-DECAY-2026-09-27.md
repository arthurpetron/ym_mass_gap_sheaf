# Audit: original small-nome covariance decay (2026-09-27)

## Proved estimate

The SAME original full-action covariance obeys

`Cov(p,q)^2 <= rho(w)^(2n) * Var(p) * Var(q)`

provided the literal link supports satisfy
`LinksDisjoint (grow extent (16*n) support) testSupport`.
The statement retains both original normalized diagonal covariances, not
Haar variances or coefficient norms. The parameter guards are `0<w<1`,
`heatRatio(w)<=1/2`, `heatRemainderBound(w)<1`, and positive
`ConditionalGeneratorMargin.margin`. The rate is strictly between zero
and one and has no extent, heat-cutoff, support-size or degree argument.

The concrete endpoint is
`BF4ExactSlabSmallNomeChebyshevCovarianceLimit.covariance_sq_geometric_bound`
at `lean/YMGap/Continuum/BF4ExactSlabSmallNomeChebyshevCovarianceLimit.lean:121`.
`existingNome_covariance_sq_geometric_bound` in the same file at line 193
discharges all scalar guards at the existing nome `1/1024`.

## Causal joins

1. `BF4ExactSlabSmallNomeChebyshevCovariance.reverseParameter`
   (`lean/YMGap/Continuum/BF4ExactSlabSmallNomeChebyshevCovariance.lean:41`)
   is `c=2+(2/625)*(gamma/2)`. `reverseParameter_gt_two` at line 44 proves
   strictness. `auxiliary_reverse_energy` at line 83 applies the already
   proved coercivity to the ACTUAL centered completed recurrence auxiliary;
   no analytic auxiliary estimate is assumed.
2. `finiteCovariance_sq_bound` in that file at line 94 supplies the existing
   finite original covariance consumer with factor `1/T_n(c-1)^2` and the
   unchanged `16*n` cone. Both the seed and test are actual original
   supported polynomials; original centering is retained.
3. `ChebyshevGeometricLower.pow_le_T`
   (`lean/YMGap/Continuum/ChebyshevGeometricLower.lean:67`) proves
   `T_n(x)>=x^n` for x>1. Its recurrence proof uses monotonicity above one;
   no trigonometric or spectral representation is assumed.
   `reciprocal_T_le_pow` at line 108 gives the inverse geometric bound.
4. `BF4ExactSlabSmallNomeCovarianceRate.rate`
   (`lean/YMGap/Continuum/BF4ExactSlabSmallNomeCovarianceRate.lean:36`)
   is the explicit rational `rho=1/(c-1)`. `rate_positive` and `rate_lt_one`
   at lines 40 and 43 prove its strict window.
   `covarianceFactor_le_rate_pow` at line 50 connects the actual factor.
   `degreeModulus` at line 64 is the explicit Nat
   `HKConvGen.powBaseCutoff rho epsilon`, with its eventual inequality at
   line 67. This is data, not extraction from a propositional existence.
5. `BF4ExactSlabConditionalVariancePositive.finiteVariance_nonnegative`
   (`lean/YMGap/Continuum/BF4ExactSlabConditionalVariancePositive.lean:47`)
   uses the exact completed-covariance identity and the positive original
   reciprocal partition. No normalization or measure is replaced.
6. `BF4ExactSlabSmallNomeChebyshevCovarianceLimit.covariance_sq_bound`
   (`lean/YMGap/Continuum/BF4ExactSlabSmallNomeChebyshevCovarianceLimit.lean:42`)
   passes the finite estimate through the EXISTING
   `BF4ExactSlabConnectedFaceResponse.finite_covariance_converges`
   (`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:166`).
   Extent, nome, degree and both observables stay fixed. Product continuity
   and closed order preserve the inequality. Diagonal positivity at line 99
   permits scalar enlargement to the geometric factor at line 121 and to
   epsilon squared at line 153 (`covariance_sq_epsilon_bound`).

## Parameter and constructive boundary

Only the coefficient is uniform across extent and cutoff: each covariance
still belongs to its specified original finite volume. The cutoff removed is
the representation/heat cutoff, not lattice spacing. The new modulus controls
the RELATIVE covariance coefficient; an absolute covariance tolerance also
needs control of the displayed variances. Increasing n requires observables
whose supports actually meet the increasingly strong separation premise.
No unrestricted n-to-infinity claim about a fixed finite-volume pair is made.

The construction uses original SU(2) conditional-link projections. These are
not identified with OS physical-time translations. This result neither
constructs a thermodynamic limit nor a justified changing-nome/vanishing-spacing
family, and it does not prove nontrivial continuum survival, QFT axioms,
physical Hamiltonian mass or the every-compact-simple-group Clay target.
The previous local collar-factor obstruction is not contradicted: the new
coercivity coefficient is independent of recurrence degree.

## Next mathematical boundary

The fixed-small-nome window must be reconciled with justified scaling and
nontrivial finite-physical-time response, not assigned an arbitrary spacing.
For volume passage, the available
`BF4ExactSlabConnectedFaceResponse.finite_response_bound`
(`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:209`) consumes a
signed response estimate on selected face sets. The present covariance result
is for the full original face set and does not discharge that response input
or a summable boundary/volume modulus. These are distinct open joins, not
consequences of the word "uniform". No canonical field is changed or claimed
inhabited; A03 and the displayed chart remain unchanged.

## Focused verification

All paths below are under `lean/YMGap/Continuum/`.

| Focused target | Printed gates |
| --- | ---: |
| `BF4ExactSlabSmallNomeChebyshevCovariance.lean` | 7 |
| `ChebyshevGeometricLower.lean` | 5 |
| `BF4ExactSlabSmallNomeCovarianceRate.lean` | 12 |
| `BF4ExactSlabConditionalVariancePositive.lean` | 2 |
| `BF4ExactSlabSmallNomeChebyshevCovarianceLimit.lean` | 5 |
| Total | 31 |

Each final file passed a focused check through `scripts/safe_lean_build.py`
with one worker, a 20 GiB worker cap, continuous safety telemetry and the
matching `--check-output` olean. All 31 printed dependencies stay within
`{propext, Quot.sound}`, with no `sorryAx`. No full-tree/root-module build,
full audit, guard, progress-metric or CI run was performed. Root imports
were registered but the aggregate root was not built.

Sol independently reviewed parameter dependence, the original variance and
carrier pins, literal cone degree, and the cutoff-versus-physical-scaling
boundary. Sol and Luna supplied independent scalar, limit and positivity
proof tasks; compilation stayed serialized. No new sorry, axiom, analytic
bundle, weakened frontier or quotient-selected modulus was introduced.
