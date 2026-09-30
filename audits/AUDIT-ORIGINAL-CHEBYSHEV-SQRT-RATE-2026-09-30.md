# Original covariance: explicit square-root Chebyshev calibration

Date: 2026-09-30 UTC. Constructive scalar proof and original finite-law
join, not a new coercivity estimate or a continuum/physical mass gap.

## Mathematical increment

For rational x>1 set eta=(x-1)/(x+1). The existing Heron construction
returns a positive rational t with eta/4 <= t*t <= eta. Then

```
s = (1-t)/(1+t),  0 < s < 1,
y = (1+t*t)/(1-t*t),  1 <= y <= x,
1/T_n(x) <= 1/T_n(y) <= 2*s^n,
(1-s)^2 >= t*t >= eta/4.
```

The new argument-monotonicity proof compares both T_n and its forward
difference D_n. The positive recurrence is
`D_(n+1) = D_n + 2*(x-1)*T_(n+1)`; no subtraction of unrelated
inequalities is used. Declaration: `ChebyshevAboveOneMonotone.T_mono`,
`lean/YMGap/Continuum/ChebyshevAboveOneMonotone.lean:49`.

The pre-existing rational square-root quality bounds are
`RationalSqrtCalibration.rho_sq_upper`,
`lean/YMGap/Continuum/RationalSqrtCalibration.lean:106`, and
`rho_sq_lower` in that file at `:122`. The reciprocal-pair bound is
`ChebyshevMarginParameters.calibrated_recip_le`,
`lean/YMGap/Continuum/ChebyshevMarginParameters.lean:231`.

New declarations in `lean/YMGap/Continuum/ChebyshevSqrtRate.lean`:

- `eta:38`, `eta_pos:41`, `eta_lt_one:44` compute and bound the actual
  argument-dependent parameter.
- Private `center_bounds:65` proves the reciprocal-pair center lies
  between one and x.
- `rate:120`, `rate_pos:123`, `rate_lt_one:126` supply the rational rate.
- `rate_deficit_sq_lower:131` quantifies the square-root dependence.
- `reciprocal_T_le:174` transfers the reciprocal bound to T_n(x).
- `degreeModulus:182` and `normalization_small:186` give the explicit
  degree threshold for a supplied positive tolerance.

The construction uses no choice, numeric root oracle or erased witness.
The modulus reuses `powBaseCutoff`, not an optimal logarithmic index:
`lean/YMGap/Continuum/HeatKernelConvGen.lean:266`. Its definition uses an
unreduced rational numerator. The square-root inequality alone is not a
runtime bound for computing that witness.

## Join to the original covariance

The actual coefficient is `reverseCoefficient`,
`lean/YMGap/Continuum/BF4ExactSlabFiniteVolumeReverseEnergy.lean:92`:
`c=2+2*delta/625`, where `delta=coercivity(hw0,hw1,extent)` is constructed
in `lean/YMGap/Continuum/BF4ExactSlabFiniteVolumeCoercivity.lean:88`.
It compares the floor and cap over ALL physical faces. The new rate uses
x=c-1; no fresh reverse-energy premise is supplied.

Declarations in
`lean/YMGap/Continuum/BF4ExactSlabFiniteVolumeChebyshevRate.lean`:

- `argument_gt_one:52`, `rate:63`, `rate_positive:65`, `rate_lt_one:68`;
- `covarianceFactor_le_two_rate_pow:73` and the squared comparison
  `covarianceFactor_sq_le_two_rate_pow_sq:78`;
- `degreeModulus:88`, `covarianceFactor_le_of_modulus:92`;
- `finiteCovariance_sq_rate_bound:102` gives, in the existing constructive
  real order, `Cov(p,q)^2 <= (2*s^n)^2 * Cov(p,p)*Cov(q,q)`.

The latter consumes the existing exact result
`BF4ExactSlabFiniteVolumeChebyshevCovariance.finiteCovariance_sq_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFiniteVolumeChebyshevCovariance.lean:64`.
All original normalized covariances and both diagonal factors are unchanged.
Their nonnegativity justifies scalar monotonicity. The geometric separation
is still `LinksDisjoint (grow extent (16*n) support) testSupport`.
The action cutoff is still `headCutoff(w)+stage`; the rate depends on nome
and extent but not on this late stage. No spacing variable is introduced.

## Exact scope and remaining mathematical work

The new geometric bound is pointwise WEAKER than the exact reciprocal
already proved. Its gain is exposing square-root-margin dependence, rather
than discarding it through T_n(x)>=x^n. It is not asserted to beat x^(-n)
for every x,n: the factor two and the calibration approximation matter.

Nor does a scalar degree modulus prove a usable separated-observable
regime. The required cone grows with n inside a fixed slab. No theorem in
this increment supplies nonconstant separated probes at the returned degree
or makes the existing volume-dependent coercivity spatially uniform.
This is the original conditional-update covariance route, not an
identification with an OS transfer matrix or physical Hamiltonian.

Next mathematical input: useful signed/collective original-action control
on justified scaling, with compatible geometric separation. Do not expand
scalar interfaces instead of supplying it. A03, nontrivial continuum
survival, thermodynamic/spacing passage, same-theory OS/QFT reconstruction,
physical mass calibration and every compact simple group remain open.
No canonical displayed claim changed, so no ASCII chart was reprinted.

## Verification and parallel work

Sol supplied argument monotonicity and the original covariance join while
main proved the scalar calibration. Luna independently checked the signs,
center comparison, square-root deficit argument and separation limitation.
Compilation was serialized through the safe-build skill, one worker and a
20 GiB hard worker cap; preflight found no competing compiler and 79% free
memory. Automatic safety remained enabled. No large enumeration was run.

All final focused checks used
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20
--check <file> --check-output <matching olean>`:

- `ChebyshevAboveOneMonotone.lean`: exit 0, one printed gate.
- `ChebyshevSqrtRate.lean`: exit 0, about 2.02 s, ten printed gates.
- `BF4ExactSlabFiniteVolumeChebyshevRate.lean`: exit 0, about 5.51 s,
  nine printed gates.

All 20 gates reported only {propext, Quot.sound}; no sorryAx or classical
axiom in the final passing results. Initial scalar argument-order errors
and a local-notation parser collision were corrected before final checks.
No new sorry, axiom, named analytic premise, weakened field or frontier
closure. Root imports were registered; the root and full tree were NOT
built/audited. The canonical chart is unchanged.
