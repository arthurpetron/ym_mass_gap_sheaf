# All-even-time response and finite-time survival of the same Wilson excitation

Date: 2026-09-17. Source baseline: `39dc67d`.

WHOLE-PROJECT GOAL: constructive nontrivial continuum Yang--Mills on R^4
for every compact simple group, with same-theory QFT axioms, isolated vacuum
and positive finite physical Hamiltonian mass gap. **OPEN.**

## The short argument and exact consumer

Use the existing completed Wilson pairing B and time map T. For any vector x
on this carrier and rational rho, put

    r_n = B(x,T(2*n)x) = B(T(n)x,T(n)x),
    e_n = r_(n+1) - rho*r_n.

The actual squared norm of T(n+2)x-rho*T(n)x is

    r_(n+2) - 2*rho*r_(n+1) + rho^2*r_n
      = e_(n+1) - rho*e_n >= 0.

This is `evenResponse_second_difference`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionResponseLower.lean:86`.
The scalar rho need not be positive for this identity/inequality. When
rho>=0 and r_1>=rho*r_0, the initial e_0 is nonnegative. Induction gives
e_n>=0 and then r_n>=rho^n*r_0, in `evenResponse_step_lower` at :106 and
`evenResponse_geometric_lower` at :121. No correlation is inverted; zero
vectors and zero rho are included in the general theorem.

The existing norm-one excitation and its proved positive two-step floor
supply the otherwise conditional input: `unitExcitation_norm`,
`normalizedResponse_pin`, `normalizedResponse_floor`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionNormalizedExcitation.lean:107`,
:134, :151. The new `unitExcitation_even_lower`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionResponseLower.lean:150`, proves

    rho^n <= B(v,T(2*n)v)        for EVERY natural n.

Together with the existing original-transfer upper decay,
`unitExcitation_even_upper` at :163 and `unitExcitation_even_band` at :175
give

    rho^n <= B(v,T(2*n)v) <= q^n.

Here rho=`rayleighFloor` and q=`rayleighCeiling` of the existing normalized
excitation module; `rayleighFloor_positive` and `rayleighCeiling_lt_one`
there at :143 and :148 prove 0<rho and q<1. No floor is squared or otherwise
degraded in extending the previous dyadic-only lower bound.

`unitExcitation_time_norm_floor` and `unitExcitation_time_ne_zero`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionResponseLower.lean:183`, :196,
give rho^n<=||T(n)v||^2 and exclude the actual completed zero at EVERY
finite integer time. They use `completedInner_even_diagonal`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionTimeForm.lean:113`, on this
very same carrier. No legacy-carrier isomorphism is assumed.

## Backward meeting point and remaining inputs

This fills a discrete-time quantitative survival subgoal using already
constructed inputs. The general theorem is conditional on a genuine initial
Rayleigh floor; its displayed normalized-vector instance supplies that floor
unconditionally at the fixed nome 1/1024. The actual completion's original
small-nome guards remain unchanged throughout.

The result concerns EVEN-lag correlations and norm squares of images at
arbitrary integer times. It does not assert positivity of odd-lag responses
or of the one-step operator. Self-adjoint time balance and squared-norm
positivity suffice. No spectral representation or classical theorem is used.

As spacing tends to zero, a fixed physical time entails increasing lattice
time. A fixed rho in (0,1) gives lower bounds tending to zero, not a uniform
positive continuum survival bound. Actual changing-spacing families, their
observable comparisons and moduli, scale-controlled response floors and
same-limit nontriviality remain unsupplied. Physical mass additionally needs
the same actual continuous-time generator and its time calibration. A
two-step response uses physical time 2*a. No such generator, continuum QFT
or every-group realization is constructed here.

The independent primary review found no new signed spatially uniform decay
estimate. Its source-backed temporal target and fusion-insertion distinction
are recorded in `AUDIT-FUSION-TEMPORAL-CONSUMER-2026-09-17.md`. This parallel
survival theorem does not replace that missing forward input.

## Verification

The complete new source was inspected by the parent and an independent
reviewer; the mathematical argument, same-carrier pins and scope passed.
The final focused check passed through `scripts/safe_lean_build.py`, with
one worker and an explicit 20 GiB ceiling, after process/swap preflight.
All eight public gates report exactly {propext, Quot.sound}. The first check
failed at a redundant rewrite after simplification had already produced the
required expression; the rewrite and unused helper were removed. Its
error-induced sorryAx output was not accepted as verification.

Final log: `/tmp/ym-wilson-response-lower-20260917.log`.
SHA-256: `78d3c2d42561d362ad82daf6f649b1b80d3163a5cf3081dbecc89f5d4a720523`.
Final Lean source SHA-256:
`dcc3ec7a3b911edb36442e3467d5484f98ee44f6b5dcc6924b398e336fa92888`.

No sorry introduced/discharged, analytic oracle, canonical field change,
resource limit or CI change. One semantic-root import added. Full root,
full-tree build, full audit, guard and progress runs were NOT performed.
