# Step back to the original normalized-source budget

Date: 2026-09-30 UTC. Starting source checkpoint: `dafa227`.
Whole-project goal remains OPEN: constructive continuum Yang--Mills on R^4
for every compact simple group, with same-theory QFT axioms, nontriviality
and a finite positive physical Hamiltonian gap.

## What changed mathematically

The previous patch coefficient is positive but too small for the recorded
collective/scaling budget. Completing further consequences of that coefficient
would not improve it. A source-only review also found that removing all
one-sided factors to diagonalize a shared plaquette is not justified:
`lean/YMGap/Continuum/BF4ExactSlabTwoLinkFourCopy.lean:151`,
`interaction_cross_determinant_pin`, RETAINS those factors in the replicas.
The opposite-coordinate independence at lines 79 and 88 does not make a
factor independent of its own link. No new convolution/spectral claim is made.

Stepping back to the ACTUAL covariance consumer reveals an avoidable
restriction. Write W for the existing forward conditional sweep, B=W^* W,
x for the original centered source, (t_n,u_n) for its actual coupled
Chebyshev state at rational parameter c, and T=Cheb.T n (c-1)>0. Put

    N = ||x||^2,
    M = 2*||W u_n||^2 - c*||B u_n||^2.

The existing exact law is ||t_n||^2+c*M=N:
`lean/YMGap/Continuum/BF4ExactSlabChebyshevRescale.lean:210`,
`coupled_norm_add_margin`. At c>0, M>=0 is equivalent to ||t_n||^2<=N,
as already proved by `coupled_first_norm_iff_reverse_energy` at line 256.
Thus a direct test of THAT unnormalized norm bound is not a new route.

But the covariance uses t_n/T. For a desired squared factor eta, the
relevant exact deficit is

    BUDGET = c*M + (eta*T^2-1)*N
           = eta*T^2*N - ||t_n||^2.

Nonnegative BUDGET implies ||t_n/T||^2<=eta*N. In particular, when
1/T^2<eta<1, negative M is admissible. The old proof is correct and gives
its sharper specified factor 1/T^2; no theorem is refuted or weakened.
This criterion allows a weaker but still strict factor when that is enough.
Even for the old covariance factor, the sign condition is not claimed
necessary for covariance itself: Cauchy--Schwarz can be strict.

## New checked original-carrier declarations

All paths below are under `lean/YMGap/Continuum/`.

| Declaration | File:line | Content |
| --- | --- | --- |
| `budget` | `BF4ExactSlabChebyshevNormBudget.lean:101` | Constructed signed CReal from the actual margin and source norm |
| `budgetRegularity` | `BF4ExactSlabChebyshevNormBudget.lean:108` | Type-level error cutoff from the existing representative moduli |
| `budgetValue` | `BF4ExactSlabChebyshevNormBudget.lean:114` | Finite rational evaluation at that cutoff |
| `budget_pin` | `BF4ExactSlabChebyshevNormBudget.lean:120` | Exact SAME-state deficit identity |
| `normalizedFirst_norm_of_finite_budget` | `BF4ExactSlabChebyshevNormBudget.lean:138` | Positive lower bracket implies the normalized norm bound |
| `finiteCovariance_sq_bound_of_finite_budget` | `BF4ExactSlabChebyshevBudgetCovariance.lean:96` | Squared original separated covariance <= eta times its original diagonal variances |

The last theorem uses the original centered `constCauchy` source and the
same degree-dependent `grow extent (16*n)` separation. The original
partition reciprocal is squared on both sides and the existing diagonal
covariance pins are used, not substituted background variances.

The finite check is `epsilon <= budgetValue ... eta epsilon` with
epsilon>0. Its computed lower bracket is therefore nonnegative. eta and c
need no sign for this algebraic implication; calling the result a strict
relative bound separately requires 0<=eta<1. No source norm is divided out,
so a zero source causes no undefined operation. Numerical `budgetValue`
depends on the SUPPLIED Cauchy representative; only the certified completed
inequality is representative-independent. No representative is chosen.

## Checked strictness witness, NOT Yang--Mills

`lean/YMGap/Continuum/RationalChebyshevNormalizationWitness.lean:28`, `P`,
and line 31, `Q`, define P=diag(1,0),
Q=[[16,12],[12,9]]/25, W=QP and B=PQP, with x=(1,0). Exact finite checks
prove symmetry/idempotence of P,Q and B=W^* W. At c=4,n=1,T=3:

    ||Wx||^2 = 16/25,       ||Bx||^2 = 256/625,
    M = -224/625,           ||t_1||^2 = 1521/625,
    ||t_1/3||^2 = 169/625 < 1/3,
    BUDGET(eta=1/3) = 354/625 > 0.

Declarations `balanced_is_adjoint_square` (line 58), `source_normSq` (61),
`chebyshev_normalized_value` (90),
`strict_normalized_contraction_with_negative_margin` (95) and
`margin_budget_positive` (103) in that same file are kernel-checked exact rational
calculations. They show a genuine distinction between the sufficient tests,
not success of the relaxed test for any interacting Yang--Mills source.

## Execution decision and precise residue

Use this normalized-source budget as the immediate analytic target.
The constructive representative/margin machinery already supplies finite
error-controlled tests. The missing producer is a useful signed budget
estimate for ACTUAL centered original observables with explicit dependence
on degree, cutoff, volume and coupling along a justified scaling family.
Do not require a stronger all-state conditional-dynamics gap unless its
proof is actually the shorter route. Do not add further budget wrappers
without producing a quantitative source bound.

A single factor eta<1 at one degree is not exponential spatial decay.
Uniformity over degree/separation and the intended regulator family must
be supplied. A successful source test cannot be iterated on new states
without proving their own tests. No uniform original-source success,
efficient finite evaluator, or decay rate is proved by these modules.

The retained-product two-link variance route remains a possible alternative:
the existing one-face square-form comparison could charge only the shared
factor, but it still lacks normalized retained-product conditional variance
on arbitrary exterior-dependent states. Its lower/upper ratio may also
deteriorate in coupling. This review did not build that machinery or assume
its estimate. No routine literature listing scan or heavy computation ran.

These are ordinary conditional-dynamics covariance statements, not physical
time. OS/scaling passage, continuum survival, finite positive physical mass,
full QFT and every compact simple group remain open. No canonical frontier
field, chart marker, or old theorem changed. No chart was reprinted.

## Verification boundary

Three final focused checks passed 20 printed gates within
{propext, Quot.sound}; the rational-witness gates use at most propext
(the two symmetry checks are axiom-free).
One serialized worker, 20 GiB hard limit, 12 GiB reserve, continuous launcher
telemetry and 300-second status cadence. All checks finished in their initial
calls. No full-root/tree build, audit or guard ran; root imports are registration.
No new sorry, analytic premise, classical axiom, native oracle or frontier
weakening, and no old sorry discharged. Independent Sol source review found
the budget sign, original-state pins and partition cancellation consistent;
Luna supplied the explicit rational witness, checked by the parent.

Final logs:

- `/tmp/ym-chebyshev-norm-budget-20260930.log`
- `/tmp/ym-chebyshev-budget-covariance-20260930.log`
- `/tmp/ym-chebyshev-normalization-witness-20260930.log`
