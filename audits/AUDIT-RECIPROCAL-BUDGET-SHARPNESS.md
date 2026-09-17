# Actual finite budget sharpness and coupled degrees — 2026-09-17 UTC

## Whole-project goal and scope

The unchanged goal is constructive continuum Yang--Mills on R^4 for every
compact simple gauge group, with the required same-theory QFT structure,
nontriviality, isolated vacuum and finite positive physical mass gap.
This checkpoint proves a finite SU(2) cost diagnostic. It does not prove a
regulator-uniform budget, a producer obstruction or a new spectral gap.

On the FULL original marginal nu=V*g_n*g_(n+1), write

    M_i = P_i nu,       J_i,k = the actual finite inverse polynomial,
    Phi = H[nu]*f-H[nu*f],       tau_i = (I-P_i)P_<i(nu*Phi),
    q_i = M_i*J_i,k*tau_i-P_i(nu*J_i,k*tau_i),
    B_i = H[M_i*J_i,k*tau_i^2],       N_i = H[nu*q_i^2].

These are the existing `marginalWeight`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualMarginalDual.lean:75`;
`inverse` and `test`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualSeed.lean:68`, `:116`;
`source` and `piece`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredHaarTelescope.lean:62`, `:66`.
The retained finite sum is `sourceCost`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialReciprocalSourceBudget.lean:65`.
None was replaced by a reduced-action or exact reciprocal object.

## The short identity and error estimate

Put e_i=1-nu*M_i*J_i,k and c_i=P_i(nu*J_i,k*tau_i). The two distinct
conditional orthogonalities are H[tau_i*c_i]=0 and H[nu*q_i*c_i]=0.
They give

    B_i = H[tau_i*q_i],
    B_i-N_i = H[e_i*tau_i*q_i].

The first uses P_i(tau_i)=0; the second additionally uses the actual
weighted centering P_i(nu*q_i)=0. These pins are `budget_pairing_pin`
and `budget_error_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualSeedBudgetError.lean:217`, `:227`.

Let ell be the existing positive density floor and rho the existing
inverse approximation rate. The inverse interval bounds
H[(e_i*tau_i)^2]<=rho^(2k)*H[tau_i^2]. The original floor together with
`test_norm_le`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualSeedNorm.lean:114`, gives
ell^2*H[q_i^2]<=H[tau_i^2]. Unweighted Haar Cauchy--Schwarz yields

    (ell*(B_i-N_i))^2 <= (rho^k*H[tau_i^2])^2,
    B_i-N_i <= rho^k*H[tau_i^2]/ell.

This is `budget_error_le_geometric`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualSeedBudgetError.lean:251`;
the sum-ready form is `budget_le_norm_add_geometric` at `:294`.
The existing opposite inequality is `test_norm_le_reciprocal_source`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualSeedReciprocalNorm.lean:118`.
Zero source norm, zero error and zero geometric factor require no division.
The proof only inverts ell>0; its private `square_reflect` at
`ActualSeedBudgetError.lean:73` includes the nonnegative boundary case.

## Actual-family consequence and finite witness

`normSum` and `gapPrefactor`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialReciprocalBudgetApproximation.lean:67`, `:73`,
retain the actual UNCORRECTED component norms and sum H[tau_i^2]/ell.
On every supplied valid finite index list, including the empty list,

    N_I <= B_I <= N_I + rho^k*gapPrefactor_I(f).

The declarations are `normSum_le_sourceCost` (:83) and
`sourceCost_le_normSum_add_geometric` (:91), in that module.
`gapCutoff` (:107) and `sourceCost_le_normSum_add` (:111) give
B_I<=N_I+epsilon for EVERY later seed degree. No degree-monotonicity
claim about B_I or N_I is used.

`approximationDegreesAfter` and `approximation_bound_after`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFamilyApproximation.lean:145`, `:159`,
enlarge the seed degree to a supplied floor and RECOMPUTE the correction
degree from those enlarged seeds. `coupledCertificate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialReciprocalBudgetApproximation.lean:129`,
returns one finite degree pair witnessing BOTH the original weighted-square
approximation tolerance and the additive cost tolerance. Neither tolerance
is an assumed analytic estimate; the witness is explicit Type-level data.

The approximation concerns the corrected SUM. The reverse cost estimate
concerns the uncorrected component norms, not the corrected active norms
or the target norm. On fringe entries only, `corrected`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:67`, is the identity.
The existing `fringe_norm_cost_lower_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSignedCostPositive.lean:131`,
makes this particular norm sum a necessary cost of the actual producer.
Thus a source-pinned finite lower calculation with enough certified slack
can test actual fringe cost, rather than merely a loose upper estimate.
No such lower calculation or growth theorem is supplied by this checkpoint.

## Parameters and remaining analytic join

`lower`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualMarginalWindow.lean:85`,
retains nome w, cutoff K, width and boundary depth n. `rate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualSeed.lean:78`, retains
the same regulators through the global lower/upper windows. This is an
INVERSE-APPROXIMATION rate, not temporal decay or physical mass.
`errorPrefactor`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualSeedBudgetError.lean:240`,
also retains the actual source norm. The sum/cutoff retain the index list,
observable and tolerance; the coupled witness retains both tolerances.
None asserts spacing, coupling, volume or depth uniformity.

The next analytic test is B_fringe versus ||Phi||_nu^2 on an adequate
coupled schedule, with the required regulator dependence. A positive
finite fringe cost alone would not refute a uniform bound. A product-density
analogy without an original-action/source pin would not refute this producer.
The active JOINT upper cost remains open even if fringe control succeeds;
its direct consumer is `approximant_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFamilyApproximation.lean:129`.
Physical calibration, same-theory continuum/QFT and every-group joins remain open.

## Verification boundary

Three focused serialized checks used the monitored launcher, one worker
and a 20 GiB ceiling, with a fresh process/swap preflight per invocation.
All 25 printed gates (18 new, seven existing) have dependencies within
{propext, Quot.sound}. Final logs contain no warnings, errors, sorryAx or
classical dependencies. Independent mathematical and final-source review passed.

Initial local checks found a parenthesis error and elaboration timeouts.
The final proof isolates scalar and polynomial identities before substituting
physical expressions; the temporary heartbeat option was removed.
Final elaboration options and machine-safety limits are unchanged.
Two root imports were added. No sorry was added/discharged, no analytic
premise introduced and no canonical frontier field changed. Root/full-tree
build, full axiom audit and guard were NOT run. CI remains unchanged.

Logs and SHA-256:

```text
/tmp/ym-centered-family-after-20260917.log
47cf3565a3319c75142d8027044b26c18a46bae055a8cdcc9868885350f45e7e
/tmp/ym-actual-seed-budget-error-20260917.log
0c62a19448f7bebb3dcbe0045ee57b0fe4b04ee5789772c6297cc4924a1582f1
/tmp/ym-reciprocal-budget-approximation-20260917.log
eb08dba002097d578ac1ab9a0cdcae4cff7b195e3c673fbab77cf78783d44315
```
