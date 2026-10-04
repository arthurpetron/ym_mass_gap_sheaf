# Macroscopic retention versus the initial-energy sufficient condition

## Outcome and exact scope

This increment checks a strict separation between the desired macroscopic
response ratio and the small INITIAL-energy sufficient condition. It does
not produce either analytic estimate for the original BF4 action, a justified
changing family, continuum survival, or a Yang--Mills counterexample.
The constructive continuum Yang--Mills/physical mass-gap target on R^4 for
every compact simple group remains OPEN.

The analytic priority is now the ORIGINAL aggregate signed-window producer.
The one-reference initial-energy route remains a valid sufficient alternative,
not an additional prerequisite. This changes execution order only: no
canonical frontier statement, field, hypothesis, or chart atom is weakened.

## Checked finite separation

Let s=n+1, q=1-1/(2s), and

    C_n(j) = (q^j + (1/2)^j)/2.

These are two literal positive scalar contraction modes with equal positive
weights. The source uses the previously constructed rates, not an original
BF4 carrier or source. The new declarations belong to namespace
`YMGap.Continuum.RationalMacroRetentionWithoutInitialEnergy`.

| Declaration | Source | Exact statement |
| --- | --- | --- |
| `response`, `macroRetention`, `initialLossFloor` | `lean/YMGap/Continuum/RationalMacroRetentionWithoutInitialEnergy.lean:29`, `:30`, `:31` | Computable response, kappa=1/8, and loss floor=1/4. |
| `response_zero` | `lean/YMGap/Continuum/RationalMacroRetentionWithoutInitialEnergy.lean:87` | C_n(0)=1 in rational setoid equality. |
| `response_positive` | `lean/YMGap/Continuum/RationalMacroRetentionWithoutInitialEnergy.lean:91` | C_n(j)>0 for every n,j. |
| `response_le_one` | `lean/YMGap/Continuum/RationalMacroRetentionWithoutInitialEnergy.lean:98` | C_n(j)<=1 for every n,j. |
| `slow_horizon_floor` | `lean/YMGap/Continuum/RationalMacroRetentionWithoutInitialEnergy.lean:108` | q^s>=1/2 by constructive Bernoulli and the actual horizon/rate pin. |
| `response_macro_retention` | `lean/YMGap/Continuum/RationalMacroRetentionWithoutInitialEnergy.lean:117` | (1/8)*C_n(s)<=C_n(2s) for EVERY n, without a retention premise. |
| `initial_loss_lower` | `lean/YMGap/Continuum/RationalMacroRetentionWithoutInitialEnergy.lean:142` | 1-C_n(1)>=1/4 for EVERY n. |
| `initial_budget_incompatible` | `lean/YMGap/Continuum/RationalMacroRetentionWithoutInitialEnergy.lean:157` | For s>=5, any c with 1-C_n(1)<=c*C_n(0) fails s*c<=1. |

The underlying rates and exact horizon loss are
`lean/YMGap/Continuum/RationalTwoModeSurvivalObstruction.lean:40`
`slowRate`, `:78` `slowRate_bounds`, `:89` `slowRate_lt_one`, and `:97`
`horizon_rate_loss`. Thus neither scalar mode is an extra stationary mode.
The old obstruction used an exponentially small slow overlap and refuted
retention; the present equal-weight example CONSTRUCTS retention and refutes
necessity of the initial-energy budget. The two examples have different
weights and different conclusions.

The short proof is q^s>=1/2, hence C_n(2s)>=1/8, together with C_n(s)<=1.
The fast half-weight mode keeps the initial loss at least 1/4; consequently
s*c>=5/4 when s>=5. No spectral theorem, real division, choice, or erased
rate witness is used. The three definitions and unit-normalization theorem
are axiom-free; the remaining six gates use only {propext, Quot.sound}.

This proves a separation from the macro-retention DEMAND. It does not
reverse that ratio into the original finite signed-window hypothesis, or
claim that the factor-two window-cost ceiling is equivalent to the ratio.

## Forward/backward route choice on the ORIGINAL objects

BACKWARD, the existing
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`
`original_window_budget_macro_ratio` already consumes

    2*sum_(t=u,...,2u-1) originalOwnBlockCost(stage,t)
       <= (1-kappa)*originalOwnBlockVariance(stage,u)

at every sufficiently late cutoff. It retains each lag's DISTINCT original
Z0,Z1 and the COMMON stage OWN center. The next mathematical task is the
producer of this aggregate estimate, not a replacement consumer or an
assumed-budget wrapper.

FORWARD, the checked
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepPredictionEnergyNormalized.lean:133`
`lastStepNoise_prediction_energy_cleared` pays the actual incoming conditional
noise by ORIGINAL incoming energy, with the terminal scale canceled against
distinct original partitions. It does not prove that this energy is small.
Use this actual energy currency together with BOTH signed Taylor terms;
do not bound and discard their cancellation separately.

The alternative
`lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:123`
`completed_reference_ratio` remains available. Its premise is ONE actual
finite reference-depth bound against SAME OWN variance at all late cutoffs,
and its effective completed coefficient is

    b = c*(1+comparisonEta(w,width,referenceDepth))^2.

An initial-loss budget s*b<=1-kappa is sufficient but not necessary in the
checked scalar example. This does NOT prove that the original BF4 source
fails that budget. There is no source-proved physical nome/side schedule
that makes it automatic: the physical 4D envelope construction remains open
in `lean/YMGap/Continuum/BF4AFHeatSpacing.lean:15`, and
`lean/YMGap/Continuum/BF4AFPhysicalSpacingToZero.lean:40`
`ShiftedAFTrajectoryIdentification` carries its identification as an input.

## Already-paid branches and retained signed debts

Do not reopen the following completed branches merely to obtain more checks:

- `lean/YMGap/Continuum/SU2QuaternionProductHeatExactAlignment.lean:59`
  `product_alignment_no_error` and `:115` `product_displacement_bound`
  already pay the full local displacement for arbitrary signed sources.
- `lean/YMGap/Continuum/SU2QuaternionProductHeatConditionalVariance.lean:166`
  `conditional_variance_angular_poincare` already gives the complete
  active-product conditional variance estimate with no link-count factor.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedVariancePoincare.lean:155`
  `projected_active_variance_source_energy_le` pays Jensen debt by SECOND
  derivatives of the COMPLETE original source, not by SAME OWN variance.

The initial-energy alternative still needs useful control of
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceTaylor.lean:42`
`varianceRemainder`. The exact growing-source pin is
`lean/YMGap/Continuum/BF4DyadicWilsonSquareVarianceTaylor.lean:257`
`paddedSquare_energy_variance`: energy=12*s*(1-w)*OWNVar+varianceRemainder.
Both signed Taylor terms, the angular-weight defect, and the OWN Ward
correction remain. The actual Ward is defined using the ORIGINAL marginal
and mean in `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceWard.lean:105`
`wardResidual`; it is not the Taylor square weight q^2. The exact weight
conversion in `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAngularMarginal.lean:104`
`angular_weight_identity` retains q*(P(q)-q), not a sign for that defect.
`lean/YMGap/Continuum/SU2QuaternionCompleteRemainderCancellation.lean:174`
`completeRemainder_cancellation` does not discard the separate OWN Ward
correction. No new identity-only leaf was added for this distinction.

## Verification boundary

Root ran one accepted focused check using `scripts/safe_lean_build.py`,
jobs=1, reserve=12 GiB, worker ceiling=20 GiB. Each launch had fresh process,
swap and memory-pressure checks: no competing compiler/runner, zero swap,
76 percent system-wide free memory. The accepted run exited zero in under
two seconds; ten axiom records were inspected, with no errors, warnings,
sorryAx, or axioms outside the permitted gate. An initial rejected run had
two rational-cast elaboration errors, repaired by existing `Q'.ofNat_nonneg`;
it is not accepted evidence. Independent mathematical/source review passed.

- Source SHA256: `c03bca8bd065c45e9251becfae89bed3a95210bc56c888ecab7b4ea3cf03d21f`.
- Accepted log: `/private/tmp/ym-macro-retention-initial-energy-20261004-2.log`.
- Log SHA256: `38f25c010080ae05de827cd202528b51f8888e20f351688f659535246abb82f8`.

Root import is registration only. No full/root build, full axiom audit,
baseline regeneration, broad guard/metrics run, CI change, or resource-limit
increase. No new sorry/axiom, frontier bundle, or weakened field. The
canonical ASCII block is unchanged and is not reprinted. Actual BF4 aggregate
control, justified scaling, nontrivial survival, physical mass calibration,
full continuum OS/QFT structure and every compact simple group remain OPEN.
