# Relative RG dissipation and ordinary budget (2026-10-07)

Whole-project goal unchanged and OPEN: constructive nontrivial continuum
Yang--Mills on R^4 for every compact simple gauge group, the required
SAME-theory QFT structure and a positive physical Hamiltonian mass gap.

Continuation of `8a347c79`. This checkpoint proves a better sufficient
comparison/budget reduction, not its Yang--Mills analytic instance.

## Relative comparison on the actual completed carriers

Write A for the original fine squared norm, F for its actual time-two squared
norm, B for the mapped coarse squared norm and C for its actual time-one
squared norm. The required estimates are

```
B <= A,       F <= delta*A+(1-delta)*C,       C <= rC^2*B.
```

For `0<=delta<=1`, `0<=rC<=1`, these give
`F <= alpha*A`, with `alpha=delta+(1-delta)*rC^2`.
The existing SAME-carrier recovery gives rate `(3+alpha)/4` and margin
`(1-delta)*(1-rC^2)/4`.

- `lean/YMGap/Continuum/BF4WilsonAllNomeRGRelativeDissipation.lean:40`,
  `relativeFactor`; `:42`, `relativeFactor_error`: its additive error is
  exactly `delta*(1-rC^2)`, with kappa=1.
- Same file `:102`, `relative_comparison_iff_dissipation`: the signed
  comparison is equivalent to `(1-delta)*(A-C) <= A-F`.
- Same file `:123`, `twoStepFactor_of_relative_comparison`; `:152`,
  `contraction_of_relative_comparison`: the actual original completed fine
  and coarse inner products/time operators are used. No lower norm bound,
  map linearity or norm inverse is assumed. The two-step factor theorem
  itself needs only `delta<=1`; recovery adds the stated sign/rate guards.
- Same file `:50`, `relativeFactor_nonnegative`; `:56`,
  `relativeFactor_le_one`; `:70`, `relativeRate_margin`: factor caps and
  recovered margin are proved, not independent numerical assumptions.

This removes an unnecessary coercivity demand: directions sent to zero by
the map can have positive fine norm, provided their actual time-two norm is
at most delta times that norm. It does NOT say the full new hypothesis
package follows from the old `ApproxRgIntertwiner` package. Its relative
comparison is a separate analytic obligation; old canonical fields remain.

## The computed upper margin pays the dyadic error weight

Use the existing recurrence at kappa=1, with
`epsilon_n <= delta_n*(1-r_n^2)`, nonnegative epsilon and delta.
The already proved OWN computed margin ceiling gives
`1-r_n <= (1-seed)*2^(-n)`. The polynomial inequality
`1-r_n^2 <= 2*(1-r_n)` then yields

```
2^n*effectiveDefect_n <= 2*(1-seed)*delta_n.
```

Thus ordinary prefix sums `sum_{k<n} delta_k <= D` feed the EXISTING weighted
budget with `S=2*(1-seed)*D`. The existing sufficient seed floor becomes
`(1-seed)*(seed-D)`, positive when `D<seed<1`.

- `lean/YMGap/Continuum/BF4WilsonAllNomeRGDissipationBudget.lean:66`,
  `weightedEffectiveDefect_le_relative`: no all-scale contraction, rate cap
  or positive lower margin is a premise of the weight cancellation.
- Same file `:103`, `relativeError_summable`: joins ordinary prefix sums to
  the existing `RgErrorSummable` predicate, with explicit sign guards.
- Same file `:132`, `seedFloor_relativeBudget_eqv`; `:152`,
  `seedFloor_relativeBudget_positive`; `:161`,
  `computedMargin_lower_of_relativeBudget`: exact floor and existing lower
  margin theorem, not an assumed lower envelope.
- Same file `:178`, `relativeRate`; `:186`, `relativeError`: explicit
  recursive rates and their own errors. `:190`, `computedRate_relativeError`,
  proves literal equality to the existing computed sequence.
- Same file `:203`, `relativeRate_bounds`; `:220`,
  `relativeError_nonnegative`; `:232`, `relativeRate_margin_lower`: under
  `0<=seed<1`, `0<=delta_n<=1`, `0<=D<seed` and the supplied ordinary prefix
  budget, the constructed rates have
  `2^(-n)*(1-seed)*(seed-D) <= 1-r_n`.

No external numerical self-consistency is assumed by this specialization.
No infinite series convergence without a modulus is asserted: the required
budget and conclusion are inequalities for every finite prefix/scale.

## Original-action ingredients and prohibited replacement

The exact integrated action remains
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLayerGluing.lean:188`,
`original_twoLayer_gluing`, with `middleIntegrand` at `:61` and `gluedMiddle`
at `:73`. It retains `K01*V1*K12` under the middle Haar integral and the
outside spatial factors. Bare heat composition does not remove V1 or identify
this kernel with a separately selected coarse heat/spatial action.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalNoise.lean:138`,
`blockNoise_variance_loss`, supplies the exact finite signed identity

```
m(noise_t(g,f)) = m(g*T^(2t)(g*f^2)) - m((T^t(g*f))^2).
```

Its endpoint term is not silently identified with A above. The existing
padded-square filtered scalar already reaches the SAME completed OS response:
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:136`,
`originalOwnBlockVariance_converges`;
`lean/YMGap/Continuum/BF4WilsonAllNomeCenteredVector.lean:159`,
`centeredVector_time_pairing`;
`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedTime.lean:158`,
`completedInner_time_sum`. These fixed-parameter scalar pins do not supply
the changing-action all-vector estimate.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialConditionalNoiseVacuumObstruction.lean:44`,
`blockNoise_one`, proves exact cancellation for f=1, without support or
positivity hypotheses. Same file `:68`, `terminal_input_not_le_noise`, uses
the actual positive terminal squared mass under `0<w<1` and
`K>=headCutoff w` to rule out bounding arbitrary input mass by ANY scalar
multiple of that noise. This is NOT a vacuum-complement no-go or a theorem
about a reciprocal algorithm's actual residual. Centering eliminates this
particular example, not the remaining quantitative comparison obligation.

## Verification and next producer

Three final serialized focused checks passed 7+9+2 printed axiom gates, all
within {propext, Quot.sound}; `computedRate_relativeError` uses no axioms.
The precise dependency-complete target
`+YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget:olean` also passed.
Missing namespace/constant-polynomial elaboration failures were repaired and
are not verification evidence. Independent read-only review confirmed the
mathematics, non-circular recurrence and stated obstruction scope.

Final focused logs and SHA-256:

- `/private/tmp/ym-oct7-rg-relative-dissipation.log`:
  `81d77c6a0bfae4008ec33791cfd46885cd0e8ccbb96e52a6ed9efecff990b822`.
- `/private/tmp/ym-oct7-rg-dissipation-budget.log`:
  `a9e8565521c0b9d8473e3a0e30d224a97fa1d204c77d9b5fc1bcba24bb54cfec`.
- `/private/tmp/ym-oct7-conditional-noise-vacuum.log`:
  `189d8f75ba4e04321576ebaa91b994bb36da17d7771ac118847f785b16a038ae`.

All checks used the monitored launcher, one 20-GiB compiler, 12-GiB reserve
and current capacity checks; swap remained zero. No source holes, new axioms,
classical shortcuts, changed canonical fields or raised heartbeats. Root
imports are registered; no full-root/tree build or audit is claimed, the
hashed baseline is not regenerated, and CI remains off.

NEXT: construct an actual fine/coarse map and prove the relative dissipated-
form comparison with a useful ordinary delta prefix budget, retaining full
middle spatial action, signed terms and separately normalized OWN forms.
Independent AF window survival, justified spacing/volume control, the SAME
limiting OS/QFT theory, every compact simple group and Clay remain OPEN.
The canonical broad chart is unchanged and is not reprinted.

## Retained/fast-sector screen (2026-10-10 UTC)

SOURCE/PAPER review of the additive and relative comparisons identifies an
extra demand on a genuine zero-preserving coarse projection P. On a
positive-norm z with Pz=0, the additive comparison requires
`||T_f^2 z||^2 <= kappa*epsilon*||z||^2`; the relative comparison requires
`||T_f^2 z||^2 <= delta*||z||^2`. A fixed fast-sector bound below one alone
does not pay either shrinking error budget. The current Phi is an arbitrary
function: this is a limitation of the proposed projection, not a contradiction
in the existing structure or a constructed Yang--Mills counterexample.

With kappa>=1 and epsilon>=0, effectiveDefect>=kappa*epsilon. The finite-prefix
weighted budget in `BF4WilsonAllNomeRGComputedMargin.lean:308`,
`computedRate_contraction_of_upperComparisons`, consequently requires
`kappa_k*epsilon_k <= S*2^(-k)`. The ordinary delta prefix budget of the
relative route likewise demands more than a fixed fast-sector gap. No actual
original-OS projection/positive kernel witness is supplied by this screen.

Selected algebraic proposition: for an actual orthogonal retained/fast split,
let A=T_f^2, squared diagonal caps alpha,beta and mixed cap
`<Ar,Af>^2 <= eta^2*||r||^2*||f||^2`. A full squared-norm cap q follows from
`q>=alpha,beta` and `eta^2 <= (q-alpha)*(q-beta)`. If
`0<g<=alpha-beta`, the computed rational q=alpha+eta^2/g meets this criterion.
This permits a fixed beta<1 rather than requiring beta to vanish. Under a
fixed positive sector separation, eta_k=O(2^(-k)) would give a weighted-
summable O(4^(-k)) correction; neither bound is produced for Yang--Mills.

Decision record BEFORE implementation: prove only the root-free, zero-safe
scalar absorption and computed rational budget in EXISTING
`RCSignedPairBudget.lean`. Its prospective consumer is the existing
`BF4WilsonAllNomeRGTwoStepRecovery.vacuumSq_of_twoStepFactor:58`, once an
original-OS split and its actual estimates exist. Do not add another sector
structure or gap premise. Available inputs are constructive square order,
scalar monotonicity and polynomial identities. Test signed mixed terms, zero
sector norms/margins and eta=0. Verification budget: ROOT only, one focused
20-GiB compiler with 12-GiB reserve; no full build/audit. Abandon/revise the
analytic route if no actual OS split or small mixed bound can be produced.
The independent late H1 survival estimate and physical scaling justification
remain PRIMARY and OPEN; this algebra does not supply either.

### Observed scalar contraction

The selected algebra is now kernel-checked in EXISTING
`lean/YMGap/Continuum/RCSignedPairBudget.lean`:

- `two_cross_le_add_of_square_le_product:168` absorbs a SIGNED mixed term
  without square roots, real-order decisions or division by a sector norm.
- `twoSector_upper_of_squared_cross:200` combines the diagonal caps with
  `eta^2 <= (q-alpha)*(q-beta)` in genuine RC order. The actual orthogonal
  input split and its diagonal/mixed estimates are NOT supplied.
- `twoSectorCost:233`, `twoSectorCost_nonnegative:236`,
  `twoSectorCost_mul_gap:241` and `twoSectorCost_cap_criteria:247` construct
  eta^2/g as rational data and prove the resulting cap criterion whenever
  `0<g<=alpha-beta`. This does NOT assert q<1 without further smallness.

Accepted focused command:

```
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --reserve-gib 12 --check lean/YMGap/Continuum/RCSignedPairBudget.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/RCSignedPairBudget.olean --log-file /private/tmp/ym-oct10-schur-pair-check1.log
```

Exit 0, no diagnostics; all six new printed gates exactly
{propext,Quot.sound}. Log SHA-256:
`427d61a4fe9e10445cd554710d93b3add4b9bcbf649441434197d33acae527df`.
Final source SHA-256:
`a74b99f6d1d91633737ac13a1d7d454f6e9ec004c8f7eb755d3e3202770f7ad7`.
Independent COMPLETE source/log and math reviews PASS, including negative m,
zero sector budgets and eta=0. Preflight: 85% memory free, zero swap and no
competing compiler/runner; one monitored worker, no raised limits.
No full root/tree build or axiom-baseline regeneration was run; CI remains off.

REVISE the prospective coarse-projection producer: test a genuine original-OS
retained/fast decomposition, not shrinking transfer norm on every discarded
mode. Demand a uniform fast-sector bound and a quantitatively small mixed
OUTPUT pairing. Generic Cauchy--Schwarz alone supplies the coefficient
alpha*beta in the SQUARED mixed cap, which does not supply a near-one full cap.
The mixed correction's O(4^(-k)) budget
does not pay any separate kappa-1 error. The existing relative route remains
available if its stronger actual comparison can be proved; no canonical field
is weakened or deleted. H1 survival, justified physical scaling and Clay stay
OPEN. No new chart-state claim, new sector bundle, hole or axiom.

### Actual split and time-frame tests (2026-10-10 UTC)

Bounded SOURCE/PAPER review; no new Lean theorem, compilation or physical
instance. The next prospective consumer remains the checked scalar join
`twoSector_upper_of_squared_cross`,
`lean/YMGap/Continuum/RCSignedPairBudget.lean:200`, followed, if a useful
strict full cap is actually produced, by `vacuumSq_of_twoStepFactor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeRGTwoStepRecovery.lean:58`.

**Existing parity split.** `sector_norm_split`,
`lean/YMGap/Continuum/BF4WilsonAllNomeSpatialAxisSwapCompletion.lean:234`,
and `sector_pairing_split`,
`lean/YMGap/Continuum/BF4WilsonAllNomeAxisEnergyProjection.lean:99`, supply
the actual orthogonal decomposition. `evenPart_time:276` and
`oddPart_time:281` in the former file show that it commutes with the ORIGINAL
completed time. Thus the output mixed pairing of even and odd parts is zero
(PAPER consequence of these declarations, not a new named gate). But no new
changing-family fast-sector rate is supplied. `completed_iterated_norm_gap`,
`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedGap.lean:214`, retains the
existing nome/width-dependent `mixRate`, defined in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferMixingRate.lean:110`.
The current diagnostic padded source is already entirely even:
`afPadded_state_even`,
`lean/YMGap/Continuum/BF4WilsonAllNomePaddedAxisSector.lean:241`.
Removing its zero odd part creates no new quantitative gain. Parity remains
a valid symmetry tool, not a produced retained/fast RG estimate.

**Time frame.** Put r=Tx, f=(I-T)x, N=||x||^2 on the SAME carrier.
`mixedMoment_nonnegative`,
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectMoments.lean:343`, gives
B(r,f)>=0 and therefore ||r||^2+||f||^2<=N. This frame is not in general
orthogonal. More importantly, positivity and contraction alone do not make
f a uniformly fast sector. Test these operator laws on the scalar positive
contraction T=lambda*I, 0<lambda<1. This is a PAPER countermodel to the generic
inference, NOT an asserted BF4 eigenstate or a Yang--Mills counterexample:

An additional orthogonal fixed-unit line gives T=diag(1,lambda), so this
test is also compatible with unit stationarity on an abstract carrier.

```
a=||r||^2=lambda^2*N          b=||f||^2=(1-lambda)^2*N
||T^2 r||^2=lambda^6*N        ||T^2 f||^2=lambda^4*(1-lambda)^2*N
m=<T^2 r,T^2 f>=lambda^5*(1-lambda)*N
||T^2 f||^2/b=lambda^4        m^2/(a*b)=lambda^8
```

For N>0 these two ratios tend to one as lambda tends to one. Taking the
smallest diagonal caps alpha=beta=lambda^4, the scalar Schur criterion needs
q>=2*lambda^4, which exceeds one near lambda=1. Increasing alpha to introduce
a positive separation g cannot improve this cap. This diagnoses that
sufficient criterion on the proposed frame; it does NOT prove that the
actual full scalar operator lacks its existing strict cap lambda^4<1.

Using the original deficit d=N-||Tx||^2=(1-lambda^2)*N instead gives the valid
PAPER inequalities ||T^2 f||^2<=d/4 and m<=d/2. They follow respectively from
4*lambda^4*(1-lambda)^2<=1-lambda^2 and
2*lambda^5*(1-lambda)<=1-lambda^2. But m/d tends to 1/2 and d/N tends to zero.
Without an independent lower deficit fraction this does not yield a uniform
strict cap; it merely rearranges the existing time contraction.

Decision: STOP these two substitutions as automatic fast-sector producers.
Retain symmetry only where it gives a real source-specific reduction; demand
an original-action quantitative diagonal or mixed-output estimate before
another RG implementation. PRIMARY stays the signed late H1 estimate on a
justified changing family. Independent source/math screens agreed with the
scope; no new interface, hole, canonical field or displayed proof-state change.
