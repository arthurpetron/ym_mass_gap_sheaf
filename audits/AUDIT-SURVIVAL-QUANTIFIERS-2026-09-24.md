# Survival quantifiers and the same-carrier boundary

Source audit at `5a13687`, 2026-09-24 UTC. This is a mathematical route review,
not a new Lean proof, numerical experiment, or axiom audit. No Lean file or
canonical frontier field is changed by this checkpoint.

The original review is preserved below. The final **checked follow-up**
records subsequent Lean proofs: the relative loss budget is weaker than the
example in the review, the fixed-width calibration consumer now exists, and
the direct necessary margin bound needs no norm cap or time sampling.

## Decision

The immediate survival task needs ONE explicitly constructed observable
family with useful actual energy/variance estimates. An upper bound on the
entire family Gram matrix for EVERY coefficient vector is a sufficient,
stronger route, not a necessary prerequisite of the existing consumer.
Keep that stronger route optional. This does not relax the separate
all-centered-vectors lower-energy requirement for a mass gap.

The whole-project target is unchanged: constructive continuum Yang--Mills on
R^4 for every compact simple group, with the same nontrivial theory's full
QFT/OS and Yang--Mills field identification, isolated vacuum, and finite
positive physical Hamiltonian mass gap. None of those continuum conclusions
is established by this review.

## What the immediate consumer actually takes

| Declaration | Source | Actual input/output |
|---|---|---|
| `JointCompletion` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointPhysicalTime.lean:111` | Fixed-width original joint carrier, for every strict nome. |
| `temporalEnergy` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointTemporalEnergy.lean:98` | `B(x,x)-B(x,T^n x)` on that same carrier. |
| `temporalEnergy_linear` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointTemporalEnergy.lean:102` | For one supplied state, the n-step loss is at most n times its whole one-step loss. |
| `centered_relative_energy` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointTemporalEnergy.lean:128` | A supplied one-step bound for `center x` propagates with the SAME centered norm. No bound for other vectors is an input. |
| `timeIncrement_pin` | `lean/YMGap/Continuum/BF4WilsonTimeZeroMomentConvexity.lean:163` | The full squared jump equals twice the drop in the same expression's lag moment. |
| `timeIncrement_linear` | `lean/YMGap/Continuum/BF4WilsonTimeZeroMomentConvexity.lean:185` | Retains the whole signed time-zero expression at every lag. |
| `combinedTimeIncrement_expand` | `lean/YMGap/Continuum/BF4WilsonAllNomeMixedTimeIncrement.lean:156` | The exact signed-pair quadratic is `c*c*Daa + 2*c*d*Dab + d*d*Dbb`. |
| `combinedTimeIncrement_linear` | `lean/YMGap/Continuum/BF4WilsonSignedPairTimeControl.lean:106` | Propagates the chosen pair's full increment, not separate absolute cross-term budgets. |

For a proposed family, write `y_j = center(x_j)`, `V_j=B_j(y_j,y_j)` and
`E_j=B_j(y_j,y_j)-B_j(y_j,T_j y_j)`. The source statements above supply
`E_j(n) <= n*E_j` and, given `E_j <= delta_j*V_j`,
`E_j(n) <= n*delta_j*V_j`. They do not construct `x_j` or `delta_j`.

The sufficient remaining producer is an explicit original-observable family
with a common positive norm floor, a norm cap, and a sufficiently small
sampled loss budget on a justified width/coupling/physical-time trajectory.
For example, bounds `v <= V_j <= C`, `E_j <= delta_j*V_j`, `0 <= delta_j`, and
`n_j*delta_j*C <= v/2` would leave a response of at least `v/2` by the exact
definition of temporal energy. This last implication is an ordered algebra
calculation in this report, not a newly checked Lean declaration. Directly
proving a positive sampled response would also suffice for that response
obligation; a one-step estimate is not logically mandatory.

There is no need to prove the proposed upper bound for every coefficient
choice. There IS a need to preserve the chosen observable across regulator
removal and establish its varying-scale identification and convergence. A
separately optimized finite-cutoff vector is not automatically that family.

## Do not reverse the mass-gap quantifier

`completed_twoStep_form_gap` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointCompletedGap.lean:150`
already bounds `B(x,T^2 x)` by the stated `twoStepRate*B(x,x)` for EVERY
vector orthogonal to the actual unit. Its rate depends on nome AND width.
This is the fixed-width lower-energy side, not a physical scaling theorem.

Thus the two tasks are distinct:

* Survival: construct one nontrivial low-relative-energy family, or prove
  its positive sampled response directly.
* Gap: control every centered vector from below in energy, with adequate
  spatial/spacing behavior and physical spectral identification.

Neither task supplies the other. A full-family UPPER Gram bound is not the
gap's all-vector LOWER bound, and a single slow vector does not prove a gap.

## No automatic join to the guarded physical-rate ceiling

`logRate_le_of_sampled_response` at
`lean/YMGap/Continuum/BF4WilsonSurvivalPhysicalRateCeiling.lean:149` consumes
one centered vector, a rational norm cap and positive sampled-response floor.
It does not consume a full-family Gram estimate. But its local carrier `V`
is the guarded `UnionCompletion`, not the fixed-width `JointCompletion`.

Its declarations at
`lean/YMGap/Continuum/BF4WilsonSurvivalPhysicalRateCeiling.lean:45` retain
`heatRatio w <= 1/2`, `heatRemainderBound w < 1`, and the entropy guard, in
addition to strict nome. The theorem also requires supplied physical spacing,
spacing-to-zero and its explicit threshold. `UnionCompletion` is defined at
`lean/YMGap/Continuum/BF4WilsonSpatialUnionSeminorm.lean:139`.

Consequently the all-nome fixed-width increment theorem is NOT by itself
an input of the guarded union theorem. A proof must establish the relevant
same-object transport and trajectory guards, or use an appropriate separately
proved physical-rate consumer. This audit supplies neither. The resulting
ceiling is on the certified logarithmic rate, not an identified Hamiltonian
spectral edge.

`nome_gt_of_sampled_response` at
`lean/YMGap/Continuum/BF4WilsonGuardedCouplingEscape.lean:58` also prevents
treating a fixed guarded coupling subinterval as an automatic survival
trajectory with uniformly bounded norms. It does not prove that nomes tend
to one or identify an entropy boundary with a physical critical point.

## Use the full edge form; do not seek a false finite eigenrelation

`energy_identity` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:253`
identifies twice the original energy with the complete edge-weighted jump
square. Both endpoint sources are already present. This formula needs no
separate cancellation of a bare-energy correction.

In contrast, `energy_eq_bare_add_correction` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean:144`
adds and subtracts the bare square of `a*f`. Its correction must be retained
WHEN USING THAT SPLIT. The actual evolution is `terminalMessage_next` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:57`, together
with `transferStep_eq_productMap` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferPositive.lean:48`:
`P(V*g_n)=g_(n+1)`, not a supplied stationary relation `P(V*g_n)=V*g_n`.

The conditional-message certificates likewise do not close the analytic
join: `conditionalMessage_lowerCertificate` and
`conditionalMessage_capCertificate` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialConditionalMessage.lean:103`
and `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialConditionalMessage.lean:117`
bound the terminal message by one erased-factor normalizer.
They do not bound cross-coordinate influence or the full endpoint `V*g` by
that same normalizer.

## Existing estimates are not yet a survival producer

`family_joint_variance_floor` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilyVariance.lean:136`
is a genuine fixed-nome floor for the actual centered family. However,
`computedLossRatio_ge` and `computedLossRatio_no_linear_scaling` at
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteAffineCalibrationObstruction.lean:102`
and `lean/YMGap/Continuum/BF4ExactSlabPlaquetteAffineCalibrationObstruction.lean:139`
show that the existing single-plaquette loss budget divided by
THIS floor is not a small spacing-scaled estimate. These are facts about
the available certificate numbers, not a refutation of actual survival.

The next analytic work is therefore to select a justified original Wilson
observable family and estimate its actual variance and full temporal form
together. Preserve its signed mixed terms. A new full-matrix certificate,
generic source-free tensorization, or source-curvature wrapper is not a
substitute for that producer. No candidate family is claimed proved here.

## Verification boundary

Root read the cited source statements. Sol independently checked the
terminal evolution, available energy bounds and survival quantifiers; Luna
reviewed the distinct carriers and diagram boundaries. The report corrects
the stronger-than-needed default search target, without changing any formal
statement. Documentation diff/whitespace checks only; no compiler, full-tree
build, axiom audit, guard or progress-metric script was run. No new `sorry`,
axiom, physical instance, or continuum closure is claimed.

## Checked same-carrier survival and calibration follow-up

2026-09-24 UTC, following the source review and full-product cancellation
checkpoint `ffcb846`. This section records new narrow kernel checks, not a
full-root build or a physical continuum theorem.

### Actual relative-energy implication

Use the original all-nome fixed-width `JointCompletion`, its constructed
centering map, pairing B and discrete transfer T. For `y=center x`, put
`N=B(y,y)` and `E_1=N-B(y,T y)`. The supplied input `E_1<=delta*N` now gives

    n*delta+theta <= 1  ==>  theta*N <= B(y,T^n y).
    0 <= theta, v <= N  ==>  theta*v <= B(y,T^n y).

Thus a positive floor v and positive theta produce an actual original
connected-response floor. The budget does NOT require the stronger
`n*delta*C<=v/2` from the original prose example. There is no norm cap in
this implication. The observable and relative-energy estimate are inputs,
not constructed here for changing nome/width/spacing.

| Declaration | Source | Checked output |
|---|---|---|
| `response_ge_fraction_of_relative_energy` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointEnergySurvival.lean:97` | Relative loss budget retains the SAME norm fraction. |
| `response_floor_of_relative_energy` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointEnergySurvival.lean:112` | Supplied norm floor gives the response floor. |
| `centered_response_floor` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointEnergySurvival.lean:126` | Pins that floor to the existing `completedCenteredScalar`. |

### Cancel the norm before estimating a rate

At lag two the same bound gives `(1-2*delta)*N<=B(y,T^2 y)`. The existing
completed strict form bound gives `B(y,T^2 y)<=q*N`, where q is the actual
certified `twoStepRate(w,width)`. A supplied POINTWISE rational witness
`0<v<=N` permits positive-factor cancellation without forming a real
reciprocal or choosing a quotient representative as data. Consequently:

    1 - q <= 2*delta,
    (1-q)/a <= (2*delta)/a   for supplied positive two-step spacing a.

| Declaration | Source | Checked output |
|---|---|---|
| `twoStepRate_ge_of_relative_energy` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointEnergySurvival.lean:140` | `1-2*delta<=q` from one actual nonzero centered state. |
| `margin_le_twice_relative_energy` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointEnergySurvival.lean:155` | `1-q<=2*delta`; no cap, uniform floor or sampling premise. |
| `marginRate_le_of_relative_energy` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointEnergySurvival.lean:167` | Same necessary inequality divided by supplied positive spacing. |

This is an UPPER constraint on a certified margin, not a proof of an
EVERY-vector lower energy estimate or the location of a physical spectrum.
The pointwise floor cancels from this necessary constraint; a surviving
observable/norm floor is still required for continuum nontriviality.

### Sampled-response consumer on the actual fixed-width carrier

The historical guarded `UnionCompletion` theorem has not been transported
or silently identified with `JointCompletion`. A separate counterpart is
now proved directly on the latter carrier. Let x be orthogonal to its actual
unit, with `B(x,x)<=C`, and supply `f<=B(x,T^(2*n) x)` with `f>0`, where
`n=floorLatticeSteps A j t`. The squared-norm decay theorem then gives
`f<=q^n*C`. The existing rational sampler/Bernoulli bounds imply

    (1-q)/a <= responseMarginCeiling C f hf t ht = 2*C/(f*t),

under `a<=t/2`. Here `a=A.spacing j` is explicitly the spacing of TWO
discrete time steps; it must not be silently read as one-step spacing.
An explicit threshold from the supplied spacing-to-zero modulus and
geometric cutoff forces `q>=1/2`, thereby excluding `q=0` before the
logarithm is constructed. The exact rate logarithm `-log(q)/a` is then at
most `c94*responseMarginCeiling C f hf t ht`.

| Declaration | Source | Checked output |
|---|---|---|
| `response_power_floor` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointSurvivalCalibration.lean:54` | Actual even response and norm cap give `f<=q^n*C`. |
| `margin_le_of_sampled_response` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointSurvivalCalibration.lean:65` | Certified margin is at most spacing times the computed ceiling. |
| `marginRate_le_of_sampled_response` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointSurvivalCalibration.lean:77` | The divided margin ceiling. |
| `transferLogRate_log_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointSurvivalCalibration.lean:107` | Exact scalar identification with negative logarithm of q. |
| `survivalRateThreshold` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointSurvivalCalibration.lean:120` | Computed threshold, retaining C, f, t and spacing modulus. |
| `halfRate_of_sampled_response` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointSurvivalCalibration.lean:126` | Positive sampled floor beyond that threshold implies `1/2<=q`. |
| `logRate_le_of_sampled_response` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointSurvivalCalibration.lean:161` | Ceiling on the exact certified logarithmic rate per two-step spacing. |

The absolute-response consumer still takes a norm cap. The direct
relative-energy constraint above does not. Neither constructs an actual
physical Hamiltonian or identifies q with its spectral edge.

### Next producer and source-reviewed alternatives

The first-order cancellation theorem
`padded_plaquette_energy_le_angular_add_quadratic` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceTaylor.lean:169` still needs
useful control of its COMPLETE source-dependent angular-plus-remainder
budget relative to the SAME centered variance on ONE justified changing-scale
family. No such family or quantitative estimate is supplied by this follow-up.

The existing finite signed filters are not an automatic replacement:
`orbitSum_pairing` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointBilinearTime.lean:163`
preserves all signed cross terms, while `orbitSum_twoStep_form_gap` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointBilinearTime.lean:193`
retains the SAME universal upper rate and does not assert that the filtered
state is nonzero. `evenResponse_geometric_lower` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointOrbitResponse.lean:101`
still requires a supplied initial relative lower response. The constructed
`centralExcitation_norm_floor` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointCentralExcitation.lean:67`
is genuine, but `centralExcitation_twoStep_bound` at that file's line 96 is
an upper response bound, not the missing near-one lower estimate. This is
a source review of the available declarations, not a theorem that every
possible filter-based analytic argument is impossible.

### Verification and unchanged boundary

Final accepted commands, each serialized with one 4 GiB worker:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointSurvivalCalibration.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointSurvivalCalibration.olean --check-worker-limit-gib 4 --log-file /tmp/ym-gap-joint-survival-calibration-check-2.log
python3 scripts/safe_lean_build.py --jobs 1 --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointEnergySurvival.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointEnergySurvival.olean --check-worker-limit-gib 4 --log-file /tmp/ym-gap-joint-energy-survival-check-2.log
```

Both commands exited zero. Each final log contains six load-bearing theorem
gates, all within `{propext, Quot.sound}`, and no error/warning/sorryAx.
Calibration check 1 failed on missing identifiers and elaboration timeouts;
it is NOT verification evidence. Sol repaired that file and reviewed the
filtering alternative; Luna independently checked the same-object, sign,
quantifier and spacing boundaries. Root proved and checked the direct
positive-norm cancellation consumer. `YMGap.lean` imports EnergySurvival,
which imports Calibration; no full-root build/audit/guard was run.

No new hole, axiom, canonical-field weakening or continuum closure. The
actual changing-scale producer, separate EVERY-vector spatial/spacing gap,
full SAME-theory QFT/YM fields, physical Hamiltonian mass and every compact
simple group remain open. The whole-project goal is unchanged.
