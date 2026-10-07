# Adaptive signed-score payment (2026-10-07)

Whole-project goal unchanged and OPEN: constructive nontrivial continuum
Yang--Mills on R^4 for every compact simple group, SAME-theory QFT axioms
and a positive physical Hamiltonian mass gap.

Previous goal turn: PROGRESS. Commit `8e80f14a` proves exact original
signed-bulk reassembly, not a scaling-family estimate.

## Decision before implementation

Consumer: `BF4ExactSlabFixedSpatialLastStepExactScoreCost.lean`,
`original_block_exact_score_cost_relative_tolerance`. The new exact identity
`BF4ExactSlabFixedSpatialLastStepSignedScoreEnergy.lean`,
`exactScoreSignedBulk_energy_split`, leaves original energy plus
`Z0*(1-w)*(sigma*L0-2*J-E)`.

Proposed next proposition: for fixed actual original data with positive
`Z1*B`, construct a positive rational sigma and an all-later reciprocal-degree
onset making this signed correction at most `epsilon*Z1*B`. Sigma must be
chosen BEFORE the degree; it cannot depend circularly on that degree's score.
This would remove the auxiliary signed-score overhead as an independent
analytic prerequisite, leaving the SAME genuine interacting-energy estimate.

Available inputs: the original positive terminal window; constructive
`QuaternionHaarSupportedPolynomialInterval.polynomialInterval` for the literal
score; `QuaternionHaarRelativeReciprocalDualNorm.reciprocal_dual_weighted_norm_le`;
the actual per-plane transmitted-relative correction modulus in
`BF4ExactSlabFixedSpatialLastStepRelativeCorrection`; and positive original
partition comparison. No scaling survival or energy smallness is assumed.

Predicted argument: certify `|G*S|` by a computed finite cap independent of
reciprocal degree. Weighted Young gives
`Debt <= (sigma+tau)*L0+(1/tau)*E`, with tau>0. Choose tau=sigma from
the actual surviving target and the finite cap, then choose the correction
degree. All chosen constants remain data. The cap may depend badly on
cutoff, width, source and depth; no parameter-uniform bound is claimed.

Decisive checks: preserve original `Vbar^2`, both partitions and the literal
reciprocal correction; confirm sigma precedes degree; do not divide by a
zero transmitted square. Zero sources remain covered separately by the
existing transmitted-null theorem. Paying approximation overhead does NOT
pay original energy or construct a changing-action all-vector comparison.

Budget: two serialized focused checks, one 20-GiB worker and a 12-GiB reserve;
no full build/audit or numerical sweep. Abandon/revise if the degree-independent
cap requires an unconstructed analytic premise or changes an original object.

## Outcome

PROGRESS: the finite approximation overhead is now constructed, including
the actual zero-target branch below. It is no longer an independent
smallness premise for this fixed-parameter consumer. No broad chart claim
or changing-family estimate is closed.

## Next degeneracy decision before implementation

The positive actual target guard can be removed if a zero weighted transmitted
square is PROVED to imply genuine Haar nullity. The existing positive spatial
floor and square certificate give `c*H[b^2] <= ell[b^2]`, with c>0. A zero
right-hand side then gives zero bare square; finite Haar radical descent and
supported-to-arbitrary insertion transport give actual Haar nullity. Only
after that proof may the existing exact-score null theorem supply the zero
branch (sigma=1, onset=0). Positive Z1 follows from terminal-message pairing.
This is decidable rational branching, not a constructive choice on continuum
states. Consumer: remove only the finite payment's positive-Q premise;
do not infer continuum nontriviality or discard a positive-norm fringe state.
Add one serialized generic-leaf check and one final actual consumer check if
this short argument implements; abandon the guard removal if nullity needs
an unproved premise. Earlier failed elaboration checks are not proof evidence.

## Checked mathematical output

Write `h=1-w`, `Q=Z1*B`, with the SAME original terminal source, action,
partitions and reciprocal correction defined in the preceding audit. For
every supported finite source and epsilon>0, a positive rational sigma and
an explicit onset are constructed such that for every k beyond the onset:

```
exactScoreSignedBulk_sigma(k+1)
  <= Z0*energy(A,phi_(k+1)) + epsilon*(Z1*B).
```

The degree-independent cap M is computed from the literal polynomial score,
the actual positive terminal floor and `H[Vbar^2]`. For Q>0:

```
Debt <= 2*sigma*M + (1/sigma)*(eta*B),
sigma = costTolerance (2*Z0*h*M) ((epsilon/2)*Q),
eta = correctionBulkTolerance ((epsilon/2)*sigma),
onset = lastStepRelativeCorrectionCutoff (correctionPlaneTolerance eta).
```

Arguments suppressed in these formulas are the unchanged original nome,
width and positivity witnesses. Sigma precedes onset/degree; it is an
auxiliary Young coefficient, not string tension or bare gauge coupling.
There is no division by B or Q. The signed Young estimate is proved before
discarding the favorable negative correction square.

For the nonpositive-Q branch, actual Z1>0 and B>=0 prove Q=0, hence B=0.
The original spatial floor proves zero bare Haar square, radical descent
gives nullity under supported insertions, and actual tail integration
extends it to arbitrary insertions. Only THEN is the existing signed-bulk
null theorem used. Sigma=1 and onset=0 suffice; original energy positivity
closes the bound. No source-survival hypothesis is required by the total
finite construction, and no nonzero excitation is inferred from it.

Exact source pins:

- `lean/YMGap/Continuum/QuaternionHaarFiniteReciprocalScoreCap.lean:41`,
  `computedScoreCap`; `:65`, `reciprocal_score_finite_cap_le`; `:138`,
  `signed_debt_le`.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAdaptiveSignedScorePayment.lean:93`,
  `originalScoreCap`; `:120`, `original_signed_debt_le`; `:277`,
  `adaptiveSignedScorePayment`. `:249`, `signedScorePaymentBound`, merely
  names the literal predicate to keep witness generation from unfolding
  the action; `:266`, `SignedScorePayment`, returns sigma and onset as data.
- `lean/YMGap/Continuum/QuaternionHaarPositiveWeightNullReflection.lean:42`,
  `haar_null_of_positive_weight_square_zero`, reuses the existing public
  floor-insertion theorem and finite Haar radical, not a new null premise.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTotalSignedScorePayment.lean:62`,
  `original_weighted_square_zero_null`; `:76`, `totalSignedScorePayment`.

## Continue at the genuine analytic producer

M and onset retain source, cutoff, width, depth and coupling dependence.
This constructs fixed-parameter approximation payment, not an AF-uniform
diagonal modulus or the estimate `Z0*energy <= c_cost*Q`. The original
cleared-cost consumer still needs its actual drift-depth/error onsets;
the selected-source cost is not the all-vector RG two-step comparison.

Reuse the existing SAME-action angular commutation and paired derivative:
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularCommutation.lean:59`,
`productMap_angular_carrier`, and
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivative.lean:80`,
`lastStepSourceDerivative_expansion`, `:159`,
`lastStep_sourceDerivative_carrier`. These retain COMPLETE D(V*c) and
D(V*a), including the signed action contribution. Their useful size in the
same surviving quadratic form is still unsupplied. Do not reopen the exact
identity or replace it by the already-refuted full historical noise ceiling.
Independent AF survival, an actual all-vector comparison/useful delta budget,
physical/volume control, SAME limiting QFT and every group remain OPEN.

The user's lattice-measurement note changes only scope checks and diagnostics;
its primary-source review is
`audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`. Numerical channel
masses, smooth Riemann sums and area laws are not substituted for these inputs.

## Verification boundary

Final focused checks of the four new targets PASS. Their 8 printed axiom
gates are exactly within {propext, Quot.sound}. The checked predecessor
`LastStepSignedScoreEnergy` was emitted separately to supply its import.
Local definition opacity repaired structure-generation expansion; no
heartbeat limit was raised. Earlier syntax/support/namespace and whnf
failures were repaired; their elaboration-generated sorryAx outputs are NOT
proof evidence. No source sorry, new axiom or classical input was introduced.

All launches were serialized monitored checks, one 20-GiB-capped worker,
12-GiB reserve, fresh dynamic preflights and zero swap. No full-root/tree
build or audit and no hashed axiom-baseline refresh. Root imports are
registered, not a claim that the entire root was rebuilt.

Final logs and SHA-256:

- `/private/tmp/ym-oct7-finite-reciprocal-score-cap.log`:
  `e1788688c16727cacb790f988c49be856e12dcc3547b8a2384fc03c11393408b`.
- `/private/tmp/ym-oct7-adaptive-signed-score-payment.log`:
  `6ac29ff290591ba0de12ae023ad0ef0d1389db8590c56857e91871bb51d689d3`.
- `/private/tmp/ym-oct7-positive-weight-null-reflection.log`:
  `535204f878e6a0cbab16481ea27b275cd05d0e5a894eb961801e4cc40a253aa4`.
- `/private/tmp/ym-oct7-total-signed-score-payment.log`:
  `f7db05a7f47b8f17b99fa3b400626d6bed77e6e719f249e71399cf242d0ac75f`.
