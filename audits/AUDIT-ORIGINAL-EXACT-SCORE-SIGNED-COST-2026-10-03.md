# ORIGINAL exact-score COMPLETE signed-cost reduction

## Outcome and scope

PROGRESS after `cdca3f5`: a shorter valid route avoids inserting Jensen's
inequality into the reciprocal-gradient estimate. It keeps the literal
output score square, rather than paying the larger conditional source
second moment. Thus the entire conditional-variance debt and its auxiliary
reference Poincare estimate are unnecessary on this direct route.

This does NOT remove the score itself or either signed Taylor remainder.
It supplies no useful bound on their combined signed bulk relative to the
surviving norm on a changing family. The whole-project goal remains OPEN:
nontrivial constructive continuum Yang--Mills on R^4 for every compact
simple group, required SAME-theory QFT axioms and a finite positive physical
Hamiltonian gap. No exact canonical chart claim changes or frontier atom
closes; the canonical fenced chart is unchanged and is not reprinted.

## 1. Actual objects and the mathematical simplification

At the original source/action/transfer cutoff K, define the existing objects

```text
A = terminalMessage(n+r+1),   b = T^(r+1)(terminalMessage(n)*psi),
G = blockReciprocal(k+1),     phi = G*b,
q = projectedEndpointSource(A) = Vbar*A,
S_alpha = A*D_alpha(b) - b*D_alpha(A),
Z0 = weightedMass(A^2),      Z1 = weightedMass(A*T A),
B = weightedMass(b^2).
```

The literal reciprocal identity is A*D(phi) = G*S + e, where e is the
existing reciprocal correction. A positive asymmetric square triangle gives

```text
H[Vbar^2 * (A*D(phi))^2]
  <= (1+sigma)*H[Vbar^2*G^2*S^2]
       + (1+1/sigma)*H[Vbar^2*e^2],       sigma > 0.
```

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepExactScoreBudget.lean:71`
`exact_score_reciprocal_plane_le` proves this for supported actual A,b and
arbitrary certified W in place of Vbar^2. It uses the actual derivative
identity, supported score/correction and polynomial coefficient recoding;
no conditional variance or requested relative bound is assumed.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepExactScoreBudget.lean:112`
`exactScoreAngularBudget` sums the literal score square over the actual
active links and six rotations with multiplier (1+sigma)*Vbar^2*G^2.
`exactScoreJensenGap` (:129) sums the corresponding ORIGINAL own conditional
variance with the same multiplier. `exactScoreAngularBudget_gap_pin` (:182)
proves the exact algebraic identity

```text
projectedDerivativeAngularBudget
  = exactScoreAngularBudget + exactScoreJensenGap.
```

The actual terminal/output step pins identify the score with the conditional
mean of the complete projected source. `exactScoreAngularBudget_le_projected`
(:225) proves the order for supported original psi and sigma >= 0 from the
existing positive conditional-square certificate. No source-chart cutoff L
is required on the new direct path.

## 2. Forward bound joins the backward COMPLETE-cost consumer

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepExactScoreCost.lean:78`
`original_block_exact_score_plane_le` instantiates the plane bound with
literal original A,b and W=Vbar^2, using the constructed q=Vbar*A pin.
`original_block_exact_score_angular_le` (:132) sums the actual planes, pays
reciprocal correction relatively with the existing computed onset, and
constructs inactive-plane zeros from actual fringe independence.

`exactScoreSignedBulk` (:218) retains the original signed expression

```text
Z0 * [(1-w)*exactScoreAngularBudget + Rmixed - Rdiagonal].
```

The two remainders are the SAME original `pairRemainder` terms at q,phi,K;
their signs are unchanged. `exactScoreSignedBulk_le_projected` (:232)
proves that the COMPLETE new bulk is no larger than its predecessor.

`original_block_exact_score_energy_le` (:251) uses the actual original
energy Taylor identity and original partition-ratio estimate to pay
reciprocal error against SAME Z1*B. `original_block_exact_score_cost_relative_tolerance`
(:324) composes actual reconstruction and boundary estimates:

```text
clearedRayleighCost(A,b)
  <= exactScoreSignedBulk(k+1) + ((zeta+delta)+epsilon)*(Z1*B).
```

The three positive tolerances have explicit guards:

- `blockConditionalDriftDepthCutoff ... delta <= n+(r+1)-1`;
- `blockEnergyRelativeErrorCutoff ... epsilon <= k+1`;
- `asymmetricCorrectionCostCutoff sigma ... zeta <= k`.

The statement also retains 0<w<1, sigma>0, relativeCutoff(w,32)<=K,
positive link count and supported original psi. All statements are finite,
with fixed-parameter error onsets; no spacing/volume/coupling uniformity is
claimed. There is no inversion of B, which can be zero, and no stationary
terminal eigenpin. The original partitions Z0 and Z1 remain distinct.

## 3. Repointed mathematical frontier

Prioritize the smaller `exactScoreSignedBulk` relative to SAME Z1*B,
jointly across the needed original time window on a JUSTIFIED changing
family. Preserve cancellation with BOTH original signed Taylor terms.
Do not enlarge the score by Jensen or a coarse Noise*cap estimate unless
that enlargement is independently useful to the downstream estimate.
The source-Poincare/Gamma(Q) branch remains checked, but optional.

The original window bridge is already written:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighWindow.lean:89`
`clearedRayleighCost_window_pin` identifies cleared cost with the original
normalized adjacent centered-window difference times Z0*Z1.
This identifies the consumer, not a supplied rate. The signed bulk bound,
changing-family/spacing control, physical calibration, nontrivial continuum
survival, full QFT axioms and every-group passage remain OPEN.

The weaker aggregate backward consumer is
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`
`original_window_budget_macro_ratio`: an eventual bound on TWICE the
original normalized signed sum at lags t=u,...,2u-1 by (1-kappa) times the
original own variance at u implies the SAME dyadic response ratio.
`originalWindowCost` (:198) retains each lag's DISTINCT Z0,Z1 and one
chronological stage OWN center. `originalWindowCost_converges` (:220) is
fixed-member convergence only. This consumer allows joint signed control;
separate absolute score/remainder estimates or source squares need not be
introduced as stronger prerequisites. The eventual aggregate estimate is
an explicit hypothesis, NOT a proved producer.

## 4. Verification boundary and independent reviews

Two final focused checks completed successfully; all 11 printed gates use
only `{propext, Quot.sound}`. Accepted logs contain no warning, error or
`sorryAx`. Source scans found no sorry/admit, new axiom, Classical,
native_decide, unsafe or noncomputable. The initial helper check failed on
local elaboration of a reduced zero sum and unspecified cutoff proof
arguments; both were made explicit without changing mathematical statements.

```sh
python3 scripts/safe_lean_build.py --jobs 1 --reserve-gib 12 \
  --check-worker-limit-gib 20 --status-seconds 300 \
  --log-file /tmp/<accepted-log> \
  --check lean/YMGap/Continuum/<module>.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/<module>.olean
```

| Module | Gates | Accepted log |
| --- | ---: | --- |
| BF4ExactSlabFixedSpatialLastStepExactScoreBudget | 5 | `/tmp/ym-exact-score-budget-20261003-2.log` |
| BF4ExactSlabFixedSpatialLastStepExactScoreCost | 6 | `/tmp/ym-exact-score-cost-20261003-1.log` |

Fresh process/swap/pressure checks preceded every compiler launch. No
competing compiler/runner/test was found; swap was zero, free memory 76%.
ONE compiler, 20 GiB worker limit and 12 GiB reserve throughout. Both
accepted checks completed in their initial calls; no heavy/full job ran.

Independent Sol semantic reviews PASS: literal score and all original
weights/messages/partitions are retained, inactive zeros are constructed,
both signed remainders are unchanged, and k versus k+1/depth guards match
the consumed estimates. Luna evidence QA PASS: 5+6 gates, source/log hashes,
declaration anchors and canonical chart fence. Source review is separate
from kernel verification. Root imports registered only; full root/tree
build, full axiom audit, guard and metrics runs NOT performed. No sorry,
new axiom, frontier-field weakening or CI change; CI remains manual-only.

### SHA-256 of final sources

```text
2f6d7f5b082ab677f388c8cd0b42c26b0f24277fbdb2883f28b27909c8127c09  BF4ExactSlabFixedSpatialLastStepExactScoreBudget.lean
80c295a33227f63f985067cbac30bcde4ab2bb579eeca845abed896d0135f93c  BF4ExactSlabFixedSpatialLastStepExactScoreCost.lean
```

### SHA-256 of accepted logs

```text
675575b537d4d04f5d156d61659352368075e20654042f86bfa5aa4fa9334cfb  ym-exact-score-budget-20261003-2.log
5613ca913a97766f3953894819b1f2b2ff53af8993f082a735fd8490018ea54b  ym-exact-score-cost-20261003-1.log
```
